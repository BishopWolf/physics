// gr_vulkan.c — minimal Vulkan compute host for general-relativity tensor
// contractions.  Dispatches shaders/tensor.comp over a lattice of spacetime
// points and reports the maximum |Ricci|, |R| and |G| it finds.
//
// Build:  make
// Run:    ./gr_vulkan shaders/tensor.comp.spv
//
// Requires libvulkan (runtime picks the ICD, e.g. RADV on AMD).

#include <vulkan/vulkan.h>

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CHECK(x)                                                              \
    do {                                                                      \
        VkResult r_ = (x);                                                    \
        if (r_ != VK_SUCCESS) {                                               \
            fprintf(stderr, "VkResult %d at %s:%d\n", (int)r_, __FILE__,      \
                    __LINE__);                                                \
            exit(2);                                                          \
        }                                                                     \
    } while (0)

typedef struct {
    int   metricId;
    float massM;
    float lambdaC;
    float h;
    float lo[4];
    float stepv[4];
    int   grid[4];
} PushParams;

static VkInstance            gInstance;
static VkPhysicalDevice      gPhys;
static VkDevice              gDev;
static VkQueue               gQueue;
static VkCommandPool         gPool;
static VkBuffer              gBuf;
static VkDeviceMemory        gMem;
static VkDescriptorSetLayout gDsl;
static VkDescriptorPool      gDpool;
static VkDescriptorSet       gDset;
static VkPipelineLayout      gPl;
static VkPipeline            gPipe;

static uint32_t computeQueueFamily(VkPhysicalDevice pd)
{
    uint32_t n = 0;
    vkGetPhysicalDeviceQueueFamilyProperties(pd, &n, NULL);
    VkQueueFamilyProperties *q = calloc(n, sizeof *q);
    vkGetPhysicalDeviceQueueFamilyProperties(pd, &n, q);
    uint32_t idx = UINT32_MAX;
    for (uint32_t i = 0; i < n; ++i) {
        if (q[i].queueFlags & VK_QUEUE_COMPUTE_BIT) {
            idx = i;
            break;
        }
    }
    free(q);
    return idx;
}

static uint32_t findMemoryType(uint32_t bits, VkMemoryPropertyFlags want)
{
    VkPhysicalDeviceMemoryProperties mp;
    vkGetPhysicalDeviceMemoryProperties(gPhys, &mp);
    for (uint32_t i = 0; i < mp.memoryTypeCount; ++i) {
        if ((bits & (1u << i)) &&
            (mp.memoryTypes[i].propertyFlags & want) == want) {
            return i;
        }
    }
    fprintf(stderr, "no host-visible coherent memory type\n");
    exit(2);
}

static void pickDevice(void)
{
    uint32_t n = 0;
    CHECK(vkEnumeratePhysicalDevices(gInstance, &n, NULL));
    if (n == 0) {
        fprintf(stderr, "no Vulkan physical device\n");
        exit(2);
    }
    VkPhysicalDevice *pds = calloc(n, sizeof *pds);
    CHECK(vkEnumeratePhysicalDevices(gInstance, &n, pds));

    int best = -1, bestScore = -1;
    for (uint32_t i = 0; i < n; ++i) {
        VkPhysicalDeviceProperties p;
        vkGetPhysicalDeviceProperties(pds[i], &p);
        if (computeQueueFamily(pds[i]) == UINT32_MAX)
            continue;
        int score = (p.deviceType == VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU) ? 2 : 1;
        if (score > bestScore) {
            bestScore = score;
            best = (int)i;
            VkPhysicalDeviceProperties props;
            vkGetPhysicalDeviceProperties(pds[best], &props);
            printf("device: %s  (Vulkan %u.%u.%u)\n", props.deviceName,
                   VK_VERSION_MAJOR(props.apiVersion),
                   VK_VERSION_MINOR(props.apiVersion),
                   VK_VERSION_PATCH(props.apiVersion));
        }
    }
    if (best < 0) {
        fprintf(stderr, "no compute-capable Vulkan device\n");
        exit(2);
    }
    gPhys = pds[best];
    free(pds);
}

static VkShaderModule loadShader(const char *path)
{
    FILE *f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "cannot open %s (run make first)\n", path);
        exit(2);
    }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (sz <= 0) {
        fprintf(stderr, "empty shader %s\n", path);
        exit(2);
    }
    void *code = malloc((size_t)sz);
    if (fread(code, 1, (size_t)sz, f) != (size_t)sz) {
        fprintf(stderr, "short read on %s\n", path);
        exit(2);
    }
    fclose(f);

    VkShaderModuleCreateInfo ci = {VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO};
    ci.codeSize = (size_t)sz;
    ci.pCode    = (const uint32_t *)code;
    VkShaderModule m;
    CHECK(vkCreateShaderModule(gDev, &ci, NULL, &m));
    free(code);
    return m;
}

typedef struct {
    int         id;
    const char *name;
    float       M;
    float       Lambda;
    double      tol;
} Case;

int main(int argc, char **argv)
{
    const char *spv = (argc > 1) ? argv[1] : "shaders/tensor.comp.spv";

    const int G[4]     = {3, 4, 3, 3};
    const uint32_t total = (uint32_t)G[0] * (uint32_t)G[1] * (uint32_t)G[2] *
                           (uint32_t)G[3];
    const int    STRIDE  = 50;
    const size_t bufSize = (size_t)total * STRIDE * sizeof(double);

    VkApplicationInfo app = {VK_STRUCTURE_TYPE_APPLICATION_INFO};
    app.pApplicationName = "gr-tensor-vulkan";
    app.applicationVersion = 1;
    app.apiVersion = VK_API_VERSION_1_2;

    VkInstanceCreateInfo ici = {VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO};
    ici.pApplicationInfo = &app;
    CHECK(vkCreateInstance(&ici, NULL, &gInstance));

    pickDevice();

    uint32_t qf = computeQueueFamily(gPhys);
    float prio = 1.0f;
    VkDeviceQueueCreateInfo qci = {VK_STRUCTURE_TYPE_DEVICE_QUEUE_CREATE_INFO};
    qci.queueFamilyIndex = qf;
    qci.queueCount = 1;
    qci.pQueuePriorities = &prio;

    VkPhysicalDeviceFeatures feats;
    vkGetPhysicalDeviceFeatures(gPhys, &feats);
    if (!feats.shaderFloat64) {
        fprintf(stderr, "this device does not support shaderFloat64, which "
                        "tensor.comp needs for double precision\n");
        exit(2);
    }
    VkPhysicalDeviceFeatures enable = {0};
    enable.shaderFloat64 = VK_TRUE;

    VkDeviceCreateInfo dci = {VK_STRUCTURE_TYPE_DEVICE_CREATE_INFO};
    dci.queueCreateInfoCount = 1;
    dci.pQueueCreateInfos = &qci;
    dci.pEnabledFeatures = &enable;
    CHECK(vkCreateDevice(gPhys, &dci, NULL, &gDev));
    vkGetDeviceQueue(gDev, qf, 0, &gQueue);

    VkCommandPoolCreateInfo pci = {VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO};
    pci.queueFamilyIndex = qf;
    pci.flags = VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT;
    CHECK(vkCreateCommandPool(gDev, &pci, NULL, &gPool));

    VkBufferCreateInfo bci = {VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO};
    bci.size = bufSize;
    bci.usage = VK_BUFFER_USAGE_STORAGE_BUFFER_BIT;
    bci.sharingMode = VK_SHARING_MODE_EXCLUSIVE;
    CHECK(vkCreateBuffer(gDev, &bci, NULL, &gBuf));

    VkMemoryRequirements mr;
    vkGetBufferMemoryRequirements(gDev, gBuf, &mr);
    VkMemoryAllocateInfo mai = {VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO};
    mai.allocationSize = mr.size;
    mai.memoryTypeIndex =
        findMemoryType(mr.memoryTypeBits, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT |
                                             VK_MEMORY_PROPERTY_HOST_COHERENT_BIT);
    CHECK(vkAllocateMemory(gDev, &mai, NULL, &gMem));
    CHECK(vkBindBufferMemory(gDev, gBuf, gMem, 0));

    VkDescriptorSetLayoutBinding bind = {0};
    bind.binding = 0;
    bind.descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    bind.descriptorCount = 1;
    bind.stageFlags = VK_SHADER_STAGE_COMPUTE_BIT;

    VkDescriptorSetLayoutCreateInfo dlci = {
        VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO};
    dlci.bindingCount = 1;
    dlci.pBindings = &bind;
    CHECK(vkCreateDescriptorSetLayout(gDev, &dlci, NULL, &gDsl));

    VkDescriptorPoolSize ps = {VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, 1};
    VkDescriptorPoolCreateInfo dpci = {
        VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO};
    dpci.maxSets = 1;
    dpci.poolSizeCount = 1;
    dpci.pPoolSizes = &ps;
    CHECK(vkCreateDescriptorPool(gDev, &dpci, NULL, &gDpool));

    VkDescriptorSetAllocateInfo dsai = {
        VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO};
    dsai.descriptorPool = gDpool;
    dsai.descriptorSetCount = 1;
    dsai.pSetLayouts = &gDsl;
    CHECK(vkAllocateDescriptorSets(gDev, &dsai, &gDset));

    VkDescriptorBufferInfo dbi = {gBuf, 0, VK_WHOLE_SIZE};
    VkWriteDescriptorSet w = {VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET};
    w.dstSet = gDset;
    w.dstBinding = 0;
    w.descriptorCount = 1;
    w.descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    w.pBufferInfo = &dbi;
    vkUpdateDescriptorSets(gDev, 1, &w, 0, NULL);

    VkPushConstantRange pcr = {VK_SHADER_STAGE_COMPUTE_BIT, 0, sizeof(PushParams)};
    VkPipelineLayoutCreateInfo plci = {
        VK_STRUCTURE_TYPE_PIPELINE_LAYOUT_CREATE_INFO};
    plci.setLayoutCount = 1;
    plci.pSetLayouts = &gDsl;
    plci.pushConstantRangeCount = 1;
    plci.pPushConstantRanges = &pcr;
    CHECK(vkCreatePipelineLayout(gDev, &plci, NULL, &gPl));

    VkShaderModule sm = loadShader(spv);
    VkComputePipelineCreateInfo cpci = {
        VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO};
    cpci.stage.sType = VK_STRUCTURE_TYPE_PIPELINE_SHADER_STAGE_CREATE_INFO;
    cpci.stage.stage = VK_SHADER_STAGE_COMPUTE_BIT;
    cpci.stage.module = sm;
    cpci.stage.pName = "main";
    cpci.layout = gPl;
    CHECK(vkCreateComputePipelines(gDev, VK_NULL_HANDLE, 1, &cpci, NULL, &gPipe));
    vkDestroyShaderModule(gDev, sm, NULL);

    const Case cases[] = {
        {0, "Minkowski (flat)", 1.0f, 0.0f, 1e-6},
        {1, "Schwarzschild (vacuum)", 1.0f, 0.0f, 1e-6},
        {2, "Schwarzschild-de Sitter", 1.0f, 0.1f, 1e-6},
    };

    int failures = 0;
    printf("\n%u lattice points per case, stride %d floats\n\n", total, STRIDE);

    for (size_t c = 0; c < sizeof cases / sizeof cases[0]; ++c) {
        PushParams P;
        memset(&P, 0, sizeof P);
        P.metricId = cases[c].id;
        P.massM    = cases[c].M;
        P.lambdaC  = cases[c].Lambda;
        P.h        = 1e-4f;
        P.lo[0] = 0.0f; P.lo[1] = 3.0f; P.lo[2] = 0.5f; P.lo[3] = 0.3f;
        P.stepv[0] = 0.1f; P.stepv[1] = 0.15f; P.stepv[2] = 0.2f; P.stepv[3] = 0.2f;
        for (int k = 0; k < 4; ++k)
            P.grid[k] = G[k];

        VkCommandBufferAllocateInfo cbai = {
            VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO};
        cbai.commandPool = gPool;
        cbai.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
        cbai.commandBufferCount = 1;
        VkCommandBuffer cb;
        CHECK(vkAllocateCommandBuffers(gDev, &cbai, &cb));

        VkCommandBufferBeginInfo cbbi = {
            VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO};
        cbbi.flags = VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT;
        CHECK(vkBeginCommandBuffer(cb, &cbbi));
        vkCmdBindPipeline(cb, VK_PIPELINE_BIND_POINT_COMPUTE, gPipe);
        vkCmdBindDescriptorSets(cb, VK_PIPELINE_BIND_POINT_COMPUTE, gPl, 0, 1,
                                &gDset, 0, NULL);
        vkCmdPushConstants(cb, gPl, VK_SHADER_STAGE_COMPUTE_BIT, 0, sizeof P, &P);
        vkCmdDispatch(cb, (total + 63u) / 64u, 1, 1);

        VkMemoryBarrier mb = {VK_STRUCTURE_TYPE_MEMORY_BARRIER};
        mb.srcAccessMask = VK_ACCESS_SHADER_WRITE_BIT;
        mb.dstAccessMask = VK_ACCESS_HOST_READ_BIT;
        vkCmdPipelineBarrier(cb, VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                             VK_PIPELINE_STAGE_HOST_BIT, 0, 1, &mb, 0, NULL, 0,
                             NULL);
        CHECK(vkEndCommandBuffer(cb));

        VkSubmitInfo si = {VK_STRUCTURE_TYPE_SUBMIT_INFO};
        si.commandBufferCount = 1;
        si.pCommandBuffers = &cb;
        CHECK(vkQueueSubmit(gQueue, 1, &si, VK_NULL_HANDLE));
        CHECK(vkQueueWaitIdle(gQueue));
        vkFreeCommandBuffers(gDev, gPool, 1, &cb);

        void *mapped;
        CHECK(vkMapMemory(gDev, gMem, 0, bufSize, 0, &mapped));
        const double *d = mapped;

        double maxRic = 0.0, maxR = 0.0, maxG = 0.0, maxDev = 0.0;
        double maxKrel = 0.0;
        const double kTol = 1e-6;
        for (uint32_t p = 0; p < total; ++p) {
            const double *o   = d + (size_t)p * STRIDE;
            const double *g   = o;
            const double *ric = o + 16;
            double        R   = o[32];
            const double *Gm  = o + 33;

            for (int i = 0; i < 16; ++i) {
                double ric_i = ric[i];
                double g_i   = g[i];
                if (fabs(ric_i) > maxRic) maxRic = fabs(ric_i);
                if (fabs((double)Gm[i]) > maxG) maxG = fabs((double)Gm[i]);
                double expect = (cases[c].id == 2) ? (double)cases[c].Lambda * g_i : 0.0;
                double dev = fabs(ric_i - expect);
                if (dev > maxDev) maxDev = dev;
            }
            if (fabs(R) > maxR) maxR = fabs(R);

            // Kretschmann check: Schwarzschild has K = 48 M^2 / r^6.
            if (cases[c].id == 1) {
                double K   = o[49];
                int    i1  = (int)((p / (uint32_t)G[0]) % (uint32_t)G[1]);
                double rr  = (double)P.lo[1] + (double)i1 * (double)P.stepv[1];
                double k2  = (double)cases[c].M * (double)cases[c].M;
                double kexp = 48.0 * k2 / (rr * rr * rr * rr * rr * rr);
                double krel = fabs(K - kexp) / kexp;
                if (krel > maxKrel) maxKrel = krel;
            }
        }
        vkUnmapMemory(gDev, gMem);

        const char *verdict = (maxDev <= cases[c].tol) ? "ok" : "FAIL";
        if (maxDev > cases[c].tol) failures++;
        if (cases[c].id == 1 && maxKrel > kTol) {
            verdict = "FAIL";
            failures++;
        }

        printf("case %d  %-26s\n", cases[c].id, cases[c].name);
        printf("        max|Ric| = %.3e   max|R| = %.3e   max|G| = %.3e\n",
               maxRic, maxR, maxG);
        if (cases[c].id == 2)
            printf("        max|Ric - Lambda g| = %.3e  (tol %.0e)  [%s]\n",
                   maxDev, cases[c].tol, verdict);
        else
            printf("        max|Ric| = %.3e  (tol %.0e)  [%s]\n", maxDev,
                   cases[c].tol, verdict);
        if (cases[c].id == 1)
            printf("        Kretschmann |K - 48M^2/r^6| / (48M^2/r^6) = %.3e  (tol %.0e)  [%s]\n",
                   maxKrel, kTol, maxKrel <= kTol ? "ok" : "FAIL");
        printf("\n");
    }

    vkDeviceWaitIdle(gDev);
    vkDestroyPipeline(gDev, gPipe, NULL);
    vkDestroyPipelineLayout(gDev, gPl, NULL);
    vkDestroyDescriptorPool(gDev, gDpool, NULL);
    vkDestroyDescriptorSetLayout(gDev, gDsl, NULL);
    vkFreeMemory(gDev, gMem, NULL);
    vkDestroyBuffer(gDev, gBuf, NULL);
    vkDestroyCommandPool(gDev, gPool, NULL);
    vkDestroyDevice(gDev, NULL);
    vkDestroyInstance(gInstance, NULL);

    printf("%s\n", failures == 0 ? "all cases within tolerance"
                                 : "some cases exceeded tolerance");
    return failures == 0 ? 0 : 1;
}
