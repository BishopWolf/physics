// gr_vulkan.c — minimal Vulkan compute host for general-relativity tensor
// contractions.  Dispatches shaders/tensor.comp over a lattice of spacetime
// points, reports the maximum |Ricci|, |R| and |G| it finds, and checks the
// closed forms proved in Physlib: Schwarzschild-de Sitter curvature against
// Lambda, Kerr vacuum, and the Reissner-Nordstrom Einstein-Maxwell equations.
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
    float       lo[4];
    float       stepv[4];
} Case;

int main(int argc, char **argv)
{
    const char *spv = (argc > 1) ? argv[1] : "shaders/tensor.comp.spv";

    const int G[4]     = {3, 4, 3, 3};
    const uint32_t total = (uint32_t)G[0] * (uint32_t)G[1] * (uint32_t)G[2] *
                           (uint32_t)G[3];
    const int    STRIDE  = 70;
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
        {0, "Minkowski (flat)", 1.0f, 0.0f, 1e-6,
         {0.0f, 3.0f, 0.5f, 0.3f}, {0.1f, 0.15f, 0.2f, 0.2f}},
        {1, "Schwarzschild (vacuum)", 1.0f, 0.0f, 1e-6,
         {0.0f, 3.0f, 0.5f, 0.3f}, {0.1f, 0.15f, 0.2f, 0.2f}},
        {2, "Schwarzschild-de Sitter", 1.0f, 0.1f, 1e-6,
         {0.0f, 3.0f, 0.5f, 0.3f}, {0.1f, 0.15f, 0.2f, 0.2f}},
        {3, "Kerr (a = 0.5, vacuum)", 1.0f, 0.5f, 1e-5,
         {0.0f, 3.0f, 0.5f, 0.3f}, {0.1f, 0.15f, 0.2f, 0.2f}},
        {4, "Reissner-Nordstrom (Q = 0.5)", 1.0f, 0.5f, 1e-6,
         {0.0f, 3.0f, 0.5f, 0.3f}, {0.1f, 0.15f, 0.2f, 0.2f}},
        {5, "FLRW (a = 1 + Ht + t^2, k = 0.3)", 1.0f, 0.3f, 1e-5,
         {0.0f, 0.5f, 0.5f, 0.3f}, {0.1f, 0.12f, 0.2f, 0.2f}},
        {6, "Interior Schwarzschild (Rc = 5, Ra = 4)", 5.0f, 4.0f, 1e-5,
         {0.0f, 1.0f, 0.5f, 0.3f}, {0.1f, 0.15f, 0.2f, 0.2f}},
    };

    int failures = 0;
    printf("\n%u lattice points per case, stride %d doubles\n\n", total, STRIDE);

    for (size_t c = 0; c < sizeof cases / sizeof cases[0]; ++c) {
        PushParams P;
        memset(&P, 0, sizeof P);
        P.metricId = cases[c].id;
        P.massM    = cases[c].M;
        P.lambdaC  = cases[c].Lambda;
        P.h        = 1e-4f;
        for (int k = 0; k < 4; ++k) {
            P.lo[k] = cases[c].lo[k];
            P.stepv[k] = cases[c].stepv[k];
        }
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
        double maxKrel = 0.0, maxEdev = 0.0, maxRtr = 0.0;
        double maxRtt = 0.0, maxRrr = 0.0, maxRtp = 0.0;
        double maxKsds = 0.0, maxRicFrame = 0.0, maxMaxwell = 0.0;
        double maxFlrw = 0.0, maxInterior = 0.0;
        const double PI = 3.14159265358979323846;
        const double kTol = 1e-6;
        const double eTol = 1e-6;
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
                if (cases[c].id <= 2) {
                    double expect =
                        (cases[c].id == 2) ? (double)cases[c].Lambda * g_i : 0.0;
                    double dev = fabs(ric_i - expect);
                    if (dev > maxDev) maxDev = dev;
                }
            }
            // The frame statement proved in Lean: Ric = Lambda eta in the
            // orthonormal frame.  The metric is diagonal, so the frame
            // component is Ric_ab / sqrt(|g_aa g_bb|), which must be
            // Lambda * diag(-1, 1, 1, 1).  At Lambda = 0 this is the vanishing
            // of the Schwarzschild frame Ricci tensor.
            if (cases[c].id <= 2) {
                double eta[16] = {0};
                double L       = (double)cases[c].Lambda;
                eta[0] = -1.0; eta[5] = 1.0; eta[10] = 1.0; eta[15] = 1.0;
                for (int a = 0; a < 4; ++a)
                for (int b = 0; b < 4; ++b) {
                    double sa   = sqrt(fabs(g[5 * a]));
                    double sb   = sqrt(fabs(g[5 * b]));
                    double ricf = ric[4 * a + b] / (sa * sb);
                    double dev  = fabs(ricf - L * eta[4 * a + b]);
                    if (dev > maxRicFrame) maxRicFrame = dev;
                }
            }
            if (fabs(R) > maxR) maxR = fabs(R);

            // Kretschmann and the Riemann components proved in Lean: the
            // Schwarzschild-de Sitter forms with general Lambda, of which
            // Schwarzschild is the Lambda = 0 special case.
            if (cases[c].id == 1 || cases[c].id == 2) {
                int    i1 = (int)((p / (uint32_t)G[0]) % (uint32_t)G[1]);
                double rr = (double)P.lo[1] + (double)i1 * (double)P.stepv[1];
                double M  = (double)cases[c].M;
                double L  = (double)cases[c].Lambda;
                double r2 = rr * rr;
                double ff = 1.0 - 2.0 * M / rr - L * r2 / 3.0;
                double s2 = g[15] / g[10];   // sin^2 theta = g_phiphi/g_thetatheta
                double dev;

                if (cases[c].id == 1) {
                    double K    = o[49];
                    double kexp = 48.0 * M * M / (r2 * r2 * r2);
                    double krel = fabs(K - kexp) / kexp;
                    if (krel > maxKrel) maxKrel = krel;
                }
                if (cases[c].id == 2) {
                    // De Sitter lifts the Weyl invariant by the trace part:
                    // K = 48M^2/r^6 + (8/3) Lambda^2.
                    double K    = o[49];
                    double kexp = 48.0 * M * M / (r2 * r2 * r2)
                                  + (8.0 / 3.0) * L * L;
                    double krel = fabs(K - kexp) / kexp;
                    if (krel > maxKsds) maxKsds = krel;
                }

                // R^t_rtr = (2M/r^3 + Lambda/3)/f  (riemann_t_rtr_sds)
                dev = fabs(o[66] - (2.0 * M / (r2 * rr) + L / 3.0) / ff);
                if (dev > maxRtr) maxRtr = dev;

                // R^t_thetatheta = R^r_thetar = Lambda r^2/3 - M/r
                dev = fabs(o[67] - (L * r2 / 3.0 - M / rr));
                if (dev > maxRtt) maxRtt = dev;
                dev = fabs(o[68] - (L * r2 / 3.0 - M / rr));
                if (dev > maxRrr) maxRrr = dev;

                // R^theta_phitheta = (2M/r + Lambda r^2/3) sin^2 theta
                dev = fabs(o[69] - (2.0 * M / rr + L * r2 / 3.0) * s2);
                if (dev > maxRtp) maxRtp = dev;

                // Weyl electric part.  In the frame Lambda enters the Riemann
                // tensor as R_{titj} = C_{titj} - (Lambda/3) delta_ij, so adding
                // Lambda/3 back leaves the Schwarzschild eigenvalues
                // diag(0, -2k, k, k) with k = M/r^3.
                const double *E = o + 50;
                double kk = M / (r2 * rr);
                double wexp[16] = {0};
                wexp[5]  = -2.0 * kk;
                wexp[10] = kk;
                wexp[15] = kk;
                for (int i = 0; i < 16; ++i) {
                    double e = E[i];
                    if (i == 5 || i == 10 || i == 15) e += L / 3.0;
                    dev = fabs(e - wexp[i]);
                    if (dev > maxEdev) maxEdev = dev;
                }
            }

            // Reissner-Nordstrom: G_ij = 8 pi T_ij for the Maxwell field
            // F_01 = -Q/r^2 (einsteinOf_rn_eq_maxwell).  The metric is diagonal,
            // so 8 pi T = diag(Q^2 f/r^4, -Q^2/(f r^4), Q^2/r^2,
            // Q^2 sin^2 theta/r^2).
            if (cases[c].id == 4) {
                int    i1 = (int)((p / (uint32_t)G[0]) % (uint32_t)G[1]);
                double rr = (double)P.lo[1] + (double)i1 * (double)P.stepv[1];
                double M  = (double)cases[c].M;
                double q  = (double)cases[c].Lambda;
                double q2 = q * q;
                double r4 = rr * rr * rr * rr;
                double ff = 1.0 - 2.0 * M / rr + q2 / (rr * rr);
                double s2 = g[15] / g[10];
                double expect[16] = {0};
                expect[0]  = q2 * ff / r4;
                expect[5]  = -q2 / (ff * r4);
                expect[10] = q2 / (rr * rr);
                expect[15] = q2 * s2 / (rr * rr);
                for (int i = 0; i < 16; ++i) {
                    double dev = fabs(Gm[i] - expect[i]);
                    if (dev > maxMaxwell) maxMaxwell = dev;
                }
            }

            // FLRW: a(t) = 1 + H t + t^2 and spatial curvature k.  The closed
            // forms are ricciOf_flrw, scalarOf_flrw and einsteinOf_flrw; with
            // a'' = 2 the second-derivative term is exercised.
            if (cases[c].id == 5) {
                int i0 = (int)(p % (uint32_t)G[0]);
                int i1 = (int)((p / (uint32_t)G[0]) % (uint32_t)G[1]);
                double t  = (double)P.lo[0] + (double)i0 * (double)P.stepv[0];
                double rr = (double)P.lo[1] + (double)i1 * (double)P.stepv[1];
                double H  = (double)cases[c].M;
                double kk = (double)cases[c].Lambda;
                double a  = 1.0 + H * t + t * t;
                double ap = H + 2.0 * t;
                double app = 2.0;
                double s2 = g[15] / g[10];
                double c1 = a * app + 2.0 * ap * ap + 2.0 * kk;
                double expect[16] = {0};
                expect[0]  = -3.0 * app / a;
                expect[5]  = c1 / (1.0 - kk * rr * rr);
                expect[10] = c1 * rr * rr;
                expect[15] = c1 * rr * rr * s2;
                for (int i = 0; i < 16; ++i) {
                    double dev = fabs(ric[i] - expect[i]);
                    if (dev > maxFlrw) maxFlrw = dev;
                }
                double sexp = 6.0 * (app / a + (ap / a) * (ap / a)
                                     + kk / (a * a));
                double sdev = fabs(R - sexp);
                if (sdev > maxFlrw) maxFlrw = sdev;
                double gdev = fabs(Gm[0] - 3.0 * ((ap / a) * (ap / a)
                                                  + kk / (a * a)));
                if (gdev > maxFlrw) maxFlrw = gdev;
            }

            // Interior Schwarzschild (incompressible sphere): constant density
            // rho = 3/(8 pi Rc^2) and pressure
            // p = rho (2 cos chi_a / (3 cos chi_a - cos chi) - 1), with
            // cos chi = sqrt(1 - r^2/Rc^2).  Checks the Einstein tensor of the
            // interior metric; the Lean module proves the junction, not the
            // field equations.
            if (cases[c].id == 6) {
                int i1 = (int)((p / (uint32_t)G[0]) % (uint32_t)G[1]);
                double rr = (double)P.lo[1] + (double)i1 * (double)P.stepv[1];
                double Rc = (double)cases[c].M;
                double Ra = (double)cases[c].Lambda;
                double c  = sqrt(1.0 - Ra * Ra / (Rc * Rc));
                double u  = 1.0 - rr * rr / (Rc * Rc);
                double cc = sqrt(u);
                double A  = 1.5 * c - 0.5 * cc;
                double rho = 3.0 / (8.0 * PI * Rc * Rc);
                double pr  = rho * (2.0 * c / (3.0 * c - cc) - 1.0);
                double s2  = g[15] / g[10];
                double expect[16] = {0};
                expect[0]  = 3.0 * (A * A) / (Rc * Rc);
                expect[5]  = (8.0 * PI * pr) / u;
                expect[10] = 8.0 * PI * pr * rr * rr;
                expect[15] = 8.0 * PI * pr * rr * rr * s2;
                for (int i = 0; i < 16; ++i) {
                    double dev = fabs(Gm[i] - expect[i]);
                    if (dev > maxInterior) maxInterior = dev;
                }
            }
        }
        vkUnmapMemory(gDev, gMem);

        int bad = 0;
        if (cases[c].id <= 2 && maxDev > cases[c].tol) bad = 1;
        if ((cases[c].id == 1 || cases[c].id == 2) &&
            (maxEdev > eTol || maxRtr > eTol || maxRtt > eTol ||
             maxRrr > eTol || maxRtp > eTol))
            bad = 1;
        if (cases[c].id == 1 && maxKrel > kTol) bad = 1;
        if (cases[c].id == 2 && maxKsds > kTol) bad = 1;
        if (cases[c].id == 3 &&
            (maxRic > cases[c].tol || maxG > cases[c].tol))
            bad = 1;
        if (cases[c].id == 4 && maxMaxwell > cases[c].tol) bad = 1;
        if (cases[c].id == 5 && maxFlrw > cases[c].tol) bad = 1;
        if (cases[c].id == 6 && maxInterior > cases[c].tol) bad = 1;
        if (cases[c].id <= 2 && maxRicFrame > eTol) bad = 1;
        if (bad) failures++;
        const char *verdict = bad ? "FAIL" : "ok";

        printf("case %d  %-32s\n", cases[c].id, cases[c].name);
        printf("        max|Ric| = %.3e   max|R| = %.3e   max|G| = %.3e\n",
               maxRic, maxR, maxG);
        if (cases[c].id == 2)
            printf("        max|Ric - Lambda g| = %.3e  (tol %.0e)  [%s]\n",
                   maxDev, cases[c].tol, verdict);
        else if (cases[c].id == 3)
            printf("        vacuum  max|Ric|, max|G| = %.3e  (tol %.0e)  [%s]\n",
                   fmax(maxRic, maxG), cases[c].tol, verdict);
        else if (cases[c].id == 4)
            printf("        max|G - 8 pi T_Maxwell| = %.3e  (tol %.0e)  [%s]\n",
                   maxMaxwell, cases[c].tol, verdict);
        else if (cases[c].id == 5)
            printf("        max|Ric, R, G - FLRW closed form| = %.3e  (tol %.0e)  [%s]\n",
                   maxFlrw, cases[c].tol, verdict);
        else if (cases[c].id == 6)
            printf("        max|G - 8 pi diag(rho, p, p, p)| = %.3e  (tol %.0e)  [%s]\n",
                   maxInterior, cases[c].tol, verdict);
        else
            printf("        max|Ric| = %.3e  (tol %.0e)  [%s]\n", maxDev,
                   cases[c].tol, verdict);
        if (cases[c].id <= 2)
            printf("        frame Ricci |Ric - Lambda eta| = %.3e  (tol %.0e)  [%s]\n",
                   maxRicFrame, eTol, maxRicFrame <= eTol ? "ok" : "FAIL");
        if (cases[c].id == 1 || cases[c].id == 2) {
            if (cases[c].id == 1)
                printf("        Kretschmann |K - 48M^2/r^6| / (48M^2/r^6) = %.3e  (tol %.0e)  [%s]\n",
                       maxKrel, kTol, maxKrel <= kTol ? "ok" : "FAIL");
            if (cases[c].id == 2)
                printf("        Kretschmann |K - 48M^2/r^6 - 8L^2/3| / (48M^2/r^6 + 8L^2/3) = %.3e  (tol %.0e)  [%s]\n",
                       maxKsds, kTol, maxKsds <= kTol ? "ok" : "FAIL");
            printf("        Weyl electric part |E + L/3 - diag(0,-2k,k,k)| = %.3e  (tol %.0e)  [%s]\n",
                   maxEdev, eTol, maxEdev <= eTol ? "ok" : "FAIL");
            printf("        R^t_rtr          |R - (2M/r^3 + L/3)/f| = %.3e  (tol %.0e)  [%s]\n",
                   maxRtr, eTol, maxRtr <= eTol ? "ok" : "FAIL");
            printf("        R^t_thetatheta   |R - (L r^2/3 - M/r)| = %.3e  (tol %.0e)  [%s]\n",
                   maxRtt, eTol, maxRtt <= eTol ? "ok" : "FAIL");
            printf("        R^r_thetar       |R - (L r^2/3 - M/r)| = %.3e  (tol %.0e)  [%s]\n",
                   maxRrr, eTol, maxRrr <= eTol ? "ok" : "FAIL");
            printf("        R^theta_phitheta |R - (2M/r + L r^2/3) sin^2| = %.3e  (tol %.0e)  [%s]\n",
                   maxRtp, eTol, maxRtp <= eTol ? "ok" : "FAIL");
        }
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
