GLSLANG ?= glslc
CC       ?= gcc
CFLAGS   ?= -O2 -Wall -Wextra -std=c11
LDLIBS   := -lvulkan -lm

all: gr_vulkan shaders/tensor.comp.spv

shaders/tensor.comp.spv: shaders/tensor.comp
	$(GLSLANG) -fshader-stage=compute $< -o $@

gr_vulkan: src/gr_vulkan.c
	$(CC) $(CFLAGS) $< -o $@ $(LDLIBS)

run: all
	./gr_vulkan shaders/tensor.comp.spv

clean:
	rm -f gr_vulkan shaders/*.spv

.PHONY: all run clean
