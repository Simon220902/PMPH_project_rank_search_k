# Variables
CUDA_DIR = rank_search_k_cub_cuda
FUTHARK_DIR = rank_search_k_futhark
FUTHARK_BENCH_FILE = $(FUTHARK_DIR)/bench_rank_search_k.fut
FUTHARK_BENCH = futhark bench --backend=cuda $(FUTHARK_BENCH_FILE)
FUTHARK_TEST_FILE = $(FUTHARK_DIR)/test_rank_search_k.fut
FUTHARK_TEST = futhark test --backend=cuda $(FUTHARK_TEST_FILE)

# Targets
.PHONY: all bench validate clean

# Benchmark
bench:
	$(FUTHARK_BENCH)
	$(MAKE) -C $(CUDA_DIR)

# Validate
validate:
	$(FUTHARK_BENCH)

# Clean (optional)
clean:
	$(MAKE) -C $(CUDA_DIR) clean