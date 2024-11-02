# Variables
CUDA_DIR = rank_search_k_cub_cuda
FUTHARK_DIR = rank_search_k_futhark
FUTHARK_BENCH_FILE = $(FUTHARK_DIR)/bench_rank_search_k.fut
FUTHARK_BENCH = futhark bench --backend=cuda $(FUTHARK_BENCH_FILE)
FUTHARK_VALIDATE_FILE = $(FUTHARK_DIR)/validate_rank_search_k.fut
FUTHARK_VALIDATE = futhark test --backend=cuda $(FUTHARK_VALIDATE_FILE)

# Targets
.PHONY: all bench validate clean

# Benchmark
bench:
	$(FUTHARK_BENCH)
	$(MAKE) -C $(CUDA_DIR)

# Validate
validate:
	$(FUTHARK_VALIDATE)

# Clean (optional)
clean:
	$(MAKE) -C $(CUDA_DIR) clean