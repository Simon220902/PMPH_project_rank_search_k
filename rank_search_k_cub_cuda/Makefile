CUB=cub-1.8.0

all: rank-search-k #cub-sort

#cub-sort: sorting_test.cu helper.cu.h
#	nvcc -I$(CUB)/cub -o test-cub sorting_test.cu
#	./test-cub 100000000

rank-search-k: batch_rank_search_k_test.cu helper.cu.h
	nvcc -I$(CUB)/cub -o test-rank-search-k batch_rank_search_k_test.cu
	./test-rank-search-k 1000000   100
	./test-rank-search-k 100000000 100
	./test-rank-search-k 100000000 10000
	./test-rank-search-k 100000000 100000
	./test-rank-search-k 400000000 400000

clean:
	rm -f test-rank-search-k

