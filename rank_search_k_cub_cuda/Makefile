CUB=cub-1.8.0

all: rank-search-k #cub-sort

#cub-sort: sorting_test.cu helper.cu.h
#	nvcc -I$(CUB)/cub -o test-cub sorting_test.cu
#	./test-cub 100000000

rank-search-k: batch_rank_search_k_test.cu helper.cu.h
	nvcc -I$(CUB)/cub -o test-rank-search-k batch_rank_search_k_test.cu
	./test-rank-search-k 6250000    1000
	./test-rank-search-k 12500000   1000
	./test-rank-search-k 25000000   1000
	./test-rank-search-k 50000000   1000
	./test-rank-search-k 100000000  1000
	./test-rank-search-k 200000000  1000
	./test-rank-search-k 400000000  1000

clean:
	rm -f test-rank-search-k

