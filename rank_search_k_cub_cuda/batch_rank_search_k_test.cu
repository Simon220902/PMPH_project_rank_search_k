//#include "../../cub-1.8.0/cub/cub.cuh"   // or equivalently <cub/device/device_histogram.cuh>
#include "cub/cub.cuh"
#include "helper.cu.h"

void randomInitNat(uint32_t* data, const uint32_t size) {
    for (int i = 0; i < size; ++i) {
        uint32_t r = rand();
        data[i] = r;
    }
}

void randomInitShp(uint32_t* data, const uint32_t M, const uint32_t N) {
    for (int i = 0; i < M; i++) { // Initialize all entries of shp to 1.
        data[i] = 1;
    }
    for (int j = 0; j < N-M; ++j) { // Add 1 to a random entry in shp.
        unsigned long int r = rand();
        data[r % M] += 1;
    }
}

void randomInitKs(uint32_t* h_ks, uint32_t* h_shp, const uint32_t M) {
    for (int i = 0; i < M; i++) { // Set entries of k to be between zero and 2/3 length of that array.
        unsigned long int r = rand();
        h_ks[i] = r % ((h_shp[i]/3)*2);
    }
}


__global__ void
extractKthElem(const uint32_t m, uint32_t* d_offsets, uint32_t* ks, uint32_t* As_sorted, uint32_t* res) {
    uint32_t gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < m) { // Assuming: 0 <= gid < m
        res[gid] = As_sorted[d_offsets[gid]+ks[gid]-1];
    }
}

// rankSearchBatch (ks: [m]i32) (shp: [m]i32) (II1: *[n]i32) (A: [n]f32) : [m]f32 = ...
double simpleBatchRankSearchK(uint32_t m, uint32_t n,
                              uint32_t* d_ks,
                              uint32_t* h_shp,
                              uint32_t* d_As,
                              uint32_t* d_res){
    // Declare, allocate, and initialize device-accessible pointers
    // for sorting data
    uint32_t  num_items = n;
    uint32_t  num_segments = m;
    uint32_t  *h_offsets = (uint32_t*) malloc(sizeof(uint32_t) * (m+1));
    // Setup offsets
    h_offsets[0] = 0;
    for (uint32_t i = 1; i < m+1; i++) {
        h_offsets[i] = h_offsets[i-1] + h_shp[i-1];
    }
    uint32_t* d_offsets;
    cudaSucceeded(cudaMalloc((void**) &d_offsets, sizeof(uint32_t) * (m+1)));
    cudaSucceeded(cudaMemcpy(d_offsets, h_offsets, sizeof(uint32_t) * (m+1), cudaMemcpyHostToDevice));

    // Setup in/out arrays
    uint32_t* d_keys_in = d_As;
    uint32_t* d_keys_out;
    cudaSucceeded(cudaMalloc((void**) &d_keys_out, n * sizeof(uint32_t)));

    // Setup for the extractKthElem kernel
    uint32_t block_size = min(m, 1024);
    uint32_t num_blocks = (m + block_size - 1) / block_size;

    // ACTUALLY DOING RANK SEARCH K
    // Determine temporary device storage requirements
    
    void     *d_temp_storage = nullptr;
    size_t   temp_storage_bytes = 0;
    {   // Sort prelude
        cub::DeviceSegmentedRadixSort::SortKeys(
            d_temp_storage, temp_storage_bytes, d_keys_in, d_keys_out,
            num_items, num_segments, d_offsets, d_offsets + 1);

        // Allocate temporary storage
        cudaSucceeded(cudaMalloc(&d_temp_storage, temp_storage_bytes));
    }
    cudaCheckError();
    {   // One dry run 
        // Run sorting operation
        cub::DeviceSegmentedRadixSort::SortKeys(
            d_temp_storage, temp_storage_bytes, d_keys_in, d_keys_out,
            num_items, num_segments, d_offsets, d_offsets + 1);
        // Extract the kth elements
        extractKthElem<<<num_blocks, block_size>>>(m, d_offsets, d_ks, d_keys_out, d_res);
    }
    cudaDeviceSynchronize();
    cudaCheckError();

    // Timing
    double elapsed;
    struct timeval t_start, t_end, t_diff;
    gettimeofday(&t_start, NULL);

    for(int k=0; k<GPU_RUNS; k++) {
        // Run sorting operation
        cub::DeviceSegmentedRadixSort::SortKeys(
            d_temp_storage, temp_storage_bytes, d_keys_in, d_keys_out,
            num_items, num_segments, d_offsets, d_offsets + 1);
        // Extract the kth elements
        extractKthElem<<<num_blocks, block_size>>>(m, d_offsets, d_ks, d_keys_out, d_res);
    }
    cudaDeviceSynchronize();

    gettimeofday(&t_end, NULL);
    timeval_subtract(&t_diff, &t_end, &t_start);
    elapsed = (t_diff.tv_sec*1e6+t_diff.tv_usec) / ((double)GPU_RUNS);

    cudaCheckError();
    // Validation
    uint32_t* h_keys_out = (uint32_t*) malloc(sizeof(uint32_t) * n);
    uint32_t* h_ks = (uint32_t*) malloc(sizeof(uint32_t) * m);
    uint32_t* h_res = (uint32_t*) malloc(sizeof(uint32_t) * m);
    cudaSucceeded(cudaMemcpy(h_keys_out, d_keys_out, sizeof(uint32_t) * n, cudaMemcpyDeviceToHost));
    cudaSucceeded(cudaMemcpy(h_ks, d_ks, sizeof(uint32_t) * m, cudaMemcpyDeviceToHost));
    cudaSucceeded(cudaMemcpy(h_res, d_res, sizeof(uint32_t) * m, cudaMemcpyDeviceToHost));

    // VALIDATION THAT THE OUTPUT ARRAY IS ACTUALLY SORTED!
    for (uint32_t j = 0; j < m; j++) {
        for (uint32_t i = h_offsets[j]+1; i < h_offsets[j+1]; i++) {
            if (h_keys_out[i-1] > h_keys_out[i]) {
                printf("INVALID RESULT for i:%d, (A[i-1]=%d > A[i]=%d)\n", i, h_keys_out[i-1], h_keys_out[i]);
                return elapsed;
            }
        }
    }
    // VALIDATION THAT THE CORRECT ELEMENTS ARE EXTRACTED
    for (uint32_t j = 0; j < m; j++) {
        if (h_res[j] != h_keys_out[h_offsets[j]+h_ks[j]-1]) {
            printf("INVALID RESULT for j:%d, (res[j]=%d != actual[j]=%d)\n", j, h_res[j], h_keys_out[h_offsets[j]+h_ks[j]-1]);
            return elapsed;
        }
    }
    printf("!!!VALID RESULT!!!\n");

    cudaFree(d_temp_storage);
    cudaFree(d_keys_out);
    cudaFree(d_offsets);
    free(h_keys_out);
    free(h_offsets);
    free(h_res);
    free(h_ks);

    return elapsed;
}


int main (int argc, char * argv[]) {
    if (argc != 3) {
        printf("Usage: %s <size-of-flat-array> <size-of-shp>\n", argv[0]);
        exit(1);
    }
    const uint64_t N = atoi(argv[1]);
    const uint64_t M = atoi(argv[2]);

    //Allocate and Initialize Host data with random values
    uint32_t* h_keys  = (uint32_t*) malloc(N*sizeof(uint32_t));
    randomInitNat(h_keys, N);
    uint32_t* h_shp   = (uint32_t*) malloc(M*sizeof(uint32_t));
    randomInitShp(h_shp, M, N);
    uint32_t* h_ks   = (uint32_t*) malloc(M*sizeof(uint32_t));
    randomInitKs(h_ks, h_shp, M);

    //Allocate and Initialize Device data
    uint32_t* d_keys_in;
    uint32_t* d_ks;
    uint32_t* d_res;
    // uint32_t* d_keys_out;
    cudaSucceeded(cudaMalloc((void**) &d_keys_in,  N * sizeof(uint32_t)));
    cudaSucceeded(cudaMemcpy(d_keys_in, h_keys, N * sizeof(uint32_t), cudaMemcpyHostToDevice));
    cudaSucceeded(cudaMalloc((void**) &d_ks,  M * sizeof(uint32_t)));
    cudaSucceeded(cudaMemcpy(d_ks, h_ks, M * sizeof(uint32_t), cudaMemcpyHostToDevice));
    cudaSucceeded(cudaMalloc((void**) &d_res,  M * sizeof(uint32_t)));
    
    printf("Batch Rank Search K for N=%lu and M=%lu\n", N, M);
    
    double elapsed = simpleBatchRankSearchK(M, N, d_ks, h_shp, d_keys_in, d_res);
    printf("Runs in: %.2f us\n", elapsed);

    //Cleanup and closing
    free(h_keys);
    free(h_shp);
    free(h_ks);
    cudaFree(d_keys_in);
    cudaFree(d_ks);
    cudaFree(d_res);
    
    return 0;
}
