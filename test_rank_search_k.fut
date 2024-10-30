import "rank_search_k"


-- Validation Unoptimized
-- ==
-- entry: validationUnoptimized
entry validationUnoptimized [m] [n] (A : [m][n]f32) : bool =
    let n_elem = i32.i64 n
    let A = flatten A
    let shp = replicate m n_elem
    let ks = replicate m (n_elem/2)
    let II1 = map (\i -> replicate n i) (iota m) |> flatten |> map i32.i64

    let valid_res = RankSearchK.radixSortRankSearchBatch ks shp A
    let test_res  = RankSearchK.flatRankSearchBatch ks shp II1 A

    in reduce (&&) true (map2 (==) valid_res test_res)
-- random input { [10000][100]f32 }
-- output { true }
-- random input { [1000000][100]f32 }
-- output { true }
-- random input { [10000][10000]f32 }
-- output { true }
-- random input { [1000][100000]f32}
-- output { true }



-- Validation Optimized
-- ==
entry validationOptimized [m] [n] (A : [m][n]f32) : bool =
    let n_elem = i32.i64 n
    let A = flatten A
    let shp = replicate m n_elem
    let ks = replicate m (n_elem/2)
    let II1 = map (\i -> replicate n i) (iota m) |> flatten |> map i32.i64

    let valid_res = RankSearchK.radixSortRankSearchBatch ks shp A
    let test_res  = RankSearchK.flatRankSearchBatchOptimized ks shp II1 A

    in reduce (&&) true (map2 (==) valid_res test_res)
-- entry: validationOptimized
-- random input { [10000][100]f32 }
-- output { true }
-- random input { [10000][10000]f32 }
-- output { true }
-- random input { [10000][10000]f32 }
-- output { true }
-- random input { [1000][100000]f32}
-- output { true }

-- Validation Compiler flattened
-- ==
-- entry: validationCompilerFlattened
-- random input { [10000][100]f32 }
-- output { true }
-- random input { [10000][10000]f32 }
-- output { true }
entry validationCompilerFlattened [m] [n] (A : [m][n]f32) : bool =
    let n_elem = i32.i64 n
    let A = flatten A
    let shp = replicate m n_elem
    let ks = replicate m (n_elem/2)

    let valid_res = RankSearchK.radixSortRankSearchBatch ks shp A
    let test_res  = RankSearchK.compilerFlattenedRankSearchBatch (map i64.i32 ks) shp A

    in reduce (&&) true (map2 (==) valid_res test_res)
-- random input { [10000][10000]f32 }
-- output { true }
-- random input { [1000][100000]f32}
-- output { true }