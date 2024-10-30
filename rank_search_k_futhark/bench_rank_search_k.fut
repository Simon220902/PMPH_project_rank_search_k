import "rank_search_k"

-- Bench Unoptimized
-- ==
-- entry: benchUnoptimized
-- random input { [10000][100]f32 }
-- random input { [1000000][100]f32 }
-- random input { [10000][10000]f32 }
-- random input { [1000][100000]f32}
entry benchUnoptimized [m] [n] (A : [m][n]f32) =
    let n_elem = i32.i64 n
    let A = flatten A
    let shp = replicate m n_elem
    let ks = replicate m (n_elem/2)
    let II1 = map (\i -> replicate n i) (iota m) |> flatten |> map i32.i64
    in RankSearchK.flatRankSearchBatch ks shp II1 A

-- Bench Optimized
-- ==
-- entry: benchOptimized
-- random input { [10000][100]f32 }
-- random input { [1000000][100]f32 }
-- random input { [10000][10000]f32 }
-- random input { [1000][100000]f32}
-- random input { [1000][400000]f32}
entry benchOptimized [m] [n] (A : [m][n]f32) =
    let n_elem = i32.i64 n
    let A = flatten A
    let shp = replicate m n_elem
    let ks = replicate m (n_elem/2)
    let II1 = map (\i -> replicate n i) (iota m) |> flatten |> map i32.i64
    let ps = map2 (\ sum len -> sum / len) (reduce_by_index (replicate m (0)) (+) (0) (map i64.i32 II1) A) (map f32.i32 shp)
    in RankSearchK.flatRankSearchBatchOptimized ps ks shp II1 A

-- Bench Compiler flattened
-- ==
-- entry: benchCompilerFlattened
-- random input { [10000][100]f32 }
-- random input { [1000000][100]f32 }
-- random input { [10000][10000]f32 }
-- random input { [1000][100000]f32}
entry benchCompilerFlattened [m] [n] (A : [m][n]f32) =
    let n_elem = i32.i64 n
    let A = flatten A
    let shp = replicate m n_elem
    let ks = replicate m (n_elem/2)
    in RankSearchK.compilerFlattenedRankSearchBatch (map i64.i32 ks) shp A