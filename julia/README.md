# Julia checks

Pure Julia, no packages. Exact BigInt arithmetic; interlacing is decided with Sturm
sequences after removing common factors.

* `julia run.jl N` checks every identity and interlacing relation of the proof for 2 <= n <= N.
* `julia neg.jl` runs negative controls (wrong inputs are rejected).
* `results_n18.txt`: output for N = 18 (2127 checks).
