# Julia checks

Pure Julia, no packages. Exact BigInt arithmetic; interlacing is decided with Sturm
sequences after removing common factors.

* `julia run.jl N` checks every identity and interlacing relation of the proof for 2 <= n <= N.
* `julia neg.jl` runs negative controls (wrong inputs are rejected).
* `results_n18.txt`: output for N = 18 (2127 checks).

Local h-polynomial of the simplex (Section 10 of the paper):

* `julia Local.jl N NF N0 NA` checks, for N0 <= n <= N, the symmetry and expansion of ell_n, the two convolution identities, the decomposition of ell_{n+1}/x and the relations ell_n < ell_{n+1}, h_n < ell_{n+1}, lbar_n < lbar_{n+1}; the sequence A_n is checked directly for n <= NA and pairwise for n <= NF.
* `julia Extra.jl N NF N0` checks pbar_n < pbar_{n+1} for N0 <= n <= N and the failure of termwise interlacing for 3 <= n <= 12.
* `results_local.txt` (1066 checks, 2 <= n <= 40, A_n direct for n <= 19, pairwise for n <= 12) and `results_extra.txt` (114 checks, 2 <= n <= 40) are the outputs, run in several ranges.
