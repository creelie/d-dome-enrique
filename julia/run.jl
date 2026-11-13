include(joinpath(@__DIR__, "Antiprism.jl"))
using .Antiprism
N = length(ARGS) > 0 ? parse(Int, ARGS[1]) : 20
total = run_checks(N)
println("ALL $total CHECKS PASSED for 2 <= n <= $N")
