include(joinpath(@__DIR__, "Antiprism.jl")); using .Antiprism
for n in 3:8
  h = hpoly(n); b = bpoly(n+1)
  println(n, " ", interlaces(b,h), " ", interlaces(h,b), " ", interlaces(hpoly(n+1), h), " ", interlaces(BigInt[1,1,1], BigInt[1,3,1]), " ", interlaces(BigInt[2,3,1],BigInt[3,4,1]))
end
