# Exact checks for the local h-polynomial of the antiprism triangulation (Section 10 of the paper).
include(joinpath(@__DIR__, "Antiprism.jl"))
using .Antiprism
const P = Vector{BigInt}
trim(p) = (q = copy(p); while length(q) > 1 && q[end] == 0; pop!(q); end; q)
deg(p) = (q = trim(p); length(q) == 1 && q[1] == 0 ? -1 : length(q) - 1)
padd(p, q) = trim([get(p, i, 0) + get(q, i, 0) for i in 1:max(length(p), length(q))])
psub(p, q) = padd(p, -q)
pscale(c, p) = trim(c .* p)
shift(p, k) = trim(vcat(zeros(BigInt, k), p))
function pmul(p, q)
    r = zeros(BigInt, length(p) + length(q) - 1)
    for i in eachindex(p), j in eachindex(q); r[i+j-1] += p[i] * q[j]; end
    trim(r)
end
divx(p) = (@assert p[1] == 0; trim(p[2:end]))
function divxm1(p)                       # exact division by x - 1
    p = trim(p); q = zeros(BigInt, length(p) - 1); r = copy(p)
    for i in length(p):-1:2; q[i-1] = r[i]; r[i-1] += r[i]; r[i] = 0; end
    @assert r[1] == 0; trim(q)
end
apart(p, n) = divxm1(psub(shift(rev(p, n - 1), 1), p))   # (x rev_{n-1} p - p)/(x-1)
B(n, k) = binomial(BigInt(n), BigInt(k))
const N = length(ARGS) > 0 ? parse(Int, ARGS[1]) : 40
const NF = length(ARGS) > 1 ? parse(Int, ARGS[2]) : 12
const N0 = length(ARGS) > 2 ? parse(Int, ARGS[3]) : 2
h(n) = hpoly(n)
const L = [foldl(padd, [pscale((-1)^(n - i) * B(n, i), h(i)) for i in 0:n]; init = P([0])) for n in 0:N+1]
ell(n) = L[n+1]
# Stirling numbers and lbar
function stir(n, k)
    S = zeros(BigInt, n + 1, n + 1); S[1, 1] = 1
    for a in 1:n, b in 1:a; S[a+1, b+1] = b * S[a, b+1] + S[a, b]; end
    S[n+1, k+1]
end
const ST = let M = N + 2; S = zeros(BigInt, M + 1, M + 1); S[1, 1] = 1
    for a in 1:M, b in 1:a; S[a+1, b+1] = b * S[a, b+1] + S[a, b]; end; S end
st(n, k) = (k < 0 || k > n) ? BigInt(0) : ST[n+1, k+1]
lbarc(n, k) = sum(factorial(BigInt(j))^2 * st(k, j) * st(n - k, j) for j in 0:n)
lbar(n) = trim([lbarc(n, k) for k in 0:n])
nchk = 0
ok(b, msg) = (b || error("FAILED: " * msg); global nchk += 1)
pbar(n) = trim([sum(B(n - k, i) * lbarc(n - i, k) for i in 0:n-k) for k in 0:n])
for n in N0:N
    ok(interlaces(pbar(n), pbar(n + 1)), "pbar_$n < pbar_$(n+1)")
    if n >= 3 && n <= 12
        s(m, r) = foldl(padd, [pscale(B(m, i), ell(i + r)) for i in 0:m]; init = P([0]))
        f = [j < n ? s(n - 1 - j, j) : ell(n) for j in 0:n]
        for i in 1:n-1
            t = foldl(padd, f[i+1:n+1]); a = apart(t, n)
            ok(!interlaces(a, h(n)), "a(T_$i) does not interlace h_$n")
        end
        ok(deg(apart(ell(n), n)) < 0, "a(T_n) = 0, n=$n")
    end
    println("n = $n ok (checks so far: $nchk)"); flush(stdout)
end
println("ALL $nchk EXTRA CHECKS PASSED for $N0 <= n <= $N")
