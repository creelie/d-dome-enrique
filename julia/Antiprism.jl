# Exact verification of the antiprism interlacing theorem.
# Pure Julia (no packages): BigInt / Rational{BigInt} polynomials, Sturm sequences.
# Polynomials are coefficient vectors, c[1] = constant term.
module Antiprism
export hpoly, bpoly, qpoly, rev, interlaces, run_checks

const P = Vector{BigInt}
trim(p) = (q = copy(p); while length(q) > 1 && q[end] == 0; pop!(q); end; q)
deg(p) = (q = trim(p); length(q) == 1 && q[1] == 0 ? -1 : length(q) - 1)
padd(p, q) = trim([get(p, i, 0) + get(q, i, 0) for i in 1:max(length(p), length(q))])
psub(p, q) = padd(p, -q)
pscale(c, p) = trim(c .* p)
shift(p, k) = trim(vcat(zeros(eltype(p), k), p))           # x^k p
function rev(p, d)                                         # x^d p(1/x)
    q = trim(p); @assert deg(q) <= d
    r = zeros(eltype(p), d + 1)
    for i in 0:length(q)-1; r[d+1-i] = q[i+1]; end
    trim(r)
end
function pmul(p, q)
    r = zeros(promote_type(eltype(p), eltype(q)), length(p) + length(q) - 1)
    for i in eachindex(p), j in eachindex(q); r[i+j-1] += p[i] * q[j]; end
    trim(r)
end
function pdivrem(p, q)                                     # over the rationals
    p = Rational{BigInt}.(trim(p)); q = Rational{BigInt}.(trim(q))
    dq = deg(q); out = zeros(Rational{BigInt}, max(deg(p) - dq + 1, 1))
    while deg(p) >= dq && deg(p) >= 0
        k = deg(p) - dq; c = p[end] / q[end]; out[k+1] = c
        p = psub(p, shift(pscale(c, q), k))
    end
    trim(out), p
end
peval(p, x) = foldr((c, acc) -> c + x * acc, p; init = zero(x))
deriv(p) = length(p) == 1 ? [zero(eltype(p))] : trim([i * p[i+1] for i in 1:length(p)-1])
function pgcd(p, q)
    a = Rational{BigInt}.(trim(p)); b = Rational{BigInt}.(trim(q))
    while deg(b) >= 0; a, b = b, pdivrem(a, b)[2]; end
    a ./ a[end]
end

# ---- antiprism data -------------------------------------------------------
# h_n = sum_{k=0}^{n-1} binom(n,k) x^k h_k(1/x),  h_0 = 1   (ABJK, eq. (12))
function hpolys(N)
    h = [P([1])]
    for n in 1:N
        s = P([0])
        for k in 0:n-1
            s = padd(s, pscale(binomial(BigInt(n), k), rev(h[k+1], k)))
        end
        push!(h, s)
    end
    h
end
const H = hpolys(42)
hpoly(n) = H[n+1]
# b_n = (h_n - x^{n-1} h_n(1/x)) / (x - 1)
function bpoly(n)
    q, r = pdivrem(psub(hpoly(n), rev(hpoly(n), n - 1)), [-1, 1])
    @assert deg(r) < 0
    @assert all(isinteger, q)
    BigInt.(q)
end
# q_{n,r} = sum_k binom(n,k) x^{k+r} h_{k+r}(1/x)
qpoly(n, r) = foldl(padd, [pscale(binomial(BigInt(n), k), rev(hpoly(k + r), k + r)) for k in 0:n]; init = P([0]))
# a-part with respect to n-1:  a(P) = (x rev_{n-1}P - P)/(x-1)
function apart(p, n)
    q, r = pdivrem(psub(shift(rev(p, n - 1), 1), p), [-1, 1])
    @assert deg(r) < 0
    BigInt.(q)
end

# ---- certified root counting (Sturm) --------------------------------------
function sturm(p)
    s = [Rational{BigInt}.(p), Rational{BigInt}.(deriv(p))]
    while deg(s[end]) > 0
        r = pdivrem(s[end-1], s[end])[2]
        deg(r) < 0 && break
        push!(s, -r)
    end
    s
end
function signchanges(s, x)
    v = [sign(peval(q, x)) for q in s]; v = filter(!=(0), v)
    count(i -> v[i] != v[i+1], 1:length(v)-1)
end
nroots(s, a, b) = signchanges(s, a) - signchanges(s, b)   # distinct roots in (a,b]
function cauchy(p)
    p = trim(p); 1 + maximum(abs.(Rational{BigInt}.(p[1:end-1]) ./ p[end]); init = 0)
end
# isolate distinct real roots of a squarefree p: disjoint intervals (a,b], descending
function isolate(p)
    s = sturm(p); B = Rational{BigInt}(ceil(BigInt, cauchy(p)) + 1)
    out = Tuple{Rational{BigInt},Rational{BigInt}}[]
    stack = [(-B, B)]
    while !isempty(stack)
        a, b = pop!(stack); k = nroots(s, a, b)
        k == 0 && continue
        if k == 1; push!(out, (a, b)); continue; end
        m = (a + b) / 2
        push!(stack, (a, m)); push!(stack, (m, b))
    end
    sort!(out, by = t -> -t[2])
    out, s
end
# Is p (with positive leading coeff) real-rooted with simple roots?  Returns intervals.
function simple_real_roots(p)
    deg(p) <= 0 && return Tuple{Rational{BigInt},Rational{BigInt}}[], true
    iv, s = isolate(p)
    iv, length(iv) == deg(p)
end
# f interlaces g (convention: ... <= a2 <= b2 <= a1 <= b1, a = roots of f),
# positive leading coefficients, deg g in {deg f, deg f + 1}.
function interlaces(f, g)
    f = trim(f); g = trim(g)
    (deg(g) == deg(f) || deg(g) == deg(f) + 1) || return false
    c = pgcd(f, g)
    f2 = pdivrem(f, c)[1]; g2 = pdivrem(g, c)[1]
    # c must be real-rooted (with multiplicity): check via squarefree decomposition
    real_rooted_mult(c) || return false
    deg(g2) <= 0 && return deg(f2) <= 0
    ivg, okg = simple_real_roots(g2); okg || return false
    _, okf = simple_real_roots(f2); okf || deg(f2) <= 0 || return false
    sf = sturm(f2)
    vals = Int[]
    for (a, b) in ivg
        sg = sturm(g2)
        while deg(f2) > 0 && nroots(sf, a, b) > 0     # refine until f2 has no root in (a,b]
            m = (a + b) / 2
            nroots(sg, a, m) == 1 ? (b = m) : (a = m)
        end
        push!(vals, Int(sign(peval(f2, b))))
    end
    sgn = Int(sign(f2[end]))
    all(k -> vals[k] == sgn * (-1)^(k - 1), eachindex(vals))
end
function real_rooted_mult(c)
    deg(c) <= 0 && return true
    # Sturm count of distinct real roots must equal degree of squarefree part,
    # and recursively for the repeated part.
    d = pgcd(c, deriv(c)); sq = pdivrem(c, d)[1]
    _, ok = simple_real_roots(sq)
    ok && real_rooted_mult(d)
end

# ---- the checks -----------------------------------------------------------
function run_checks(N; io = stdout)
    nchk = 0
    ok(b, msg) = (b || error("FAILED: " * msg); nchk += 1)
    # table of ABJK, Section 5
    ok(hpoly(4) == [1, 28, 42, 4], "h_4"); ok(hpoly(7) == [1, 441, 8211, 23625, 13685, 1323, 7], "h_7")
    for n in 2:N
        h = hpoly(n); R = rev(h, n - 1)
        f = [j < n ? qpoly(n - 1 - j, j) : qpoly(0, n) for j in 0:n]
        Ps = [foldl(padd, f[1:i]; init = P([0])) for i in 1:n]
        ok(Ps[n] == h, "P_n = h_n, n=$n")
        ok(foldl(padd, [pscale(BigInt(j + 1), f[j+1]) for j in 0:n]) == hpoly(n + 1), "(17), n=$n")
        ok(f[n+1] == shift(R, 1), "f_n = xR, n=$n")
        b = bpoly(n + 1)
        ok(foldl(padd, [apart(Ps[i], n) for i in 1:n]) == b, "Step 1 identity, n=$n")
        ok(b[end] == n && deg(b) == n - 1 && all(>=(0), b), "b_{n+1} degree/leading/nonneg, n=$n")
        for j in 0:n-1, l in j+1:n
            ok(interlaces(f[j+1], f[l+1]), "Q_{n-1} interlacing ($j,$l), n=$n")
        end
        ok(interlaces(R, h), "R < h_n, n=$n")
        ok(interlaces(R, f[1]), "R < f_0, n=$n")
        for i in 1:n
            ok(interlaces(Ps[i], h), "P_$i < h_n, n=$n")
            ok(interlaces(R, Ps[i]), "R < P_$i, n=$n")
            ok(interlaces(rev(Ps[i], n - 1), h), "rev P_$i < h_n, n=$n")
            ok(interlaces(apart(Ps[i], n), h), "a(P_$i) < h_n, n=$n")
            i < n && ok(interlaces(Ps[i], Ps[i+1]), "P_$i < P_$(i+1), n=$n")
        end
        ok(interlaces(b, h), "b_{n+1} < h_n, n=$n")
        ok(interlaces(h, shift(b, 1)), "MAIN: h_n interlaces theta_{n+1}, n=$n")
        println(io, "n = $n  ok  (checks so far: $nchk)"); flush(io)
    end
    nchk
end
end
