/-!
# Kernel-checked antiprism data

Integer coefficient lists (constant term first).  Everything below is evaluated
by the Lean kernel (`decide`), with no `native_decide` and no axioms beyond the
standard ones.

* `h n`  = h-polynomial of the antiprism triangulation of the (n-1)-simplex,
  from the recurrence `h_n = ∑_{k<n} binom(n,k) x^k h_k(1/x)` (ABJK, eq. (12));
* `b n`  = `(h_n - x^{n-1} h_n(1/x)) / (x - 1)`;
* `q n r = ∑_k binom(n,k) x^{k+r} h_{k+r}(1/x)`.

We check, for `2 ≤ n ≤ 11`: the published table, the identity (17)
`h_{n+1} = ∑_{j=0}^{n} (j+1) f_j`, `P_n = h_n`, `f_n = x · rev_{n-1} h_n`, and the
Step 1 identity `b_{n+1} = ∑_{i=1}^{n} a(P_i)`, together with
`deg b_{n+1} = n-1`, leading coefficient `n` and nonnegative coefficients.
-/

namespace AntiprismData

def trim : List Int → List Int
  | l => (l.reverse.dropWhile (· == 0)).reverse

def padd : List Int → List Int → List Int
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: padd p q

def pscale (c : Int) (p : List Int) : List Int := p.map (c * ·)

def psub (p q : List Int) : List Int := padd p (pscale (-1) q)

/-- `x^d p(1/x)` (coefficients of degree `> d` are dropped; never used). -/
def rev (p : List Int) (d : Nat) : List Int :=
  (List.range (d + 1)).map fun i => p.getD (d - i) 0

def shift (p : List Int) : List Int := 0 :: p

/-- Pascal row `n`. -/
def pascal : Nat → List Nat
  | 0 => [1]
  | n + 1 => let r := pascal n; List.zipWith (· + ·) (0 :: r) (r ++ [0])

def binom (n k : Nat) : Int := ((pascal n).getD k 0 : Nat)

/-- `[h_0, …, h_N]`. -/
def hs : Nat → List (List Int)
  | 0 => [[1]]
  | n + 1 =>
    let prev := hs n
    prev ++ [trim ((List.range (n + 1)).foldl
      (fun s k => padd s (pscale (binom (n + 1) k) (rev (prev.getD k []) k))) [])]

def H : List (List Int) := hs 12
def h (n : Nat) : List Int := H.getD n []

/-- Division by `x - 1` of a polynomial vanishing at 1 (synthetic division). -/
def divXsub1 (p : List Int) : List Int :=
  -- p = (x-1) q;  q_{k} = -(p_0 + … + p_k)
  trim ((List.range (p.length - 1)).map fun k => -((p.take (k + 1)).foldl (· + ·) 0))

def b (n : Nat) : List Int := divXsub1 (psub (h n) (rev (h n) (n - 1)))

def q (n r : Nat) : List Int :=
  trim ((List.range (n + 1)).foldl
    (fun s k => padd s (pscale (binom n k) (rev (h (k + r)) (k + r)))) [])

def f (n j : Nat) : List Int := if j < n then q (n - 1 - j) j else q 0 n

def P (n i : Nat) : List Int := trim ((List.range i).foldl (fun s j => padd s (f n j)) [])

/-- a-part with respect to `n - 1`. -/
def apart (n : Nat) (p : List Int) : List Int := divXsub1 (psub (shift (rev p (n - 1))) p)

def checkN (n : Nat) : Bool :=
  let bn := b (n + 1)
  -- (17)
  trim ((List.range (n + 1)).foldl (fun s (j : Nat) => padd s (pscale ((j : Int) + 1) (f n j))) []) == h (n + 1)
  -- P_n = h_n,  f_n = x rev_{n-1} h_n
  && P n n == h n
  && f n n == trim (shift (rev (h n) (n - 1)))
  -- Step 1
  && trim ((List.range n).foldl (fun s i => padd s (apart n (P n (i + 1)))) []) == bn
  -- degree n-1, leading coefficient n, nonnegative coefficients
  && bn.length == n && bn.getLast? == some (n : Int) && bn.all (· ≥ 0)

theorem table_h4 : h 4 = [1, 28, 42, 4] := by decide
theorem table_h7 : h 7 = [1, 441, 8211, 23625, 13685, 1323, 7] := by decide
theorem b_small : b 3 = [2, 2] ∧ b 4 = [3, 17, 3] := by decide

theorem checks : (List.range 10).all (fun k => checkN (k + 2)) = true := by decide

end AntiprismData
