# Lean 4 certificate

Lean 4 (toolchain in `lean-toolchain`) with Mathlib `v4.36.0-rc2`.

* `AntiprismLean/Identity.lean`: the telescoping identity behind the decomposition
  b_{n+1} = a(P_1) + ... + a(P_n), for any additive group and two additive maps.
* `AntiprismLean/StepOne.lean`: the identity specialised to polynomials.
* `AntiprismLean/Signs.lean`: the sign transfer inequality used at the roots of h_n.
* `AntiprismLean/Data.lean`: exact integer checks of the recurrence, the table of
  Athanasiadis–Brunink–Juhnke-Kubitzke and the decomposition for 2 <= n <= 11, by `decide`.
* `Axioms.lean`: prints the axioms used (only `propext`, `Classical.choice`, `Quot.sound`).

Build: `lake exe cache get && lake build && lake env lean Axioms.lean`.
