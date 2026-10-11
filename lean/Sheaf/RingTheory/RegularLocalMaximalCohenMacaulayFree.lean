/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Sheaf.RingTheory.Depth

/-!
# Maximal Cohen–Macaulay modules over regular local rings

Source: Stacks Project, Algebra, Lemma 10.106.6 (Tag 00NT) and Definition 10.103.8
(Tag 00NF) (blueprint: lem-weil-pbc-regular-local-mcm-free).
-/

@[expose] public section

universe u v

namespace IsRegularLocalRing

/-- A finite module of depth `d` over a regular local ring of dimension `d` is free,
with a finite basis (Stacks, Tags 00NT and 00NF)
(blueprint: lem-weil-pbc-regular-local-mcm-free).

Proof, following the node's split of Stacks 00NT:
1. Induct on `d`, quantifying over all regular local rings of that dimension.
   The depth definition (def-weil-pbc-depth) gives depth infinity for the zero module,
   so the depth hypothesis makes `M` nonzero.
2. For `d = 0`, the maximal ideal is zero and `R` is a field. Thus `M` is free by
   lem-weil-pbc-vector-space-free. Finite generation makes its basis finite: the union
   of the supports of finitely many generators spans, so independence excludes other vectors.
3. For `d > 0`, choose the first element `x` of a regular system of parameters.
   By lem-weil-pbc-regular-local-generators-regular-sequence, `R/xR` is regular local
   of dimension `d - 1`.
4. By lem-weil-pbc-depth-le-support-dimension, the support of `M` has dimension `d`.
   The support intersected with `V(x)` has dimension at most `d - 1` by step 3 and
   at least `d - 1` by lem-weil-pbc-support-dimension-quotient-element-bound and
   the inclusion of the support of `M/xM` in that intersection. Hence equality holds.
5. Apply lem-weil-pbc-cm-module-good-element-nonzerodivisor: `x` is a nonzerodivisor
   on `M` and the depth over `R` of `M/xM` is `d - 1`.
6. The quotient is finite over `R/xR`. Its depths over `R` and `R/xR` agree by
   def-weil-pbc-depth and def-weil-pbc-regular-sequence: scalar multiplication on
   all successive quotients is the same, and sequences in the quotient maximal ideal lift.
7. Induction makes `M/xM` free over `R/xR`. Then lem-weil-pbc-free-mod-nonzerodivisor
   makes `M` free over `R`; its basis is finite by the argument of step 2, giving
   the displayed isomorphism with a finite direct sum of copies of `R`. -/
theorem free_of_depth_eq_ringKrullDim
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (d : ℕ) (hdim : ringKrullDim R = (d : WithBot ℕ∞))
    (hdepth : IsLocalRing.depth (R := R) M = (d : ℕ∞)) :
    Module.Free R M ∧ ∃ r : ℕ, Nonempty (M ≃ₗ[R] (Fin r →₀ R)) := by
  sorry

end IsRegularLocalRing
