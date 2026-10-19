/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic
public import Sheaf.RingTheory.IsMittagLeffler
import Sheaf.RingTheory.Flat.LazardPresentation
import Sheaf.RingTheory.FlatMLDualCriterion
import Sheaf.RingTheory.FlatMittagLefflerMinimalSupport

/-!
# Flat Mittag-Leffler criterion

Source: Stacks Project, Algebra, Tag 059S, lemma-flat-ML-criterion
(blueprint: lem-trf-flat-mittag-leffler-criterion).
-/

@[expose] public section

universe u v w s t

namespace Module

/-- Let `R` be a commutative ring and `M` a flat `R`-module.  Then `M` is
Mittag-Leffler if and only if, for every `R`-module `F` isomorphic to `R^n`
(`n ≥ 0`) and every `x : F ⊗[R] M`, the submodules of `F` whose tensor image
contains `x` have a least element under inclusion.  Source: Stacks Project,
Algebra, Tag 059S, lemma-flat-ML-criterion
(blueprint: lem-trf-flat-mittag-leffler-criterion).

Universes.  The index universe of `Module.IsMittagLeffler` is `max u s`, at least
that of `R`, and the test module `F` lives in `Type (max u w)`.  Both are needed:
the forward implication indexes a product by the submodules of `R^n`, and for an
index universe below that of `R` the predicate is weaker (the fraction field of a
valuation ring whose value group has cofinality beyond that universe passes it but
has no least support for `1`); for `F` below the universe of `R` only `n = 0` may
occur.  Since the predicate passes from a larger index universe to a smaller one by
`ULift`, nothing is lost.

Proof (Stacks 059S, with Tags 0AS6 and 059G):
1. If `M` is Mittag-Leffler, the least-support lemma for flat Mittag-Leffler
   modules (Tag 0AS6, blueprint lem-trf-flat-ml-minimal-support) gives the least
   submodule of `F` whose tensor image contains `x`.
2. Conversely, `M` is flat, so `- ⊗[R] M` is exact and Lazard's theorem writes `M`
   as the colimit of a small directed system of finite free modules `(M_i, f_ij)`
   with canonical maps `f_i : M_i → M`.
3. Fix `i`; for `j ≥ i` let `Q_j` be the image of `Hom(M_j, R) → Hom(M_i, R)`.
   Under `Hom(M_i, R) ⊗ M_j ≅ Hom(M_i, M_j)` (bases of `M_i`, `M_j`), `Q_j` is the
   least submodule `G` of `Hom(M_i, R)` whose tensor image contains `f_ij`.
4. In the same way `f_i ∈ Hom(M_i, R) ⊗ M`; the hypothesis gives a least `Q` with
   `f_i` in the image of `Q ⊗ M`; `f_i = f_j ∘ f_ij` gives `Q ≤ Q_j` for `j ≥ i`.
5. Tensor products commute with the colimit and finite free modules are flat, so a
   preimage of `f_i` in some `Q ⊗ M_l` and `f_ii` agree at a stage `j ≥ l, i`; then
   `f_ij` lies in the image of `Q ⊗ M_j`, so `Q_j ≤ Q`, and `Q_k = Q` for `k ≥ j`.
6. Hence every dual system `(Hom(M_i, R))` is Mittag-Leffler, and the dual
   criterion (Tag 059G, blueprint lem-trf-flat-ml-dual-criterion) shows that `M`
   is Mittag-Leffler.
-/
theorem flat_mittag_leffler_criterion
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Flat R M] :
    Module.IsMittagLeffler.{u, v, max u s, t} R M ↔
      ∀ (F : Type (max u w)) [AddCommGroup F] [Module R F],
        (∃ n : ℕ, Nonempty (F ≃ₗ[R] (Fin n → R))) →
          ∀ (x : TensorProduct R F M),
            ∃ G₀ : Submodule R F,
              x ∈ Set.range (LinearMap.rTensor M G₀.subtype) ∧
                ∀ G : Submodule R F,
                  x ∈ Set.range (LinearMap.rTensor M G.subtype) → G₀ ≤ G := by
  sorry

end Module
