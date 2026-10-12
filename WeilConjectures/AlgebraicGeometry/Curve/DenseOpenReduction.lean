/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.DenseOpen
public import WeilConjectures.AlgebraicGeometry.Curve.Reductions

/-!
# Localisation of the eight curve assertions to a dense open

Let `X` be a reduced curve over an algebraically closed field `k` and `F` a constructible sheaf
of `𝐅_r`-modules on `X`. There is a dense open `j : U ⟶ X`, a finite disjoint union of
irreducible opens `U_a`, on which `F` is finite locally constant, and the eight curve
assertions for `F` are equivalent to those for `j_! j^* F`, and to those for all the
`j_{a,!} (F|_{U_a})`.

## Main statements

- `AlgebraicGeometry.IsCurve.exists_dense_assertions_iff_lowerShriek`: localisation to a dense
  open on which the coefficients are finite locally constant.
- `AlgebraicGeometry.IsCurve.exists_dense_assertions_iff_forall_lowerShriek`: the same, split
  along the irreducible components of the dense open.

## References

- Stacks Project, Section 59.83, <https://stacks.math.columbia.edu/tag/03SB>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Dense-open localisation reduction.** Let `X` be a reduced curve over an algebraically
closed field `k` and `F` a constructible sheaf of `Λ`-modules killed by a prime `r`, over a
finite ring `Λ`. There is a dense open `j : U ⟶ X` whose connected components are irreducible
and on which `F` is finite locally constant, and for it the eight assertions for `F` are
equivalent to those for `j_! j^* F`: the open–closed sequence `0 → j_! j^* F → F → i_* i^* F → 0`
has third term
supported on the zero-dimensional complement `Z` of `U`, whose cohomology is concentrated in
degree zero and invariant under field extension.
(blueprint: `lemma-weil-pbc-curve-dense-open-reduction`) -/
theorem IsCurve.exists_dense_assertions_iff_lowerShriek [Finite Λ] {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (r : ℕ) [Fact r.Prime] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (hF : r • 𝟙 F = 0) :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      (∀ x ∈ (U : Set X), IsIrreducible (connectedComponentIn (U : Set X) x)) ∧
      Scheme.IsFiniteLocallyConstantSheaf ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F) ∧
      (IsCurve.Assertions Λ f F ↔ IsCurve.Assertions Λ f
        ((U.ι)_!open[ModuleCat.{u + 1} Λ].obj ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F))) :=
  sorry

/-- **Dense-open localisation, componentwise.** Let `C` be a reduced curve over an
algebraically closed field `k` and `F` a constructible sheaf of `Λ`-modules killed by a prime
`r`, over a finite ring `Λ`. There are finitely many pairwise disjoint irreducible opens
`U_a ⊆ C`, with dense union `U` and zero-dimensional complement `Z = C ∖ U`, on each of which
`F` is finite locally constant, such that, writing `j_a : U_a ⟶ C` for the inclusions,
`C(C, F) ↔ ∀ a, C(C, j_{a,!}(F|_{U_a}))`. This combines the open–closed sequence
`0 → j_! j^* F → F → i_* i^* F → 0`, the assertions on the zero-dimensional `Z`, the
decomposition `j_! j^* F = ⨁_a j_{a,!}(F|_{U_a})` and dévissage.
(blueprint: `lem-weil-pbc-curve-dense-open-localization`) -/
theorem IsCurve.exists_dense_assertions_iff_forall_lowerShriek [Finite Λ] {k : Type u}
    [Field k]
    [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsReduced C]
    (r : ℕ) [Fact r.Prime] (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (hF : r • 𝟙 F = 0) :
    ∃ (n : ℕ) (U : Fin n → C.Opens), Dense (⋃ a, (U a : Set C)) ∧
      Pairwise (fun a b ↦ Disjoint (U a : Set C) (U b)) ∧ (∀ a, IsIrreducible (U a : Set C)) ∧
      topologicalKrullDim ↥(⋃ a, (U a : Set C))ᶜ ≤ 0 ∧
      (∀ a, Scheme.IsFiniteLocallyConstantSheaf (((U a).ι)^*[ModuleCat.{u + 1} Λ].obj F)) ∧
      (IsCurve.Assertions Λ f F ↔ ∀ a, IsCurve.Assertions Λ f
        (((U a).ι)_!open[ModuleCat.{u + 1} Λ].obj (((U a).ι)^*[ModuleCat.{u + 1} Λ].obj F))) :=
  sorry

end AlgebraicGeometry
