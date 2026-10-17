/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheafCohomology
public import WeilConjectures.WeilSheaf.CohomologyProEtale
public import WeilConjectures.WeilSheaf.Constant

/-!
# Vanishing of the cohomology of the constant Weil sheaf outside `[0, 2e]`

Let `X` be a quasi-compact quasi-separated `k₀`-scheme of finite type whose geometric fiber
`X̄ = X ⊗ k̄` has dimension at most `e`. Then the cohomology `Hʳ(X ⊗ k̄, ℚ̄_ℓ)` of the constant
Weil sheaf vanishes for `r < 0` and for `r > 2e` (blueprint `prop-cohomological-finiteness`,
`sk-lem-finite`).

The proof compares, forgetting the Frobenius, `Hʳ(X ⊗ k̄, ℚ̄_ℓ)` with the pro-étale cohomology
`Hʳ(X̄_proét, ℚ̄_ℓ)` of the constant `ℓ`-adic sheaf
(`AlgebraicGeometry.WeilSheaf.cohomologyIsoRightDerivedGlobalSections`), computed in sheaves of
`ℚ̄_ℓ`-modules, then with the cohomology of the underlying abelian sheaf
(`AlgebraicGeometry.ProEtale.forgetRightDerivedGlobalSectionsIso`), which vanishes above `2e`
(`AlgebraicGeometry.ProEtale.subsingleton_H_adicConstantSheaf_of_two_mul_lt`): `ℚ̄_ℓ,X̄` is a
filtered union of sheaves `C(-, L)` for compact lattices `L ≅ ℤ_ℓʳ`, whose cohomology is the
limit of the étale cohomology with coefficients `L/ℓᵐ`, of cohomological dimension `2e`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant_of_topologicalKrullDim`:
  `Hʳ(X ⊗ k̄, ℚ̄_ℓ) = 0` for `r ∉ [0, 2e]`.
- `AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant_of_smooth`: the case of `X`
  smooth of pure dimension `d`, with `e = d`.
-/

@[expose] public section

/- The comparison with étale cohomology imports `AlgebraicGeometry.specOverSpec` (from
`Mathlib.AlgebraicGeometry.Group.Affine`), which gives `Spec k₀` a second structure over
itself, `Spec.map (algebraMap k₀ k₀)`. The Weil sheaves on `Spec k₀` of the repository are
formed for the identity structure; we give it priority so that downstream files keep
elaborating `Spec k₀ ↘ Spec k₀` as the identity. -/
attribute [instance high] CategoryTheory.instOverClass

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]


instance : IsAddTorsionFree (ULift.{u + 1} (PadicAlgCl l)) :=
  ⟨fun _ hn _ _ h ↦ ULift.ext _ _ (nsmul_right_injective hn (congrArg ULift.down h))⟩

variable (k₀ l X) in
/-- Blueprint `prop-cohomological-finiteness` (constant sheaf, `sk-lem-finite`): if the
geometric fiber `X ⊗ k̄` has dimension at most `e`, the cohomology `Hʳ(X ⊗ k̄, ℚ̄_ℓ)` of the
constant Weil sheaf vanishes for `r < 0` and for `r > 2e`. -/
theorem subsingleton_cohomology_adicConstant_of_topologicalKrullDim (e : ℕ)
    (he : topologicalKrullDim (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≤ (e : WithBot ℕ∞))
    {r : ℤ} (hr : r < 0 ∨ 2 * (e : ℤ) < r) :
    Subsingleton ((adicConstant k₀ l X).cohomology r).carrier := by
  rcases hr with hr | hr
  · exact subsingleton_cohomology_of_lt_zero _ hr
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, r = ((m + 1 : ℕ) : ℤ) := ⟨(r - 1).toNat, by omega⟩
  set a := X ↘ Spec (CommRingCat.of k₀)
  let X' := a.geometricFiber
  have : CompactSpace X' :=
    QuasiCompact.compactSpace_of_compactSpace a.geometricFiberToAlgebraicClosure
  have : QuasiSeparatedSpace X' :=
    quasiSeparatedSpace_of_quasiSeparated a.geometricFiberToAlgebraicClosure
  have h₁ : Subsingleton (Sheaf.H (ProEtale.adicConstantSheafAb l X') (m + 1)) :=
    ProEtale.subsingleton_H_adicConstantSheaf_of_two_mul_lt l a.geometricFiberToAlgebraicClosure
      e he (m + 1) (by omega)
  obtain ⟨e₁⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    (Scheme.ProEt.topology X') _ (Scheme.ProEt.isTerminalMkId X')
    (ProEtale.adicConstantSheafAb l X') m
  let e₂ := ProEtale.forgetRightDerivedGlobalSectionsIso (ULift.{u + 1} (PadicAlgCl l)) X'
    (ProEtale.adicConstantSheaf l X') (m + 1)
  have : ((sheafSections (Scheme.ProEt.topology X') (WeilCoefficients.{u} l)).obj
      (Opposite.op (Scheme.ProEt.mk (𝟙 X')))).Additive := { map_add := rfl }
  have : (ProEtale.globalSectionsFunctor (WeilCoefficients.{u} l) X').Additive :=
    { map_add := rfl }
  let e₃ : ((Sheaf.Γ (Scheme.ProEt.topology X') (WeilCoefficients.{u} l)).rightDerived
      (m + 1)).obj (ProEtale.adicConstantSheaf l X') ≅
      ((ProEtale.globalSectionsFunctor (WeilCoefficients.{u} l) X').rightDerived (m + 1)).obj
        (ProEtale.adicConstantSheaf l X') :=
    Functor.rightDerivedObjIsoOfIso
      (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X')) (m + 1) _
  have h₂ : Subsingleton ((forget₂ (WeilCoefficients.{u} l) AddCommGrpCat.{u + 1}).obj
      (((ProEtale.globalSectionsFunctor (WeilCoefficients.{u} l) X').rightDerived (m + 1)).obj
        (ProEtale.adicConstantSheaf l X'))) :=
    (e₂.addCommGroupIsoToAddEquiv.trans e₁.symm).toEquiv.subsingleton
  refine subsingleton_cohomology_of_isZero_rightDerived _ (m + 1) ?_
  refine IsZero.of_iso ?_ e₃
  have : Subsingleton (((ProEtale.globalSectionsFunctor (WeilCoefficients.{u} l) X').rightDerived
      (m + 1)).obj (ProEtale.adicConstantSheaf l X')) := h₂
  exact ModuleCat.isZero_of_subsingleton _

variable (k₀ l X) in
/-- Blueprint `sk-lem-finite` (constant-sheaf clause): the cohomology `Hⁱ(X ⊗ k̄, ℚ̄_ℓ)` of a
smooth `k₀`-scheme of finite type and pure dimension `d` vanishes for `i ∉ [0, 2d]`, the
geometric fiber `X ⊗ k̄` being smooth of relative dimension `d` over `k̄`, hence of dimension
at most `d`. -/
theorem subsingleton_cohomology_adicConstant_of_smooth (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] {i : ℤ}
    (hi : i < 0 ∨ 2 * (d : ℤ) < i) :
    Subsingleton ((adicConstant k₀ l X).cohomology i).carrier := by
  have : SmoothOfRelativeDimension d
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (SmoothOfRelativeDimension d (Limits.pullback.snd _ _))
  exact subsingleton_cohomology_adicConstant_of_topologicalKrullDim k₀ l X d
    (topologicalKrullDim_le_of_smoothOfRelativeDimension
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure d) hi

end WeilSheaf

end AlgebraicGeometry
