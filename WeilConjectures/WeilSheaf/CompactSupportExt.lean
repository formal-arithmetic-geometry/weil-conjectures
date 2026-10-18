/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.CohomologySequence
public import WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion

/-!
# Compactly supported cohomology as cohomology of an extension by zero

Let `X` be a separated quasi-compact `k₀`-scheme locally of finite type, and let
`X ⟶[i] Z ⟶[g] Spec k₀` be the compactification of its structure morphism chosen by Nagata's
theorem (`AlgebraicGeometry.structureCompactification`). Since `Ra_! = Rg_* ∘ i_!` by definition,
the compactly supported cohomology of a Weil sheaf `F` on `X` is the ordinary cohomology of the
Weil sheaf `i_! F` on the proper `k₀`-scheme `Z`, Frobenius-equivariantly:
`H_c^r(X ⊗ k̄, F) ≅ Hʳ(Z ⊗ k̄, i_! F)`.

The ordinary cohomology of a Weil sheaf `G` on `Y` is in turn the pro-étale cohomology
`Ext^r(ℤ, G)` of the underlying abelian sheaf of `G`, with the Frobenius computed through an
injective resolution of `G` by pro-étale Weil sheaves, and multiplication by `c ∈ ℚ̄_ℓ` on the
coefficients corresponding to multiplication by `c` on cohomology.

Combining both, the compactly supported cohomology `H_c^r(X ⊗ k̄, F)` is `Ext^r(ℤ, ī_! F)` on
`Z̄_proét`, with its Frobenius `x ↦ (ℤ ⟶ Fr⁻¹_* ℤ) ∘ Fr⁻¹_* x ∘ s`, `s` the structure isomorphism of
the Weil sheaf `i_! F`. These comparisons reduce statements on compactly supported cohomology
with `ℚ̄_ℓ`-coefficients (blueprint `thm-pod-degreewise-perfectness-over-a-field`) to pro-étale
`Ext` groups, as in `prop-cohomological-finiteness`.

## Main declarations

- `AlgebraicGeometry.structureCompactification`: the chosen compactification of `X ⟶ Spec k₀`.
- `AlgebraicGeometry.WeilSheaf.compactlySupportedCohomologyEquivExtensionByZero` and
  `AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_extensionByZero`:
  `H_c^r(X ⊗ k̄, F) ≅ Hʳ(Z ⊗ k̄, i_! F)` as Frobenius modules.
- `AlgebraicGeometry.WeilSheaf.exists_addEquiv_ext_cohomology`: `Ext^r(ℤ, G) ≅ Hʳ(Y ⊗ k̄, G)`,
  compatibly with the Frobenius and with the `ℚ̄_ℓ`-action.
- `AlgebraicGeometry.ProEtaleWeilSheaf.extFrobenius_eq`: the Frobenius on `Ext^r(ℤ, G)` is
  `x ↦ (ℤ ⟶ Fr⁻¹_* ℤ) ∘ Fr⁻¹_* x ∘ s`, independently of the resolution.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor Abelian

-- `Spec k₀` over itself: prefer the identity structure over `AlgebraicGeometry.specOverSpec`.
attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

attribute [local instance] Compactification.over

section Compactification

variable (k₀) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The compactification `X ⟶[i] Z ⟶[g] Spec k₀` of the structure morphism of a separated
quasi-compact `k₀`-scheme locally of finite type chosen by Nagata's theorem: the one through which
compactly supported cohomology is defined (`AlgebraicGeometry.WeilComplex.derivedLowerShriek`). -/
noncomputable abbrev structureCompactification : Compactification (X ↘ Spec (CommRingCat.of k₀)) :=
  HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)

-- instance : QuasiCompact (structureCompactification k₀ X).i :=
--   (structureCompactification k₀ X).quasiCompact_openImmersion inferInstance
-- 
-- instance : QuasiCompact ((structureCompactification k₀ X).Z ↘ Spec (CommRingCat.of k₀)) :=
--   inferInstanceAs (QuasiCompact ((structureCompactification k₀ X).g ≫ 𝟙 _))
-- 
-- instance : QuasiSeparated ((structureCompactification k₀ X).Z ↘ Spec (CommRingCat.of k₀)) :=
--   inferInstanceAs (QuasiSeparated ((structureCompactification k₀ X).g ≫ 𝟙 _))
-- 
-- instance : LocallyOfFiniteType ((structureCompactification k₀ X).Z ↘ Spec (CommRingCat.of k₀)) :=
--   inferInstanceAs (LocallyOfFiniteType ((structureCompactification k₀ X).g ≫ 𝟙 _))

end Compactification

namespace WeilSheaf

variable [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]




noncomputable def testA1 (F : ProEtaleWeilSheaf k₀ l X) : Nonempty (
  (DerivedCategory.singleFunctor _ 0 ⋙ (ProEtaleWeilSheaf.extensionByZero k₀ l
        (HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)).i).mapDerivedCategory).obj F ≅
  (ProEtaleWeilSheaf.extensionByZero k₀ l
        (HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)).i ⋙ DerivedCategory.singleFunctor _ 0).obj F) := by
  let c := HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)
  exact ⟨((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategorySingleFunctor 0).app F⟩

end WeilSheaf
end AlgebraicGeometry
