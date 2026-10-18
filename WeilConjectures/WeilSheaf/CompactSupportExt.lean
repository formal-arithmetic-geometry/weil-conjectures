/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.CohomologySequence
public import WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion
import WeilConjectures.WeilSheaf.CompactSupportAdicConstant

/-!
# Compactly supported cohomology as cohomology of an extension by zero

Let `X` be a separated quasi-compact `k₀`-scheme locally of finite type, and let
`X ⟶[i] Z ⟶[g] Spec k₀` be the compactification of its structure morphism chosen by Nagata's
theorem (`AlgebraicGeometry.structureCompactification`). Since `Ra_! = Rg_* ∘ i_!` by definition,
the compactly supported cohomology of a Weil sheaf `F` on `X` is the ordinary cohomology of the
Weil sheaf `i_! F` on the proper `k₀`-scheme `Z`, Frobenius-equivariantly:
`H_c^r(X ⊗ k̄, F) ≅ Hʳ(Z ⊗ k̄, i_! F)`.

Together with the description of ordinary cohomology as pro-étale `Ext`
(`WeilConjectures.WeilSheaf.CompactSupportExtFrobenius`), this reduces statements on compactly
supported cohomology with `ℚ̄_ℓ`-coefficients (blueprint
`thm-pod-degreewise-perfectness-over-a-field`) to pro-étale `Ext` groups on `Z̄_proét`, as in
`prop-cohomological-finiteness`.

## Main declarations

- `AlgebraicGeometry.structureCompactification`: the chosen compactification of `X ⟶ Spec k₀`.
- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_extensionByZero`:
  `H_c^r(X ⊗ k̄, F) ≅ Hʳ(Z ⊗ k̄, i_! F)` as Frobenius modules.
-/

@[expose] public section

universe u

open CategoryTheory Limits

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
compactly supported cohomology is defined (`AlgebraicGeometry.WeilComplex.derivedLowerShriek`).
The scheme `Z` is a `k₀`-scheme through `g` (`AlgebraicGeometry.Compactification.over`). -/
noncomputable abbrev structureCompactification :
    Compactification (X ↘ Spec (CommRingCat.of k₀)) :=
  HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)

instance : QuasiCompact (structureCompactification k₀ X).i :=
  (structureCompactification k₀ X).quasiCompact_openImmersion inferInstance

instance : QuasiCompact ((structureCompactification k₀ X).Z ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (QuasiCompact ((structureCompactification k₀ X).g ≫ 𝟙 _))

instance : QuasiSeparated ((structureCompactification k₀ X).Z ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (QuasiSeparated ((structureCompactification k₀ X).g ≫ 𝟙 _))

instance :
    LocallyOfFiniteType ((structureCompactification k₀ X).Z ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (LocallyOfFiniteType ((structureCompactification k₀ X).g ≫ 𝟙 _))

end Compactification

namespace WeilSheaf

variable [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **Compactly supported cohomology is cohomology of the extension by zero.** For a Weil sheaf
`F` on `X` and the chosen compactification `X ⟶[i] Z ⟶[g] Spec k₀`
(`AlgebraicGeometry.structureCompactification`), `H_c^r(X ⊗ k̄, F) ≅ Hʳ(Z ⊗ k̄, i_! F)`,
compatibly with the geometric Frobenii: by definition `Ra_! F = Rg_*(i_! F)`, the extension by
zero `i_!` being exact, and `g` is the structure morphism of `Z`. -/
theorem nonempty_equiv_compactlySupportedCohomology_extensionByZero (F : WeilSheaf k₀ l X)
    (r : ℤ) :
    Nonempty ((F.compactlySupportedCohomology r).Equiv
      (((extensionByZero (HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
        (hf := hasCompactification_of_over (k₀ := k₀) _)).i).obj F).cohomology r)) := by
  let c := HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)
  -- the isomorphism of underlying complexes, stated explicitly to keep the kernel check cheap
  have e : (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F.obj)) ≅
      (ProEtaleWeilSheaf.lowerStar k₀ l (c.Z ↘ Spec (CommRingCat.of k₀))).rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).obj F.obj)) :=
    (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
      (((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategorySingleFunctor 0).app
        F.obj) ≪≫
    (Functor.rightDerivedFunctorNatIso
      (ProEtaleWeilSheaf.lowerStarCongr k₀ l (Category.comp_id c.g).symm)).app _
  have e' : (WeilComplex.derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
        (toComplex.obj F) ≅
      (WeilComplex.derivedLowerStar (c.Z ↘ Spec (CommRingCat.of k₀))).obj
        (toComplex.obj ((extensionByZero c.i).obj F)) :=
    ObjectProperty.isoMk _ e
  exact ⟨WeilComplex.cohomologyEquivOfIso e' r⟩

end WeilSheaf

end AlgebraicGeometry
