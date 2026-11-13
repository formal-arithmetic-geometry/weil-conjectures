/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices

/-! # The fixed untwisted comparison

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives
noncomputable section

/-- The comparison is composed from the actual section isomorphism and resolution
isomorphism; no witness of an unproved existence theorem is chosen. -/
def resolutionOpenComparison {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (R : RestrictedResolutionSections I (f ⁻¹ᵁ W)) :
    (sectionCohomologyPresheaf
      (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex) q).obj (op W) ≃+
      (RingedSpace.openModuleCohomology (f ⁻¹ᵁ W).toScheme.toRingedSpace q ⊤).obj
        ((restrictFunctor (f ⁻¹ᵁ W).ι).obj F) := by
  let Y := (f ⁻¹ᵁ W).toScheme
  let : (RingedSpace.openModuleSections Y.toRingedSpace ⊤).Additive :=
    RingedSpace.openModuleSections_additive Y.toRingedSpace ⊤
  let K := ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let B := ((SheafOfModules.forget T.ringCatSheaf).mapHomologicalComplex (.up ℕ)).obj K
  let E := PresheafOfModules.toPresheaf T.ringCatSheaf.obj ⋙
    (evaluation T.Opensᵒᵖ AddCommGrpCat.{u}).obj (op W)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) q
  let eB := (B.sc q).mapHomologyIso E
  let eR := R.resolution.isoRightDerivedObj (RingedSpace.openModuleSections
    Y.toRingedSpace ⊤) q
  let e : (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).obj
        ((restrictFunctor (f ⁻¹ᵁ W).ι).obj F) ≅
      AddCommGrpCat.of ((sectionCohomologyPresheaf K q).obj (op W)) :=
    eR ≪≫ H.mapIso R.sections ≪≫ eB
  exact e.symm.addCommGroupIsoToAddEquiv

end
end AlgebraicGeometry.Scheme.Modules
