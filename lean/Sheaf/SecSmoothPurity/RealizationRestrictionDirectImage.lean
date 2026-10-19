/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Paper.EtaleProEtaleCoefficientTransport

/-! # Realization respects coefficient restriction and direct image

Source: Stacks Tags 00YV and 03D3, and the section normalization of
lem-sfb-etale-proetale-scalar-mate, Step 2.
(blueprint: lem-sp-realization-restriction-direct-image).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale
private theorem realizationUnit_bijective (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (W : T.ProEtᵒᵖ) : Function.Bijective (sfIntrinsicRealizationUnit T A M W) := by
  let α := finiteCoefficientIntrinsicScalarMap T A
  let E := sheafToPresheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⋙
      finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} A)
  have hi : IsIso ((PresheafOfModules.sheafificationAdjunction α).unit.app (E.obj M)) := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1})).obj M).property
  let hj := (PresheafOfModules.sheafificationAdjunction α).unit.app (E.obj M)
  have : IsIso hj := hi
  have : IsIso ((PresheafOfModules.toPresheaf _).map hj) := inferInstance
  have : IsIso (((PresheafOfModules.toPresheaf _).map hj).app W) := inferInstance
  exact ConcreteCategory.bijective_of_isIso
    (((PresheafOfModules.toPresheaf _).map hj).app W)


/-- Realization's normalized coefficient and direct-image comparisons form a square.
Source: Stacks Tags 00YV and 03D3; the coefficient/site cube in Step 2 of
lem-sfb-etale-proetale-scalar-mate
(blueprint: lem-sp-realization-restriction-direct-image).

Proof: the realization unit is an isomorphism on the underlying abelian sheaf,
so its section maps are bijections. Write a section over the base change of W
as the realization unit of m. The direct-image comparison preserves this unit;
the restriction comparison preserves it as well. The intrinsic coefficient/
direct-image comparison is identity on sections. Substitution of these three
normalizations gives the realization unit of m on both sides. -/
theorem realizationRestrictionDirectImage
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    (proEtaleCoefficientRestrictScalars Y φ).map
        ((sfIntrinsicDirectImageComparison f B).hom.app N) ≫
      (sfRealizationRestriction Y φ).hom.app
        ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).obj N) =
    (proEtaleCoefficientDirectImageComparison f φ).hom.app
        ((sfIntrinsicModuleEquivalence X B).functor.obj N) ≫
      (proEtaleConstantModuleDirectImage f A).map
        ((sfRealizationRestriction X φ).hom.app N) ≫
      (sfIntrinsicDirectImageComparison f A).hom.app
        ((sfFixedRestriction X φ).obj N) := by
  ext W x
  obtain ⟨m, rfl⟩ := (realizationUnit_bijective X B N
    ((proEtaleBaseChange f).op.obj W)).surjective x
  change ((sfRealizationRestriction Y φ).hom.app
      ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).obj N)).val.app W
      (((sfIntrinsicDirectImageComparison f B).hom.app N).val.app W
        (sfIntrinsicRealizationUnit X B N ((proEtaleBaseChange f).op.obj W) m)) =
    ((sfIntrinsicDirectImageComparison f A).hom.app
      ((sfFixedRestriction X φ).obj N)).val.app W
      (((sfRealizationRestriction X φ).hom.app N).val.app _
        (((proEtaleCoefficientDirectImageComparison f φ).hom.app
          ((sfIntrinsicModuleEquivalence X B).functor.obj N)).val.app W
          (sfIntrinsicRealizationUnit X B N ((proEtaleBaseChange f).op.obj W) m)))
  erw [(sfIntrinsicDirectImageComparison_existsUnique f B).exists.choose_spec,
    (sfRealizationRestriction_existsUnique Y φ).exists.choose_spec,
    (Classical.choose_spec (proEtaleCoefficientDirectImageComparison_existsUnique f φ)).1,
    (sfRealizationRestriction_existsUnique X φ).exists.choose_spec]
  change _ = ((sfIntrinsicDirectImageComparison f A).hom.app
      ((sfFixedRestriction X φ).obj N)).val.app W
      (sfIntrinsicRealizationUnit X A ((sfFixedRestriction X φ).obj N)
        ((proEtaleBaseChange f).op.obj W) m)
  erw [(sfIntrinsicDirectImageComparison_existsUnique f A).exists.choose_spec]
  rfl


end AlgebraicGeometry.ProEtale
