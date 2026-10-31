/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackComparison
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import all WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted

/-! # Derived canonical scalar pullback comparison

Source: the derived exact-functor composition and natural-isomorphism comparisons.
(blueprint: def-sbc-raw-scalar-derived-pullback-iso).
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private theorem reverseDerivedComparison {C D E B : Type*}
    [Category C] [Category D] [Category E] [Category B]
    [Abelian C] [Abelian D] [Abelian E] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory B]
    (M : C ⥤ D) (VA : D ⥤ B) (V : C ⥤ E) (H : E ⥤ B)
    [M.Additive] [VA.Additive] [V.Additive] [H.Additive]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    [PreservesFiniteLimits VA] [PreservesFiniteColimits VA]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : V ⋙ H ≅ M ⋙ VA) :
    (mapDerivedCategoryPlusCompIso M VA).symm ≪≫ mapDerivedCategoryPlusNatIso e.symm ≪≫
        mapDerivedCategoryPlusCompIso V H =
      ((mapDerivedCategoryPlusCompIso V H).symm ≪≫ mapDerivedCategoryPlusNatIso e ≪≫
        mapDerivedCategoryPlusCompIso M VA).symm := by
  rw [plusNatIso_symm]
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Category.assoc]
end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.RawModuleScalarComparison

/-- Forget scalar operations on a module sheaf.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
noncomputable abbrev forget (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :=
  moduleAbelianForget Λ X

/-- Scalar forgetting is additive, section by section.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
instance forget_additive (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (forget Λ X).Additive := moduleAbelianForget_additive Λ X

/-- Scalar forgetting preserves finite limits, as does its presheaf composite.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
instance forget_preservesFiniteLimits (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    PreservesFiniteLimits (forget Λ X) := moduleAbelianForget_preservesFiniteLimits Λ X

/-- Scalar forgetting preserves finite colimits by the constant-coefficient theorem.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
instance forget_preservesFiniteColimits (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    PreservesFiniteColimits (forget Λ X) := moduleAbelianForget_preservesFiniteColimits Λ X

/-- Compose the derived exact-functor comparisons for scalar forgetting.
(blueprint: def-sbc-raw-scalar-derived-pullback-iso). -/
noncomputable def derivedPullbackIsoImpl (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (forget Λ X).mapDerivedCategoryPlus ≅
      (forget Λ Y).mapDerivedCategoryPlus ⋙
        (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus :=
  (moduleAbelianDerivedUpperStarIso Λ f).symm

/-- Historical name for the inverse canonical derived scalar comparison.
Source: the exact derived comparison and its inverse-isomorphism construction.
The explicit inverse structure keeps both components reducible, as in the original API.
(blueprint: def-sbc-raw-scalar-derived-pullback-iso). -/
noncomputable abbrev derivedPullbackIso (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (forget Λ X).mapDerivedCategoryPlus ≅
      (forget Λ Y).mapDerivedCategoryPlus ⋙
        (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus where
  hom := (moduleAbelianDerivedUpperStarIso Λ f).inv
  inv := (moduleAbelianDerivedUpperStarIso Λ f).hom
  hom_inv_id := (moduleAbelianDerivedUpperStarIso Λ f).inv_hom_id
  inv_hom_id := (moduleAbelianDerivedUpperStarIso Λ f).hom_inv_id


/-- The inverse canonical comparison is exactly the historical reverse composite.
Source: the natural-isomorphism symmetry identity for exact derived functors.
Proof: derived lifting sends an inverse natural isomorphism to the inverse lifted
isomorphism. Reversing the three factors and associating composition gives the
canonical forward comparison's inverse.
(blueprint: def-sbc-raw-scalar-derived-pullback-iso). -/
theorem derivedPullbackIsoImpl_eq_formula (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Functor.mapDerivedCategoryPlusCompIso
      (upperStar (ModuleCat.{u + 1} Λ) f) (forget Λ X)).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso (pullbackIso Λ f) ≪≫
      Functor.mapDerivedCategoryPlusCompIso
        (forget Λ Y) (upperStar AddCommGrpCat.{u + 1} f) =
      derivedPullbackIsoImpl Λ f := by
  unfold derivedPullbackIsoImpl moduleAbelianDerivedUpperStarIso
  exact Functor.reverseDerivedComparison
    (upperStar (ModuleCat.{u + 1} Λ) f) (forget Λ X) (forget Λ Y)
    (upperStar AddCommGrpCat.{u + 1} f) (moduleAbelianUpperStarIso Λ f)

/-- The scalar pullback comparison has the forgotten module unit as its adjoint.
Source: Stacks Project, Tags 03D3 and 03D7, the inverse-image adjunction.
Proof: the canonical comparison is the inverse image of the forgotten module
unit under the abelian adjunction Hom equivalence. Applying that equivalence
recovers the module unit by `Equiv.apply_symm_apply`.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
theorem pullback_unit (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((forget Λ Y).obj F) ≫
      (lowerStar AddCommGrpCat.{u + 1} f).map (pullback Λ f F) =
      (forget Λ Y).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F) := by
  change (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
    ((moduleAbelianUpperStarComparison Λ f).app F) = _
  exact Equiv.apply_symm_apply _ _

/-- The unit equation uniquely determines the scalar pullback comparison.
Source: Stacks Project, Tags 03D3 and 03D7, the inverse-image adjunction.
Proof: apply the injective abelian adjunction Hom equivalence. Its value on
each map is the unit followed by the direct image of that map, so the asserted
unit equation and `pullback_unit` identify the two values.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
theorem eq_pullback_of_unit (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (c : (upperStar AddCommGrpCat.{u + 1} f).obj ((forget Λ Y).obj F) ⟶
      (forget Λ X).obj ((upperStar (ModuleCat.{u + 1} Λ) f).obj F))
    (hc : (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((forget Λ Y).obj F) ≫ (lowerStar AddCommGrpCat.{u + 1} f).map c =
      (forget Λ Y).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F)) :
    c = pullback Λ f F := by
  apply (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _ |>.injective
  simpa only [Adjunction.homEquiv_unit, pullback_unit] using hc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The Kan-extension and sheafification composite is the canonical scalar comparison.
Source: Stacks Project, Tags 03D3 and 03D7; Mathlib's canonical Kan-extension
and sheafification comparison unit factorizations.

Proof: form the inverse Kan-extension comparison, sheafify it, and follow it
by the sheafification coefficient comparison. Naturality of the abelian
sheafification unit and `sheafComposeNatTrans_fac` compute the composite with
that unit. Expand the module and abelian inverse-image units as composite
Kan-extension/sheafification units. The inverse Kan-extension unit factorization
then identifies the abelian adjoint of the composite with the forgotten module
unit. Injectivity of the abelian adjunction Hom equivalence identifies the
composite with `pullback`. No nonempty, finiteness or nonzero hypotheses occur.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
theorem kanSheafification_eq_pullback (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    let G := (MorphismProperty.Over.pullback @Etale ⊤ f).op
    let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (U.leftKanExtensionCompIsoOfPreserves F.obj G).inv ≫
      (sheafComposeNatTrans X.smallEtaleTopology U
        (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1})).app
          (G.lan.obj F.obj) = pullback Λ f F := by
  let G := (MorphismProperty.Over.pullback @Etale ⊤ f).op
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let c := (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      (U.leftKanExtensionCompIsoOfPreserves F.obj G).inv ≫
    (sheafComposeNatTrans X.smallEtaleTopology U
      (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1})).app
        (G.lan.obj F.obj)
  have hm : ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F).hom =
      ((G.lanAdjunction (ModuleCat.{u + 1} Λ)).comp
        (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).unit.app
          F.obj := by
    change (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F) = _
    dsimp only [upperStarLowerStarAdjunction,
      Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp [G]
    rfl
  have ha : ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
      ((sheafCompose Y.smallEtaleTopology U).obj F)).hom =
      ((G.lanAdjunction AddCommGrpCat.{u + 1}).comp
        (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1})).unit.app
          ((sheafCompose Y.smallEtaleTopology U).obj F).obj := by
    change (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((sheafCompose Y.smallEtaleTopology U).obj F)) = _
    dsimp only [upperStarLowerStarAdjunction,
      Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp [G]
    rfl
  have hf : toSheafify X.smallEtaleTopology (G.lan.obj (F.obj ⋙ U)) ≫ c.hom =
      (U.leftKanExtensionCompIsoOfPreserves F.obj G).inv ≫
        Functor.whiskerRight (toSheafify X.smallEtaleTopology (G.lan.obj F.obj)) U := by
    change (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app
      (G.lan.obj (F.obj ⋙ U)) ≫
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (U.leftKanExtensionCompIsoOfPreserves F.obj G).inv ≫
          (sheafComposeNatTrans X.smallEtaleTopology U
            (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
            (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1})).app
              (G.lan.obj F.obj)) = _
    rw [Functor.map_comp, ← Category.assoc]
    erw [← (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.naturality]
    rw [Category.assoc]
    erw [sheafComposeNatTrans_fac]
    rfl
  change c = pullback Λ f F
  apply eq_pullback_of_unit Λ f F c
  apply (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map_injective
  change ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
    ((sheafCompose Y.smallEtaleTopology U).obj F)).hom ≫
      Functor.whiskerLeft G c.hom =
    Functor.whiskerRight
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F).hom U
  rw [hm, ha]
  simp only [Adjunction.comp_unit_app]
  change (G.lanUnit.app (F.obj ⋙ U) ≫
    Functor.whiskerLeft G (toSheafify X.smallEtaleTopology (G.lan.obj (F.obj ⋙ U)))) ≫
      Functor.whiskerLeft G c.hom =
    Functor.whiskerRight (G.lanUnit.app F.obj ≫
      Functor.whiskerLeft G (toSheafify X.smallEtaleTopology (G.lan.obj F.obj))) U
  rw [Category.assoc, ← Functor.whiskerLeft_comp, hf, Functor.whiskerLeft_comp,
    ← Category.assoc]
  erw [Functor.leftKanExtensionCompIsoOfPreserves_inv_fac]
  ext W
  simp
  rfl

end AlgebraicGeometry.Etale.RawModuleScalarComparison
