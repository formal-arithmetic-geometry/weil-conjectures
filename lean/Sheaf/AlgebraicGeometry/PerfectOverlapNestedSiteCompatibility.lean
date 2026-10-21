/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare
public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons
import Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackNormalization

/-! # An explicit nested site comparison -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
private theorem coherence_from_inverse {C : Type*} [Category* C]
    {A B D E : C} (a : A ⟶ B) (b : B ≅ D) (c : A ≅ E) (d : D ≅ E)
    (h : b.inv = d.hom ≫ c.inv ≫ a) : a ≫ b.hom = c.hom ≫ d.inv := by
  apply (cancel_mono b.inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom
  Scheme.Modules.instCategory
attribute [local instance_reducible] TopologicalSpace.Opens.map OrderHomClass.toOrderHom
  TopCat.Hom.frameHom
attribute [local irreducible] perfectHomComposition
  singleComplexOpenPullbackSquareIso openSiteReturnIso
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

set_option maxHeartbeats 1500000 in
-- Comparing the localized-site functors needs additional elaboration steps.
private theorem normalized_gamma_rhs
    {X Y : Scheme.{u}} (g : X ⟶ Y) {W U : Y.Opens} {T P : X.Opens}
    (iY : W ⟶ U) (iX : T ⟶ P)
    (hP : P ≤ g ⁻¹ᵁ U) (hT : T ≤ g ⁻¹ᵁ W) :
    let RY := (schemeOpenRestriction Y U).mapDerivedCategory
    let rP := g.resLE U P hP
    let rT := g.resLE W T hT
    let _LU := (overlapSiteInverse P).mapDerivedCategory
    let LW := (overlapSiteInverse T).mapDerivedCategory
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) iX).mapDerivedCategory
    let _SY := (schemeOpenOverlapRestriction Y iY).mapDerivedCategory
    let _SX := (schemeOpenOverlapRestriction X iX).mapDerivedCategory
    let τ := (Functor.mapDerivedCategoryCompIso
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) P)
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) iX)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) iX)
    ∀ M : schemeDerivedCategory Y,
      ((derivedPullback rT ⋙ LW).map
          ((schemeDerivedOpenRestrictionCompIso Y iY).hom.app M) ≫
        (perfectOverlapRestrictionBeta g W T hT).inv.app M ≫
        τ.inv.app ((derivedPullback g).obj M) ≫
        SP.map ((perfectOverlapRestrictionBeta g U P hP).hom.app M)) ≫
          (openSiteOverlapIso X iX).hom.app ((derivedPullback rP).obj (RY.obj M)) =
        LW.map ((perfectOverlapNestedPullbackSquare g iY iX hP hT).inv.app (RY.obj M)) := by
  intro RY rP rT _LU LW SP _SY SX τ M
  rw [perfectOverlapRestrictionBeta_inv_app_square,
    perfectOverlapRestrictionBeta_hom_app_square]
  simp only [Functor.map_comp, Category.assoc]
  have hreturn := openSiteReturn_overlap_triangle_inv_app X iX
    ((derivedPullback g).obj M)
  conv_lhs =>
    slice 3 5
    exact hreturn
  simp only [Category.assoc]
  have hn := openSiteOverlap_inv_map_hom X iX
    ((singleComplexOpenPullbackSquareIso g U P rP
      (Scheme.Hom.resLE_comp_ι g hP)).inv.app M)
  conv_lhs =>
    slice 4 6
    exact hn
  let ξ := perfectOverlapNestedPullbackSquare g iY iX hP hT
  let dP := singleComplexOpenPullbackSquareIso g U P rP
    (Scheme.Hom.resLE_comp_ι g hP)
  let dT := singleComplexOpenPullbackSquareIso g W T rT
    (Scheme.Hom.resLE_comp_ι g hT)
  let αX := schemeDerivedOpenRestrictionCompIso X iX
  let αY := schemeDerivedOpenRestrictionCompIso Y iY
  have hi : ξ.hom.app (RY.obj M) ≫
      (derivedPullback rT).map (αY.hom.app M) ≫ dT.hom.app M =
      SX.map (dP.hom.app M) ≫ αX.hom.app ((derivedPullback g).obj M) :=
    perfectOverlapNestedPullbackSquare_on_image g iY iX hP hT M
  have hi' : (derivedPullback rT).map (αY.hom.app M) ≫ dT.hom.app M ≫
      αX.inv.app ((derivedPullback g).obj M) ≫ SX.map (dP.inv.app M) =
      ξ.inv.app (RY.obj M) := by
    apply (cancel_epi (ξ.hom.app (RY.obj M))).mp
    slice_lhs 1 3 => exact hi
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.id_comp]
    rw [← SX.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    rfl
  change LW.map ((derivedPullback rT).map (αY.hom.app M)) ≫
    LW.map (dT.hom.app M) ≫
    LW.map (αX.inv.app ((derivedPullback g).obj M)) ≫
    LW.map (SX.map (dP.inv.app M)) = LW.map (ξ.inv.app (RY.obj M))
  rw [← LW.map_comp, ← LW.map_comp, ← LW.map_comp, hi']

private theorem gamma_nested
    {X Y : Scheme.{u}} (g : X ⟶ Y) {W U : Y.Opens} {T P : X.Opens}
    (iY : W ⟶ U) (iX : T ⟶ P)
    (hP : P ≤ g ⁻¹ᵁ U) (hT : T ≤ g ⁻¹ᵁ W) :
    let RY := (schemeOpenRestriction Y U).mapDerivedCategory
    let rP := g.resLE U P hP
    let rT := g.resLE W T hT
    let LU := (overlapSiteInverse P).mapDerivedCategory
    let LW := (overlapSiteInverse T).mapDerivedCategory
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) iX).mapDerivedCategory
    let SY := (schemeOpenOverlapRestriction Y iY).mapDerivedCategory
    let _SX := (schemeOpenOverlapRestriction X iX).mapDerivedCategory
    let τ := (Functor.mapDerivedCategoryCompIso
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) P)
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) iX)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) iX)
    ∀ (γ : (derivedPullback rP ⋙ LU) ⋙ SP ≅ SY ⋙ (derivedPullback rT ⋙ LW)),
      (∀ M : schemeDerivedCategory Y, γ.inv.app (RY.obj M) =
        (derivedPullback rT ⋙ LW).map
          ((schemeDerivedOpenRestrictionCompIso Y iY).hom.app M) ≫
        (perfectOverlapRestrictionBeta g W T hT).inv.app M ≫
        τ.inv.app ((derivedPullback g).obj M) ≫
        SP.map ((perfectOverlapRestrictionBeta g U P hP).hom.app M)) →
      ∀ Z : schemeDerivedCategory U.toScheme,
      γ.inv.app Z ≫ (openSiteOverlapIso X iX).hom.app ((derivedPullback rP).obj Z) =
        LW.map ((perfectOverlapNestedPullbackSquare g iY iX hP hT).inv.app Z) := by
  intro RY rP rT LU LW SP SY SX τ γ hγ Z
  let left : SY ⋙ (derivedPullback rT ⋙ LW) ⟶ derivedPullback rP ⋙ (SX ⋙ LW) :=
    γ.inv ≫ Functor.whiskerLeft (derivedPullback rP) (openSiteOverlapIso X iX).hom
  let right : SY ⋙ (derivedPullback rT ⋙ LW) ⟶ derivedPullback rP ⋙ (SX ⋙ LW) :=
    Functor.whiskerRight (perfectOverlapNestedPullbackSquare g iY iX hP hT).inv LW
  have : RY.IsLocalization ((MorphismProperty.isomorphisms _).inverseImage RY) :=
    schemeDerivedOpenRestriction_isLocalization Y U
  have := Localization.faithful_whiskeringLeft RY
    ((MorphismProperty.isomorphisms _).inverseImage RY)
    (DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over T)))
  have heq : left = right := by
    apply (((Functor.whiskeringLeft _ _ _).obj RY)).map_injective
    ext M
    change γ.inv.app (RY.obj M) ≫
      (openSiteOverlapIso X iX).hom.app ((derivedPullback rP).obj (RY.obj M)) = _
    rw [hγ M]
    exact normalized_gamma_rhs g iY iX hP hT M
  exact congrArg (fun α ↦ α.app Z) heq


/-- The site comparison obtained directly from the nested pullback square.
Source: Stacks Project, Tags 08DW and 0D5S. Associate the three functors,
apply the site overlap comparison, then the inverse-site image of the fixed
nested pullback square. This constructs the comparison without a localization
preimage choice.
(blueprint: def-pc-perfect-overlap-nested-site-gamma). -/
@[no_expose] noncomputable def perfectOverlapNestedSiteGamma
    {X Y : Scheme.{u}} (g : X ⟶ Y) {W U : Y.Opens} {T P : X.Opens}
    (iY : W ⟶ U) (iX : T ⟶ P)
    (hP : P ≤ g ⁻¹ᵁ U) (hT : T ≤ g ⁻¹ᵁ W) :
    (derivedPullback (g.resLE U P hP) ⋙ (overlapSiteInverse P).mapDerivedCategory) ⋙
        (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) iX).mapDerivedCategory ≅
      (schemeOpenOverlapRestriction Y iY).mapDerivedCategory ⋙
        (derivedPullback (g.resLE W T hT) ⋙ (overlapSiteInverse T).mapDerivedCategory) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (openSiteOverlapIso X iX) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectOverlapNestedPullbackSquare g iY iX hP hT) _ ≪≫
    Functor.associator _ _ _

/-- The inverse component of the explicit site comparison cancels the site overlap map.
Source: the defining composite, functoriality, and inverse cancellation. -/
theorem perfectOverlapNestedSiteGamma_inv_comp
    {X Y : Scheme.{u}} (g : X ⟶ Y) {W U : Y.Opens} {T P : X.Opens}
    (iY : W ⟶ U) (iX : T ⟶ P)
    (hP : P ≤ g ⁻¹ᵁ U) (hT : T ≤ g ⁻¹ᵁ W)
    (Z : schemeDerivedCategory U.toScheme) :
    (perfectOverlapNestedSiteGamma g iY iX hP hT).inv.app Z ≫
        (openSiteOverlapIso X iX).hom.app ((derivedPullback (g.resLE U P hP)).obj Z) =
      (overlapSiteInverse T).mapDerivedCategory.map
        ((perfectOverlapNestedPullbackSquare g iY iX hP hT).inv.app Z) := by
  unfold perfectOverlapNestedSiteGamma
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_inv, Category.id_comp, Category.comp_id, Category.assoc,
    Iso.inv_hom_id_app]
  erw [Category.comp_id]

/-- The explicit comparison satisfies the restriction coherence.
Source: Stacks Project, Tags 08DW and 0D5S. Normalize the inverse comparison
on globally restricted objects using the nested square, then cancel its
invertible factors. This supplies coherence without constructing a localization lift. -/
theorem perfectOverlapNestedSiteGamma_coherence
    {X Y : Scheme.{u}} (g : X ⟶ Y) {W U : Y.Opens} {T P : X.Opens}
    (iY : W ⟶ U) (iX : T ⟶ P)
    (hP : P ≤ g ⁻¹ᵁ U) (hT : T ≤ g ⁻¹ᵁ W) :
    let RY := (schemeOpenRestriction Y U).mapDerivedCategory
    let _rP := g.resLE U P hP
    let rT := g.resLE W T hT
    let _LU := (overlapSiteInverse P).mapDerivedCategory
    let LW := (overlapSiteInverse T).mapDerivedCategory
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) iX).mapDerivedCategory
    let _SY := (schemeOpenOverlapRestriction Y iY).mapDerivedCategory
    let _SX := (schemeOpenOverlapRestriction X iX).mapDerivedCategory
    let τ := (Functor.mapDerivedCategoryCompIso
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) P)
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) iX)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) iX)
    ∀ M : schemeDerivedCategory Y,
      τ.inv.app ((derivedPullback g).obj M) ≫
        SP.map ((perfectOverlapRestrictionBeta g U P hP).hom.app M) ≫
        (perfectOverlapNestedSiteGamma g iY iX hP hT).hom.app (RY.obj M) =
      (perfectOverlapRestrictionBeta g W T hT).hom.app M ≫
        (derivedPullback rT ⋙ LW).map
          ((schemeDerivedOpenRestrictionCompIso Y iY).inv.app M) := by
  intro RY rP rT LU LW SP SY SX τ M
  let γ := perfectOverlapNestedSiteGamma g iY iX hP hT
  have hi : γ.inv.app (RY.obj M) =
      (derivedPullback rT ⋙ LW).map
          ((schemeDerivedOpenRestrictionCompIso Y iY).hom.app M) ≫
        (perfectOverlapRestrictionBeta g W T hT).inv.app M ≫
        τ.inv.app ((derivedPullback g).obj M) ≫
        SP.map ((perfectOverlapRestrictionBeta g U P hP).hom.app M) := by
    apply (cancel_mono ((openSiteOverlapIso X iX).hom.app
      ((derivedPullback rP).obj (RY.obj M)))).mp
    exact (perfectOverlapNestedSiteGamma_inv_comp g iY iX hP hT (RY.obj M)).trans
      (normalized_gamma_rhs g iY iX hP hT M).symm
  simpa only [Iso.app_hom, Iso.app_inv, Functor.mapIso_inv, Category.assoc] using
    coherence_from_inverse
    (τ.inv.app ((derivedPullback g).obj M) ≫
      SP.map ((perfectOverlapRestrictionBeta g U P hP).hom.app M))
    (γ.app (RY.obj M)) ((perfectOverlapRestrictionBeta g W T hT).app M)
    ((derivedPullback rT ⋙ LW).mapIso ((schemeDerivedOpenRestrictionCompIso Y iY).app M))
    hi

/-- Any comparison with the prescribed restriction coherence is the explicit one.
Source: Stacks Project, Tags 08DW and 0D5S.

Proof: The localization compatibility lemma proves that its inverse, followed
by the site overlap map, equals the inverse-site image of the nested square.
The preceding component calculation gives the same equation for the explicit
comparison. Cancel the invertible overlap map at every object, and use
extensionality for inverse natural transformations. Thus this construction
preserves the existing chosen comparison rather than changing its meaning. -/
theorem perfectOverlapNestedSiteGamma_eq
    {X Y : Scheme.{u}} (g : X ⟶ Y) {W U : Y.Opens} {T P : X.Opens}
    (iY : W ⟶ U) (iX : T ⟶ P)
    (hP : P ≤ g ⁻¹ᵁ U) (hT : T ≤ g ⁻¹ᵁ W) :
    let RY := (schemeOpenRestriction Y U).mapDerivedCategory
    let rP := g.resLE U P hP
    let rT := g.resLE W T hT
    let LU := (overlapSiteInverse P).mapDerivedCategory
    let LW := (overlapSiteInverse T).mapDerivedCategory
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) iX).mapDerivedCategory
    let SY := (schemeOpenOverlapRestriction Y iY).mapDerivedCategory
    let τ := (Functor.mapDerivedCategoryCompIso
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) P)
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) iX)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) iX)
    ∀ (γ : (derivedPullback rP ⋙ LU) ⋙ SP ≅ SY ⋙ (derivedPullback rT ⋙ LW)),
      (∀ M : schemeDerivedCategory Y, γ.inv.app (RY.obj M) =
        (derivedPullback rT ⋙ LW).map
          ((schemeDerivedOpenRestrictionCompIso Y iY).hom.app M) ≫
        (perfectOverlapRestrictionBeta g W T hT).inv.app M ≫
        τ.inv.app ((derivedPullback g).obj M) ≫
        SP.map ((perfectOverlapRestrictionBeta g U P hP).hom.app M)) →
      γ = perfectOverlapNestedSiteGamma g iY iX hP hT := by
  intro RY rP rT LU LW SP SY τ γ hγ
  apply Iso.ext_inv
  ext Z
  apply (cancel_mono ((openSiteOverlapIso X iX).hom.app
    ((derivedPullback rP).obj Z))).mp
  exact (gamma_nested g iY iX hP hT γ hγ Z).trans
    (perfectOverlapNestedSiteGamma_inv_comp g iY iX hP hT Z).symm

end AlgebraicGeometry
