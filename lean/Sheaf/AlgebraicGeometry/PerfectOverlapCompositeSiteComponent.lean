/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapCompositeStageMap
import WeilConjectures.AlgebraicGeometry.PerfectOverlapCanonicalSiteTriangle
import Sheaf.AlgebraicGeometry.PerfectOverlapNestedSiteCompatibility
import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport
import Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence

/-! # A component of composite overlap compatibility
Source: Stacks Project, Tags 08DW and 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom
  Scheme.Modules.instCategory
attribute [local instance_reducible] TopologicalSpace.Opens.map OrderHomClass.toOrderHom
  TopCat.Hom.frameHom
attribute [local irreducible] perfectHomComposition
  openSiteReturnIso perfectOverlapApexObjectIso perfectOverlapStageObjectIso
  perfectOverlapStageEquivalence overlapSchemeIsoDerivedEquivalence

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
private theorem mapped_three
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {a b c d : C} {z : D}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (k : F.obj d ⟶ z) :
    F.map (f ≫ g ≫ h) ≫ k = F.map f ≫ F.map g ≫ F.map h ≫ k := by
  simp only [Functor.map_comp, Category.assoc]

private theorem counit_pasting
    {C D T : Type*} [Category* C] [Category* D] [Category* T]
    (L : C ⥤ D) (R : D ⥤ C) (F : C ⥤ T) (ε : L ⋙ R ⟶ 𝟭 C)
    {a b : C} {M N : D} {z : T}
    (γ : L.obj a ⟶ M) (κ : M ⟶ N) (ω : N ⟶ L.obj b)
    (δ : a ⟶ b) (σ : F.obj b ⟶ z) (h : γ ≫ κ ≫ ω = L.map δ) :
    (R ⋙ F).map γ ≫ (R ⋙ F).map κ ≫ (R ⋙ F).map ω ≫
        F.map (ε.app b) ≫ σ = F.map (ε.app a) ≫ F.map δ ≫ σ := by
  have hn := congrArg F.map (ε.naturality δ)
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp] at hn
  calc
    _ = F.map (R.map (γ ≫ κ ≫ ω)) ≫ F.map (ε.app b) ≫ σ := by
      simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
    _ = _ := by rw [h, reassoc_of% hn]

private theorem overlap_pasting
    {A B P Q : Type*} [Category* A] [Category* B] [Category* P] [Category* Q]
    (LP : A ⥤ P) (SP : P ⥤ Q) (SX : A ⥤ B) (LW : B ⥤ Q)
    (ω : LP ⋙ SP ≅ SX ⋙ LW) {a b : A} {c : B}
    (γ : LW.obj c ⟶ SP.obj (LP.obj a)) (κ : LP.obj a ⟶ LP.obj b)
    (t : a ⟶ b) (ξ : c ⟶ SX.obj a)
    (hκ : κ = LP.map t) (hγ : γ ≫ ω.hom.app a = LW.map ξ) :
    γ ≫ SP.map κ ≫ ω.hom.app b = LW.map (ξ ≫ SX.map t) := by
  rw [hκ]
  have hn := ω.hom.naturality t
  simp only [Functor.comp_map] at hn
  rw [hn, ← Category.assoc, hγ, LW.map_comp]

private theorem site_triangle_pasting
    {A B P Q T : Type*} [Category* A] [Category* B] [Category* P]
    [Category* Q] [Category* T]
    (LP : A ⥤ P) (SP : P ⥤ Q) (SX : A ⥤ B) (LW : B ⥤ Q)
    (R : Q ⥤ B) (C : B ⥤ T) (ε : LW ⋙ R ⟶ 𝟭 B)
    (ω : LP ⋙ SP ≅ SX ⋙ LW) {a b : A} {c : B} {z : T}
    (γ : LW.obj c ⟶ SP.obj (LP.obj a)) (κ : LP.obj a ⟶ LP.obj b)
    (t : a ⟶ b) (ξ : c ⟶ SX.obj a)
    (tail : (R ⋙ C).obj (SP.obj (LP.obj a)) ⟶ z)
    (σ : C.obj (SX.obj b) ⟶ z)
    (hκ : κ = LP.map t) (hγ : γ ≫ ω.hom.app a = LW.map ξ)
    (ht : tail = (R ⋙ C).map (SP.map κ) ≫ (R ⋙ C).map (ω.hom.app b) ≫
      C.map (ε.app (SX.obj b)) ≫ σ) :
    (R ⋙ C).map γ ≫ tail = C.map (ε.app c) ≫ C.map (ξ ≫ SX.map t) ≫ σ := by
  rw [ht]
  exact counit_pasting LW R C ε γ (SP.map κ) (ω.hom.app b)
    (ξ ≫ SX.map t) σ (overlap_pasting LP SP SX LW ω γ κ t ξ hκ hγ)

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

set_option maxHeartbeats 400000 in
-- The fixed comparison interfaces involve several derived categories.
/-- The gluing-side composite equals the constructed cartesian stage map.
Source: Stacks Project, Tags 08DW and 0D5S, restriction comparisons in Tag 09RE.

Proof: The comparison constructor stores the explicit nested-site gamma.
Its inverse, followed by the overlap comparison, is the inverse-site image
of the fixed nested-square inverse. Apply this equation on each branch.
The normalization and uniqueness API for this construction proves agreement
with the former localization-lift comparison.

Substitute theta = kappa followed by the inverse-site image of phi followed
by the site-return map. The U or V canonical site triangle cancels the return
map against tau and the prescribed apex-object comparison. The kappa component
is the inverse-site image of the fixed local composite comparison. Naturality
of the overlap comparison moves kappa across gamma. Naturality of the site
counit leaves the counit, nested-square inverse, local composite comparison,
and fixed stage-object map: the four factors of the stage map. Its Boolean
branch equation finishes each clause. This argument uses no cover,
nonempty-open or boundedness hypothesis.
(blueprint: lem-pc-perfect-overlap-composite-site-component). -/
theorem perfectOverlapCompositeSiteComponent
    {X Y K C S : Scheme.{u}}
    (f : K ⟶ Y) (gk : X ⟶ K) (g : X ⟶ Y) (hgf : gk ≫ f = g)
    (pX : X ⟶ C) (pY : Y ⟶ S)
    (b : C ⟶ S)
    (hg : IsPullback g pX pY b)
    (U V : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (g ∣_ U)).obj A ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (g ∣_ V)).obj B ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
  let W := U ⊓ V
  let _r := gk.resLE (f ⁻¹ᵁ W) (g ⁻¹ᵁ W)
    (by rw [← Scheme.Hom.comp_preimage, hgf])
  let data := transportDataOfComposite f gk g hgf U V A B E φU φV
  let F : Bool → schemeDerivedCategory (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V).toScheme := fun a ↦
    if a then
      (schemeOpenOverlapRestriction K
        (homOfLE (inf_le_right : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V))).mapDerivedCategory.obj
        ((derivedPullback (f ∣_ V)).obj B)
    else
      (schemeOpenOverlapRestriction K
        (homOfLE (inf_le_left : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U))).mapDerivedCategory.obj
        ((derivedPullback (f ∣_ U)).obj A)
  let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
    (homOfLE (inf_le_left : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U))).mapDerivedCategory
  let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
    (homOfLE (inf_le_right : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ V))).mapDerivedCategory
  let τU := (Functor.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (g ⁻¹ᵁ U))
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
      (homOfLE (inf_le_left : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U)))).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (inf_le_left : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U)))
  let τV := (Functor.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (g ⁻¹ᵁ V))
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
      (homOfLE (inf_le_right : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ V)))).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (inf_le_right : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ V)))
  let ψ : ∀ a, data.d.toDiagram.HW.obj (F a) ≅
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)).mapDerivedCategory.obj E := fun a ↦
    Bool.casesOn a
      (data.d.toDiagram.γU.symm.app ((derivedPullback (f ∣_ U)).obj A) ≪≫
        SP.mapIso data.θU ≪≫ τU.app E)
      (data.d.toDiagram.γV.symm.app ((derivedPullback (f ∣_ V)).obj B) ≪≫
        SQ.mapIso data.θV ≪≫ τV.app E)
  let apex := perfectOverlapApexEquivalence g pX pY b hg U V
  let ρ : ∀ a : Bool, apex.functor.obj
      ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)).mapDerivedCategory.obj E) ≅
        (derivedPullback (pullback.fst (W.ι ≫ pY) b)).obj
          (if a then (derivedPullback (Y.homOfLE (inf_le_right : W ≤ V))).obj B
          else (derivedPullback (Y.homOfLE (inf_le_left : W ≤ U))).obj A) := fun a ↦
    Bool.casesOn a
      (perfectOverlapApexObjectIso g pX pY b hg U V U inf_le_left A E φU)
      (perfectOverlapApexObjectIso g pX pY b hg U V V inf_le_right B E φV)
  (apex.functor.map (ψ false).hom ≫ (ρ false).hom =
    perfectOverlapCompositeStageMap f gk g hgf pX pY b hg U V A B E φU φV false) ∧
  (apex.functor.map (ψ true).hom ≫ (ρ true).hom =
    perfectOverlapCompositeStageMap f gk g hgf pX pY b hg U V A B E φU φV true) := by
  intro W r data F SP SQ τU τV ψ apex ρ
  let hP (L : Y.Opens) : g ⁻¹ᵁ L ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ L) := by
    rw [← Scheme.Hom.comp_preimage, hgf]
  let iKU : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ⟶ f ⁻¹ᵁ U := homOfLE inf_le_left
  let iKV : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ⟶ f ⁻¹ᵁ V := homOfLE inf_le_right
  let iXU : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ⟶ g ⁻¹ᵁ U := homOfLE inf_le_left
  let iXV : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ⟶ g ⁻¹ᵁ V := homOfLE inf_le_right
  have hγU := perfectOverlapNestedSiteGamma_inv_comp gk iKU iXU (hP U) (hP (U ⊓ V))
    ((derivedPullback (f ∣_ U)).obj A)
  have hγV := perfectOverlapNestedSiteGamma_inv_comp gk iKV iXV (hP V) (hP (U ⊓ V))
    ((derivedPullback (f ∣_ V)).obj B)
  constructor
  · have ht := perfectOverlapCanonicalSiteTriangleU g pX pY b hg U V A E φU
      _ (data.κU.app A) data.θU data.hθU
    have hκ : (data.κU.app A).hom =
        (overlapSiteInverse (g ⁻¹ᵁ U)).mapDerivedCategory.map
          ((perfectOverlapCompositeLocalIso f gk g hgf U).hom.app A) :=
      transportDataOfComposite_kappaU_hom_app f gk g hgf U V A B E φU φV
    let LU := (overlapSiteInverse (g ⁻¹ᵁ U)).mapDerivedCategory
    let LW := (overlapSiteInverse (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)).mapDerivedCategory
    let SX := (schemeOpenOverlapRestriction X iXU).mapDerivedCategory
    let ξ := perfectOverlapNestedPullbackSquare gk iKU iXU (hP U) (hP (U ⊓ V))
    let κ := perfectOverlapCompositeLocalIso f gk g hgf U
    let site : SheafOfModules.{u}
        ((moduleRings X.toRingedSpace).over (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)) ≌
        SheafOfModules.{u}
          (moduleRings (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V).toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv _
    have hz := site_triangle_pasting LU SP SX LW site.mapDerivedCategory.functor
      (perfectOverlapStageEquivalence g pX pY b hg U V).functor
      site.mapDerivedCategory.counitIso.hom (openSiteOverlapIso X iXU)
      (data.d.toDiagram.γU.inv.app ((derivedPullback (f ∣_ U)).obj A))
      (data.κU.app A).hom (κ.hom.app A)
      (ξ.inv.app ((derivedPullback (f ∣_ U)).obj A))
      (apex.functor.map (SP.map data.θU.hom) ≫ apex.functor.map (τU.app E).hom ≫
        (perfectOverlapApexObjectIso g pX pY b hg U V U inf_le_left A E φU).hom)
      ((perfectOverlapStageObjectIso g pX pY b hg U V U inf_le_left).hom.app A)
      hκ hγU ht
    have hf := perfectOverlapCompositeStageMap_false f gk g hgf pX pY b hg U V
      A B E φU φV
    have hn := mapped_three apex.functor
      (data.d.toDiagram.γU.inv.app ((derivedPullback (f ∣_ U)).obj A))
      (SP.map data.θU.hom) (τU.app E).hom
      (perfectOverlapApexObjectIso g pX pY b hg U V U inf_le_left A E φU).hom
    refine hn.trans (hz.trans ?_)
    unfold perfectOverlapCompositeStageMapAt at hf
    with_unfolding_all exact hf.symm
  · have ht := perfectOverlapCanonicalSiteTriangleV g pX pY b hg U V B E φV
      _ (data.κV.app B) data.θV data.hθV
    have hκ : (data.κV.app B).hom =
        (overlapSiteInverse (g ⁻¹ᵁ V)).mapDerivedCategory.map
          ((perfectOverlapCompositeLocalIso f gk g hgf V).hom.app B) :=
      associator_symm_whiskerRight_hom_app
        (derivedPullback (f ∣_ V))
        (derivedPullback (gk.resLE (f ⁻¹ᵁ V) (g ⁻¹ᵁ V) (hP V)))
        (overlapSiteInverse (g ⁻¹ᵁ V)).mapDerivedCategory
        (derivedPullback (g ∣_ V)) (perfectOverlapCompositeLocalIso f gk g hgf V) B
    let LV := (overlapSiteInverse (g ⁻¹ᵁ V)).mapDerivedCategory
    let LW := (overlapSiteInverse (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)).mapDerivedCategory
    let SX := (schemeOpenOverlapRestriction X iXV).mapDerivedCategory
    let ξ := perfectOverlapNestedPullbackSquare gk iKV iXV (hP V) (hP (U ⊓ V))
    let κ := perfectOverlapCompositeLocalIso f gk g hgf V
    let site : SheafOfModules.{u}
        ((moduleRings X.toRingedSpace).over (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)) ≌
        SheafOfModules.{u}
          (moduleRings (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V).toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv _
    have hz := site_triangle_pasting LV SQ SX LW site.mapDerivedCategory.functor
      (perfectOverlapStageEquivalence g pX pY b hg U V).functor
      site.mapDerivedCategory.counitIso.hom (openSiteOverlapIso X iXV)
      (data.d.toDiagram.γV.inv.app ((derivedPullback (f ∣_ V)).obj B))
      (data.κV.app B).hom (κ.hom.app B)
      (ξ.inv.app ((derivedPullback (f ∣_ V)).obj B))
      (apex.functor.map (SQ.map data.θV.hom) ≫ apex.functor.map (τV.app E).hom ≫
        (perfectOverlapApexObjectIso g pX pY b hg U V V inf_le_right B E φV).hom)
      ((perfectOverlapStageObjectIso g pX pY b hg U V V inf_le_right).hom.app B)
      hκ hγV ht
    have hf := perfectOverlapCompositeStageMap_true f gk g hgf pX pY b hg U V
      A B E φU φV
    have hn := mapped_three apex.functor
      (data.d.toDiagram.γV.inv.app ((derivedPullback (f ∣_ V)).obj B))
      (SQ.map data.θV.hom) (τV.app E).hom
      (perfectOverlapApexObjectIso g pX pY b hg U V V inf_le_right B E φV).hom
    refine hn.trans (hz.trans ?_)
    unfold perfectOverlapCompositeStageMapAt at hf
    with_unfolding_all exact hf.symm

end AlgebraicGeometry
