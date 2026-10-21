/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenCounitCompatibility
import all WeilConjectures.AlgebraicGeometry.PerfectHomComparisonTriangle

/-! # Normalization of the nested pullback square on restricted objects -/

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
  singleComplexOpenPullbackSquareIso compositionTo
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

private theorem pinnedComposition_eq
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    singleComplexOpenPinnedComposition f g = perfectHomComposition f g := by
  unfold singleComplexOpenPinnedComposition perfectHomComposition
  rfl

set_option maxHeartbeats 1500000 in
-- The component normalization compares several derived functor expressions.
/-- The two paths around a nested restricted square agree on a global restriction.
Source: Stacks Project, Tags 08DW and 0D5S.

Proof: Cancel the larger open immersion to identify the restricted composites.
Replace nested exact restriction by its fixed inclusion-pullback comparison.
Expand the two pinned open squares, and cancel the common open comparisons.
Naturality moves the inverse open comparison to the front. Apply the three
named-composite associativity triangles for the paths through the two nested
inclusions, then cancel their invertible terminal comparisons. This argument
uses no nonempty-open or boundedness hypothesis.
(blueprint: lem-pc-perfect-overlap-nested-pullback-normalization). -/
theorem perfectOverlapNestedPullbackSquare_on_image
    {X Y : Scheme.{u}} (g : X ⟶ Y) {W U : Y.Opens} {T P : X.Opens}
    (iY : W ⟶ U) (iX : T ⟶ P)
    (hP : P ≤ g ⁻¹ᵁ U) (hT : T ≤ g ⁻¹ᵁ W)
    (M : schemeDerivedCategory Y) :
    let rP := g.resLE U P hP
    let rT := g.resLE W T hT
    let ξ := perfectOverlapNestedPullbackSquare g iY iX hP hT
    let αY := schemeDerivedOpenRestrictionCompIso Y iY
    let αX := schemeDerivedOpenRestrictionCompIso X iX
    let dP := singleComplexOpenPullbackSquareIso g U P rP
      (Scheme.Hom.resLE_comp_ι g hP)
    let dT := singleComplexOpenPullbackSquareIso g W T rT
      (Scheme.Hom.resLE_comp_ι g hT)
    ξ.hom.app ((schemeOpenRestriction Y U).mapDerivedCategory.obj M) ≫
        (derivedPullback rT).map (αY.hom.app M) ≫ dT.hom.app M =
      (schemeOpenOverlapRestriction X iX).mapDerivedCategory.map (dP.hom.app M) ≫
        αX.hom.app ((derivedPullback g).obj M) := by
  intro rP rT ξ αY αX dP dT
  let jX := X.homOfLE (leOfHom iX)
  let jY := Y.homOfLE (leOfHom iY)
  have hn := (overlapOpenInclusionPullbackIso X iX).hom.naturality (dP.hom.app M)
  have hY := overlapOpenInclusionPullbackIso_hom_comp Y iY M
  have hX := overlapOpenInclusionPullbackIso_hom_comp X iX ((derivedPullback g).obj M)
  dsimp only [ξ]
  unfold perfectOverlapNestedPullbackSquare
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Category.assoc]
  apply (cancel_epi ((overlapOpenInclusionPullbackIso X iX).hom.app
    ((derivedPullback rP).obj ((schemeOpenRestriction Y U).mapDerivedCategory.obj M)))).mp
  dsimp only [rP, rT]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% hn]
  dsimp only [αX, αY]
  rw [hX]
  rw [← (derivedPullback rT).map_comp_assoc, hY]
  dsimp only [dP, dT]
  simp only [singleComplexOpenPullbackSquareIso, NatIso.ofComponents_hom_app,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  let c := @compositionTo.{u,w} _
  have hcP : rP ≫ U.ι = P.ι ≫ g := Scheme.Hom.resLE_comp_ι g hP
  have hcT : rT ≫ W.ι = T.ι ≫ g := Scheme.Hom.resLE_comp_ι g hT
  have hx : jX ≫ P.ι = T.ι := Scheme.homOfLE_ι X (leOfHom iX)
  have hy : jY ≫ U.ι = W.ι := Scheme.homOfLE_ι Y (leOfHom iY)
  have hnest : jX ≫ rP = rT ≫ jY :=
    (perfectOverlapNestedRestrictedMaps g iY iX hP hT).symm
  suffices (c jX rP (rT ≫ jY) hnest).hom.app
      ((schemeOpenRestriction Y U).mapDerivedCategory.obj M) ≫
    (c rT jY (rT ≫ jY) rfl).inv.app
      ((schemeOpenRestriction Y U).mapDerivedCategory.obj M) ≫
    (derivedPullback rT).map ((derivedPullback jY).map
      ((singleComplexOpenPullbackIso Y U).inv.app M)) ≫
    (derivedPullback rT).map ((c jY U.ι W.ι hy).hom.app M) ≫
    (c rT W.ι (T.ι ≫ g) hcT).hom.app M ≫
    (c T.ι g (T.ι ≫ g) rfl).inv.app M ≫
    (singleComplexOpenPullbackIso X T).hom.app ((derivedPullback g).obj M) =
      (derivedPullback jX).map ((derivedPullback rP).map
        ((singleComplexOpenPullbackIso Y U).inv.app M)) ≫
      (derivedPullback jX).map ((c rP U.ι (P.ι ≫ g) hcP).hom.app M ≫
        (c P.ι g (P.ι ≫ g) rfl).inv.app M) ≫
      (c jX P.ι T.ι hx).hom.app ((derivedPullback g).obj M) ≫
      (singleComplexOpenPullbackIso X T).hom.app ((derivedPullback g).obj M)
    by
      simpa only [c, compositionTo, pinnedComposition_eq,
        Iso.trans_hom, Iso.trans_inv, Iso.refl_inv, Iso.refl_hom,
        NatTrans.comp_app, eqToIso_refl,
        eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_refl, NatTrans.id_app,
        Functor.map_comp, Category.assoc, Category.comp_id, Category.id_comp,
        CategoryTheory.Functor.map_id, jX, jY, rP, rT] using this
  simp only [← Category.assoc, cancel_mono]
  have hnB := (c rT jY (rT ≫ jY) rfl).inv.naturality
    ((singleComplexOpenPullbackIso Y U).inv.app M)
  have hnA := (c jX rP (rT ≫ jY) hnest).hom.naturality
    ((singleComplexOpenPullbackIso Y U).inv.app M)
  simp only [Functor.comp_map] at hnB hnA
  simp only [Category.assoc, Functor.map_comp]
  rw [← reassoc_of% hnB, ← reassoc_of% hnA]
  rw [cancel_epi]
  have htot : jX ≫ (P.ι ≫ g) = T.ι ≫ g := by
    rw [← Category.assoc, hx]
  have ht1 := congrArg Iso.hom (compositionTo_triangle jX rP U.ι
    (P.ι ≫ g) (T.ι ≫ g) (rT ≫ jY) hcP htot hnest M)
  have ht2 := congrArg Iso.hom (compositionTo_triangle rT jY U.ι
    W.ι (T.ι ≫ g) (rT ≫ jY) hy hcT rfl M)
  have ht3 := congrArg Iso.hom (compositionTo_triangle jX P.ι g
    (P.ι ≫ g) (T.ι ≫ g) T.ι rfl htot hx M)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at ht1 ht2 ht3
  apply (cancel_mono ((c T.ι g (T.ι ≫ g) rfl).hom.app M)).mp
  dsimp only [c]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← ht3]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [ht1, ht2]
  simp only [Iso.inv_hom_id_app_assoc]


end AlgebraicGeometry
