/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapOpenSquareCube
public import Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence
public import Sheaf.AlgebraicGeometry.PerfectOverlapRestrictedComposition
public import Sheaf.AlgebraicGeometry.PerfectOverlapOpenSquareComponents
public import Sheaf.AlgebraicGeometry.PerfectOverlapCompositionCube

/-! # Pasting pinned open squares across a nested restriction -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
  schemeOpenRestriction_additive schemeOpenRestriction_preservesFiniteLimits
  schemeOpenRestriction_preservesFiniteColimits schemeOpenOverlapRestriction_additive
  schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

/-- The two ways to pass a pinned pullback square through a nested open
restriction agree. Source: Stacks Project, Tag 0D5S.

Proof: Apply the pinned open-pullback cube to the same scheme map in both
horizontal positions, the identity maps vertically, and the two nested opens.
The identity faces cancel by the unit law for the fixed composition family.
The remaining two faces are the named open squares. The pinned identification
of nested restriction with pullback along its inclusion is the component
equation for `overlapOpenInclusionPullbackIso`. -/
theorem perfectOverlapNestedOpenSquarePasting
    {X K : Scheme.{u}} (gk : X ⟶ K) (U V : K.Opens)
    (F : schemeDerivedCategory K) :
    let W := U ⊓ V
    let P := gk ⁻¹ᵁ U
    let Q := gk ⁻¹ᵁ W
    let hQ : Q ≤ gk ⁻¹ᵁ W := le_refl _
    let iK : W ⟶ U := homOfLE inf_le_left
    let iX : Q ⟶ P := homOfLE (gk.preimage_mono inf_le_left)
    let r := gk.resLE W Q hQ
    let j := gk ∣_ U
    let SU := (schemeOpenOverlapRestriction K iK).mapDerivedCategory
    let SX := (schemeOpenOverlapRestriction X iX).mapDerivedCategory
    let z := (schemeDerivedOpenRestrictionCompIso K iK).hom.app F
    let cW := singleComplexOpenPullbackSquareIso gk W Q r
      (Scheme.Hom.resLE_comp_ι gk hQ)
    let cU := singleComplexOpenPullbackSquareIso gk U P j
      (morphismRestrict_ι gk U)
    let hs : r ≫ K.homOfLE inf_le_left =
        X.homOfLE (gk.preimage_mono inf_le_left) ≫ j := by
      dsimp only [r, j]
      apply (cancel_mono U.ι).1
      simp only [Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι,
        Scheme.Hom.resLE_comp_ι]
      rw [← Category.assoc, Scheme.homOfLE_ι]
    let αK := overlapOpenInclusionPullbackIso K iK
    let αX := overlapOpenInclusionPullbackIso X iX
    (derivedPullback r).map z ≫ cW.hom.app F ≫
        (schemeDerivedOpenRestrictionCompIso X iX).inv.app ((derivedPullback gk).obj F) ≫
          SX.map (cU.inv.app F) =
      (derivedPullback r).map (αK.inv.app ((schemeOpenRestriction K U).mapDerivedCategory.obj F)) ≫
        (singleComplexOpenSquareComparison j r (K.homOfLE inf_le_left)
          (X.homOfLE (gk.preimage_mono inf_le_left)) hs.symm).app
          ((schemeOpenRestriction K U).mapDerivedCategory.obj F) ≫
            αX.hom.app
              ((derivedPullback j).obj
                ((schemeOpenRestriction K U).mapDerivedCategory.obj F)) := by
  intro W P Q hQ iK iX r j SU SX z cW cU hs αK αX
  let hV' : W ≤ (𝟙 K) ⁻¹ᵁ U := by
    change W ≤ U
    exact inf_le_left
  let j0 := X.homOfLE (gk.preimage_mono (inf_le_left : W ≤ U))
  have hj : j0 ≫ P.ι = Q.ι ≫ 𝟙 X := by
    rw [Category.comp_id]
    exact Scheme.homOfLE_ι X (gk.preimage_mono (inf_le_left : W ≤ U))
  have h0 : j0 ≫ (gk ∣_ U) = (gk ∣_ W) ≫
      Scheme.Hom.resLE (𝟙 K) U W hV' := by
    apply (cancel_mono U.ι).1
    simp only [Category.assoc, morphismRestrict_ι,
      Scheme.Hom.resLE_comp_ι, Category.comp_id]
    rw [← Category.assoc, Scheme.homOfLE_ι]
  have h : (𝟙 X) ≫ gk = gk ≫ (𝟙 K) := by simp
  have hc := singleComplexOpen_pullback_cube gk gk (𝟙 K) (𝟙 X)
    h U W hV' j0 hj h0 F
  let RU := (schemeOpenRestriction K U).mapDerivedCategory
  let RX := (schemeOpenRestriction X P).mapDerivedCategory
  have hnX := αX.inv.naturality (cU.inv.app F)
  have hnX' : SX.map (cU.inv.app F) ≫
      αX.inv.app ((derivedPullback j).obj (RU.obj F)) =
    αX.inv.app (RX.obj ((derivedPullback gk).obj F)) ≫
      (derivedPullback (X.homOfLE (gk.preimage_mono inf_le_left))).map
        (cU.inv.app F) := by
    simpa only [Functor.comp_obj, SX, RX, RU] using hnX
  apply (cancel_mono
    (αX.inv.app ((derivedPullback j).obj (RU.obj F)))).1
  apply (cancel_epi
    ((derivedPullback r).map (αK.hom.app (RU.obj F)))).1
  simp only [Category.assoc]
  rw [hnX']
  dsimp only [RU, RX]
  simp only [Category.assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, Functor.map_id, Category.id_comp,
    Iso.hom_inv_id_app_assoc, Category.comp_id]
  rw [overlapOpenInclusionPullbackIso_hom_comp K iK F]
  dsimp only [αX]
  slice_lhs 3 4 =>
    exact overlapOpenInclusionPullbackIso_inv_comp X iX ((derivedPullback gk).obj F)
  dsimp only [cW, cU]
  rw [singleComplexOpenPullbackSquareIso_hom_app_eq_compositionTo gk W Q r
    (Scheme.Hom.resLE_comp_ι gk hQ) F,
    singleComplexOpenPullbackSquareIso_inv_app_eq_compositionTo gk U P j
      (morphismRestrict_ι gk U) F]
  simp only [Category.assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp, Category.comp_id]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp]
  simp only [← Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_app_assoc, Category.id_comp]
  let iK' := K.homOfLE (inf_le_left : W ≤ U)
  let iX' := X.homOfLE (gk.preimage_mono (inf_le_left : W ≤ U))
  have hi : iK' ≫ U.ι = W.ι := Scheme.homOfLE_ι K inf_le_left
  have hr : r ≫ W.ι = Q.ι ≫ gk := Scheme.Hom.resLE_comp_ι gk hQ
  have hq : iX' ≫ P.ι = Q.ι := Scheme.homOfLE_ι X (gk.preimage_mono inf_le_left)
  have hj' : j ≫ U.ι = P.ι ≫ gk := morphismRestrict_ι gk U
  have H := perfectOverlapCompositionCube r iK' U.ι W.ι Q.ι gk
    iX' P.ι j hi hr hq hj' hs F
  have Hhom := congrArg Iso.hom H
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at Hhom
  let q0 := singleComplexOpenSquareComparison j r iK' iX' hs.symm
  let o := singleComplexOpenPullbackIso K U
  have hn := q0.naturality (o.inv.app F)
  simp only [Functor.comp_map] at hn
  have hn' := congrArg (fun z => z ≫
    (derivedPullback iX').map ((derivedPullback j).map (o.hom.app F))) hn
  simp only [Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp] at hn'
  simp only [← Functor.map_comp, Iso.inv_hom_id_app,
    Functor.map_id, Category.comp_id] at hn'
  dsimp only [q0] at hn'
  rw [singleComplexOpenSquareComparison_app_eq_compositionTo] at hn'
  rw [(derivedPullback j).map_id,
    (derivedPullback iX').map_id] at hn'
  have Hhom' := congrArg (fun z =>
    (derivedPullback r).map ((derivedPullback iK').map (o.inv.app F)) ≫ z ≫
      (derivedPullback iX').map ((derivedPullback j).map (o.hom.app F))) Hhom
  simp only [compositionTo, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, NatTrans.comp_app, Functor.map_comp,
    Category.assoc] at Hhom'
  simp only [compositionTo, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, NatTrans.comp_app, Functor.map_comp,
    Category.assoc]
  calc
    _ = _ := Hhom'
    _ = _ := by
      simpa only [compositionTo, Iso.trans_hom, Iso.trans_inv,
        Iso.symm_hom, Iso.app_hom, Iso.app_inv, NatTrans.comp_app,
        Functor.map_comp, Category.assoc, (derivedPullback r).map_id,
        Category.id_comp, Category.comp_id] using hn'

end AlgebraicGeometry
