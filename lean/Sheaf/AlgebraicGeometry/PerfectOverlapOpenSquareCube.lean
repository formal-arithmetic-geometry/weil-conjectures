/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons
public import Sheaf.AlgebraicGeometry.SingleComplexOpenPullbackCube
public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport

/-! # Pinned overlap and open-pullback squares -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
/-- The inverse of the named open-pullback restriction comparison is the
componentwise pinned open square. Both use the same chosen pullback-composition
isomorphism; their open comparisons cancel in opposite order. -/
theorem openPullbackRestrictionIso_inv_app_eq_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) (P : X.Opens) (U : Y.Opens)
    (h : P ≤ g ⁻¹ᵁ U) (M : schemeDerivedCategory Y) :
    (openPullbackRestrictionIso g P U h).inv.app M =
      (singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
        (Scheme.Hom.resLE_comp_ι g h)).hom.app M := by
  simp only [openPullbackRestrictionIso, singleComplexOpenPullbackSquareIso,
    NatIso.ofComponents_hom_app, Iso.trans_inv, NatTrans.comp_app,
    Iso.symm_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Iso.symm_inv, eqToIso.hom, eqToIso.inv, eqToHom_app]
  simp only [Category.assoc, perfectHomComposition,
    singleComplexOpenPinnedComposition]

/-- The forward named restriction comparison is the inverse pinned open
square component. This is the inverse of the preceding component equality. -/
theorem openPullbackRestrictionIso_hom_app_eq_square_inv
    {X Y : Scheme.{u}} (g : X ⟶ Y) (P : X.Opens) (U : Y.Opens)
    (h : P ≤ g ⁻¹ᵁ U) (M : schemeDerivedCategory Y) :
    (openPullbackRestrictionIso g P U h).hom.app M =
      (singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
        (Scheme.Hom.resLE_comp_ι g h)).inv.app M := by
  have he : (openPullbackRestrictionIso g P U h).symm.app M =
      (singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
        (Scheme.Hom.resLE_comp_ι g h)).app M := by
    apply Iso.ext
    exact openPullbackRestrictionIso_inv_app_eq_square g P U h M
  have := congrArg Iso.symm he
  exact congrArg Iso.hom this

section

variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian

/-- The canonical restriction/pullback component is the inverse pinned open
square, transported into the localized site and preceded by its return unit. -/
theorem perfectOverlapRestrictionBeta_hom_app_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) (P : X.Opens) (U : Y.Opens)
    (h : P ≤ g ⁻¹ᵁ U) (M : schemeDerivedCategory Y) :
    (perfectOverlapRestrictionBeta g U P h).hom.app M =
      (openSiteReturnIso X P).inv.app ((derivedPullback g).obj M) ≫
        (overlapSiteInverse P).mapDerivedCategory.map
          ((singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
            (Scheme.Hom.resLE_comp_ι g h)).inv.app M) := by
  rw [perfectOverlapRestrictionBeta_hom_app,
    openPullbackRestrictionIso_hom_app_eq_square_inv]

/-- The inverse canonical restriction/pullback component is the forward
pinned open square, followed by the site return map. -/
theorem perfectOverlapRestrictionBeta_inv_app_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) (P : X.Opens) (U : Y.Opens)
    (h : P ≤ g ⁻¹ᵁ U) (M : schemeDerivedCategory Y) :
    (perfectOverlapRestrictionBeta g U P h).inv.app M =
      (overlapSiteInverse P).mapDerivedCategory.map
        ((singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
          (Scheme.Hom.resLE_comp_ι g h)).hom.app M) ≫
        (openSiteReturnIso X P).hom.app ((derivedPullback g).obj M) := by
  rw [perfectOverlapRestrictionBeta_inv_app,
    openPullbackRestrictionIso_inv_app_eq_square]

end

variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

/-- The local pullback map induced by a two-step scheme map and a lifted
object. It first crosses the pinned open square, transports the lifted object,
then uses the fixed restricted-composite comparison. -/
@[no_expose] noncomputable def perfectOverlapCompositeLocalMap
    {X K Y : Scheme.{u}} (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (hgf : gk ≫ f = g) (W : Y.Opens) (A : schemeDerivedCategory W.toScheme)
    (F : schemeDerivedCategory K)
    (e : (schemeOpenRestriction K (f ⁻¹ᵁ W)).mapDerivedCategory.obj F ≅
      (derivedPullback (f ∣_ W)).obj A) :
    (schemeOpenRestriction X (g ⁻¹ᵁ W)).mapDerivedCategory.obj
        ((derivedPullback gk).obj F) ⟶
      (derivedPullback (g ∣_ W)).obj A := by
  let hP : g ⁻¹ᵁ W ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, hgf]
  let j := gk.resLE (f ⁻¹ᵁ W) (g ⁻¹ᵁ W) hP
  exact (singleComplexOpenPullbackSquareIso gk (f ⁻¹ᵁ W) (g ⁻¹ᵁ W) j
      (Scheme.Hom.resLE_comp_ι gk hP)).inv.app F ≫
    (derivedPullback j).map e.hom ≫
      (perfectOverlapCompositeLocalIso f gk g hgf W).hom.app A

/-- Defining component equation for the named local composite map. -/
theorem perfectOverlapCompositeLocalMap_eq
    {X K Y : Scheme.{u}} (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (hgf : gk ≫ f = g) (W : Y.Opens) (A : schemeDerivedCategory W.toScheme)
    (F : schemeDerivedCategory K)
    (e : (schemeOpenRestriction K (f ⁻¹ᵁ W)).mapDerivedCategory.obj F ≅
      (derivedPullback (f ∣_ W)).obj A) :
    let hP : g ⁻¹ᵁ W ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, hgf]
    let j := gk.resLE (f ⁻¹ᵁ W) (g ⁻¹ᵁ W) hP
    perfectOverlapCompositeLocalMap g gk f hgf W A F e =
      (singleComplexOpenPullbackSquareIso gk (f ⁻¹ᵁ W) (g ⁻¹ᵁ W) j
        (Scheme.Hom.resLE_comp_ι gk hP)).inv.app F ≫
      (derivedPullback j).map e.hom ≫
        (perfectOverlapCompositeLocalIso f gk g hgf W).hom.app A := by
  intro hP j
  unfold perfectOverlapCompositeLocalMap
  rfl

/-- The pinned open-pullback cube for a two-step scheme map, on any open.
Source: Stacks Project, Tag 0D5S. The composite restriction equation supplies
the lower face; the identity map on the target supplies the upper face. The
general pinned cube then equates the two orders of restriction and pullback. -/
theorem perfectOverlapCompositeOpenCube
    {X K Y : Scheme.{u}} (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (hgf : gk ≫ f = g) (W : Y.Opens) (M : schemeDerivedCategory Y) :
    let hP : g ⁻¹ᵁ W ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, hgf]
    let h : gk ≫ f = g ≫ 𝟙 Y := by simpa using hgf
    let hW : W ≤ (𝟙 Y) ⁻¹ᵁ W := by simp
    let j := gk.resLE (f ⁻¹ᵁ W) (g ⁻¹ᵁ W) hP
    let hj : j ≫ (f ⁻¹ᵁ W).ι = (g ⁻¹ᵁ W).ι ≫ gk :=
      Scheme.Hom.resLE_comp_ι gk hP
    let h0 : j ≫ (f ∣_ W) = (g ∣_ W) ≫ Scheme.Hom.resLE (𝟙 Y) W W hW := by
      have hid : Scheme.Hom.resLE (𝟙 Y) W W hW = 𝟙 W.toScheme := by
        rw [Scheme.Hom.resLE_id]
        exact Scheme.homOfLE_rfl Y W
      rw [hid, Category.comp_id]
      exact perfectOverlapRestrictedComposite f gk g hgf W
    let q := singleComplexOpenSquareComparison f g (𝟙 Y) gk h
    let q0 := singleComplexOpenSquareComparison (f ∣_ W) (g ∣_ W)
      (Scheme.Hom.resLE (𝟙 Y) W W hW) j h0
    let RS := (schemeOpenRestriction Y W).mapDerivedCategory
    let RX := (schemeOpenRestriction X (g ⁻¹ᵁ W)).mapDerivedCategory
    let d := singleComplexOpenPullbackSquareIso f W (f ⁻¹ᵁ W) (f ∣_ W)
      (morphismRestrict_ι f W)
    let d' := singleComplexOpenPullbackSquareIso g W (g ⁻¹ᵁ W) (g ∣_ W)
      (morphismRestrict_ι g W)
    let e := singleComplexOpenPullbackSquareIso (𝟙 Y) W W
      (Scheme.Hom.resLE (𝟙 Y) W W hW)
      (Scheme.Hom.resLE_comp_ι (𝟙 Y) hW)
    let e' := singleComplexOpenPullbackSquareIso gk (f ⁻¹ᵁ W) (g ⁻¹ᵁ W) j hj
    q0.app (RS.obj M) ≫ (derivedPullback j).map (d.hom.app M) ≫
        e'.hom.app ((derivedPullback f).obj M) =
      (derivedPullback (g ∣_ W)).map (e.hom.app M) ≫
        d'.hom.app ((derivedPullback (𝟙 Y)).obj M) ≫ RX.map (q.app M) := by
  intro hP h hW j hj h0 q q0 RS RX d d' e e'
  exact singleComplexOpen_pullback_cube f g (𝟙 Y) gk h W W hW j hj h0 M

end AlgebraicGeometry
