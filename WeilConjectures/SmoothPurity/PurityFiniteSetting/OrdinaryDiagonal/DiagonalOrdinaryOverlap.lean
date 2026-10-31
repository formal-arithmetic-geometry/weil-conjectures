/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrdinaryDiagonal.DiagonalOrdinaryChartLift
public import WeilConjectures.AlgebraicGeometry.DegreeZeroMapGluing.DegreeZeroDerivedMapGluing
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.OpenClosed.Conservative
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrdinaryDiagonal.DiagonalOrdinaryRealizeRestriction

/-! # Ordinary overlap compatibility of local diagonal orientations

Source: latest blueprint, diagonal-dualizing proof, combining paragraph; Stacks 06XS.
(blueprint: lem-pur-diagonal-ordinary-overlap).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.OrdinaryDiagonal

attribute [local irreducible] Etale.derivedTensor

/-- Shift a local isomorphism using the exact restriction's canonical shift comparison.
Source: Stacks 06XS (blueprint: lem-pur-diagonal-ordinary-overlap). -/
def shiftLocal (P : PurityFiniteSetting.{u}) {T S : Scheme.{u}} (j : T ⟶ S)
    {M N : _root_.DerivedCategory (Sheaf S.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))}
    (b : (restrict P j).obj M ≅ (restrict P j).obj N) (n : ℤ) :
    (restrict P j).obj (M⟦n⟧) ≅ (restrict P j).obj (N⟦n⟧) :=
  ((restrict P j).commShiftIso n).app M ≪≫
    (shiftFunctor _ n).mapIso b ≪≫ (((restrict P j).commShiftIso n).app N).symm

/-- Restrict an isomorphism to an overlap with its canonical endpoint comparisons.
Source: Stacks 06XS (blueprint: lem-pur-diagonal-ordinary-overlap). -/
def onSmallerIso (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    {M N : _root_.DerivedCategory (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))} {U V : T.Opens} (h : U ≤ V)
    (b : (restrict P V.ι).obj M ≅ (restrict P V.ι).obj N) :
    (restrict P U.ι).obj M ≅ (restrict P U.ι).obj N :=
  let c := DegreeZeroMapGluing.openComp
    (fun X : Scheme.{u} ↦ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    (fun {_ _} f ↦ Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f)
    (fun {_ _ _} f g ↦ Etale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) f g) T h
  (c.app M).symm ≪≫ (restrict P (T.homOfLE h)).mapIso b ≪≫ c.app N

private def comp (P : PurityFiniteSetting.{u}) {R S T : Scheme.{u}}
    (i : T ⟶ S) (j : S ⟶ R) (k : T ⟶ R) (h : k = i ≫ j) :
    restrict P k ≅ restrict P j ⋙ restrict P i :=
  Functor.mapDerivedCategoryTriangleIso
    (Etale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) i j k h)

private theorem comp_assoc (P : PurityFiniteSetting.{u})
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h) :
    comp P f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc]) ≪≫
        Functor.isoWhiskerRight (comp P g h gh hgh) (restrict P f) =
      comp P fg h fgh hfgh ≪≫
        Functor.isoWhiskerLeft (restrict P h) (comp P f g fg hfg) := by
  let A := ModuleCat.{u + 1} P.Coefficient
  let F := Etale.upperStar A h
  let G := Etale.upperStar A g
  let H := Etale.upperStar A f
  let a := Etale.upperStarComp A g h gh hgh
  let b := Etale.upperStarComp A f gh fgh
    (by rw [hfgh, hfg, hgh, Category.assoc])
  let c := Etale.upperStarComp A f g fg hfg
  let d := Etale.upperStarComp A fg h fgh hfgh
  have hab : b ≪≫ Functor.isoWhiskerRight a H =
      d ≪≫ Functor.isoWhiskerLeft F c := by
    apply Iso.ext
    exact Etale.upperStarComp_assoc' A f g h fg gh fgh hfg hgh hfgh
  apply Iso.ext
  have hm := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom) hab
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hm
  have hwr := Functor.mapDerivedCategoryNatIso_isoWhiskerRight a H
  have hwl := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F c
  have ha := Functor.mapDerivedCategoryCompIso_assoc F G H
  change (Functor.mapDerivedCategoryTriangleIso b ≪≫
      Functor.isoWhiskerRight (Functor.mapDerivedCategoryTriangleIso a)
        H.mapDerivedCategory).hom =
    (Functor.mapDerivedCategoryTriangleIso d ≪≫
      Functor.isoWhiskerLeft F.mapDerivedCategory
        (Functor.mapDerivedCategoryTriangleIso c)).hom
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_comp,
    Functor.whiskerLeft_comp, Category.assoc]
  rw [← reassoc_of% hwr, ← reassoc_of% hwl, ← ha, reassoc_of% hm]

private theorem openComp_eq (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    {U V : T.Opens} (h : U ≤ V) :
    DegreeZeroMapGluing.openComp
      (fun X : Scheme.{u} ↦ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
      (fun {_ _} f ↦ Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f)
      (fun {_ _ _} f g ↦ Etale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) f g) T h =
      (comp P (T.homOfLE h) V.ι U.ι (T.homOfLE_ι h).symm).symm := by
  let A := ModuleCat.{u + 1} P.Coefficient
  have hc {R S Q : Scheme.{u}} (i : Q ⟶ S) (j : S ⟶ R)
      (k : Q ⟶ R) (hk : i ≫ j = k) :
      (Etale.upperStarComp A i j).symm ≪≫
          eqToIso (congrArg (fun f ↦ Etale.upperStar A f) hk) =
        (Etale.upperStarComp A i j k hk.symm).symm := by
    subst k
    simp
  simp only [DegreeZeroMapGluing.openComp, comp,
    Functor.mapDerivedCategoryTriangleIso, Iso.trans_symm]
  rw [hc _ _ _ (T.homOfLE_ι h)]
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapDerivedCategoryNatIso_symm, Iso.symm_hom]
  rfl

private theorem map_eq_of_cover (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    {I : Type u} {T : I → Scheme.{u}} (j : ∀ i, T i ⟶ S)
    (hcov : ∀ x : S, ∃ i, x ∈ Set.range (j i))
    {M N : _root_.DerivedCategory (Sheaf S.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))}
    (hM : _root_.DerivedCategory.homologyConcentratedIn 0 0 M)
    (hN : _root_.DerivedCategory.homologyConcentratedIn 0 0 N)
    (a b : M ⟶ N) (hab : ∀ i, (restrict P (j i)).map a = (restrict P (j i)).map b) :
    a = b := by
  have := hM.2
  have := hN.1
  apply (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE 0).injective
  have hf : JointlyFaithful
      (fun i ↦ Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (j i)) := by
    apply JointlyReflectIsomorphisms.jointlyFaithful
    constructor
    intro K L z hz
    exact Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective
      (ModuleCat.{u + 1} P.Coefficient) j hcov z hz
  apply hf.map_injective
  intro i
  let e := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
    (j i)).mapDerivedCategoryHomologyFunctorIso 0
  exact (NatIso.naturality_2 e a).symm.trans
    ((congrArg (fun z ↦ e.hom.app M ≫ z ≫ e.inv.app N)
      ((_root_.DerivedCategory.homologyFunctor _ 0).congr_map (hab i))).trans
        (NatIso.naturality_2 e b))

private theorem onSmaller_comp (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    {M N : _root_.DerivedCategory (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))} {U V : T.Opens} (h : U ≤ V)
    (b : (restrict P V.ι).obj M ≅ (restrict P V.ι).obj N) :
    onSmallerIso P T h b =
      (comp P (T.homOfLE h) V.ι U.ι (T.homOfLE_ι h).symm).app M ≪≫
        (restrict P (T.homOfLE h)).mapIso b ≪≫
          ((comp P (T.homOfLE h) V.ι U.ι (T.homOfLE_ι h).symm).app N).symm := by
  simp only [onSmallerIso, openComp_eq]
  rfl

private def localIso (P : PurityFiniteSetting.{u}) {R S T : Scheme.{u}}
    (i : T ⟶ S) (j : S ⟶ R) (k : T ⟶ R) (h : k = i ≫ j)
    {M N : _root_.DerivedCategory (Sheaf R.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))}
    (b : (restrict P j).obj M ≅ (restrict P j).obj N) :
    (restrict P k).obj M ≅ (restrict P k).obj N :=
  (comp P i j k h).app M ≪≫ (restrict P i).mapIso b ≪≫
    ((comp P i j k h).app N).symm

private theorem localIso_trans (P : PurityFiniteSetting.{u})
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    {M N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))}
    (b : (restrict P h).obj M ≅ (restrict P h).obj N) :
    localIso P fg h fgh hfgh b =
      localIso P f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])
        (localIso P g h gh hgh b) := by
  apply Iso.ext
  have a₁ : (comp P f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app M ≫
      (restrict P f).map ((comp P g h gh hgh).hom.app M) =
      (comp P fg h fgh hfgh).hom.app M ≫
        (comp P f g fg hfg).hom.app ((restrict P h).obj M) :=
    congrArg (fun e ↦ e.hom.app M) (comp_assoc P f g h fg gh fgh hfg hgh hfgh)
  have a₂ : (comp P f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app N ≫
      (restrict P f).map ((comp P g h gh hgh).hom.app N) =
      (comp P fg h fgh hfgh).hom.app N ≫
        (comp P f g fg hfg).hom.app ((restrict P h).obj N) :=
    congrArg (fun e ↦ e.hom.app N) (comp_assoc P f g h fg gh fgh hfg hgh hfgh)
  have hn := (comp P f g fg hfg).hom.naturality b.hom
  have a₂' : (comp P f g fg hfg).hom.app ((restrict P h).obj N) ≫
      (restrict P f).map ((comp P g h gh hgh).inv.app N) ≫
        (comp P f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).inv.app N =
      (comp P fg h fgh hfgh).inv.app N := by
    rw [← cancel_epi ((comp P fg h fgh hfgh).hom.app N), ← reassoc_of% a₂]
    erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    simp only [Category.id_comp, Iso.hom_inv_id_app]
  simp only [localIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% a₁]
  erw [← reassoc_of% hn]
  rw [a₂']

private theorem onSmaller_shift (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    {M N : _root_.DerivedCategory (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))} {U V : T.Opens} (h : U ≤ V)
    (b : (restrict P V.ι).obj M ≅ (restrict P V.ι).obj N) (n : ℤ) :
    onSmallerIso P T h (shiftLocal P V.ι b n) =
      shiftLocal P U.ι (onSmallerIso P T h b) n := by
  rw [onSmaller_comp, onSmaller_comp]
  let c := comp P (T.homOfLE h) V.ι U.ι (T.homOfLE_ι h).symm
  have hc : NatTrans.CommShift c.hom ℤ := by
    dsimp only [c, comp, Functor.mapDerivedCategoryTriangleIso]
    change NatTrans.CommShift (_ ≫ _) ℤ
    infer_instance
  have hc' : NatTrans.CommShift c.inv ℤ := inferInstance
  apply Iso.ext
  simp only [shiftLocal, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  change c.hom.app (M⟦n⟧) ≫ _ = _
  rw [NatTrans.app_shift c.hom n M, NatTrans.app_shift c.inv n N]
  simp only [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app,
    Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  erw [← (restrict P (T.homOfLE h)).commShiftIso_inv_naturality_assoc b.hom n]
  simp only [Iso.inv_hom_id_app_assoc, Functor.map_comp, Category.assoc]
  rfl

private theorem realize_injective (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) (V : Y.affineOpens)
    (b b' : (restrict P (f ⁻¹ᵁ V.1).ι).obj (P.diagonalOrdinaryDualizing f) ≅
      (restrict P (f ⁻¹ᵁ V.1).ι).obj (P.diagonalTwistEtale X d))
    (hb : realize P f aY d V b = realize P f aY d V b') : b = b' := by
  let n : ℤ := -(2 * (d : ℤ))
  let N := (restrict P (f ⁻¹ᵁ V.1).ι).obj (P.diagonalTwistEtale X d)
  have hN : _root_.DerivedCategory.homologyConcentratedIn 0 0 (N⟦n⟧) := by
    exact concentrated_iso
      (((restrict P (f ⁻¹ᵁ V.1).ι).commShiftIso n).app (P.diagonalTwistEtale X d))
      (Functor.homologyConcentratedIn_mapDerivedCategory_obj
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (f ⁻¹ᵁ V.1).ι)
        (twist_concentrated P X (f ≫ aY) d))
  have hplus : _root_.DerivedCategory.TStructure.t.plus N := by
    have := hN.1
    have := _root_.DerivedCategory.TStructure.t.isGE_shift (N⟦n⟧) 0 (-n) n (by omega)
    exact ⟨n, _root_.DerivedCategory.TStructure.t.isGE_of_iso (shiftShiftNeg N n) n⟩
  apply Iso.ext
  apply (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map _ _ hplus).injective
  have h := congrArg Iso.hom hb
  simp only [realize, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv] at h
  have h := (cancel_epi _).1 ((cancel_epi _).1 h)
  simp only [← Category.assoc] at h
  exact (cancel_mono _).1 ((cancel_mono _).1 h)

private theorem nested (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] {V V' : Y.affineOpens}
    (D : OrientationRefinement.Chart P f aY d V)
    (D' : OrientationRefinement.Chart P f aY d V') (h : V'.1 ≤ V.1)
    (hD : OrientationRefinement.Agrees P f aY d D D' h)
    (b : (restrict P (f ⁻¹ᵁ V.1).ι).obj (P.diagonalOrdinaryDualizing f) ≅
      (restrict P (f ⁻¹ᵁ V.1).ι).obj (P.diagonalTwistEtale X d))
    (b' : (restrict P (f ⁻¹ᵁ V'.1).ι).obj (P.diagonalOrdinaryDualizing f) ≅
      (restrict P (f ⁻¹ᵁ V'.1).ι).obj (P.diagonalTwistEtale X d))
    (hb : realize P f aY d V b =
      OrientationRefinement.theta P f aY d V D.geometry D.betaEtale)
    (hb' : realize P f aY d V' b' =
      OrientationRefinement.theta P f aY d V' D'.geometry D'.betaEtale) :
    onSmallerIso P X (f.preimage_mono h) b = b' := by
  apply realize_injective P f aY d V'
  rw [show realize P f aY d V' (onSmallerIso P X (f.preimage_mono h) b) = _ from
    realize_restriction P f aY d h b]
  rw [hb, hb']
  change OrientationRefinement.sourceComposition P f aY h ≪≫ _ = _ at hD
  rw [← hD]
  simp only [Iso.symm_self_id_assoc]

set_option linter.unusedVariables false in
/-- The ordinary lifts agree on a possibly nonaffine overlap, after removing the
common even shift. This asserts only compatibility of existing local maps, with
no global map or gluing conclusion.
Source: latest blueprint thm-pur-diagonal-dualizing-object.proof.md, combining
paragraph; parent gluing plan Step 2; Stacks 06XS, 03EM and 04TQ.
(blueprint: lem-pur-diagonal-ordinary-overlap).

Proof: cover V intersect V' by finite-type affine subopens W; their inverse images
cover the source overlap. On each W, Agrees identifies the two theta restrictions
with theta_W. Naturality of the ordinary/pro-etale pullback comparison transports
these equations to realize. The Tate pullback comparisons compose by the Cartesian
coefficient-twist theorem, and the source compositors compose by inverse-image
functoriality. Cancel those comparison isomorphisms. Ordinary comparison is fully
faithful on bounded-below objects; the target here is a shifted finite Tate sheaf.
Thus the two ordinary restrictions agree on W. Remove the even shift using its
canonical commuting isomorphisms. The Tate object and, via each local isomorphism,
the source are now concentrated in degree zero. The equality test of
 degreeZeroDerivedMapGluing on this cover of the overlap gives equality on the
whole overlap. Equality of homs gives equality of isomorphisms. This does not assume
affine intersections; empty overlaps use the empty-cover equality test. -/
theorem overlap (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] [IsNoetherian X] [IsNoetherian Y]
    [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (D : ∀ (V : Y.affineOpens), (V.1.ι ≫ aY).appTop.hom.FiniteType →
      OrientationRefinement.Chart P f aY d V)
    (hD : ∀ (V V' : Y.affineOpens)
      (hV : (V.1.ι ≫ aY).appTop.hom.FiniteType)
      (hV' : (V'.1.ι ≫ aY).appTop.hom.FiniteType) (h : V'.1 ≤ V.1),
      OrientationRefinement.Agrees P f aY d (D V hV) (D V' hV') h)
    (b : ∀ (V : Y.affineOpens) (hV : (V.1.ι ≫ aY).appTop.hom.FiniteType),
      (restrict P (f ⁻¹ᵁ V.1).ι).obj (P.diagonalOrdinaryDualizing f) ≅
        (restrict P (f ⁻¹ᵁ V.1).ι).obj (P.diagonalTwistEtale X d))
    (hb : ∀ V hV, realize P f aY d V (b V hV) =
      OrientationRefinement.theta P f aY d V (D V hV).geometry (D V hV).betaEtale)
    (V V' : Y.affineOpens)
    (hV : (V.1.ι ≫ aY).appTop.hom.FiniteType)
    (hV' : (V'.1.ι ≫ aY).appTop.hom.FiniteType) :
    onSmallerIso P X (inf_le_left : f ⁻¹ᵁ V.1 ⊓ f ⁻¹ᵁ V'.1 ≤ f ⁻¹ᵁ V.1)
        (shiftLocal P _ (b V hV) (-(2 * (d : ℤ)))) =
      onSmallerIso P X (inf_le_right : f ⁻¹ᵁ V.1 ⊓ f ⁻¹ᵁ V'.1 ≤ f ⁻¹ᵁ V'.1)
        (shiftLocal P _ (b V' hV') (-(2 * (d : ℤ)))) := by
  classical
  let N := P.diagonalTwistEtale X d
  let n : ℤ := -(2 * (d : ℤ))
  let O : X.Opens := f ⁻¹ᵁ V.1 ⊓ f ⁻¹ᵁ V'.1
  let a := onSmallerIso P X (inf_le_left : O ≤ f ⁻¹ᵁ V.1)
    (shiftLocal P _ (b V hV) n)
  let a' := onSmallerIso P X (inf_le_right : O ≤ f ⁻¹ᵁ V'.1)
    (shiftLocal P _ (b V' hV') n)
  have hN : _root_.DerivedCategory.homologyConcentratedIn 0 0
      ((restrict P O.ι).obj (N⟦n⟧)) :=
    Functor.homologyConcentratedIn_mapDerivedCategory_obj
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) O.ι)
      (twist_concentrated P X (f ≫ aY) d)
  have hM := concentrated_iso a.symm hN
  let I := {W : Y.affineOpens // W.1 ≤ V.1 ⊓ V'.1}
  have hft (W : Y.affineOpens) : (W.1.ι ≫ aY).appTop.hom.FiniteType :=
    HasRingHomProperty.appTop @LocallyOfFiniteType (W.1.ι ≫ aY) inferInstance
  let U (W : I) := f ⁻¹ᵁ W.val.1
  have hU (W : I) : U W ≤ O :=
    le_inf (f.preimage_mono (W.property.trans inf_le_left))
      (f.preimage_mono (W.property.trans inf_le_right))
  let j (W : I) := X.homOfLE (hU W)
  have hcov : ∀ x : O.toScheme, ∃ W : I, x ∈ Set.range (j W) := by
    intro x
    have hx : f x.val ∈ V.1 ⊓ V'.1 := x.property
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hsub⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hx (V.1 ⊓ V'.1).isOpen
    refine ⟨⟨⟨W, hW⟩, hsub⟩, ⟨x.val, hxW⟩, ?_⟩
    apply Subtype.ext
    exact Scheme.homOfLE_apply _ _
  apply Iso.ext
  change a.hom = a'.hom
  apply map_eq_of_cover P j hcov hM hN
  intro W
  have heq (Q : Y.affineOpens) (hQ : (Q.1.ι ≫ aY).appTop.hom.FiniteType)
      (hOQ : O ≤ f ⁻¹ᵁ Q.1) (hWQ : W.val.1 ≤ Q.1) :
      localIso P (j W) O.ι (U W).ι (X.homOfLE_ι (hU W)).symm
          (onSmallerIso P X hOQ (shiftLocal P _ (b Q hQ) n)) =
        shiftLocal P _ (b W.val (hft W.val)) n := by
    have hnest := nested P f aY d (D Q hQ) (D W.val (hft W.val)) hWQ
      (hD Q W.val hQ (hft W.val) hWQ) (b Q hQ) (b W.val (hft W.val))
      (hb Q hQ) (hb W.val (hft W.val))
    have ht := localIso_trans P (j W) (X.homOfLE hOQ) (f ⁻¹ᵁ Q.1).ι
      (X.homOfLE (f.preimage_mono hWQ)) O.ι (U W).ι
      (by dsimp only [j]; exact (X.homOfLE_homOfLE (hU W) hOQ).symm)
      (X.homOfLE_ι hOQ).symm (X.homOfLE_ι (f.preimage_mono hWQ)).symm
      (shiftLocal P _ (b Q hQ) n)
    have ht' : onSmallerIso P X (f.preimage_mono hWQ)
        (shiftLocal P _ (b Q hQ) n) =
        localIso P (j W) O.ι (U W).ι (X.homOfLE_ι (hU W)).symm
          (onSmallerIso P X hOQ (shiftLocal P _ (b Q hQ) n)) := by
      simpa only [onSmaller_comp, localIso] using ht
    rw [← ht', onSmaller_shift, hnest]
  have hh := congrArg Iso.hom
    ((heq V hV inf_le_left (W.property.trans inf_le_left)).trans
      (heq V' hV' inf_le_right (W.property.trans inf_le_right)).symm)
  simp only [localIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv] at hh
  have hh := (cancel_epi _).1 hh
  exact (cancel_mono _).1 hh

end WeilConjectures.PurityFiniteSetting.OrdinaryDiagonal
