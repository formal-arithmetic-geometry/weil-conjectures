/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrdinaryDiagonal.DiagonalOrdinaryChartLift
public import WeilConjectures.AlgebraicGeometry.DegreeZeroMapGluing.DegreeZeroDerivedMapGluing
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTateExactOpenComposition
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Restriction of the ordinary realization coordinates

Source: diagonal-dualizing proof, combining paragraph; Stacks 06XS and 099R.
(blueprint: lem-pur-diagonal-ordinary-realize-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
open AlgebraicGeometry.Etale (purityTwistTransport)
namespace WeilConjectures.PurityFiniteSetting.OrdinaryDiagonal

attribute [local irreducible] Etale.derivedTensor OrientationRefinement.tate unit
  PurityFiniteSetting.diagonalOrdinaryDualizing Etale.dualizingComplex
attribute [local implicit_reducible] PurityFiniteSetting.diagonalExponent
  PurityFiniteSetting.diagonalTwistEtale OrientationRefinement.inclusion

private theorem reverse_square
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {X₁ X₂ : C} {Y₀ Y₁ Z₀ : D}
    (q₀ : Y₀ ≅ Z₀) (q₁ : Y₁ ≅ G.obj X₁)
    (q₂ : X₁ ≅ X₂) (a : Y₀ ⟶ Y₁) (b : Z₀ ⟶ G.obj X₂)
    (h : a ≫ q₁.hom ≫ G.map q₂.hom = q₀.hom ≫ b) :
    q₀.inv ≫ a = b ≫ G.map q₂.inv ≫ q₁.inv := by
  have he := congrArg (fun t ↦ q₀.inv ≫ t ≫ G.map q₂.inv ≫ q₁.inv) h
  simpa only [Category.assoc, ← G.map_comp_assoc, ← G.map_comp, Iso.hom_inv_id,
    G.map_id, Category.id_comp, Category.comp_id, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id_assoc] using he

private theorem move_compositors
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {X Y : C} {V W : D} (p : V ≅ W) (e : X ≅ Y)
    (s : V ⟶ G.obj X) (r : W ⟶ G.obj Y)
    (h : s ≫ G.map e.hom = p.hom ≫ r) :
    p.inv ≫ s = r ≫ G.map e.inv := by
  have he := congrArg (fun a ↦ p.inv ≫ a ≫ G.map e.inv) h
  simpa only [Category.assoc, ← G.map_comp, Iso.hom_inv_id, G.map_id,
    Category.comp_id, Iso.inv_hom_id_assoc] using he

section Pasting
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  (A : C₀ ⥤ D₀) (B : C₁ ⥤ D₁) (C : C₂ ⥤ D₂)
  (R : C₀ ⥤ C₁) (S : C₁ ⥤ C₂) (T : C₀ ⥤ C₂)
  (P : D₀ ⥤ D₁) (Q : D₁ ⥤ D₂) (L : D₀ ⥤ D₂)
  (c : R ⋙ S ≅ T) (p : P ⋙ Q ≅ L)
  (q : A ⋙ P ≅ R ⋙ B) (r : B ⋙ Q ≅ S ⋙ C) (s : A ⋙ L ≅ T ⋙ C)
  (hc : ∀ K, p.app (A.obj K) ≪≫ s.app K =
    Q.mapIso (q.app K) ≪≫ r.app (R.obj K) ≪≫ C.mapIso (c.app K))

include hc

private theorem paste_transport (K : C₀) {N₁ : C₁} {N₂ : C₂}
    (v : R.obj K ≅ N₁) (w : T.obj K ≅ N₂) (z : S.obj N₁ ≅ N₂)
    (ho : c.app K ≪≫ w = S.mapIso v ≪≫ z) :
    p.app (A.obj K) ≪≫ s.app K ≪≫ C.mapIso w =
      Q.mapIso (q.app K ≪≫ B.mapIso v) ≪≫ r.app N₁ ≪≫ C.mapIso z := by
  have hh := congrArg Iso.hom (hc K)
  have hm := congrArg (fun a ↦ C.map a) (congrArg Iso.hom ho)
  have hn := r.hom.naturality v.hom
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp] at hh hm
  simp only [Functor.comp_map] at hn
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hh, hm, ← reassoc_of% hn]

private theorem paste_realize {M N : C₀} {E : D₀} (e : E ≅ A.obj M)
    (b : R.obj M ≅ R.obj N) {Z : D₁} {Z' : D₂}
    (v : P.obj (A.obj N) ≅ Z) (w : L.obj (A.obj N) ≅ Z')
    (z : Q.obj Z ≅ Z')
    (pE : (P ⋙ Q).obj E ≅ L.obj E) (hE : pE = p.app E)
    (ht : p.app (A.obj N) ≪≫ w = Q.mapIso v ≪≫ z) :
    L.mapIso e ≪≫ s.app M ≪≫
        C.mapIso ((c.app M).symm ≪≫ S.mapIso b ≪≫ c.app N) ≪≫
        (s.app N).symm ≪≫ w =
      pE.symm ≪≫
        Q.mapIso (P.mapIso e ≪≫ q.app M ≪≫ B.mapIso b ≪≫
          (q.app N).symm ≪≫ v) ≪≫ z := by
  subst pE
  have hM := congrArg Iso.hom (hc M)
  have hN := congrArg Iso.hom (hc N)
  have ht' := congrArg Iso.hom ht
  have hu := p.hom.naturality e.hom
  have hb := r.hom.naturality b.hom
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at hM hN ht'
  simp only [Functor.comp_map] at hu hb
  apply Iso.ext
  rw [← cancel_epi (p.app E).hom]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% hu, reassoc_of% hM]
  simp only [← C.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  simp only [C.map_comp, Category.assoc]
  rw [← reassoc_of% hb]
  rw [← cancel_mono w.inv]
  simp only [Category.assoc]
  rw [← reassoc_of% ht']
  simp only [Iso.hom_inv_id, Category.comp_id]
  rw [← cancel_mono (s.hom.app N)]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app]
  simp only [Functor.comp_obj]
  rw [Category.comp_id, hN]
  rw [← Q.map_comp_assoc (q.inv.app N) (q.hom.app N)]
  simp only [Iso.inv_hom_id_app, Functor.comp_obj, Q.map_id, Category.id_comp]
end Pasting

private def proOpenComp (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    {U V : X.Opens} (h : U ≤ V) :
    OrientationRefinement.pull P V.ι ⋙
        OrientationRefinement.pull P (X.homOfLE h) ≅
      OrientationRefinement.pull P U.ι :=
  (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    (X.homOfLE h) V.ι).symm ≪≫
    eqToIso (congrArg (fun j ↦ OrientationRefinement.pull P j) (X.homOfLE_ι h))

private theorem comparison_comp (P : PurityFiniteSetting.{u})
    {T S X : Scheme.{u}} (i : T ⟶ S) (j : S ⟶ X)
    (K : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) i j).symm.app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj K) ≪≫
      (comparison P (i ≫ j)).app K =
      (OrientationRefinement.pull P i).mapIso ((comparison P j).app K) ≪≫
        (comparison P i).app ((restrict P j).obj K) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.mapIso
          ((Functor.mapDerivedCategoryNatIso
            (Etale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) i j) ≪≫
              Functor.mapDerivedCategoryCompIso
                (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) j)
                (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) i)).symm.app K) := by
  let A := ModuleCat.{u + 1} P.Coefficient
  have hq (F : Sheaf X.smallEtaleTopology A) :
      (ProEtale.comparisonUpperStarCompUpperStarIso A (i ≫ j)).hom.app F ≫
        (ProEtale.comparisonUpperStar A T).map ((Etale.upperStarComp A i j).hom.app F) =
      (ProEtale.upperStarComp A i j).hom.app
          ((ProEtale.comparisonUpperStar A X).obj F) ≫
        (ProEtale.upperStar A i).map
          ((ProEtale.comparisonUpperStarCompUpperStarIso A j).hom.app F) ≫
        (ProEtale.comparisonUpperStarCompUpperStarIso A i).hom.app
          ((Etale.upperStar A j).obj F) := by
    have hh := (ProEtale.comparison_pullback_coherent.2.2 P.Coefficient).2.1 T S X i j F
    change (ProEtale.comparisonUpperStar A T).map
        ((Etale.upperStarComp A i j).hom.app F) ≫
      (ProEtale.comparisonUpperStarCompUpperStarIso A i).inv.app
        ((Etale.upperStar A j).obj F) ≫
      (ProEtale.upperStar A i).map
        ((ProEtale.comparisonUpperStarCompUpperStarIso A j).inv.app F) =
      (ProEtale.comparisonUpperStarCompUpperStarIso A (i ≫ j)).inv.app F ≫
        (ProEtale.upperStarComp A i j).hom.app
          ((ProEtale.comparisonUpperStar A X).obj F) at hh
    exact reverse_square (ProEtale.upperStar A i)
      ((ProEtale.comparisonUpperStarCompUpperStarIso A (i ≫ j)).app F).symm
      ((ProEtale.comparisonUpperStarCompUpperStarIso A i).app
        ((Etale.upperStar A j).obj F)).symm
      ((ProEtale.comparisonUpperStarCompUpperStarIso A j).app F).symm _ _ hh
  have hd := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (ProEtale.comparisonUpperStarCompUpperStarIso A j)
    (ProEtale.comparisonUpperStarCompUpperStarIso A i)
    (ProEtale.comparisonUpperStarCompUpperStarIso A (i ≫ j))
    (ProEtale.upperStarComp A i j) (Etale.upperStarComp A i j) hq K
  apply Iso.ext
  simp only [ProEtale.leftDerivedUpperStarComp, comparison,
    ProEtale.leftDerivedUpperStarIsoMapDerivedCategory,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Iso.app_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  have hn := (ProEtale.upperStar A i).leftDerivedFunctorIsoMapDerivedCategory.hom.naturality
    ((comparison P j).hom.app K)
  simp only [comparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    ProEtale.leftDerivedUpperStarIsoMapDerivedCategory] at hn
  rw [← Functor.map_comp_assoc, reassoc_of% hn]
  simp only [Functor.map_comp, Category.assoc]
  apply congrArg (fun a ↦
    (ProEtale.upperStar A i).leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((OrientationRefinement.pull P j).obj
          ((ProEtale.comparisonUpperStar A X).mapDerivedCategory.obj K)) ≫
      (ProEtale.upperStar A i).mapDerivedCategory.map
        ((ProEtale.upperStar A j).leftDerivedFunctorIsoMapDerivedCategory.hom.app
          ((ProEtale.comparisonUpperStar A X).mapDerivedCategory.obj K)) ≫ a)
  have hd' := move_compositors (ProEtale.comparisonUpperStar A T).mapDerivedCategory
    ((Functor.mapDerivedCategoryTriangleIso (ProEtale.upperStarComp A i j)).app
      ((ProEtale.comparisonUpperStar A X).mapDerivedCategory.obj K))
    ((Functor.mapDerivedCategoryTriangleIso (Etale.upperStarComp A i j)).app K) _ _ hd
  dsimp only [A, restrict] at hd' ⊢
  simpa only [Functor.mapDerivedCategoryTriangleIso,
    Functor.mapDerivedCategorySquareIso,
    ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso,
    Iso.app_inv, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc] using hd'

private theorem comparison_comp_congr (P : PurityFiniteSetting.{u})
    {T S X : Scheme.{u}} (i : T ⟶ S) (j : S ⟶ X) (k : T ⟶ X) (hk : i ≫ j = k)
    (K : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    let c := (Functor.mapDerivedCategoryCompIso
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) j)
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) i)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        ((Etale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) i j).symm ≪≫
          eqToIso (congrArg (fun a ↦ Etale.upperStar
            (ModuleCat.{u + 1} P.Coefficient) a) hk))
    let p := (ProEtale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} P.Coefficient) i j).symm ≪≫
      eqToIso (congrArg (fun a ↦ OrientationRefinement.pull P a) hk)
    p.app ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj K) ≪≫
      (comparison P k).app K =
      (OrientationRefinement.pull P i).mapIso ((comparison P j).app K) ≪≫
        (comparison P i).app ((restrict P j).obj K) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.mapIso (c.app K) := by
  subst k
  have hs : Functor.mapDerivedCategoryNatIso
      (Etale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) i j).symm =
      (Functor.mapDerivedCategoryNatIso
        (Etale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) i j)).symm :=
    Iso.ext (Functor.mapDerivedCategoryNatIso_symm _)
  simpa only [eqToIso_refl, Iso.trans_refl, hs, Iso.trans_symm] using comparison_comp P i j K

private theorem comparison_openComp (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    {U V : X.Opens} (h : U ≤ V)
    (K : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    let c := DegreeZeroMapGluing.openComp
      (fun T : Scheme.{u} ↦ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
      (fun {_ _} j ↦ Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) j)
      (fun {_ _ _} i j ↦ Etale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) i j) X h
    (proOpenComp P X h).app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj K) ≪≫
      (comparison P U.ι).app K =
      (OrientationRefinement.pull P (X.homOfLE h)).mapIso ((comparison P V.ι).app K) ≪≫
        (comparison P (X.homOfLE h)).app ((restrict P V.ι).obj K) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) U.toScheme).mapDerivedCategory.mapIso (c.app K) := by
  exact comparison_comp_congr P (X.homOfLE h) V.ι U.ι (X.homOfLE_ι h) K

private theorem tate_eq (P : PurityFiniteSetting.{u}) {T S : Scheme.{u}}
    (j : T ⟶ S) (aS : S ⟶ Spec (.of P.field.k)) (d : ℕ) :
    OrientationRefinement.tate P j aS d =
      (comparison P j).app (P.diagonalTwistEtale S d) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.mapIso
          (Etale.orderedTateExactPullback P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates
            (purityTwistTransport P.Coefficient P.diagonalExponent
              (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates)
            j (P.diagonalExponent_isUnit aS) d) := by
  apply Iso.ext
  simp only [OrientationRefinement.tate, Dnc.pullComparison, comparison,
    Etale.orderedTateExactPullback, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Iso.app_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rfl

private theorem tate_openComp (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (d : ℕ) {U V : X.Opens} (h : U ≤ V) :
    (proOpenComp P X h).app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
            (P.diagonalTwistEtale X d)) ≪≫
      OrientationRefinement.tate P U.ι aX d =
      (OrientationRefinement.pull P (X.homOfLE h)).mapIso
          (OrientationRefinement.tate P V.ι aX d) ≪≫
        OrientationRefinement.tate P (X.homOfLE h) (V.ι ≫ aX) d := by
  let A := ModuleCat.{u + 1} P.Coefficient
  let t := purityTwistTransport P.Coefficient P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates
  let tau := fun {T S : Scheme.{u}} (j : T ⟶ S)
      (hS : IsUnit (P.diagonalExponent : Γ(S, ⊤))) ↦
    Etale.orderedTateExactPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t j hS d
  have ho := Etale.orderedTateExactOpenComposition
    P.Coefficient P.diagonalExponent P.diagonalExponent_annihilates t X
    (P.diagonalExponent_isUnit aX) d h (P.diagonalExponent_isUnit (V.ι ≫ aX))
  have hp := paste_transport
    (ProEtale.comparisonUpperStar A X).mapDerivedCategory
    (ProEtale.comparisonUpperStar A V.toScheme).mapDerivedCategory
    (ProEtale.comparisonUpperStar A U.toScheme).mapDerivedCategory
    (restrict P V.ι) (restrict P (X.homOfLE h)) (restrict P U.ι)
    (OrientationRefinement.pull P V.ι) (OrientationRefinement.pull P (X.homOfLE h))
    (OrientationRefinement.pull P U.ι)
    (DegreeZeroMapGluing.openComp
      (fun T : Scheme.{u} ↦ Sheaf T.smallEtaleTopology A)
      (fun {_ _} j ↦ Etale.upperStar A j)
      (fun {_ _ _} i j ↦ Etale.upperStarComp A i j) X h)
    (proOpenComp P X h) (comparison P V.ι) (comparison P (X.homOfLE h))
    (comparison P U.ι) (comparison_openComp P X h) (P.diagonalTwistEtale X d)
    (N₁ := P.diagonalTwistEtale V.toScheme d)
    (N₂ := P.diagonalTwistEtale U.toScheme d)
    (tau V.ι (P.diagonalExponent_isUnit aX))
    (tau U.ι (P.diagonalExponent_isUnit aX))
    (tau (X.homOfLE h) (P.diagonalExponent_isUnit (V.ι ≫ aX))) ho
  simp only [tate_eq]
  dsimp only [A, t, tau, PurityFiniteSetting.diagonalTwistEtale] at hp ⊢
  simpa only [Iso.trans_assoc] using hp

private theorem tate_openComp_structural (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (d : ℕ) {U V : X.Opens} (h : U ≤ V)
    (aV : V.toScheme ⟶ Spec (.of P.field.k)) (ha : aV = V.ι ≫ aX) :
    (proOpenComp P X h).app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
            (P.diagonalTwistEtale X d)) ≪≫
      OrientationRefinement.tate P U.ι aX d =
      (OrientationRefinement.pull P (X.homOfLE h)).mapIso
          (OrientationRefinement.tate P V.ι aX d) ≪≫
        OrientationRefinement.tate P (X.homOfLE h) aV d := by
  subst aV
  exact tate_openComp P X aX d h

/-- Evaluate the transport abstractly, without reducing the geometric equality proof. -/
private theorem app_trans_congr
    {C D I : Type*} [Category C] [Category D] (F : I → C ⥤ D)
    {i j : I} (h : i = j) {G : C ⥤ D} (e : G ≅ F i) (K : C) :
    e.app K ≪≫ eqToIso (congrArg (fun a ↦ (F a).obj K) h) =
      (e ≪≫ eqToIso (congrArg F h)).app K := by
  subst j
  simp

private theorem sourceComp_eq_openComp (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    {V V' : Y.affineOpens} (h : V'.1 ≤ V.1) : OrientationRefinement.sourceComposition P f aY h =
      (proOpenComp P X (f.preimage_mono h)).app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
          (Etale.dualizingComplex P.Coefficient f)) := by
  dsimp only [OrientationRefinement.sourceComposition, proOpenComp,
    OrientationRefinement.omega, OrientationRefinement.inclusion]
  exact app_trans_congr
    (fun j : (f ⁻¹ᵁ V'.1).toScheme ⟶ X ↦ OrientationRefinement.pull P j)
    (X.homOfLE_ι (f.preimage_mono h)) _ _

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  ProEtale.comparisonUpperStar Etale.upperStar ProEtale.upperStar
  proOpenComp DegreeZeroMapGluing.openComp

/-- The realization coordinates commute with one nested affine restriction.
This is an identity for every ordinary local isomorphism; there is no choice of
charts, agreement hypothesis, cover, shift removal or descent assertion.
Source: diagonal-dualizing proof, combining paragraph, restriction of the two
sides; Stacks 099R (comparison with inverse image) and 06XS (exact restriction).
(blueprint: lem-pur-diagonal-ordinary-realize-restriction).

Proof: expand realize and the ordinary open compositor. Naturality of comparison
moves the ordinary arrow through the site-comparison isomorphism. The composition
law for comparisonUpperStarCompUpperStarIso, derived termwise, identifies the
source factors with sourceComposition; naturality also moves the unit conversion
through this compositor. On the target the Cartesian finite Tate comparisons
compose: at degree zero this is the constant-unit pullback law; for each next
factor it is tensor pullback composition and the normalized roots/finite-line
pullback law, followed by the shift comparison. Induction on d thus identifies
the target factors with the indicated tate map. The structural k-morphisms agree
by morphismRestrict_ι and homOfLE_ι; their invertibility proofs are propositionally
irrelevant. Cancel the adjacent comparison inverses and reassociate. The same
identities hold for the empty scheme and the zero-fold tensor, so neither
nonemptiness nor positive relative dimension is required. -/
theorem realize_restriction (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) {V V' : Y.affineOpens} (h : V'.1 ≤ V.1)
    (b : (restrict P (f ⁻¹ᵁ V.1).ι).obj (P.diagonalOrdinaryDualizing f) ≅
      (restrict P (f ⁻¹ᵁ V.1).ι).obj (P.diagonalTwistEtale X d)) :
    let c := DegreeZeroMapGluing.openComp
      (fun T : Scheme.{u} ↦ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
      (fun {_ _} j ↦ Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) j)
      (fun {_ _ _} i j ↦ Etale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) i j)
      X (f.preimage_mono h)
    realize P f aY d V'
        ((c.app (P.diagonalOrdinaryDualizing f)).symm ≪≫
          (restrict P (OrientationRefinement.inclusion f h)).mapIso b ≪≫
          c.app (P.diagonalTwistEtale X d)) =
      (OrientationRefinement.sourceComposition P f aY h).symm ≪≫
        (OrientationRefinement.pull P (OrientationRefinement.inclusion f h)).mapIso
          (realize P f aY d V b) ≪≫
        OrientationRefinement.tate P (OrientationRefinement.inclusion f h)
          ((f ∣_ V.1) ≫ V.1.ι ≫ aY) d := by
  dsimp only
  unfold realize
  exact paste_realize
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) (f ⁻¹ᵁ V.1).toScheme).mapDerivedCategory
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) (f ⁻¹ᵁ V'.1).toScheme).mapDerivedCategory
    (restrict P (f ⁻¹ᵁ V.1).ι) (restrict P (OrientationRefinement.inclusion f h))
    (restrict P (f ⁻¹ᵁ V'.1).ι)
    (OrientationRefinement.pull P (f ⁻¹ᵁ V.1).ι)
    (OrientationRefinement.pull P (OrientationRefinement.inclusion f h))
    (OrientationRefinement.pull P (f ⁻¹ᵁ V'.1).ι)
    (DegreeZeroMapGluing.openComp
      (fun T : Scheme.{u} ↦ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
      (fun {_ _} j ↦ Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) j)
      (fun {_ _ _} i j ↦ Etale.upperStarComp (ModuleCat.{u + 1} P.Coefficient) i j)
      X (f.preimage_mono h))
    (proOpenComp P X (f.preimage_mono h))
    (comparison P (f ⁻¹ᵁ V.1).ι) (comparison P (OrientationRefinement.inclusion f h))
    (comparison P (f ⁻¹ᵁ V'.1).ι) (comparison_openComp P X (f.preimage_mono h))
    (M := P.diagonalOrdinaryDualizing f) (N := P.diagonalTwistEtale X d)
    (E := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
      (Etale.dualizingComplex P.Coefficient f))
    (Z := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) (f ⁻¹ᵁ V.1).toScheme).mapDerivedCategory.obj
      (P.diagonalTwistEtale (f ⁻¹ᵁ V.1).toScheme d))
    (Z' := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) (f ⁻¹ᵁ V'.1).toScheme).mapDerivedCategory.obj
      (P.diagonalTwistEtale (f ⁻¹ᵁ V'.1).toScheme d))
    ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso (unit P f)) b
    (OrientationRefinement.tate P (f ⁻¹ᵁ V.1).ι (f ≫ aY) d)
    (OrientationRefinement.tate P (f ⁻¹ᵁ V'.1).ι (f ≫ aY) d)
    (OrientationRefinement.tate P (OrientationRefinement.inclusion f h)
      ((f ∣_ V.1) ≫ V.1.ι ≫ aY) d)
    (OrientationRefinement.sourceComposition P f aY h) (sourceComp_eq_openComp P f aY h)
    (tate_openComp_structural P X (f ≫ aY) d (f.preimage_mono h)
      ((f ∣_ V.1) ≫ V.1.ι ≫ aY) (by rw [reassoc_of% morphismRestrict_ι]))

end WeilConjectures.PurityFiniteSetting.OrdinaryDiagonal
