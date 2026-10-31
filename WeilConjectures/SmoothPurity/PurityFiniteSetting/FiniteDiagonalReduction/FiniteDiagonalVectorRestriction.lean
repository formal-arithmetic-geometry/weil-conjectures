/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.RestrictionGeometry.FiniteDiagonalRestrictionGeometry
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionBaseComparisonLaws
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.ComparisonPullbackDerivedCoherence
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTatePullbackSquare
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalEtaleLocalityUnitChange
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseCoefficientComposition

/-! # Vector open restriction

Source: orientation charts, Steps 1--4.
(blueprint: lem-pur-finite-diagonal-vector-restriction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open RestrictionGeometry

namespace VectorRestrictionProof
open SectionRestriction

private theorem lift_orientation
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {K L M : C} {K' L' M' : D}
    (u : K ≅ L) (o : L ≅ M) (u' : K' ≅ L') (o' : L' ≅ M')
    (r : F.obj L ⟶ L') (s : F.obj K ⟶ K') (t : F.obj M ⟶ M')
    (hu : F.map u.hom ≫ r = s ≫ u'.hom)
    (ho : F.map o.hom ≫ t = r ≫ o'.hom) :
    F.map (u ≪≫ o).hom ≫ t = s ≫ (u' ≪≫ o').hom := by
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
  rw [ho, ← Category.assoc, hu, Category.assoc]

private theorem ordinary_etale (P : PurityFiniteSetting.{u})
    {N N' B : Scheme.{u}} (d : ℕ) (q : N ⟶ B)
    [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q]
    [SmoothOfRelativeDimension d q]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (v : N' ⟶ N) [Etale v] [IsSeparated v] [QuasiCompact v]
    (q' : N' ⟶ B) [IsSeparated q'] [LocallyOfFiniteType q'] [QuasiCompact q']
    [SmoothOfRelativeDimension d q'] (hq : v ≫ q = q')
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := P.noetherian aB
    letI := P.noetherian (q ≫ aB)
    letI := P.noetherian (q' ≫ aB)
    letI := Dnc.compactifiable P q aB
    letI := Dnc.compactifiable P q' aB
    (Etale.ordinaryFinitePullback P.Coefficient v).map
        (P.chartDualizingUnit q ≪≫ P.chartOrdinaryOrientation d q aB).hom ≫
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t v (P.diagonalExponent_isUnit (q ≫ aB)) d).hom =
      (Etale.sectionStructuralLocalityIso P.Coefficient v q q' hq).hom ≫
        (P.chartDualizingUnit q' ≪≫ P.chartOrdinaryOrientation d q' aB).hom := by
  subst q'
  let := P.noetherian aB
  let := P.noetherian (q ≫ aB)
  let := P.noetherian ((v ≫ q) ≫ aB)
  let := Dnc.compactifiable P q aB
  let := Dnc.compactifiable P (v ≫ q) aB
  let M := Etale.canonicalEtaleCompactSupportNormalization P.Coefficient
  have hu := congrArg Iso.hom (P.diagonalEtaleLocality_unitChange M v q (v ≫ q) rfl)
  simp only [Iso.trans_hom, Functor.mapIso_hom, diagonalDualizingCongr,
    eqToIso_refl, Iso.refl_hom, Category.comp_id] at hu
  exact lift_orientation _ _ _ _ _ _ _ _ hu
    (P.chartOrientation_etale_restriction d q aB v M t)

private theorem section_paste
    {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B']
    (S : A ⥤ B) (F : B ⥤ B') (V : A ⥤ A') (S' : A' ⥤ B')
    (η : S ⋙ F ≅ V ⋙ S')
    {W T : A} {W' T' : A'} {L : B} {L' : B'}
    (o : W ≅ T) (o' : W' ≅ T') (bc : V.obj W ≅ W') (cv : V.obj T ≅ T')
    (cs : S.obj T ≅ L) (cs' : S'.obj T' ≅ L') (cb : F.obj L ≅ L')
    (ho : V.map o.hom ≫ cv.hom = bc.hom ≫ o'.hom)
    (hc : F.map cs.inv ≫ η.hom.app T ≫ S'.map cv.hom = cb.hom ≫ cs'.inv) :
    F.map (S.mapIso o ≪≫ cs).hom ≫ cb.hom =
      (η.app W ≪≫ S'.mapIso bc).hom ≫ (S'.mapIso o' ≪≫ cs').hom := by
  have hc' := congrArg (fun e ↦ F.map cs.hom ≫ e ≫ cs'.hom) hc
  simp only [Category.assoc, ← F.map_comp_assoc, Iso.hom_inv_id, F.map_id,
    Category.id_comp, Iso.inv_hom_id, Category.comp_id] at hc'
  have hn := η.hom.naturality o.hom
  simp only [Functor.comp_map] at hn
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← hc', ← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← S'.map_comp_assoc, ho, S'.map_comp]
  simp only [Category.assoc, Iso.app_hom]

private theorem section_open (P : PurityFiniteSetting.{u})
    {B B' : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (b : B' ⟶ B) [IsOpenImmersion b] [QuasiCompact b]
    (d : ℕ) (X : Pair B d) (X' : Pair B' d) (sq : BaseChange b X' X)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := SmoothOfRelativeDimension.smooth d X.g
    letI := SmoothOfRelativeDimension.smooth d X'.g
    letI := Dnc.compactifiable P X.g aB
    letI := Dnc.compactifiable P X'.g (b ≫ aB)
    letI := Dnc.invertibleExponent P (X.g ≫ aB)
    (Etale.ordinaryFinitePullback P.Coefficient b).map
        (P.chartSectionOrientation d X.g aB X.s t).hom ≫
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t b (P.diagonalExponent_isUnit aB) d).hom =
      (Dnc.sectionBaseChange P.Coefficient d X.g sq.square X.s X'.s sq.section_eq).hom ≫
        (P.chartSectionOrientation d X'.g (b ≫ aB) X'.s t).hom := by
  let := SmoothOfRelativeDimension.smooth d X.g
  let := SmoothOfRelativeDimension.smooth d X'.g
  let := Dnc.compactifiable P X.g aB
  let := Dnc.compactifiable P X'.g (b ≫ aB)
  let := Dnc.invertibleExponent P (X.g ≫ aB)
  let M := ModuleCat.{u + 1} P.Coefficient
  let u := P.chartDualizingUnit X.g
  let u' := P.chartDualizingUnit X'.g
  let R := Etale.ordinaryFinitePullback P.Coefficient sq.map
  let := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
    P.Coefficient X.g d sq.square
  let := (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient sq.square).2
    (NatIso.isIso_app_of_isIso
      (Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq.square) (𝟙_ _))
  let bc := asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient sq.square)
  let c := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t sq.map
    (P.diagonalExponent_isUnit (X.g ≫ aB)) d
  have hu : R.map u.hom ≫ (P.chartOrdinaryBaseChange d X.g aB b X'.g
      sq.map sq.square).hom = bc.hom ≫ u'.hom := by
    simp only [chartOrdinaryBaseChange, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom]
    change R.map u.hom ≫ R.map u.inv ≫ bc.hom ≫ u'.hom = _
    rw [← R.map_comp_assoc, u.hom_inv_id, R.map_id, Category.id_comp]
  have ho := lift_orientation R u (P.chartOrdinaryOrientation d X.g aB)
    u' (P.chartOrdinaryOrientation d X'.g (b ≫ aB)) _ bc.hom c.hom hu
    (P.chartOrientation_open_baseChange d X.g aB b X'.g sq.map sq.square t)
  let η := (Etale.leftDerivedUpperStarComp M b X.s).symm ≪≫
    Etale.leftDerivedUpperStarComp M X'.s sq.map (b ≫ X.s) sq.section_eq.symm
  have hp := section_paste (Etale.ordinaryFinitePullback P.Coefficient X.s)
    (Etale.ordinaryFinitePullback P.Coefficient b) R
    (Etale.ordinaryFinitePullback P.Coefficient X'.s) η
    (u ≪≫ P.chartOrdinaryOrientation d X.g aB)
    (u' ≪≫ P.chartOrdinaryOrientation d X'.g (b ≫ aB)) bc c
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t X.s (P.diagonalExponent_isUnit (X.g ≫ aB)) d)
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t X'.s
      (P.diagonalExponent_isUnit (X'.g ≫ b ≫ aB)) d)
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t b (P.diagonalExponent_isUnit aB) d) ho
    (by
      simpa only [η, M, c, diagonalTwistEtale, Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app, Category.assoc] using
        (Etale.orderedTatePullbackSquare P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t X.s X'.s b sq.map sq.section_eq
          (P.diagonalExponent_isUnit (X.g ≫ aB)) (P.diagonalExponent_isUnit aB)
          (P.diagonalExponent_isUnit (X'.g ≫ b ≫ aB)) d))
  dsimp only [chartSectionOrientation, Dnc.sectionBaseChange, η, R, M, u, u', bc,
    Etale.ordinaryFinitePullback, Etale.sectionInvariant, Iso.trans, Iso.symm,
    Iso.app, Functor.mapIso] at hp ⊢
  simp only [NatTrans.comp_app, Category.assoc] at hp ⊢
  convert hp using 1; rfl

private theorem section_etale_paste
    {A A' B : Type*} [Category A] [Category A'] [Category B]
    (S : A ⥤ B) (V : A ⥤ A') (S' : A' ⥤ B) (η : S ≅ V ⋙ S')
    {W T : A} {W' T' : A'} {L : B}
    (o : W ≅ T) (o' : W' ≅ T') (e : V.obj W ≅ W') (cv : V.obj T ≅ T')
    (cs : S.obj T ≅ L) (cs' : S'.obj T' ≅ L)
    (ho : V.map o.hom ≫ cv.hom = e.hom ≫ o'.hom)
    (hc : η.hom.app T ≫ S'.map cv.hom ≫ cs'.hom = cs.hom) :
    (η.app W ≪≫ S'.mapIso e).inv ≫ (S.mapIso o ≪≫ cs).hom =
      (S'.mapIso o' ≪≫ cs').hom := by
  have hn := η.hom.naturality o.hom
  simp only [Functor.comp_map] at hn
  apply (cancel_epi (η.app W ≪≫ S'.mapIso e).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  symm
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [← S'.map_comp_assoc, ← ho]
  simp only [S'.map_comp, Category.assoc]
  rw [← reassoc_of% hn, hc]

private theorem section_etale (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d : ℕ) {X' X : Pair B d} (a : EtaleMap X' X)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := SmoothOfRelativeDimension.smooth d X.g
    letI := SmoothOfRelativeDimension.smooth d X'.g
    (restrictionEtale P aB a).hom ≫
        (P.chartSectionOrientation d X.g aB X.s t).hom =
      (P.chartSectionOrientation d X'.g aB X'.s t).hom := by
  let := SmoothOfRelativeDimension.smooth d X.g
  let := SmoothOfRelativeDimension.smooth d X'.g
  let := P.noetherian aB
  let := P.noetherian (X.g ≫ aB)
  let := P.noetherian (X'.g ≫ aB)
  let := Dnc.compactifiable P X.g aB
  let := Dnc.compactifiable P X'.g aB
  let M := ModuleCat.{u + 1} P.Coefficient
  let S := Etale.ordinaryFinitePullback P.Coefficient X.s
  let S' := Etale.ordinaryFinitePullback P.Coefficient X'.s
  let R := Etale.ordinaryFinitePullback P.Coefficient a.map
  let o := P.chartDualizingUnit X.g ≪≫ P.chartOrdinaryOrientation d X.g aB
  let o' := P.chartDualizingUnit X'.g ≪≫ P.chartOrdinaryOrientation d X'.g aB
  let η := Etale.leftDerivedUpperStarComp M X'.s a.map X.s a.section_eq.symm
  have ho := ordinary_etale P d X.g aB a.map X'.g a.over_eq t
  have ht := Etale.vectorIntegrationBaseCoefficientPullback_comp P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t X'.s a.map X.s
    a.section_eq.symm (P.diagonalExponent_isUnit (X.g ≫ aB))
    (P.diagonalExponent_isUnit (X'.g ≫ aB)) d
  rw [restrictionEtale_locality]
  exact section_etale_paste S R S' η o o'
    (Etale.sectionStructuralLocalityIso P.Coefficient a.map X.g X'.g a.over_eq)
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t a.map (P.diagonalExponent_isUnit (X.g ≫ aB)) d)
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t X.s (P.diagonalExponent_isUnit (X.g ≫ aB)) d)
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t X'.s (P.diagonalExponent_isUnit (X'.g ≫ aB)) d)
    ho (by simpa only [η, M, diagonalTwistEtale] using ht)

private theorem transport_restriction
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (A : C ⥤ D) (B : E ⥤ F) (R : D ⥤ F) (S : C ⥤ E)
    {x y : C} {x' y' : E} {z : D} {z' : F}
    (q : z ≅ A.obj x) (q' : z' ≅ B.obj x')
    (o : x ≅ y) (o' : x' ≅ y')
    (s : S.obj x ≅ x') (t : S.obj y ≅ y')
    (c : R.obj (A.obj x) ≅ B.obj (S.obj x))
    (c' : R.obj (A.obj y) ≅ B.obj (S.obj y))
    (hn : R.map (A.map o.hom) ≫ c'.hom = c.hom ≫ B.map (S.map o.hom))
    (h : S.map o.hom ≫ t.hom = s.hom ≫ o'.hom) :
    R.map (q ≪≫ A.mapIso o).hom ≫ (c' ≪≫ B.mapIso t).hom =
      (R.mapIso q ≪≫ c ≪≫ B.mapIso s ≪≫ q'.symm).hom ≫
        (q' ≪≫ B.mapIso o').hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hn, ← B.map_comp, h, B.map_comp]

private def pairOrientation (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] {d : ℕ} (X : Pair B d)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :=
  letI := SmoothOfRelativeDimension.smooth d X.g
  Dnc.sourceComparison P d X.g aB X.s ≪≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
      (P.chartSectionOrientation d X.g aB X.s t)

private theorem pair_open (P : PurityFiniteSetting.{u})
    {B B' : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB' : B' ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB'] [QuasiCompact aB']
    (b : B' ⟶ B) [IsOpenImmersion b] [QuasiCompact b] (ha : b ≫ aB = aB')
    (d : ℕ) (X : Pair B d) (X' : Pair B' d) (sq : BaseChange b X' X)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.map
        (pairOrientation P aB X t).hom ≫
      (Dnc.pullComparison P b (P.diagonalTwistEtale B d) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) B').mapDerivedCategory.mapIso
          (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates t b (P.diagonalExponent_isUnit aB) d)).hom =
      (baseComparison P aB aB' sq).hom ≫
        (pairOrientation P aB' X' t).hom := by
  subst aB'
  let := SmoothOfRelativeDimension.smooth d X.g
  let := SmoothOfRelativeDimension.smooth d X'.g
  let := Dnc.compactifiable P X.g aB
  let := Dnc.compactifiable P X'.g (b ≫ aB)
  let := Dnc.invertibleExponent P (X.g ≫ aB)
  exact transport_restriction _ _ _ _ _ _ _ _ _ _ _ _
    (congrArg Iso.hom (Dnc.pullComparison_naturality P b
      (P.chartSectionOrientation d X.g aB X.s t)))
    (section_open P aB b d X X' sq t)

private theorem comparison_etale
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x y z : C} {x' y' : D} (q : x' ≅ F.obj x) (q' : y' ≅ F.obj y)
    (e : y ≅ x) (o : x ≅ z) (o' : y ≅ z) (h : e.hom ≫ o.hom = o'.hom) :
    (q' ≪≫ F.mapIso e ≪≫ q.symm).hom ≫ (q ≪≫ F.mapIso o).hom =
      (q' ≪≫ F.mapIso o').hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← F.map_comp, h]

private theorem paste_restriction
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x y : C} {x' m y' : D} (o : x ≅ y) (b : F.obj x ≅ m)
    (e : x' ≅ m) (om : m ≅ y') (on : x' ≅ y') (t : F.obj y ≅ y')
    (hb : F.map o.hom ≫ t.hom = b.hom ≫ om.hom)
    (he : e.hom ≫ om.hom = on.hom) :
    F.map o.hom ≫ t.hom = (b ≪≫ e.symm).hom ≫ on.hom := by
  rw [hb, ← he]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

private theorem pair_etale (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d : ℕ) {X' X : Pair B d} (a : EtaleMap X' X)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    (restriction P aB a).hom ≫ (pairOrientation P aB X t).hom =
      (pairOrientation P aB X' t).hom := by
  exact comparison_etale _ _ _ _ _ _ (section_etale P aB d a t)

end VectorRestrictionProof

variable {X Y : Scheme.{u}} [IsNoetherian X]
variable (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
variable [SmoothOfRelativeDimension d (f.resLE V.1 U.1 hUV)]
variable (P : PurityFiniteSetting.{u})
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- Zero-section restriction of the normalized vector orientation commutes with
open restriction of the actual normal cones and the specified Tate comparison.
Source: orientation charts Step 4; vector-bundle purity, base-change paragraph.
(blueprint: lem-pur-finite-diagonal-vector-restriction).
Proof: apply chartOrientation_open_baseChange to the Cartesian normalBaseChange
square, and chartOrientation_etale_restriction to normalEtaleMap of the ambient
restriction. Pull each equation along its augmentation section. The two section
equations identify the pullback-composition constraints. The ordered Tate pullback
square composes the coefficient comparisons along these sections without permuting
factors. In ordinary etale coordinates, baseComparison is the smooth section
exchange, while restrictionEtale_locality identifies ambient restriction with the
inverse counit-normalized section locality. Thus the two squares compose to the
specified normalRestriction. Naturality of the site comparison and cancellation of
the normalComparison factors give the displayed equation. Rank zero uses the unit
comparison and the same argument applies to empty schemes. No delta or alpha occurs. -/
theorem vector_square :
    letI : IsAffine U.1.toScheme := U.2
    letI : IsAffine V.1.toScheme := V.2
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) U.1.ι).leftDerivedFunctor.map
        (vectorFactor P d f aY).hom ≫ (affineTateRestriction P f aY d U).hom =
    (normalRestriction d f U V hUV P aY).hom ≫
      (vectorFactor P d (f.resLE V.1 U.1 hUV) (V.1.ι ≫ aY)).hom := by
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine V.1.toScheme := V.2
  have _ := (inferInstance : IsSeparated aY)
  let h := f.resLE V.1 U.1 hUV
  let aX := f ≫ aY
  let aU := h ≫ V.1.ι ≫ aY
  have ha : U.1.ι ≫ aX = aU := by
    dsimp only [aX, aU, h]
    simp only [← Category.assoc, Scheme.Hom.resLE_comp_ι]
  let t := Etale.projectiveLineTraceTransport P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level)
    P.Coefficient P.diagonalExponent_annihilates
  let A := SectionRestriction.normalPair P aX (diagonalPair d f)
  let B := SectionRestriction.normalPair P aU (mixedPair d f U)
  let C := SectionRestriction.normalPair P aU (diagonalPair d h)
  let sq := SectionRestriction.normalBaseChange P aX aU (sourceSquare d f U)
  let e := SectionRestriction.normalEtaleMap P aU (ambientRestriction d f U V hUV)
  have hb := VectorRestrictionProof.pair_open P aX aU U.1.ι ha d A B sq t
  have he := VectorRestrictionProof.pair_etale P aU d e t
  have hh :
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) U.1.ι).leftDerivedFunctor.map
          (VectorRestrictionProof.pairOrientation P aX A t).hom ≫
        (affineTateRestriction P f aY d U).hom =
      (SectionRestriction.baseComparison P aX aU sq ≪≫
        (SectionRestriction.restriction P aU e).symm).hom ≫
          (VectorRestrictionProof.pairOrientation P aU C t).hom := by
    exact VectorRestrictionProof.paste_restriction _ _ _ _ _ _ _
      (by convert hb using 1; rfl) he
  simpa only [vectorFactor, chartDiagonalBeta, VectorRestrictionProof.pairOrientation,
    SectionRestriction.normalPair, diagonalPair, normalRestriction,
    Dnc.sourceComparison, Dnc.normalComparison, Dnc.sourceSection, Dnc.normalSection,
    SectionRestriction.invariant, Dnc.sourceEtale, Dnc.normalEtale,
    SectionRestriction.sectionEtale, Etale.sectionInvariant,
    A, B, C, sq, e, aX, aU, h, t] using hh

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
