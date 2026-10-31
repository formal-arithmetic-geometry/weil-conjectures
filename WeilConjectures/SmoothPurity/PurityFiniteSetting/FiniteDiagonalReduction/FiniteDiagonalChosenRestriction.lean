/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalOrientationRestrictionData
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionBaseComparisonLaws
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleSourceEndpoint

/-! # Chosen diagonal restriction
(blueprint: lem-pur-finite-diagonal-chosen-restriction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

namespace RestrictionProof

private theorem recover_chain
    {C : Type*} [Category C] {W V Z Q R : C}
    (e : W ≅ V) (c : V ≅ Z) (j : Z ≅ Q) (i : Q ≅ R) (b : W ⟶ R)
    (h : b ≫ i.inv ≫ j.inv = e.hom ≫ c.hom) :
    (e ≪≫ c ≪≫ j ≪≫ i).hom = b := by
  have hh := congrArg (fun z ↦ z ≫ j.hom ≫ i.hom) h
  simpa only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using hh.symm

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

private theorem unit_conjugation
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {K L : C} {K' L' : D} (u : K ≅ L) (u' : K' ≅ L')
    (r : F.obj L ⟶ L') (s : F.obj K ⟶ K')
    (hr : r = F.map u.inv ≫ s ≫ u'.hom) :
    F.map u.hom ≫ r = s ≫ u'.hom := by
  rw [hr, ← F.map_comp_assoc, u.hom_inv_id, F.map_id, Category.id_comp]

private theorem cancel_target_chain
    {C : Type*} [Category C] {W V Z Q R T : C}
    (e : W ≅ V) (c : V ≅ Z) (j : Z ≅ Q) (i : Q ≅ R)
    (a : V ⟶ T) (b : Z ⟶ T) (r : R ⟶ T)
    (hc : c.hom ≫ b = a)
    (h : e.hom ≫ a = (e ≪≫ c ≪≫ j ≪≫ i).hom ≫ r) :
    b = j.hom ≫ i.hom ≫ r := by
  simp only [Iso.trans_hom, Category.assoc] at h
  rw [← hc] at h
  exact (cancel_epi c.hom).mp ((cancel_epi e.hom).mp h)

private theorem paste_chain
    {C : Type*} [Category C] {W V Z Q R T : C}
    (e : W ≅ V) (c : V ≅ Z) (j : Z ≅ Q) (i : Q ≅ R)
    (b : W ⟶ T) (a : V ⟶ T) (a' : Z ⟶ T) (r : R ⟶ T)
    (hs : b = e.hom ≫ a) (hc : c.hom ≫ a' = a)
    (ht : a' = j.hom ≫ i.hom ≫ r) :
    b = (e ≪≫ c ≪≫ j ≪≫ i).hom ≫ r := by
  rw [hs, ← hc, ht]
  simp only [Iso.trans_hom, Category.assoc]

private theorem insert_unit
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {K L M : C} {Z : D} (q : Z ≅ F.obj L) (u : K ≅ L) (o : L ≅ M) :
    q ≪≫ F.mapIso o = (q ≪≫ F.mapIso u.symm) ≪≫ F.mapIso (u ≪≫ o) := by
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc,
    Iso.symm_self_id_assoc]

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

open AlgebraicGeometry.ProEtale.FiniteEtaleNormalization

attribute [local irreducible] Etale.upperStar Etale.lowerStar
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Etale.rightDerivedUpperShriek Etale.rightDerivedUpperShriekAdjunction

variable (P : PurityFiniteSetting.{u})
variable {X Y X' Y' : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [X'.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X' ↘ Spec (.of P.field.k))]
variable [Y'.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y' ↘ Spec (.of P.field.k))]

private theorem restriction_beta
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [Smooth f]
    (h : X' ⟶ Y') [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] [Smooth h]
    (e : X' ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v] [Etale v]
    (sq : IsPullback e h f v) :
    (ProEtale.DualizingLocality.restriction P f h e v sq.toCommSq).hom =
      beta P f h v e sq := by
  let := compactification P h
  let := compactification P v
  let := compactification P (h ≫ v)
  have hb := smooth_baseChange_law P v f h e sq
  obtain ⟨s, hs, hi, _⟩ := P.dualizingComposite_inverse h v (eta P v)
  have ht : targetUnit P.Coefficient h v (rho P v) =
      dualizingCompositeTrivialization P.Coefficient h v (eta P v) := rfl
  have hσ : sigma P.Coefficient h v (comp P h v) =
      dualizingCompositeSigma P.Coefficient h v := by
    simp only [sigma, dualizingCompositeSigma, dualizingCompositeConjugate,
      finiteExceptionalComposition, comp, Etale.dualizingComplexTensorMap, Iso.app_inv]
    rfl
  have hc := inverseNormalization
    (dualizingCompositeTrivialization P.Coefficient h v (eta P v)) s
    (dualizingCompositeConjugate P.Coefficient h v)
    ((ProEtale.FiniteEtaleNormalization.exceptional P h).mapIso (eta P v)) hi
  rw [hs, ← ht, ← hσ] at hc
  have hc' : (targetUnit P.Coefficient h v (rho P v)).inv ≫
      sigma P.Coefficient h v (comp P h v) =
        (ProEtale.FiniteEtaleNormalization.exceptional P h).map (eta P v).inv ≫
          (comp P h v).inv.app
            (ProEtale.FiniteEtaleNormalization.coefficientUnit
              (ModuleCat.{u + 1} P.Coefficient) Y) := hc
  rw [hc'] at hb
  exact recover_chain (sourceEtale P e f).symm
    ((ProEtale.FiniteEtaleNormalization.congr P (e ≫ f) (h ≫ v) sq.w).app
      (ProEtale.FiniteEtaleNormalization.coefficientUnit
        (ModuleCat.{u + 1} P.Coefficient) Y))
    ((comp P h v).app (ProEtale.FiniteEtaleNormalization.coefficientUnit
      (ModuleCat.{u + 1} P.Coefficient) Y))
    ((ProEtale.FiniteEtaleNormalization.exceptional P h).mapIso (eta P v))
    (beta P f h v e sq) hb

private theorem source_unit
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (e : X' ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    letI := compactification P f
    letI := compactification P (e ≫ f)
    letI := fieldSchemeNoetherian P X
    letI := fieldSchemeNoetherian P X'
    letI := fieldSchemeNoetherian P Y
    (pull P e).map (P.chartDualizingUnit f).hom ≫
        (P.diagonalEtaleLocality N e f).hom =
      (sourceEtale P e f).inv ≫ (P.chartDualizingUnit (e ≫ f)).hom := by
  let := compactification P f
  let := compactification P (e ≫ f)
  let := fieldSchemeNoetherian P X
  let := fieldSchemeNoetherian P X'
  let := fieldSchemeNoetherian P Y
  let H := Etale.rightDerivedUpperShriek P.Coefficient f
  let H' := Etale.rightDerivedUpperShriek P.Coefficient (e ≫ f)
  let I := Functor.isoWhiskerLeft H
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} P.Coefficient) e) ≪≫
      Etale.tensorMateEtalePrecompLocalityIso P.Coefficient N e f
  rw [SectionRestriction.sourceEtale_locality P e f,
    DiagonalEtaleComparison.locality_tensorMate P.Coefficient N e f]
  change (H ⋙ pull P e).map (smoothPurityUnitIso P.Coefficient Y).inv ≫
      I.hom.app (Etale.ordinaryFiniteUnit P.Coefficient Y) =
    I.hom.app (𝟙_ _) ≫ H'.map (smoothPurityUnitIso P.Coefficient Y).inv
  exact I.hom.naturality _

private theorem orientation_congr
    (d : ℕ) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f g : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g] (w : f = g) :
    letI := compactification P f
    letI := compactification P g
    (ProEtale.FiniteEtaleNormalization.congr P f g w).hom.app
        (ProEtale.FiniteEtaleNormalization.coefficientUnit
          (ModuleCat.{u + 1} P.Coefficient) Y) ≫
        (P.chartDualizingUnit g ≪≫ P.chartOrdinaryOrientation d g aY).hom =
      (P.chartDualizingUnit f ≪≫ P.chartOrdinaryOrientation d f aY).hom := by
  subst g
  simp only [ProEtale.FiniteEtaleNormalization.congr, Etale.unboundedEtaleLowerShriekCongr,
    conjugateIsoEquiv_apply_hom, Iso.refl_hom, conjugateEquiv_id,
    NatTrans.id_app]
  exact Category.id_comp _

private theorem source_orientation
    (d : ℕ) (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : X' ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e]
    [SmoothOfRelativeDimension d (e ≫ f)]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := compactification P f
    letI := compactification P (e ≫ f)
    (pull P e).map (P.chartDualizingUnit f ≪≫ P.chartOrdinaryOrientation d f aY).hom ≫
        (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t e (P.diagonalExponent_isUnit (f ≫ aY)) d).hom =
      (sourceEtale P e f).inv ≫
        (P.chartDualizingUnit (e ≫ f) ≪≫
          P.chartOrdinaryOrientation d (e ≫ f) aY).hom := by
  let := compactification P f
  let := compactification P (e ≫ f)
  let := fieldSchemeNoetherian P X
  let := fieldSchemeNoetherian P X'
  let := fieldSchemeNoetherian P Y
  exact lift_orientation (pull P e)
    (P.chartDualizingUnit f) (P.chartOrdinaryOrientation d f aY)
    (P.chartDualizingUnit (e ≫ f)) (P.chartOrdinaryOrientation d (e ≫ f) aY)
    (P.diagonalEtaleLocality N e f).hom (sourceEtale P e f).inv
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t e (P.diagonalExponent_isUnit (f ≫ aY)) d).hom
    (source_unit P f e N) (P.chartOrientation_etale_restriction d f aY e N t)

private theorem base_orientation
    (d : ℕ) (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (h : X' ⟶ Y') [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (e : X' ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsOpenImmersion v] [QuasiCompact v] (sq : IsPullback e h f v)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := compactification P f
    letI := compactification P h
    (pull P e).map (P.chartDualizingUnit f ≪≫ P.chartOrdinaryOrientation d f aY).hom ≫
        (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t e (P.diagonalExponent_isUnit (f ≫ aY)) d).hom =
      beta P f h v e sq ≫
        (P.chartDualizingUnit h ≪≫ P.chartOrdinaryOrientation d h (v ≫ aY)).hom := by
  let := compactification P f
  let := compactification P h
  have hu : (pull P e).map (P.chartDualizingUnit f).hom ≫
      (P.chartOrdinaryBaseChange d f aY v h e sq).hom =
        beta P f h v e sq ≫ (P.chartDualizingUnit h).hom := by
    exact unit_conjugation (pull P e) (P.chartDualizingUnit f) (P.chartDualizingUnit h)
      (P.chartOrdinaryBaseChange d f aY v h e sq).hom (beta P f h v e sq) rfl
  exact lift_orientation (pull P e)
    (P.chartDualizingUnit f) (P.chartOrdinaryOrientation d f aY)
    (P.chartDualizingUnit h) (P.chartOrdinaryOrientation d h (v ≫ aY))
    (P.chartOrdinaryBaseChange d f aY v h e sq).hom (beta P f h v e sq)
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t e (P.diagonalExponent_isUnit (f ≫ aY)) d).hom
    hu (P.chartOrientation_open_baseChange d f aY v h e sq t)

private theorem target_orientation
    (d : ℕ) (h : X ⟶ Y') [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsOpenImmersion v] [QuasiCompact v]
    [SmoothOfRelativeDimension d (h ≫ v)]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := compactification P h
    letI := compactification P (h ≫ v)
    (P.chartDualizingUnit (h ≫ v) ≪≫ P.chartOrdinaryOrientation d (h ≫ v) aY).hom =
      (comp P h v).hom.app
          (ProEtale.FiniteEtaleNormalization.coefficientUnit
            (ModuleCat.{u + 1} P.Coefficient) Y) ≫
        (ProEtale.FiniteEtaleNormalization.exceptional P h).map (eta P v).hom ≫
        (P.chartDualizingUnit h ≪≫ P.chartOrdinaryOrientation d h (v ≫ aY)).hom := by
  let := compactification P h
  let := compactification P (h ≫ v)
  let := SmoothOfRelativeDimension.smooth d h
  let := SmoothOfRelativeDimension.smooth d (h ≫ v)
  let : SmoothOfRelativeDimension d (𝟙 X ≫ (h ≫ v)) := by
    simpa only [Category.id_comp] using
      (inferInstance : SmoothOfRelativeDimension d (h ≫ v))
  let sq : IsPullback (𝟙 X) h (h ≫ v) v :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  have hs := source_orientation P d (h ≫ v) aY (𝟙 X) N t
  have hb := base_orientation P d (h ≫ v) aY h (𝟙 X) v sq t
  rw [← restriction_beta P (h ≫ v) h (𝟙 X) v sq] at hb
  have hc := orientation_congr P d aY (𝟙 X ≫ (h ≫ v)) (h ≫ v)
    (Category.id_comp (h ≫ v))
  exact cancel_target_chain (sourceEtale P (𝟙 X) (h ≫ v)).symm
    ((ProEtale.FiniteEtaleNormalization.congr P (𝟙 X ≫ (h ≫ v)) (h ≫ v)
      (Category.id_comp (h ≫ v))).app
        (ProEtale.FiniteEtaleNormalization.coefficientUnit
          (ModuleCat.{u + 1} P.Coefficient) Y))
    ((comp P h v).app (ProEtale.FiniteEtaleNormalization.coefficientUnit
      (ModuleCat.{u + 1} P.Coefficient) Y))
    ((ProEtale.FiniteEtaleNormalization.exceptional P h).mapIso (eta P v))
    _ _ _ hc (hs.symm.trans hb)

end RestrictionProof

variable (P : PurityFiniteSetting.{u})
variable {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

-- Retain the original separatedness binder, unused by this comparison argument.
set_option linter.unusedSectionVars false in
/-- The chosen orientation commutes with source and target open restriction.
This does not compare it to a three-factor composite.
Source: latest diagonal-dualizing-object proof, final canonicity/base-change
paragraph, and orientation-chart proof Steps 3--4. Proof: use the ordinary chosen
orientation's source-etale and open-base-change equations. Convert their coefficient
objects to the monoidal
unit, using naturality of the structural-locality tensor mate. Finite-etale
normalization identifies the smooth base-change map with the actual exceptional
restriction composite. Its square with identity source gives target-open
composition compatibility. Combine source restriction, morphism congruence and
target-open composition to obtain the ordinary restriction square. Apply the
site comparison and its pullback naturality, then cancel the coefficient-unit
comparisons. The resulting maps are exactly affineDualizingRestriction and
affineTateRestriction. All these identities also apply to empty opens and d=0.
(blueprint: lem-pur-finite-diagonal-chosen-restriction). -/
theorem diagonalChosenRestriction
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    [SmoothOfRelativeDimension d (f.resLE V.1 U.1 hUV)] :
    letI : IsAffine U.1.toScheme := U.2
    letI : IsAffine V.1.toScheme := V.2
    let h := f.resLE V.1 U.1 hUV
    let R := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      U.1.ι).leftDerivedFunctor
    R.map (P.diagonalDualizingObject d f aY).hom ≫
        (affineTateRestriction P f aY d U).hom =
      (affineDualizingRestriction P f aY U V hUV).hom ≫
        (P.diagonalDualizingObject d h (V.1.ι ≫ aY)).hom := by
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine V.1.toScheme := V.2
  let h := f.resLE V.1 U.1 hUV
  let := P.noetherian aY
  let := P.noetherian (f ≫ aY)
  let := Dnc.compactifiable P f aY
  let : X.Over (Spec (.of P.field.k)) := ⟨f ≫ aY⟩
  let : Y.Over (Spec (.of P.field.k)) := ⟨aY⟩
  let : U.1.toScheme.Over (Spec (.of P.field.k)) := ⟨U.1.ι ≫ f ≫ aY⟩
  let : V.1.toScheme.Over (Spec (.of P.field.k)) := ⟨V.1.ι ≫ aY⟩
  let : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (f ≫ aY))
  let : QuasiCompact (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (f ≫ aY))
  let : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (aY))
  let : QuasiCompact (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (aY))
  let : LocallyOfFiniteType (U.1.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (U.1.ι ≫ f ≫ aY))
  let : QuasiCompact (U.1.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (U.1.ι ≫ f ≫ aY))
  let : LocallyOfFiniteType (V.1.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (V.1.ι ≫ aY))
  let : QuasiCompact (V.1.toScheme ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (V.1.ι ≫ aY))
  let : f.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : U.1.ι.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : V.1.ι.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : h.IsOver (Spec (.of P.field.k)) := ⟨by
    change h ≫ V.1.ι ≫ aY = U.1.ι ≫ f ≫ aY
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]⟩
  let := Dnc.compactifiable P h (V.1.ι ≫ aY)
  let : SmoothOfRelativeDimension d (U.1.ι ≫ f) := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + d) (U.1.ι ≫ f))
  let : SmoothOfRelativeDimension d (h ≫ V.1.ι) := by
    simpa only [Nat.add_zero] using
      (inferInstance : SmoothOfRelativeDimension (d + 0) (h ≫ V.1.ι))
  let N := Etale.canonicalEtaleCompactSupportNormalization P.Coefficient
  let t := Etale.projectiveLineTraceTransport P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level)
    P.Coefficient P.diagonalExponent_annihilates
  let o := P.chartDualizingUnit f ≪≫ P.chartOrdinaryOrientation d f aY
  let o' := P.chartDualizingUnit h ≪≫
    P.chartOrdinaryOrientation d h (V.1.ι ≫ aY)
  have hs := RestrictionProof.source_orientation P d f aY U.1.ι N t
  have hc := RestrictionProof.orientation_congr P d aY
    (U.1.ι ≫ f) (h ≫ V.1.ι) (Scheme.Hom.resLE_comp_ι f hUV).symm
  have ht := RestrictionProof.target_orientation P d h aY V.1.ι N t
  have ho :
      (Etale.ordinaryFinitePullback P.Coefficient U.1.ι).map o.hom ≫
          (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates t U.1.ι
              (P.diagonalExponent_isUnit (f ≫ aY)) d).hom =
        (ProEtale.DualizingLocality.restriction P f h U.1.ι V.1.ι
          ⟨(Scheme.Hom.resLE_comp_ι f hUV).symm⟩).hom ≫ o'.hom := by
    exact RestrictionProof.paste_chain
      (ProEtale.FiniteEtaleNormalization.sourceEtale P U.1.ι f).symm
      ((ProEtale.FiniteEtaleNormalization.congr P (U.1.ι ≫ f) (h ≫ V.1.ι)
        (Scheme.Hom.resLE_comp_ι f hUV).symm).app
          (ProEtale.FiniteEtaleNormalization.coefficientUnit
            (ModuleCat.{u + 1} P.Coefficient) Y))
      ((ProEtale.FiniteEtaleNormalization.comp P h V.1.ι).app
        (ProEtale.FiniteEtaleNormalization.coefficientUnit
          (ModuleCat.{u + 1} P.Coefficient) Y))
      ((ProEtale.FiniteEtaleNormalization.exceptional P h).mapIso
        (ProEtale.FiniteEtaleNormalization.eta P V.1.ι)) _ _ _ _ hs hc ht
  let J := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) U.1.toScheme).mapDerivedCategory
  let R := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
    U.1.ι).leftDerivedFunctor
  let q := P.diagonalDualizingComparison f ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
        (P.chartDualizingUnit f).symm
  let q' := P.diagonalDualizingComparison h ≪≫ J.mapIso (P.chartDualizingUnit h).symm
  let A := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  have hf : P.diagonalDualizingObject d f aY = q ≪≫ A.mapIso o :=
    (P.chartOrdinaryOrientation_spec d f aY).2.trans
      (RestrictionProof.insert_unit A (P.diagonalDualizingComparison f)
        (P.chartDualizingUnit f) (P.chartOrdinaryOrientation d f aY))
  have hh : P.diagonalDualizingObject d h (V.1.ι ≫ aY) = q' ≪≫ J.mapIso o' :=
    (P.chartOrdinaryOrientation_spec d h (V.1.ι ≫ aY)).2.trans
      (RestrictionProof.insert_unit J (P.diagonalDualizingComparison h)
        (P.chartDualizingUnit h) (P.chartOrdinaryOrientation d h (V.1.ι ≫ aY)))
  have hn := congrArg Iso.hom (Dnc.pullComparison_naturality P U.1.ι o)
  change R.map (P.diagonalDualizingObject d f aY).hom ≫
      (affineTateRestriction P f aY d U).hom =
    (affineDualizingRestriction P f aY U V hUV).hom ≫
      (P.diagonalDualizingObject d h (V.1.ι ≫ aY)).hom
  erw [hf, hh]
  exact RestrictionProof.transport_restriction A J R
    (Etale.ordinaryFinitePullback P.Coefficient U.1.ι) q q' o o'
    (ProEtale.DualizingLocality.restriction P f h U.1.ι V.1.ι
      ⟨(Scheme.Hom.resLE_comp_ι f hUV).symm⟩)
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t U.1.ι (P.diagonalExponent_isUnit (f ≫ aY)) d)
    (Dnc.pullComparison P U.1.ι (Etale.dualizingComplex P.Coefficient f))
    (Dnc.pullComparison P U.1.ι (P.diagonalTwistEtale X d)) hn ho

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
