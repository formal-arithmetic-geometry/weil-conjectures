/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.Current.IntegralCurrentPullbackNormalizations
import WeilConjectures.SixFunctors.SequenceComparisonConstruction.NormalizedDerivedComparisonDescent
import WeilConjectures.CategoryTheory.Derived.DerivedResolvingPairRestriction
import WeilConjectures.CategoryTheory.SixFunctors.UnaryWhiskeringOfProduct
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # Normalized IntegralTowerDerivedPullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
private theorem internal_resolving_ext {T : Scheme.{u}}
    {D : Type*} [Category D] (F G : Integral l E T ⥤ D) (a b : F ⟶ G)
    (h : ∀ (P : CochainComplex (Modules l E T) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T)
        (((spIntegralModuleEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj P) →
      (∀ i : ℤ, IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := spIntegralSectionRing l E T)
        ((spIntegralModuleEquivalence l E T).functor.obj (P.X i))) →
      a.app (DerivedCategory.Q.obj P) = b.app (DerivedCategory.Q.obj P)) : a = b := by
  let eqv := spIntegralModuleEquivalence l E T
  let : eqv.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : eqv.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let ec := eqv.mapHomologicalComplex (.up ℤ)
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules l E T) (.up ℤ))
  intro K
  obtain ⟨P, p, hP, hf, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := spIntegralSectionRing l E T) (ec.functor.obj K)
  let L := ec.inverse.obj P
  let q : L ⟶ K := ec.inverse.map p ≫ ec.unitIso.inv.app K
  have hp' : QuasiIso (ec.inverse.map p) := by
    have := hp
    change QuasiIso ((eqv.inverse.mapHomologicalComplex (.up ℤ)).map p)
    infer_instance
  have : QuasiIso q := by
    dsimp only [q]
    infer_instance
  have hL : CochainComplex.IsKFlatIndependentCoefficients
      (R := spIntegralSectionRing l E T) (ec.functor.obj L) :=
    kflat_iso l E (ec.counitIso.symm.app P) hP
  have hLf (i : ℤ) : IsFlatOnSite (J := Scheme.ProEt.topology T)
      (R := spIntegralSectionRing l E T) (eqv.functor.obj (L.X i)) := by
    apply flat_iso l E ((HomologicalComplex.eval _ _ i).mapIso
      (ec.counitIso.symm.app P))
    exact (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso (spIntegralSectionRing l E T) (P.X i)).symm (hf i)
  apply (cancel_epi (F.map (DerivedCategory.Q.map q))).1
  rw [a.naturality, b.naturality]
  rw [h L hL hLf]


-- The universal counit is composed as a natural transformation before taking components.
set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
private def reductionCounit (s : Coefficients l E) (T : Scheme.{u}) :
    DerivedCategory.Q ⋙ derivedReduction l E s T ⟶
      (ordinaryReduction l E s T).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := by
  let := (s.towers T).hasDerived
  let E₀ := (spIntegralModuleEquivalence l E T).functor
  let V := (s.base.realization T).functor
  let R := (s.reduction T).red
  let a := Functor.whiskerRight
    (Functor.whiskerRight E₀.mapDerivedCategoryFactors.hom R) (realization l E s T).functor
  let b := Functor.whiskerRight
    (Functor.whiskerLeft (E₀.mapHomologicalComplex (.up ℤ)) (s.reduction T).counit)
    (realization l E s T).functor
  let c := Functor.whiskerLeft
    ((E₀ ⋙ (s.reduction T).ordinary).mapHomologicalComplex (.up ℤ))
    V.mapDerivedCategoryFactors.hom
  exact a ≫ b ≫ c

set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
private theorem reductionCounit_app (s : Coefficients l E) (T : Scheme.{u})
    (P : CochainComplex (Modules l E T) ℤ) :
    (reductionCounit l E s T).app P = reductionComplexComparison l E s T P := by
  simp only [reductionCounit, reductionComplexComparison, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]

set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
private theorem reduction_comparison_isIso (s : Coefficients l E) (T : Scheme.{u})
    (P : CochainComplex (Modules l E T) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T)
      (((spIntegralModuleEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj P)) :
    IsIso (reductionComplexComparison l E s T P) := by
  let := (s.towers T).hasDerived
  let := s.base.realizationAdditive T
  have := (s.reduction T).computes _ hP
  unfold reductionComplexComparison
  infer_instance

set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
-- Elaborating the fixed section equivalence and its tensor structures needs this budget.
set_option synthInstance.maxHeartbeats 200000 in
private theorem good_resolution (T : Scheme.{u}) (K : CochainComplex (Modules l E T) ℤ) :
    ∃ (L : CochainComplex (Modules l E T) ℤ) (a : L ⟶ K), good l E T L ∧ QuasiIso a := by
  let eqv := spIntegralModuleEquivalence l E T
  let : eqv.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : eqv.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let ec := eqv.mapHomologicalComplex (.up ℤ)
  obtain ⟨P, p, hP, hf, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := spIntegralSectionRing l E T) (ec.functor.obj K)
  let L := ec.inverse.obj P
  let q : L ⟶ K := ec.inverse.map p ≫ ec.unitIso.inv.app K
  have hp' : QuasiIso (ec.inverse.map p) := by
    have := hp
    change QuasiIso ((eqv.inverse.mapHomologicalComplex (.up ℤ)).map p)
    infer_instance
  have hq : QuasiIso q := by
    dsimp only [q]
    infer_instance
  refine ⟨L, q, ⟨kflat_iso l E (ec.counitIso.symm.app P) hP, ?_⟩, hq⟩
  intro i
  apply flat_iso l E ((HomologicalComplex.eval _ _ i).mapIso (ec.counitIso.symm.app P))
  exact (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso (spIntegralSectionRing l E T) (P.X i)).symm (hf i)

set_option maxHeartbeats 1600000 in
-- The descent comparison elaborates the internal and section presentations together.
set_option synthInstance.maxHeartbeats 200000 in
/-- An ordinary scalar/pullback comparison extends uniquely with the fixed counits.
Source: blueprint direct-image proof paragraph (3), K-flat descent step.
Proof: let R be the class of internal complexes whose section complexes are K-flat
with flat terms. Transport flat-term K-flat resolutions through the exact section
module equivalence. Restriction from the derived category to R is fully faithful:
apply the resolving-pair restriction theorem to bifunctors constant in the second
variable and restrict their lifts to the diagonal. Integral inverse image is exact,
since abelian inverse image is exact and its scalar change is along a ring
isomorphism. The ordinary system inverse image is exact by its supplied operations.
The fixed reduction counits compute on K-flat section complexes. Module inverse
image preserves K-flatness, and scalar change along the coefficient isomorphism
and the section equivalence preserve it, so the X counit also computes after
pullback. Apply normalized derived comparison descent with good=R; its replacement
condition is the identity map. The two supplied natural transformations are the
fixed reductionComplexComparison counits. Its conclusion has D(p) on the left;
transport through the canonical Lf* to D(p) comparison. The prescribed exact-functor
factorizations then give precisely pullComplexComparison and the displayed
representative equation. The descent theorem's uniqueness transports through the
same isomorphism. This argument permits any ordinary q and uses neither its
generator equation nor the evaluation e. Zero complexes and the empty scheme
are included.
(blueprint: lem-sp-current-derived-pullback). -/
theorem derived_reduction_pullback_existsUnique (s : Coefficients l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (q : OrdinaryPullComparison l E s f) :
    ∃! d : DerivedPullComparison l E s f, DerivedPullNormalized l E s f q d := by
  let p := CondensedRing.upperStar (spIntegralCondensed l E) f
  let r := (s.operations.geometry f).pull
  let R := good l E Y
  obtain ⟨ff₂⟩ := derivedResolvingPairRestriction (SpTowerShriek.D l E X) R
    (good_resolution l E Y)
  let ff := Functor.unaryWhiskeringOfProduct (SpTowerShriek.D l E X)
    (R.ι ⋙ DerivedCategory.Q) ff₂
  obtain ⟨a, ha, hu⟩ := SequenceComparisonConstruction.derivedComparison p r
    (ordinaryReduction l E s Y) (ordinaryReduction l E s X)
    (derivedReduction l E s Y) (derivedReduction l E s X)
    (reductionCounit l E s Y) (reductionCounit l E s X) q R R ff
    (fun _ h ↦ h) (fun P hP ↦ ⟨P, 𝟙 P, hP, inferInstance⟩)
    (fun P hP ↦ by
      rw [reductionCounit_app]
      exact reduction_comparison_isIso l E s Y P hP.1)
    (fun P hP ↦ by
      rw [reductionCounit_app]
      exact reduction_comparison_isIso l E s X _ (pullback_kflat l E f P hP.1))
  let e := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
    (spIntegralCondensed l E) f
  let d : DerivedPullComparison l E s f :=
    Functor.isoWhiskerRight e (derivedReduction l E s X) ≪≫ a
  have hd : DerivedPullNormalized l E s f q d := by
    intro P hP hf
    have h := ha P ⟨hP, hf⟩
    simp only [reductionCounit_app] at h
    dsimp only [d, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      NatTrans.comp_app, Functor.whiskerRight_app]
    rw [Category.assoc, ← h]
    simp only [pullComplexComparison, Iso.trans_hom, Iso.app_hom, Functor.map_comp,
      Category.assoc]
    rfl
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply Iso.ext
  apply internal_resolving_ext l E _ _
  intro P hP hf
  have := reduction_comparison_isIso l E s Y P hP
  apply (cancel_mono
    ((SpTowerShriek.pull l E s.base (s.operations.geometry f)).map
        (reductionComplexComparison l E s Y P) ≫
      (s.operations.geometry f).pull.mapDerivedCategoryFactors.hom.app
        (((ordinaryReduction l E s Y).mapHomologicalComplex (.up ℤ)).obj P))).1
  exact (hd' P hP hf).trans (hd P hP hf).symm

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
