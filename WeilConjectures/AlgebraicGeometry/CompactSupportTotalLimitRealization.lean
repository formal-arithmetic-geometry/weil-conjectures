/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.CompactSupportReductionTower
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructibleTriangulated
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Linear
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import all WeilConjectures.AlgebraicGeometry.CoefficientConstantTowerRoos
import all WeilConjectures.AlgebraicGeometry.CompactSupportRepresentativeIndependence

/-! # Integral compact support through the total limit of its strict tower

Source: current Weil blueprint, `prop-functor-package.proof.md`, clause (3);
Stacks Tags 0940, 0941 and 08TC
(blueprint: lem-sf-compact-support-total-limit-realization).

The supplied tower is constrained to the recorded choice, before finite evaluation.
The total limit is the K-injective right-derived inverse-limit construction, with
its resolution-normalized projections. Natural index n means positive exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u a b d r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted sfIntegralConstructible

/-- Restrict the specified strict tower and then apply total derived inverse limit.
This is a literal composite, so it specifies the action on every derived morphism.
Source: blueprint `prop-functor-package.proof.md`, clause (3), realization steps 2--3
(blueprint: lem-sf-compact-support-total-limit-realization). -/
def sfCompactSupportTotalLimitFunctor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X Y : Scheme.{u})
    (T : DerivedCategory (scalarReductionSource l E X) ⥤
      coefficientSequenceRestrictedDerived l E Y) :
    sfIntegralConstructibleCategory l E X ⥤ DerivedCategory (scalarReductionSource l E Y) :=
  (sfIntegralConstructible l E X).ι ⋙ T ⋙ coefficientConstantTowerLimit l E Y

end WeilConjectures

namespace CategoryTheory
@[no_expose] private def totalRoosP
    {A : Type a} [Category.{b} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasDerivedCategory.{d} A] [HasCountableProducts (DerivedCategory.{d} A)]
    [IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ A)]
    (RF : DerivedCategory.{d} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{d} A)
    (η : CoreWork.L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{d} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{d} A))
    (ε : DerivedCategory.Q ⋙ E ≅ CoreWork.evQ) : RF ⟶ E ⋙ CoreWork.DP :=
  CoreWork.pNat RF η hI E ε

@[no_expose] private def totalRoosDelta
    {A : Type a} [Category.{b} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasDerivedCategory.{d} A] [HasCountableProducts (DerivedCategory.{d} A)]
    [IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ A)]
    (RF : DerivedCategory.{d} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{d} A)
    (η : CoreWork.L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{d} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{d} A))
    (ε : DerivedCategory.Q ⋙ E ≅ CoreWork.evQ) : E ⋙ CoreWork.DP ⟶ RF ⋙ shiftFunctor _ (1 : ℤ) :=
  CoreWork.deltaNat RF η hI E ε

private theorem totalRoos_triangle
    {A : Type a} [Category.{b} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasDerivedCategory.{d} A] [HasCountableProducts (DerivedCategory.{d} A)]
    [IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ A)]
    (RF : DerivedCategory.{d} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{d} A)
    (η : CoreWork.L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{d} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{d} A))
    (ε : DerivedCategory.Q ⋙ E ≅ CoreWork.evQ) :
    ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      IsDerivedLimitTriangle
        (fun n ↦ (E.obj (DerivedCategory.Q.obj X)).map (homOfLE n.le_succ).op)
        (RF.obj (DerivedCategory.Q.obj X))
        ((totalRoosP RF η hI E ε).app (DerivedCategory.Q.obj X))
        ((totalRoosDelta RF η hI E ε).app (DerivedCategory.Q.obj X)) := by
  intro X
  exact CoreWork.roos_Q RF η hI E ε X

private theorem totalRoos_first
    {A : Type a} [Category.{b} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasDerivedCategory.{d} A] [HasCountableProducts (DerivedCategory.{d} A)]
    [IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ A)]
    (RF : DerivedCategory.{d} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{d} A)
    (η : CoreWork.L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{d} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{d} A))
    (ε : DerivedCategory.Q ⋙ E ≅ CoreWork.evQ) :
    ∀ X, η.app X ≫ (totalRoosP RF η hI E ε).app (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map (CoreWork.inc.app X) ≫ CoreWork.pc.app X ≫
        CoreWork.DP.map (ε.inv.app X) := by
  have ha (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      DerivedCategory.Q.map (CoreWork.L.map (CoreWork.q.app X)) ≫
          (CoreWork.aIso RF η hI).hom.app X = η.app X := by
    have : QuasiIso (CoreWork.q.app X) := CoreWork.q_quasiIso X
    have : IsIso (η.app (CoreWork.F.obj X)) := hI _ inferInstance
    dsimp only [CoreWork.aIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, asIso_hom, asIso_inv,
      Functor.comp_obj, Category.id_comp, Category.comp_id]
    simp only [Category.id_comp, NatIso.isIso_inv_app, Functor.whiskerRight_app]
    change DerivedCategory.Q.map (CoreWork.L.map (CoreWork.q.app X)) ≫
      η.app (CoreWork.F.obj X) ≫ RF.map (inv (DerivedCategory.Q.map
        (CoreWork.q.app X))) = _
    erw [η.naturality_assoc]
    simp
  have hb (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      DerivedCategory.Q.map (CoreWork.P.map (CoreWork.q.app X)) ≫
          (CoreWork.bIso E ε).hom.app X = (CoreWork.pc.app X ≫ CoreWork.DP.map (ε.inv.app X)) := by
    have : QuasiIso (CoreWork.q.app X) := CoreWork.q_quasiIso X
    have : ∀ n : ℕᵒᵖ,
        IsIso ((CoreWork.evQ.map (CoreWork.q.app X)).app n) := by
      intro n
      change IsIso (DerivedCategory.Q.map
        ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).map
          (CoreWork.q.app X)))
      infer_instance
    have : IsIso (CoreWork.evQ.map (CoreWork.q.app X)) := NatIso.isIso_of_isIso_app _
    have hqapp (Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
        IsIso ((Functor.whiskerRight (CoreWork.q (A := A)) CoreWork.evQ).app Y) := by
      have : QuasiIso (CoreWork.q.app Y) := CoreWork.q_quasiIso Y
      change IsIso (CoreWork.evQ.map (CoreWork.q.app Y))
      have (n : ℕᵒᵖ) : IsIso ((CoreWork.evQ.map (CoreWork.q.app Y)).app n) := by
        change IsIso (DerivedCategory.Q.map
          ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).map
            (CoreWork.q.app Y)))
        infer_instance
      exact NatIso.isIso_of_isIso_app _
    have hq : IsIso (Functor.whiskerRight (CoreWork.q (A := A)) CoreWork.evQ) :=
      NatIso.isIso_of_isIso_app _
    let c := (asIso (Functor.whiskerRight (CoreWork.q (A := A)) CoreWork.evQ)).symm ≪≫
      ε.symm
    have hc : (CoreWork.bIso E ε).hom.app X =
        CoreWork.pc.app (CoreWork.F.obj X) ≫ CoreWork.DP.map (c.hom.app X) := by
      simp only [CoreWork.bIso, Iso.trans_hom, Iso.symm_hom,
        Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, asIso_hom, Functor.associator,
        Category.id_comp, Category.comp_id, c]
    rw [hc, ← Category.assoc]
    have hn := (CoreWork.pc (A := A)).naturality (CoreWork.q.app X)
    change DerivedCategory.Q.map (CoreWork.P.map (CoreWork.q.app X)) ≫
      CoreWork.pc.app (CoreWork.F.obj X) =
      CoreWork.pc.app X ≫ CoreWork.DP.map (CoreWork.evQ.map (CoreWork.q.app X)) at hn
    rw [hn, Category.assoc, ← Functor.map_comp]
    have hh : CoreWork.evQ.map (CoreWork.q.app X) ≫ c.hom.app X = ε.inv.app X := by
      simp [c, NatIso.isIso_inv_app]
    rw [hh]
  intro X
  change η.app X ≫ (CoreWork.pNat RF η hI E ε).app _ = _
  rw [CoreWork.pNat_app]
  change η.app X ≫ (CoreWork.aIso RF η hI).inv.app X ≫
    DerivedCategory.Q.map (CoreWork.inc.app (CoreWork.F.obj X)) ≫
    (CoreWork.bIso E ε).hom.app X = _
  rw [← ha X]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← DerivedCategory.Q.map_comp_assoc]
  erw [CoreWork.inc.naturality]
  rw [DerivedCategory.Q.map_comp, Category.assoc, hb X]
  all_goals rfl
private theorem totalRoos_first_projection
    {A : Type a} [Category.{b} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasDerivedCategory.{d} A] [HasCountableProducts (DerivedCategory.{d} A)]
    [IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ A)]
    (RF : DerivedCategory.{d} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{d} A)
    (η : CoreWork.L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{d} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{d} A))
    (ε : DerivedCategory.Q ⋙ E ≅ CoreWork.evQ) :
    ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ),
      η.app X ≫ (totalRoosP RF η hI E ε).app (DerivedCategory.Q.obj X) ≫
        Pi.π (fun k : ℕ ↦ (E.obj (DerivedCategory.Q.obj X)).obj (op k)) n ≫
          (ε.hom.app X).app (op n) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X) := by
  intro X n
  rw [← Category.assoc, totalRoos_first]
  dsimp only [CoreWork.DP, CoreWork.evQ]
  simp only [Category.assoc]
  erw [Category.assoc]
  change DerivedCategory.Q.map (CoreWork.inc.app X) ≫ CoreWork.pc.app X ≫
    Limits.Pi.map (fun k ↦ (ε.inv.app X).app (op k)) ≫ Pi.π _ n ≫
      (ε.hom.app X).app (op n) = _
  rw [Limits.Pi.map_π_assoc]
  have he : (ε.inv.app X).app (op n) ≫ (ε.hom.app X).app (op n) = 𝟙 _ := by
    simpa only [NatTrans.comp_app, NatTrans.id_app] using
      congrArg (fun z ↦ z.app (op n)) (ε.inv_hom_id_app X)
  rw [he, Category.comp_id]
  change DerivedCategory.Q.map (CoreWork.inc.app X) ≫
    piComparison DerivedCategory.Q (fun k : ℕ ↦ X.asFunctor.obj (op k)) ≫
      Pi.π _ n = _
  rw [piComparison_comp_π, ← DerivedCategory.Q.map_comp]
  congr 1
  exact Pi.lift_π _ n

private theorem totalProductIsoInvNatural
    {D : Type a} [Category.{b} D] {A : Type d} [Category.{r} A]
    [HasCountableProducts A] (P Q : ℕ → D ⥤ A) (e : ∀ n, P n ≅ Q n)
    {K M : D} (v : K ⟶ M) :
    Limits.Pi.map (fun n ↦ (Q n).map v) ≫
        (Limits.Pi.mapIso (fun n ↦ (e n).app M)).inv =
      (Limits.Pi.mapIso (fun n ↦ (e n).app K)).inv ≫
        Limits.Pi.map (fun n ↦ (P n).map v) := by
  apply Pi.hom_ext
  intro n
  simpa only [Iso.app_inv, Category.assoc, Limits.Pi.mapIso_inv_π,
    Limits.Pi.mapIso_inv_π_assoc, Limits.Pi.map_π, Limits.Pi.map_π_assoc] using
      congrArg (fun z ↦ Pi.π (fun k ↦ (Q k).obj K) n ≫ z)
        ((e n).inv.naturality v)

private theorem totalProductProjectionNatural
    {D : Type a} [Category.{b} D] {A : Type d} [Category.{r} A]
    [HasCountableProducts A] (L : D ⥤ A) (P Q : ℕ → D ⥤ A)
    (π : ∀ n, L ⟶ P n) (e : ∀ n, P n ≅ Q n)
    {K M : D} (v : K ⟶ M) :
    L.map v ≫ (Pi.lift (fun n ↦ (π n).app M) ≫
        (Limits.Pi.mapIso (fun n ↦ (e n).app M)).hom) =
      (Pi.lift (fun n ↦ (π n).app K) ≫
        (Limits.Pi.mapIso (fun n ↦ (e n).app K)).hom) ≫
          Limits.Pi.map (fun n ↦ (Q n).map v) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, Limits.Pi.mapIso_hom_π,
    Limits.Pi.map_π, Limits.Pi.mapIso_hom_π_assoc, Pi.lift_π_assoc]
  rw [← Category.assoc, (π n).naturality, Category.assoc]
  exact congrArg (fun z ↦ (π n).app K ≫ z) ((e n).hom.naturality v)

private theorem totalProductDeltaNatural
    {D : Type a} [Category.{b} D] {A : Type d} [Category.{r} A]
    [HasCountableProducts A] [HasShift A ℤ]
    (L : D ⥤ A) (P Q : ℕ → D ⥤ A) (e : ∀ n, P n ≅ Q n)
    (δ : ∀ K, (∏ᶜ fun n ↦ (P n).obj K) ⟶ (L.obj K)⟦(1 : ℤ)⟧)
    (hδ : ∀ {K M} (v : K ⟶ M),
      Limits.Pi.map (fun n ↦ (P n).map v) ≫ δ M = δ K ≫ (L.map v)⟦(1 : ℤ)⟧')
    {K M : D} (v : K ⟶ M) :
    Limits.Pi.map (fun n ↦ (Q n).map v) ≫
        ((Limits.Pi.mapIso (fun n ↦ (e n).app M)).inv ≫ δ M) =
      ((Limits.Pi.mapIso (fun n ↦ (e n).app K)).inv ≫ δ K) ≫
        (L.map v)⟦(1 : ℤ)⟧' := by
  rw [← Category.assoc, totalProductIsoInvNatural, Category.assoc, hδ,
    Category.assoc]

private theorem totalCompositeShift
    {A : Type a} [Category.{b} A] {B : Type d} [Category.{r} B]
    {C : Type a} [Category.{b} C] {D : Type d} [Category.{r} D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (I : A ⥤ B) (T : B ⥤ C) (L : C ⥤ D)
    [I.CommShift ℤ] [T.CommShift ℤ] [L.CommShift ℤ] (K : A) :
    ((I ⋙ T ⋙ L).commShiftIso (1 : ℤ)).hom.app K =
      L.map (T.map ((I.commShiftIso (1 : ℤ)).hom.app K) ≫
        (T.commShiftIso (1 : ℤ)).hom.app (I.obj K)) ≫
          (L.commShiftIso (1 : ℤ)).hom.app (T.obj (I.obj K)) := by
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
    Functor.comp_map, Functor.map_comp, Category.assoc]

private theorem totalCompositeTriangle
    {A : Type a} [Category.{b} A] {B : Type d} [Category.{r} B]
    {C : Type a} [Category.{b} C] {D : Type d} [Category.{r} D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    [HasZeroObject A] [HasZeroObject B] [HasZeroObject C] [HasZeroObject D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor A n).Additive]
    [∀ n : ℤ, (shiftFunctor B n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated A] [Pretriangulated B] [Pretriangulated C] [Pretriangulated D]
    (I : A ⥤ B) (T : B ⥤ C) (L : C ⥤ D)
    [I.CommShift ℤ] [T.CommShift ℤ] [L.CommShift ℤ]
    [I.IsTriangulated] [T.IsTriangulated] [L.IsTriangulated]
    (S : Triangle A) (hS : S ∈ distTriang A) :
    Triangle.mk ((I ⋙ T ⋙ L).map S.mor₁) ((I ⋙ T ⋙ L).map S.mor₂)
      ((I ⋙ T ⋙ L).map S.mor₃ ≫
        L.map (T.map ((I.commShiftIso (1 : ℤ)).hom.app S.obj₁) ≫
          (T.commShiftIso (1 : ℤ)).hom.app (I.obj S.obj₁)) ≫
            (L.commShiftIso (1 : ℤ)).hom.app (T.obj (I.obj S.obj₁))) ∈
      distTriang D := by
  simpa only [Functor.mapTriangle_obj, Functor.commShiftIso_comp_hom_app,
    Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc] using
      (I ⋙ T ⋙ L).map_distinguished S hS

end CategoryTheory

namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted sfIntegralConstructible

@[no_expose] private def totalEvaluationIso
    (A : Type a) [Category.{b} A] [Abelian A]
    [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ A)]
    (V : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤
      (ℕᵒᵖ ⥤ DerivedCategory (A)))
    (ε : DerivedCategory.Q ⋙ V ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (Functor.whiskeringRight ℕᵒᵖ (CochainComplex (A) ℤ)
          (DerivedCategory (A))).obj DerivedCategory.Q)
    (n : ℕ) :
    V ⋙ (evaluation ℕᵒᵖ _).obj (op n) ≅ evD A n := by
  let εn : DerivedCategory.Q ⋙ V ⋙ (evaluation ℕᵒᵖ _).obj (op n) ≅
      ((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ε ((evaluation ℕᵒᵖ _).obj (op n))
  exact (Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
    (DerivedCategory A)).preimageIso
      (εn ≪≫ (evF A n).symm)

private theorem totalEvaluationIso_fac
    (A : Type a) [Category.{b} A] [Abelian A]
    [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ A)]
    (V : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤
      (ℕᵒᵖ ⥤ DerivedCategory (A)))
    (ε : DerivedCategory.Q ⋙ V ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (Functor.whiskeringRight ℕᵒᵖ (CochainComplex (A) ℤ)
          (DerivedCategory (A))).obj DerivedCategory.Q)
    (n : ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (totalEvaluationIso A V ε n).hom.app (DerivedCategory.Q.obj I) ≫
      (evF A n).hom.app I =
        (ε.hom.app I).app (op n) := by
  have h := congrArg (fun z ↦ z.app I)
    ((Localization.fullyFaithfulWhiskeringLeft
      (DerivedCategory.Q : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ _)
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
      (DerivedCategory (A))).map_preimage
        ((((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight ε ((evaluation ℕᵒᵖ _).obj (op n))) ≪≫
          (evF A n).symm).hom))
  change (totalEvaluationIso A V ε n).hom.app (DerivedCategory.Q.obj I) = _ at h
  rw [h]
  change ((𝟙 _ ≫ (ε.hom.app I).app (op n)) ≫ (evF A n).inv.app I) ≫
    (evF A n).hom.app I = _
  erw [Category.id_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

attribute [local irreducible] totalEvaluationIso CategoryTheory.totalRoosP
  CategoryTheory.totalRoosDelta

private theorem totalLimitNatural
    (A : Type a) [Category.{b} A] [Abelian A]
    [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ A)]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [HasCountableProducts (DerivedCategory A)]
    [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]
    (π : ∀ n : ℕ, (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor ⟶ evD A n)
    (hπ : ∀ n : ℕ, ∃! α : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor ⟶ evD A n,
      ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective],
        α.app (DerivedCategory.Q.obj I) ≫ (evF A n).hom.app I =
          ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorObjQIso I).hom ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I))
    (hpπ : ∀ n : ℕ, ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective],
      (π n).app (DerivedCategory.Q.obj I) ≫ (evF A n).hom.app I =
        ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorObjQIso I).hom ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)) :
    ∃ (δ : ∀ Z : DerivedCategory (ℕᵒᵖ ⥤ A),
      (∏ᶜ fun n : ℕ ↦ (evD A n).obj Z) ⟶
        (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor).obj Z)⟦(1 : ℤ)⟧),
      (∀ Z : DerivedCategory (ℕᵒᵖ ⥤ A), IsDerivedLimitTriangle
        (fun n ↦ (trD A n).app Z)
        (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor).obj Z)
        (Pi.lift (fun n ↦ (π n).app Z)) (δ Z)) ∧
      (∀ {Z Z' : DerivedCategory (ℕᵒᵖ ⥤ A)} (v : Z ⟶ Z'),
        Limits.Pi.map (fun n ↦ (evD A n).map v) ≫ δ Z' =
          δ Z ≫ (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor).map v)⟦(1 : ℤ)⟧') := by
  let RF := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor
  let η : CategoryTheory.CoreWork.L (A := A) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF :=
    { app := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ
      naturality := by
        intro I J v
        exact (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ_naturality v }
  have hη (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (hI : I.IsKInjective) :
      IsIso (η.app I) := by
    letI := hI
    change IsIso ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ I)
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  obtain ⟨V, ⟨ε⟩⟩ := CategoryTheory.evaluationData (A := A)
  let b (n : ℕ) := totalEvaluationIso A V ε n
  let B (Z : DerivedCategory (ℕᵒᵖ ⥤ A)) :=
    Limits.Pi.mapIso (fun n ↦ (b n).app Z)
  let p : RF ⟶ V ⋙ CategoryTheory.CoreWork.DP :=
    CategoryTheory.totalRoosP RF η hη V ε
  let δ : V ⋙ CategoryTheory.CoreWork.DP ⟶ RF ⋙ shiftFunctor _ (1 : ℤ) :=
    CategoryTheory.totalRoosDelta RF η hη V ε
  have hp (Z : DerivedCategory (ℕᵒᵖ ⥤ A)) :
      p.app Z ≫ (B Z).hom =
        Pi.lift (fun n ↦ (π n).app Z) := by
    apply Pi.hom_ext
    intro n
    let ρ : CategoryTheory.CoreWork.DP (A := A) ⟶
        (evaluation ℕᵒᵖ (DerivedCategory A)).obj (op n) :=
      { app := fun Z ↦ Pi.π (fun k : ℕ ↦ Z.obj (op k)) n
        naturality := by
          intro Z Z' v
          change Limits.Pi.map (fun k : ℕ ↦ v.app (op k)) ≫ _ = _
          exact Limits.Pi.map_π (fun k : ℕ ↦ v.app (op k)) n }
    let γ : RF ⟶ evD A n :=
      p ≫ Functor.whiskerLeft V ρ ≫ (b n).hom
    have hγ : γ = π n := by
      apply (hπ n).unique ?_
        (hpπ n)
      intro I hI
      letI := hI
      haveI : IsIso (η.app I) := hη I hI
      have hηI : η.app I =
          ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorObjQIso I).inv :=
        Functor.rightDerivedFunctorUnitQ_eq _ _
      apply (cancel_epi (η.app I)).1
      change η.app I ≫
        ((p.app (DerivedCategory.Q.obj I) ≫ Pi.π _ n ≫
          (b n).hom.app (DerivedCategory.Q.obj I)) ≫
            (evF A n).hom.app I) = _
      simp only [Category.assoc]
      rw [totalEvaluationIso_fac]
      erw [CategoryTheory.totalRoos_first_projection RF η hη V ε I n,
        hηI, Iso.inv_hom_id_assoc]
    simp only [Category.assoc, B, Limits.Pi.mapIso_hom_π, Pi.lift_π]
    exact NatTrans.congr_app hγ Z
  have ht (Z : DerivedCategory (ℕᵒᵖ ⥤ A)) (n : ℕ) :
      (V.obj Z).map (homOfLE n.le_succ).op ≫ (b n).hom.app Z =
        (b (n + 1)).hom.app Z ≫
          (trD A n).app Z := by
    let τ : V ⋙ (evaluation ℕᵒᵖ _).obj (op (n + 1)) ⟶
        V ⋙ (evaluation ℕᵒᵖ _).obj (op n) :=
      Functor.whiskerLeft V ((evaluation ℕᵒᵖ _).map (homOfLE n.le_succ).op)
    have h : τ ≫ (b n).hom = (b (n + 1)).hom ≫
        trD A n := by
      apply Localization.natTrans_ext DerivedCategory.Q
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
      intro I
      apply (cancel_mono
        ((evF A n).hom.app I)).1
      dsimp only [NatTrans.comp_app]
      rw [Category.assoc, totalEvaluationIso_fac]
      have hd :
          (trD A n).app (DerivedCategory.Q.obj I) ≫
            (evF A n).hom.app I =
          (evF A (n + 1)).hom.app I ≫
            DerivedCategory.Q.map (I.asFunctor.map (homOfLE n.le_succ).op) := by
        exact trD_fac A n I
      erw [Category.assoc, hd, ← Category.assoc, totalEvaluationIso_fac]
      exact (ε.hom.app I).naturality (homOfLE n.le_succ).op
    exact NatTrans.congr_app h Z
  refine ⟨fun Z ↦ (B Z).inv ≫ δ.app Z, ?_, ?_⟩
  · intro Z
    have hZ : IsDerivedLimitTriangle
        (fun n ↦ (V.obj Z).map (homOfLE n.le_succ).op)
        (RF.obj Z) (p.app Z) (δ.app Z) := by
      let I := DerivedCategory.Q.objPreimage Z
      let eI : DerivedCategory.Q.obj I ≅ Z := DerivedCategory.Q.objObjPreimageIso Z
      let aI := RF.mapIso eI
      let bI := (V ⋙ CategoryTheory.CoreWork.DP).mapIso eI
      exact (distinguished_iff_of_iso (Triangle.isoMk _ _ aI bI bI
        (p.naturality eI.hom).symm
        (CategoryTheory.CoreWork.dDP.naturality (V.map eI.hom)).symm
        (δ.naturality eI.hom).symm)).mp
          (CategoryTheory.totalRoos_triangle RF η hη V ε I)
    let S := Triangle.mk (p.app Z)
      (towerTransitionEndomorphism (fun n ↦ (V.obj Z).map (homOfLE n.le_succ).op))
      (δ.app Z)
    let U := Triangle.mk
      (Pi.lift (fun n ↦ (π n).app Z))
      (towerTransitionEndomorphism (fun n ↦
        (trD A n).app Z)) ((B Z).inv ≫ δ.app Z)
    have ee : S ≅ U := Triangle.isoMk _ _ (Iso.refl _) (B Z) (B Z)
      (by
        change p.app Z ≫ (B Z).hom = 𝟙 _ ≫ _
        simpa only [Category.id_comp, U, Triangle.mk] using hp Z)
      ((towerTransitionEndomorphism_natural_backward _ _
        (fun n ↦ (b n).hom.app Z) (fun n ↦ (ht Z n).symm)).symm)
      (by
        change δ.app Z ≫ (𝟙 _)⟦(1 : ℤ)⟧' = (B Z).hom ≫ (B Z).inv ≫ δ.app Z
        simp only [(shiftFunctor (DerivedCategory A) (1 : ℤ)).map_id,
          Iso.hom_inv_id_assoc]
        exact Category.comp_id (δ.app Z))
    exact (distinguished_iff_of_iso ee).mp hZ
  · intro Z Z' v
    have hn := totalProductIsoInvNatural
      (fun n ↦ V ⋙ (evaluation ℕᵒᵖ (DerivedCategory A)).obj (op n))
      (fun n ↦ evD A n) b v
    rw [← Category.assoc, hn, Category.assoc]
    simpa only [B, RF, Category.assoc, Functor.comp_map, CategoryTheory.evaluation,
      CategoryTheory.CoreWork.DP] using
      congrArg (fun z ↦ (B Z).inv ≫ z) (δ.naturality v)

private theorem totalFunctorLinear
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X Y : Scheme.{u})
    [sX : Linear (Padic.coefficientExtensionIntegers l E) (scalarReductionSource l E X)]
    [sY : Linear (Padic.coefficientExtensionIntegers l E) (scalarReductionSource l E Y)]
    (hx : IsCompactSupportScalarAction l E X) (hy : IsCompactSupportScalarAction l E Y)
    (T : DerivedCategory (scalarReductionSource l E X) ⥤
      coefficientSequenceRestrictedDerived l E Y)
    (ht : @Functor.Linear (Padic.coefficientExtensionIntegers l E) _ _ _ _ _ _ _
      (DerivedCategory.instLinear _ _) (DerivedCategory.instLinear _ _) T) :
    (sfCompactSupportTotalLimitFunctor l E X Y T).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  letI : Linear (Padic.coefficientExtensionIntegers l E)
      (DerivedCategory (scalarReductionSource l E X)) := DerivedCategory.instLinear _ _
  letI : Linear (Padic.coefficientExtensionIntegers l E)
      (DerivedCategory (scalarReductionSource l E Y)) := DerivedCategory.instLinear _ _
  letI : T.Linear (Padic.coefficientExtensionIntegers l E) := ht
  let L := coefficientConstantTowerLimit l E Y
  have hX := normalizedDerivedLinear l E X sX hx
  letI : (sfIntegralConstructible l E X).ι.Linear
      (Padic.coefficientExtensionIntegers l E) := by
    change @Functor.Linear (Padic.coefficientExtensionIntegers l E) _ _ _ _ _ _ _ _
      (DerivedCategory.instLinear (Padic.coefficientExtensionIntegers l E)
        (scalarReductionSource l E X)) _
    rw [hX]
    infer_instance
  haveI : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤
      scalarReductionSource l E Y).Linear (Padic.coefficientExtensionIntegers l E) := by
    constructor
    intro M N v a
    apply limit.hom_ext
    intro n
    simp only [lim_map, limMap_π, Linear.smul_comp, NatTrans.app_smul, Linear.comp_smul]
  haveI : L.Linear (Padic.coefficientExtensionIntegers l E) := by
    dsimp only [L, coefficientConstantTowerLimit]
    exact Functor.linear_rightDerivedFunctor (Padic.coefficientExtensionIntegers l E)
      (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤ scalarReductionSource l E Y)
  have hY := normalizedDerivedLinear l E Y sY hy
  change @Functor.Linear (Padic.coefficientExtensionIntegers l E) _ _ _ _ _ _ _ _
    (sfIntegralCoefficientLinear l E Y) _
  apply (congrArg (fun s ↦
    @Functor.Linear (Padic.coefficientExtensionIntegers l E) _ _ _ _ _ _ _ _ s
      (sfCompactSupportTotalLimitFunctor l E X Y T)) hY).mp
  dsimp only [sfCompactSupportTotalLimitFunctor]
  infer_instance

attribute [local irreducible] coefficientConstantTowerProjection

private theorem totalSuccessorTransition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    compactSupportRestrictedTransition l E c (n + 1) n n.le_succ K =
      sfCompactSupportTransition l E c K n := rfl

attribute [local irreducible] compactSupportRestrictedTransition sfCompactSupportTransition

private theorem totalCompactSupportRoos
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X Y : Scheme.{u})
    [HasCountableProducts (DerivedCategory (scalarReductionSource l E Y))]
    {f : X ⟶ Y} (c : Compactification f)
    (T : DerivedCategory (scalarReductionSource l E X) ⥤
      coefficientSequenceRestrictedDerived l E Y)
    (e : ∀ n, T ⋙ coefficientConstantTowerEvaluation l E Y n ≅
      compactSupportRestrictedLevel l E c n)
    (ht : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
      (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y)
        (n + 1) n n.le_succ).app (T.obj K.obj) ≫ (e n).hom.app K.obj =
          (e (n + 1)).hom.app K.obj ≫ sfCompactSupportTransition l E c K.obj n) :
    ∃ (p : ∀ K : sfIntegralConstructibleCategory l E X,
              (sfCompactSupportTotalLimitFunctor l E X Y T).obj K ⟶
                ∏ᶜ fun n : ℕ ↦ (compactSupportRestrictedLevel l E c n).obj K.obj)
      (δ : ∀ K : sfIntegralConstructibleCategory l E X,
              (∏ᶜ fun n : ℕ ↦ (compactSupportRestrictedLevel l E c n).obj K.obj) ⟶
                ((sfCompactSupportTotalLimitFunctor l E X Y T).obj K)⟦(1 : ℤ)⟧),
    (∀ K : sfIntegralConstructibleCategory l E X,
      IsDerivedLimitTriangle (sfCompactSupportTransition l E c K.obj)
        ((sfCompactSupportTotalLimitFunctor l E X Y T).obj K) (p K) (δ K)) ∧
    (∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
      p K ≫ Pi.π _ n =
        (coefficientConstantTowerProjection l E Y n).app (T.obj K.obj) ≫
          (e n).hom.app K.obj) ∧
    (∀ (K M : sfIntegralConstructibleCategory l E X) (v : K ⟶ M),
      (sfCompactSupportTotalLimitFunctor l E X Y T).map v ≫ p M =
        p K ≫ Limits.Pi.map (fun n : ℕ ↦
          (compactSupportRestrictedLevel l E c n).map v.hom)) ∧
    (∀ (K M : sfIntegralConstructibleCategory l E X) (v : K ⟶ M),
      Limits.Pi.map (fun n : ℕ ↦ (compactSupportRestrictedLevel l E c n).map v.hom) ≫
          δ M = δ K ≫
            ((sfCompactSupportTotalLimitFunctor l E X Y T).map v)⟦(1 : ℤ)⟧') := by
  letI : IsGrothendieckAbelian.{u + 1} (scalarReductionSource l E Y) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u+1,u,u}
      (ProEt.topology Y) (completedIntegralCommRingSheafUnrestricted l E Y)).1
  letI : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ scalarReductionSource l E Y) :=
    CategoryTheory.tower_grothendieck _
  let R := totalLimitNatural (scalarReductionSource l E Y)
    (coefficientConstantTowerProjection l E Y)
    (coefficientConstantTowerProjection_exists l E Y)
    (fun n I hI ↦ by
      letI := hI
      unfold coefficientConstantTowerProjection
      exact (coefficientConstantTowerProjection_exists l E Y n).choose_spec.1 I)
  let δ₀ := R.choose
  have hδ₀ := R.choose_spec.1
  have hδnat {Z Z' : coefficientSequenceRestrictedDerived l E Y} (v : Z ⟶ Z') :
      Limits.Pi.map (fun n ↦ (coefficientConstantTowerEvaluation l E Y n).map v) ≫
        δ₀ Z' = δ₀ Z ≫ ((coefficientConstantTowerLimit l E Y).map v)⟦(1 : ℤ)⟧' :=
    R.choose_spec.2 v
  let B (K : sfIntegralConstructibleCategory l E X) :=
    Limits.Pi.mapIso (fun n : ℕ ↦ (e n).app K.obj)
  let p (K : sfIntegralConstructibleCategory l E X) :=
    Pi.lift (fun n : ℕ ↦
      (coefficientConstantTowerProjection l E Y n).app (T.obj K.obj)) ≫ (B K).hom
  let δ (K : sfIntegralConstructibleCategory l E X) :=
    (B K).inv ≫ δ₀ (T.obj K.obj)
  refine ⟨p, δ, ?_, ?_, ?_, ?_⟩
  · intro K
    have htransition (n : ℕ) := ht K n
    let S := Triangle.mk
      (Pi.lift (fun n ↦ (coefficientConstantTowerProjection l E Y n).app (T.obj K.obj)))
      (towerTransitionEndomorphism (fun n ↦
        (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y)
          (n + 1) n n.le_succ).app (T.obj K.obj))) (δ₀ (T.obj K.obj))
    let U := Triangle.mk (p K)
      (towerTransitionEndomorphism (sfCompactSupportTransition l E c K.obj)) (δ K)
    have ee : S ≅ U := Triangle.isoMk _ _ (Iso.refl _) (B K) (B K)
      (by
        change (Pi.lift (fun n ↦
          (coefficientConstantTowerProjection l E Y n).app (T.obj K.obj))) ≫
            (B K).hom = 𝟙 _ ≫ p K
        rw [Category.id_comp])
      ((towerTransitionEndomorphism_natural_backward _ _
        (fun n ↦ (e n).hom.app K.obj) (fun n ↦ (htransition n).symm)).symm)
      (by
        change δ₀ (T.obj K.obj) ≫ (𝟙 _)⟦(1 : ℤ)⟧' =
          (B K).hom ≫ (B K).inv ≫ δ₀ (T.obj K.obj)
        erw [(shiftFunctor (DerivedCategory (scalarReductionSource l E Y)) (1 : ℤ)).map_id,
          Category.comp_id, Iso.hom_inv_id_assoc])
    exact (distinguished_iff_of_iso ee).mp (hδ₀ (T.obj K.obj))
  · intro K n
    dsimp only [p]
    erw [Category.assoc]
    change (Pi.lift (fun k ↦
      (coefficientConstantTowerProjection l E Y k).app (T.obj K.obj))) ≫
        (B K).hom ≫ Pi.π _ n = _
    erw [show (B K).hom ≫ Pi.π _ n = Pi.π _ n ≫ (e n).hom.app K.obj from
      Limits.Pi.mapIso_hom_π _ n]
    simpa only [Category.assoc, Functor.comp_obj] using
      congrArg (fun z ↦ z ≫ (e n).hom.app K.obj)
        (Pi.lift_π (fun k : ℕ ↦
          (coefficientConstantTowerProjection l E Y k).app (T.obj K.obj)) n)
  · intro K M v
    exact totalProductProjectionNatural (T ⋙ coefficientConstantTowerLimit l E Y)
      (fun n ↦ T ⋙ coefficientConstantTowerEvaluation l E Y n)
      (fun n ↦ compactSupportRestrictedLevel l E c n)
      (fun n ↦ Functor.whiskerLeft T (coefficientConstantTowerProjection l E Y n))
      e v.hom
  · intro K M v
    exact totalProductDeltaNatural (T ⋙ coefficientConstantTowerLimit l E Y)
      (fun n ↦ T ⋙ coefficientConstantTowerEvaluation l E Y n)
      (fun n ↦ compactSupportRestrictedLevel l E c n) e
      (fun K ↦ δ₀ (T.obj K)) (fun v ↦ hδnat (T.map v)) v.hom

@[no_expose] private def totalRealizationProperty
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra ℚ_[C.l] E] [FiniteDimensional ℚ_[C.l] E]
    (level : ℕ) (hlevel : 1 ≤ level)
    (_operations : SixFunctorOperationDatum D C E level hlevel)
    (X Y : Scheme.{u}) [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hl : IsUnit (C.l : D.k)) (c : Compactification f)
    (H : type_of% (exists_compactSupportReductionTower C.l E D.k X Y f hl c))
    (T : DerivedCategory (scalarReductionSource C.l E X) ⥤
      coefficientSequenceRestrictedDerived C.l E Y)
 : Prop :=
    (fun [linearX : Linear (Padic.coefficientExtensionIntegers C.l E)
        (scalarReductionSource C.l E X)]
      [linearY : Linear (Padic.coefficientExtensionIntegers C.l E)
        (scalarReductionSource C.l E Y)]
      [products : HasCountableProducts (DerivedCategory (scalarReductionSource C.l E Y))] ↦
      ∃ (sT : T.CommShift ℤ)
        (sL : (coefficientConstantTowerLimit C.l E Y).CommShift ℤ),
      sL = (inferInstance : (coefficientConstantTowerLimit C.l E Y).CommShift ℤ) ∧
      (fun [shiftT : T.CommShift ℤ]
        [shiftL : (coefficientConstantTowerLimit C.l E Y).CommShift ℤ] ↦
        HEq sT (Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec (H))).2.2).2) ∧
        T.IsTriangulated ∧ (coefficientConstantTowerLimit C.l E Y).IsTriangulated ∧
        ∃ sF : (sfCompactSupportTotalLimitFunctor C.l E X Y T).CommShift ℤ,
        (fun [shiftF : (sfCompactSupportTotalLimitFunctor C.l E X Y T).CommShift ℤ] ↦
          (sfCompactSupportTotalLimitFunctor C.l E X Y T).IsTriangulated ∧
          (sfCompactSupportTotalLimitFunctor C.l E X Y T).Linear
            (Padic.coefficientExtensionIntegers C.l E) ∧
          ∃ (e : ∀ n : ℕ,
              T ⋙ coefficientConstantTowerEvaluation C.l E Y n ≅
                compactSupportRestrictedLevel C.l E c n)
            (p : ∀ K : sfIntegralConstructibleCategory C.l E X,
              (sfCompactSupportTotalLimitFunctor C.l E X Y T).obj K ⟶
                ∏ᶜ fun n : ℕ ↦ (compactSupportRestrictedLevel C.l E c n).obj K.obj)
            (δ : ∀ K : sfIntegralConstructibleCategory C.l E X,
              (∏ᶜ fun n : ℕ ↦ (compactSupportRestrictedLevel C.l E c n).obj K.obj) ⟶
                ((sfCompactSupportTotalLimitFunctor C.l E X Y T).obj K)⟦(1 : ℤ)⟧),
          HEq e (Classical.choose (Classical.choose_spec
            (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
              (H))).2.2).2).2) ∧
          (∀ (m n : ℕ) (h : n ≤ m) (K : sfIntegralConstructibleCategory C.l E X),
            (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted C.l E Y)
                m n h).app (T.obj K.obj) ≫ (e n).hom.app K.obj =
              (e m).hom.app K.obj ≫ compactSupportRestrictedTransition C.l E c m n h K.obj) ∧
          (∀ (K : sfIntegralConstructibleCategory C.l E X) (n : ℕ),
            compactSupportRestrictedTransition C.l E c (n + 1) n (Nat.le_succ n) K.obj =
              sfCompactSupportTransition C.l E c K.obj n) ∧
          (∀ K : sfIntegralConstructibleCategory C.l E X,
            IsDerivedLimitTriangle (sfCompactSupportTransition C.l E c K.obj)
              ((sfCompactSupportTotalLimitFunctor C.l E X Y T).obj K) (p K) (δ K)) ∧
          (∀ (K : sfIntegralConstructibleCategory C.l E X) (n : ℕ),
            p K ≫ Pi.π _ n =
              (coefficientConstantTowerProjection C.l E Y n).app (T.obj K.obj) ≫
                (e n).hom.app K.obj) ∧
          (∀ (K M : sfIntegralConstructibleCategory C.l E X) (v : K ⟶ M),
            (sfCompactSupportTotalLimitFunctor C.l E X Y T).map v ≫ p M =
              p K ≫ Limits.Pi.map (fun n : ℕ ↦
                (compactSupportRestrictedLevel C.l E c n).map v.hom)) ∧
          (∀ (K M : sfIntegralConstructibleCategory C.l E X) (v : K ⟶ M),
            Limits.Pi.map (fun n : ℕ ↦ (compactSupportRestrictedLevel C.l E c n).map v.hom) ≫
                δ M = δ K ≫
                  ((sfCompactSupportTotalLimitFunctor C.l E X Y T).map v)⟦(1 : ℤ)⟧') ∧
          (∀ (K M : sfIntegralConstructibleCategory C.l E X) (v : K ⟶ M),
            (sfCompactSupportTotalLimitFunctor C.l E X Y T).map v =
              (coefficientConstantTowerLimit C.l E Y).map (T.map v.hom)) ∧
          (∀ K : sfIntegralConstructibleCategory C.l E X,
            ((sfCompactSupportTotalLimitFunctor C.l E X Y T).commShiftIso (1 : ℤ)).hom.app K =
              (coefficientConstantTowerLimit C.l E Y).map
                  (T.map (((sfIntegralConstructible C.l E X).ι.commShiftIso
                    (1 : ℤ)).hom.app K) ≫ (T.commShiftIso (1 : ℤ)).hom.app K.obj) ≫
                ((coefficientConstantTowerLimit C.l E Y).commShiftIso (1 : ℤ)).hom.app
                  (T.obj K.obj)) ∧
          (∀ (A : Triangle (sfIntegralConstructibleCategory C.l E X))
            (_hA : A ∈ distTriang (sfIntegralConstructibleCategory C.l E X)),
            Triangle.mk
                ((sfCompactSupportTotalLimitFunctor C.l E X Y T).map A.mor₁)
                ((sfCompactSupportTotalLimitFunctor C.l E X Y T).map A.mor₂)
                ((sfCompactSupportTotalLimitFunctor C.l E X Y T).map A.mor₃ ≫
                  (coefficientConstantTowerLimit C.l E Y).map
                    (T.map (((sfIntegralConstructible C.l E X).ι.commShiftIso
                      (1 : ℤ)).hom.app A.obj₁) ≫
                      (T.commShiftIso (1 : ℤ)).hom.app A.obj₁.obj) ≫
                  ((coefficientConstantTowerLimit C.l E Y).commShiftIso (1 : ℤ)).hom.app
                    (T.obj A.obj₁.obj)) ∈
              distTriang (DerivedCategory (scalarReductionSource C.l E Y)))) (shiftF := sF))
        (shiftT := sT) (shiftL := sL))
      (linearX := (H).choose)
      (linearY := (H).choose_spec.choose)
      (products := integralOperationsDerivedCountableProducts C.l E Y)

private theorem totalRealizationCore
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X Y : Scheme.{u})
    [HasCountableProducts (DerivedCategory (scalarReductionSource l E Y))]
    {f : X ⟶ Y} (c : Compactification f)
    (T : DerivedCategory (scalarReductionSource l E X) ⥤
      coefficientSequenceRestrictedDerived l E Y)
    [T.CommShift ℤ] [T.IsTriangulated]
    [(coefficientConstantTowerLimit l E Y).CommShift ℤ]
    [(coefficientConstantTowerLimit l E Y).IsTriangulated]
    (e : ∀ n, T ⋙ coefficientConstantTowerEvaluation l E Y n ≅
      compactSupportRestrictedLevel l E c n)
    (he : ∀ (m n : ℕ) (h : n ≤ m)
      (K : DerivedCategory (scalarReductionSource l E X)),
      (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y)
        m n h).app (T.obj K) ≫ (e n).hom.app K =
          (e m).hom.app K ≫ compactSupportRestrictedTransition l E c m n h K) :
    ∃ sF : (sfCompactSupportTotalLimitFunctor l E X Y T).CommShift ℤ,
    (fun [shiftF : (sfCompactSupportTotalLimitFunctor l E X Y T).CommShift ℤ] ↦
    (sfCompactSupportTotalLimitFunctor l E X Y T).IsTriangulated ∧
    ∃ (p : ∀ K : sfIntegralConstructibleCategory l E X,
          (sfCompactSupportTotalLimitFunctor l E X Y T).obj K ⟶
            ∏ᶜ fun n : ℕ ↦ (compactSupportRestrictedLevel l E c n).obj K.obj)
      (δ : ∀ K : sfIntegralConstructibleCategory l E X,
          (∏ᶜ fun n : ℕ ↦ (compactSupportRestrictedLevel l E c n).obj K.obj) ⟶
            ((sfCompactSupportTotalLimitFunctor l E X Y T).obj K)⟦(1 : ℤ)⟧),
    (∀ (m n : ℕ) (h : n ≤ m) (K : sfIntegralConstructibleCategory l E X),
      (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y)
          m n h).app (T.obj K.obj) ≫ (e n).hom.app K.obj =
        (e m).hom.app K.obj ≫ compactSupportRestrictedTransition l E c m n h K.obj) ∧
    (∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
      compactSupportRestrictedTransition l E c (n + 1) n (Nat.le_succ n) K.obj =
        sfCompactSupportTransition l E c K.obj n) ∧
    (∀ K : sfIntegralConstructibleCategory l E X,
      IsDerivedLimitTriangle (sfCompactSupportTransition l E c K.obj)
        ((sfCompactSupportTotalLimitFunctor l E X Y T).obj K) (p K) (δ K)) ∧
    (∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
      p K ≫ Pi.π _ n =
        (coefficientConstantTowerProjection l E Y n).app (T.obj K.obj) ≫
          (e n).hom.app K.obj) ∧
    (∀ (K M : sfIntegralConstructibleCategory l E X) (v : K ⟶ M),
      (sfCompactSupportTotalLimitFunctor l E X Y T).map v ≫ p M =
        p K ≫ Limits.Pi.map (fun n : ℕ ↦
          (compactSupportRestrictedLevel l E c n).map v.hom)) ∧
    (∀ (K M : sfIntegralConstructibleCategory l E X) (v : K ⟶ M),
      Limits.Pi.map (fun n : ℕ ↦ (compactSupportRestrictedLevel l E c n).map v.hom) ≫
          δ M = δ K ≫
            ((sfCompactSupportTotalLimitFunctor l E X Y T).map v)⟦(1 : ℤ)⟧') ∧
    (∀ (K M : sfIntegralConstructibleCategory l E X) (v : K ⟶ M),
      (sfCompactSupportTotalLimitFunctor l E X Y T).map v =
        (coefficientConstantTowerLimit l E Y).map (T.map v.hom)) ∧
    (∀ K : sfIntegralConstructibleCategory l E X,
      ((sfCompactSupportTotalLimitFunctor l E X Y T).commShiftIso (1 : ℤ)).hom.app K =
        (coefficientConstantTowerLimit l E Y).map
            (T.map (((sfIntegralConstructible l E X).ι.commShiftIso
              (1 : ℤ)).hom.app K) ≫ (T.commShiftIso (1 : ℤ)).hom.app K.obj) ≫
          ((coefficientConstantTowerLimit l E Y).commShiftIso (1 : ℤ)).hom.app
            (T.obj K.obj)) ∧
    (∀ (A : Triangle (sfIntegralConstructibleCategory l E X))
      (_hA : A ∈ distTriang (sfIntegralConstructibleCategory l E X)),
      Triangle.mk
          ((sfCompactSupportTotalLimitFunctor l E X Y T).map A.mor₁)
          ((sfCompactSupportTotalLimitFunctor l E X Y T).map A.mor₂)
          ((sfCompactSupportTotalLimitFunctor l E X Y T).map A.mor₃ ≫
            (coefficientConstantTowerLimit l E Y).map
              (T.map (((sfIntegralConstructible l E X).ι.commShiftIso
                (1 : ℤ)).hom.app A.obj₁) ≫
                (T.commShiftIso (1 : ℤ)).hom.app A.obj₁.obj) ≫
            ((coefficientConstantTowerLimit l E Y).commShiftIso (1 : ℤ)).hom.app
              (T.obj A.obj₁.obj)) ∈
        distTriang (DerivedCategory (scalarReductionSource l E Y)))) (shiftF := sF) := by
  let sF : (sfCompactSupportTotalLimitFunctor l E X Y T).CommShift ℤ :=
    inferInstanceAs (((sfIntegralConstructible l E X).ι ⋙ T ⋙
      coefficientConstantTowerLimit l E Y).CommShift ℤ)
  refine ⟨sF, ?_, ?_⟩
  · change ((sfIntegralConstructible l E X).ι ⋙ T ⋙
      coefficientConstantTowerLimit l E Y).IsTriangulated
    infer_instance
  have ht (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :
      (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y)
        (n + 1) n n.le_succ).app (T.obj K.obj) ≫ (e n).hom.app K.obj =
          (e (n + 1)).hom.app K.obj ≫ sfCompactSupportTransition l E c K.obj n := by
    rw [← totalSuccessorTransition l E c K.obj n]
    exact he (n + 1) n n.le_succ K.obj
  obtain ⟨p, δ, htriangle, hp, hpnat, hδnat⟩ :=
    totalCompactSupportRoos l E X Y c T e ht
  refine ⟨p, δ, ?_, ?_, htriangle, hp, hpnat, hδnat, ?_, ?_, ?_⟩
  · intro m n h K
    exact he m n h K.obj
  · intro K n
    exact totalSuccessorTransition l E c K.obj n
  · intro K M v
    rfl
  · intro K
    exact totalCompositeShift (sfIntegralConstructible l E X).ι T
      (coefficientConstantTowerLimit l E Y) K
  · intro A hA
    exact totalCompositeTriangle (sfIntegralConstructible l E X).ι T
      (coefficientConstantTowerLimit l E Y) A hA

private theorem totalCanonicalRealization
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra ℚ_[C.l] E] [FiniteDimensional ℚ_[C.l] E]
    (level : ℕ) (hlevel : 1 ≤ level)
    (_operations : SixFunctorOperationDatum D C E level hlevel)
    (X Y : Scheme.{u}) [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hl : IsUnit (C.l : D.k)) (c : Compactification f)
    (H : type_of% (exists_compactSupportReductionTower C.l E D.k X Y f hl c))
    (sL : (coefficientConstantTowerLimit C.l E Y).CommShift ℤ)
    (hL : letI : (coefficientConstantTowerLimit C.l E Y).CommShift ℤ := sL
      (coefficientConstantTowerLimit C.l E Y).IsTriangulated)
    : totalRealizationProperty D C E level hlevel _operations X Y f hl c H
        H.choose_spec.choose_spec.2.2.choose := by
  unfold totalRealizationProperty
  classical
  let HX := H.choose
  let HY := H.choose_spec.choose
  have HA := H.choose_spec.choose_spec
  let := HX
  let := HY
  let := integralOperationsDerivedCountableProducts C.l E Y
  have HT := HA.2.2
  let T : DerivedCategory (scalarReductionSource C.l E X) ⥤
      coefficientSequenceRestrictedDerived C.l E Y := HT.choose
  have hT := HT.choose_spec
  let : T.CommShift ℤ := hT.2.choose
  have : T.IsTriangulated := hT.2.choose_spec.1
  let : (coefficientConstantTowerLimit C.l E Y).CommShift ℤ := sL
  have : (coefficientConstantTowerLimit C.l E Y).IsTriangulated := hL
  refine Exists.intro hT.2.choose ?_
  refine Exists.intro sL ?_
  apply And.intro rfl
  apply And.intro HEq.rfl
  apply And.intro hT.2.choose_spec.1
  apply And.intro (inferInstance : (coefficientConstantTowerLimit C.l E Y).IsTriangulated)
  let e : ∀ n, T ⋙ coefficientConstantTowerEvaluation C.l E Y n ≅
      compactSupportRestrictedLevel C.l E c n := hT.2.choose_spec.2.choose
  have he (m n : ℕ) (h : n ≤ m)
      (K : DerivedCategory (scalarReductionSource C.l E X)) :
      (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted C.l E Y)
        m n h).app (T.obj K) ≫ (e n).hom.app K =
          (e m).hom.app K ≫ compactSupportRestrictedTransition C.l E c m n h K :=
    hT.2.choose_spec.2.choose_spec.1 m n h K
  have hdata := @totalRealizationCore C.l _ E _ _ _ X Y
    (integralOperationsDerivedCountableProducts C.l E Y) f c T
    (inferInstance : T.CommShift ℤ) (inferInstance : T.IsTriangulated)
    sL (inferInstance : (coefficientConstantTowerLimit C.l E Y).IsTriangulated) e he
  rcases hdata with ⟨sF, htriang, p, δ, hcore⟩
  refine ⟨sF, htriang, ?_, e, p, δ, HEq.rfl, hcore⟩
  exact totalFunctorLinear C.l E X Y HA.1 HA.2.1 T hT.1

/-- The designated compact-support strict tower, followed by total limit, realizes
integral compact support with its quotient transitions, natural Roos triangle,
linear morphism action and composite shift comparison. It makes a permitted
coherent choice of the defining derived limits; it does not identify arbitrary
choices of Roos vertices or recover a tower morphism from its evaluations.

Source: current blueprint `prop-functor-package.proof.md`, clause (3);
Stacks Tags 0940, 0941 and 08TC
(blueprint: lem-sf-compact-support-total-limit-realization).

Proof plan:
1. Apply lem-weil-compact-support-reduction-tower-functor over D.k. Its natural
   evaluation isomorphisms identify the terms, all quotient-induced transitions,
   and their action on morphisms with the defining compact-support system.
2. Apply lem-weil-pbc-ringed-strict-tower-homotopy-limit to the completed ring
   sheaf on Y. Transport its Roos triangle by the product of those evaluation
   isomorphisms. The transition equations intertwine 1-s, giving precisely
   def-weil-derived-limit for the defining integral compact-support system.
3. Choose these vertices and triangles in def-weil-integral-rational-qbar-compact-support.
   Define every map by total limit of the whole strict-tower map. Functor laws
   and naturality of the two Roos arrows supply identities and composition.
4. Ordinary inverse limit is R-linear, since sums and constant-section scalars
   are computed coordinatewise. Use lem-weil-linear-abelian-derived-category
   and lem-weil-kinjective-total-derived-linear on K-injective representatives.
   Composing with the R-linear tower gives the asserted linear realization.
5. Restrict to the exact full inclusion supplied by
   lem-weil-integral-constructible-triangulated. Compose the two shift comparisons.
   Exactness sends w to F(w) followed by L(s_T) and then s_L, with no extra sign.
-/
theorem sfCompactSupportTotalLimitRealization
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra ℚ_[C.l] E] [FiniteDimensional ℚ_[C.l] E]
    (level : ℕ) (hlevel : 1 ≤ level)
    (_operations : SixFunctorOperationDatum D C E level hlevel)
    (X Y : Scheme.{u}) [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hl : IsUnit (C.l : D.k)) (c : Compactification f)
    (T : DerivedCategory (scalarReductionSource C.l E X) ⥤
      coefficientSequenceRestrictedDerived C.l E Y)
    (_hT : T = Classical.choose (Classical.choose_spec (Classical.choose_spec
      (exists_compactSupportReductionTower C.l E D.k X Y f hl c))).2.2) :
    (fun [linearX : Linear (Padic.coefficientExtensionIntegers C.l E)
        (scalarReductionSource C.l E X)]
      [linearY : Linear (Padic.coefficientExtensionIntegers C.l E)
        (scalarReductionSource C.l E Y)]
      [products : HasCountableProducts (DerivedCategory (scalarReductionSource C.l E Y))] ↦
      ∃ (sT : T.CommShift ℤ)
        (sL : (coefficientConstantTowerLimit C.l E Y).CommShift ℤ),
      sL = (inferInstance : (coefficientConstantTowerLimit C.l E Y).CommShift ℤ) ∧
      (fun [shiftT : T.CommShift ℤ]
        [shiftL : (coefficientConstantTowerLimit C.l E Y).CommShift ℤ] ↦
        HEq sT (Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec (exists_compactSupportReductionTower
            C.l E D.k X Y f hl c))).2.2).2) ∧
        T.IsTriangulated ∧ (coefficientConstantTowerLimit C.l E Y).IsTriangulated ∧
        ∃ sF : (sfCompactSupportTotalLimitFunctor C.l E X Y T).CommShift ℤ,
        (fun [shiftF : (sfCompactSupportTotalLimitFunctor C.l E X Y T).CommShift ℤ] ↦
          (sfCompactSupportTotalLimitFunctor C.l E X Y T).IsTriangulated ∧
          (sfCompactSupportTotalLimitFunctor C.l E X Y T).Linear
            (Padic.coefficientExtensionIntegers C.l E) ∧
          ∃ (e : ∀ n : ℕ,
              T ⋙ coefficientConstantTowerEvaluation C.l E Y n ≅
                compactSupportRestrictedLevel C.l E c n)
            (p : ∀ K : sfIntegralConstructibleCategory C.l E X,
              (sfCompactSupportTotalLimitFunctor C.l E X Y T).obj K ⟶
                ∏ᶜ fun n : ℕ ↦ (compactSupportRestrictedLevel C.l E c n).obj K.obj)
            (δ : ∀ K : sfIntegralConstructibleCategory C.l E X,
              (∏ᶜ fun n : ℕ ↦ (compactSupportRestrictedLevel C.l E c n).obj K.obj) ⟶
                ((sfCompactSupportTotalLimitFunctor C.l E X Y T).obj K)⟦(1 : ℤ)⟧),
          HEq e (Classical.choose (Classical.choose_spec
            (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
              (exists_compactSupportReductionTower C.l E D.k X Y f hl c))).2.2).2).2) ∧
          (∀ (m n : ℕ) (h : n ≤ m) (K : sfIntegralConstructibleCategory C.l E X),
            (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted C.l E Y)
                m n h).app (T.obj K.obj) ≫ (e n).hom.app K.obj =
              (e m).hom.app K.obj ≫ compactSupportRestrictedTransition C.l E c m n h K.obj) ∧
          (∀ (K : sfIntegralConstructibleCategory C.l E X) (n : ℕ),
            compactSupportRestrictedTransition C.l E c (n + 1) n (Nat.le_succ n) K.obj =
              sfCompactSupportTransition C.l E c K.obj n) ∧
          (∀ K : sfIntegralConstructibleCategory C.l E X,
            IsDerivedLimitTriangle (sfCompactSupportTransition C.l E c K.obj)
              ((sfCompactSupportTotalLimitFunctor C.l E X Y T).obj K) (p K) (δ K)) ∧
          (∀ (K : sfIntegralConstructibleCategory C.l E X) (n : ℕ),
            p K ≫ Pi.π _ n =
              (coefficientConstantTowerProjection C.l E Y n).app (T.obj K.obj) ≫
                (e n).hom.app K.obj) ∧
          (∀ (K M : sfIntegralConstructibleCategory C.l E X) (v : K ⟶ M),
            (sfCompactSupportTotalLimitFunctor C.l E X Y T).map v ≫ p M =
              p K ≫ Limits.Pi.map (fun n : ℕ ↦
                (compactSupportRestrictedLevel C.l E c n).map v.hom)) ∧
          (∀ (K M : sfIntegralConstructibleCategory C.l E X) (v : K ⟶ M),
            Limits.Pi.map (fun n : ℕ ↦ (compactSupportRestrictedLevel C.l E c n).map v.hom) ≫
                δ M = δ K ≫
                  ((sfCompactSupportTotalLimitFunctor C.l E X Y T).map v)⟦(1 : ℤ)⟧') ∧
          (∀ (K M : sfIntegralConstructibleCategory C.l E X) (v : K ⟶ M),
            (sfCompactSupportTotalLimitFunctor C.l E X Y T).map v =
              (coefficientConstantTowerLimit C.l E Y).map (T.map v.hom)) ∧
          (∀ K : sfIntegralConstructibleCategory C.l E X,
            ((sfCompactSupportTotalLimitFunctor C.l E X Y T).commShiftIso (1 : ℤ)).hom.app K =
              (coefficientConstantTowerLimit C.l E Y).map
                  (T.map (((sfIntegralConstructible C.l E X).ι.commShiftIso
                    (1 : ℤ)).hom.app K) ≫ (T.commShiftIso (1 : ℤ)).hom.app K.obj) ≫
                ((coefficientConstantTowerLimit C.l E Y).commShiftIso (1 : ℤ)).hom.app
                  (T.obj K.obj)) ∧
          (∀ (A : Triangle (sfIntegralConstructibleCategory C.l E X))
            (_hA : A ∈ distTriang (sfIntegralConstructibleCategory C.l E X)),
            Triangle.mk
                ((sfCompactSupportTotalLimitFunctor C.l E X Y T).map A.mor₁)
                ((sfCompactSupportTotalLimitFunctor C.l E X Y T).map A.mor₂)
                ((sfCompactSupportTotalLimitFunctor C.l E X Y T).map A.mor₃ ≫
                  (coefficientConstantTowerLimit C.l E Y).map
                    (T.map (((sfIntegralConstructible C.l E X).ι.commShiftIso
                      (1 : ℤ)).hom.app A.obj₁) ≫
                      (T.commShiftIso (1 : ℤ)).hom.app A.obj₁.obj) ≫
                  ((coefficientConstantTowerLimit C.l E Y).commShiftIso (1 : ℤ)).hom.app
                    (T.obj A.obj₁.obj)) ∈
              distTriang (DerivedCategory (scalarReductionSource C.l E Y)))) (shiftF := sF))
        (shiftT := sT) (shiftL := sL))
      (linearX := (exists_compactSupportReductionTower C.l E D.k X Y f hl c).choose)
      (linearY := (exists_compactSupportReductionTower C.l E D.k X Y f hl c).choose_spec.choose)
      (products := integralOperationsDerivedCountableProducts C.l E Y) := by
  let H := exists_compactSupportReductionTower C.l E D.k X Y f hl c
  change totalRealizationProperty D C E level hlevel _operations X Y f hl c H T
  let sL : (coefficientConstantTowerLimit C.l E Y).CommShift ℤ := by
    unfold coefficientConstantTowerLimit
    infer_instance
  have hL : letI : (coefficientConstantTowerLimit C.l E Y).CommShift ℤ := sL
      (coefficientConstantTowerLimit C.l E Y).IsTriangulated := by
    unfold coefficientConstantTowerLimit
    infer_instance
  exact _hT.symm ▸
    totalCanonicalRealization D C E level hlevel _operations X Y f hl c H sL hL

end WeilConjectures
