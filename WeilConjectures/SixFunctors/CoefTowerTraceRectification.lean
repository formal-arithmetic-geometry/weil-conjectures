/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefTowerTraceData
import WeilConjectures.SixFunctors.ScalarUnitRestrictionSingle
import WeilConjectures.SixFunctors.CoefTraceOrdinaryQuotient
import WeilConjectures.SixFunctors.CoefTraceSupportModel
import WeilConjectures.SixFunctors.CoefTraceFiniteSupportTransport

/-! Rectification of the finite counit trace tower. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

set_option maxHeartbeats 2000000 in
-- The normalized scalar adjunction has large exact-single comparison terms.
/-- The scalar-unit transition is exactly the quotient map on coefficient modules.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification).
Proof: the extension--restriction unit at the regular module sends r to r tensor 1.
The scalar-unit comparison sends that tensor to its residue class. The constant
sheaf and sections identifications in coefTraceTargetIso fix those same sections.
Exact localization therefore gives the displayed equality in D(R).
(blueprint: new-lem-coef-trace-target-transition-degree-zero) -/
theorem coefTraceTargetTransition_quotient {m n : ℕ} (h : n ≤ m) :
    coefTraceTargetTransition l E D h ≫ (coefTraceTargetIso l E D n).hom =
      (coefTraceTargetIso l E D m).hom ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (coefTraceRing l E)) 0).map
          (coefTraceQuotientMap l E h) := by
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (coefTraceRing l E)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let T := Spec (.of D.k)
  let J := T.smallEtaleTopology
  let U := Sheaf.restrictScalars J (coefTraceQuotient l E m)
  let V := Sheaf.restrictScalars J (coefTraceQuotient l E n)
  let Γ := (sheafSections J (ModuleCat.{u + 1} (coefTraceRing l E))).obj
    (op (etalePoint D.k))
  let P := coefTracePointSections l E D
  let f := U.map (Functor.LaxMonoidal.ε (Sheaf.restrictScalars J
      (finiteDualizingQuotient l E h))) ≫
    (Sheaf.restrictScalarsCompIso J (coefTraceQuotient l E m)
      (finiteDualizingQuotient l E h) (coefTraceQuotient l E n)
      (coefTraceQuotient_comp l E h)).hom.app (𝟙_ _)
  have hs := Etale.scalarUnit_restriction_comp_single
    (coefTraceQuotient l E m) (finiteDualizingQuotient l E h)
    (coefTraceQuotient l E n) (coefTraceQuotient_comp l E h) T
  have hp := congrArg P.map hs
  have hn := (Γ.mapDerivedCategorySingleFunctor 0).hom.naturality f
  have ho : Γ.map f ≫ (coefTraceUnitSectionsIso l E D n).hom =
      (coefTraceUnitSectionsIso l E D m).hom ≫ coefTraceQuotientMap l E h :=
    coefTraceOrdinaryQuotient l E D h
  dsimp only [coefTraceTargetTransition, coefTraceTargetIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, coefTraceFiniteSections, Functor.comp_map]
  change P.map _ ≫ _ = _
  simp only [P.map_comp, Category.assoc] at hp ⊢
  erw [reassoc_of% hp]
  change P.map _ ≫ P.map _ ≫
    Γ.mapDerivedCategory.map ((DerivedCategory.singleFunctor _ 0).map f) ≫
      (Γ.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
        (DerivedCategory.singleFunctor _ 0).map (coefTraceUnitSectionsIso l E D n).hom = _
  erw [reassoc_of% hn]
  have ho' := congrArg (DerivedCategory.singleFunctor
    (ModuleCat.{u + 1} (coefTraceRing l E)) 0).map ho
  simp only [Functor.map_comp] at ho'
  rw [ho']

/-- Evaluation and transition part of the tower rectification.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification).
Proof: apply the dualizing-support evaluation comparison to the fixed strict input,
then transport its level isomorphisms through the constant-scalar restriction and
separate derived point sections. The transition equation is the conjugated
projection-transpose formula. This is strictly the evaluation/transition part of
the final theorem; the counit square is handled separately.
(blueprint: new-lem-coef-tower-trace-evaluation-assembly).
-/
theorem coefTowerTraceRectification_evaluation_step (hl : l ≠ D.p)
    (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n)
    (hQ : ∀ {m n : ℕ} (h : n ≤ m),
      (coefficientSequenceDerivedTransition.{u, u} l E X h).app (coefTraceInput l E X Q) ≫
          (normalizedDVRRes.{u, u} l E X h).map (eQ n).hom =
        (eQ m).hom ≫ integralDualizingExceptionalTransition l E D X hl h) :
    ∃ e : ∀ n : ℕ,
      (coefTraceEvaluation l E n).obj (coefTraceDualizingTower l E D X Q) ≅
        coefTraceFiniteValue l E D X n,
      ∀ {m n : ℕ} (h : n ≤ m),
        (coefTraceTransition l E h).app (coefTraceDualizingTower l E D X Q) ≫ (e n).hom =
          (e m).hom ≫ coefTraceFiniteTransition l E D X h  := by
  obtain ⟨θ, hθ⟩ := coefTraceSupportModel l E D X hl
  obtain ⟨i, hi⟩ := coefTraceFiniteSupportTransport l E D X hl
  let q := coefTraceInput l E X Q
  let c := finiteDualizingCompactification D X
  let f (n : ℕ) := (coefTraceSmallSections l E).mapIso
    ((DualizingSupportEvaluation.sections D l E n).mapIso
      ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).mapIso
        (eQ n))) ≪≫ i n
  let e (n : ℕ) := (θ n).app q ≪≫ f n
  refine ⟨e, ?_⟩
  intro m n h
  have ht := hθ q h
  have hf : (coefTraceSmallSections l E).map
        (DualizingSupportEvaluation.sectionTransition D l E c h q) ≫ (f n).hom =
      (f m).hom ≫ coefTraceFiniteTransition l E D X h := by
    simpa only [f, c, Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using
      hi q eQ hQ h
  dsimp only [e, Iso.trans_hom, Iso.app_hom]
  simp only [Category.assoc]
  change (coefTraceTransition l E h).app
    ((coefTraceCompactSections l E (finiteDualizingCompactification D X)).obj q) ≫ _ = _
  erw [reassoc_of% ht, hf]

/-- The finite transition and finite counit form the local square used in the tower proof.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification). -/
theorem coefTraceFiniteCounit_transition_square (hl : l ≠ D.p)
    {m n : ℕ} (h : n ≤ m) :
    coefTraceFiniteTransition l E D X h ≫ coefTraceFiniteCounit l E D X n =
      coefTraceFiniteCounit l E D X m ≫ coefTraceTargetTransition l E D h := by
  let J := (Spec (.of D.k)).smallEtaleTopology
  let R := Sheaf.derivedRestrictScalars J (finiteDualizingQuotient l E h)
  let U := Sheaf.derivedRestrictScalars J (coefTraceQuotient l E m)
  let V := Sheaf.derivedRestrictScalars J (coefTraceQuotient l E n)
  let α := Sheaf.derivedRestrictScalarsCompIso J (coefTraceQuotient_comp l E h)
  let c := finiteDualizingCompactComparison l E D X h
  let b := (finiteDualizingEtaleSupport l E D X n).map
    (finiteDualizingEtaleComparison l E D X h)
  let εm := finiteDualizingEtaleCounit l E D X m
  let εn := finiteDualizingEtaleCounit l E D X n
  let lam := (Etale.ExceptionalCoefficients.unitIso
    (finiteDualizingQuotient l E h) (Spec (.of D.k))).hom
  have hc := ((finiteDualizingCoefficientComparisons l E D X hl).1 h).1
  have : IsIso c := hc
  have he := ((finiteDualizingCoefficientComparisons l E D X hl).1 h).2.2
  have hi : Etale.ExceptionalCoefficients.comparisonInverse
      (finiteDualizingQuotient l E h) (finiteDualizingCompactification D X)
        (finiteDualizingEtaleTerm l E D X m) = inv c := by
    unfold Etale.ExceptionalCoefficients.comparisonInverse
    split_ifs with hi
    · rfl
    · exact False.elim (hi hc)
  have hb : (c ≫ b) ≫ εn =
      (Etale.scalarExtension (finiteDualizingQuotient l E h) (Spec (.of D.k))).map εm ≫
        lam := by
    dsimp only [b, εm, εn, lam]
    rw [Category.assoc, he, hi, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  let ad := Adjunction.ofIsRightAdjoint R
  have hn := ad.unit.naturality εm
  change εm ≫ ad.unit.app _ = ad.unit.app _ ≫ R.map ((Etale.scalarExtension
    (finiteDualizingQuotient l E h) (Spec (.of D.k))).map εm) at hn
  have hu : (ad.unit.app _ ≫ R.map (c ≫ b)) ≫ R.map εn =
      εm ≫ ad.unit.app _ ≫ R.map lam := by
    rw [Category.assoc, ← R.map_comp, hb, R.map_comp, ← Category.assoc]
    simpa only [Functor.id_map, Functor.comp_map, Category.assoc] using
      congrArg (fun f ↦ f ≫ R.map lam) hn.symm
  unfold coefTraceFiniteTransition coefTraceFiniteCounit coefTraceTargetTransition
  dsimp only [coefTraceFiniteSections, Functor.comp_map]
  simp only [← Functor.map_comp]
  apply congrArg (coefTracePointSections l E D).map
  change (U.map (ad.unit.app _ ≫ R.map (c ≫ b)) ≫ α.hom.app _) ≫ V.map εn =
    U.map εm ≫ U.map (ad.unit.app _ ≫ R.map lam) ≫ α.hom.app _
  rw [Category.assoc, ← α.hom.naturality εn]
  dsimp only [Functor.comp_map]
  rw [← Category.assoc, ← U.map_comp, hu, U.map_comp, Category.assoc]
  rfl

private theorem counitSquareAssembly {C : Type*} [Category C]
    {A B M N U V Z W : C} (t : A ⟶ B) (en : B ⟶ N) (em : A ⟶ M)
    (f : M ⟶ N) (cn : N ⟶ V) (cm : M ⟶ U) (un : V ⟶ W)
    (um : U ⟶ Z) (q : Z ⟶ W) (s : U ⟶ V)
    (he : t ≫ en = em ≫ f) (hf : f ≫ cn = cm ≫ s)
    (hu : s ≫ un = um ≫ q) :
    t ≫ en ≫ cn ≫ un = em ≫ cm ≫ um ≫ q := by
  rw [← Category.assoc, he]
  simp only [Category.assoc]
  rw [← Category.assoc f cn un, hf]
  simp only [Category.assoc]
  rw [hu]

set_option maxHeartbeats 2000000 in
-- Checking the transported counit unfolds the specified derived comparisons.
/-- Counit assembly after the evaluated transitions have been constructed.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-trace-rectification).
Proof: transport the finite counit restriction square along the evaluation
isomorphisms and substitute the already established transition equation. The
regular scalar unit is replaced by the quotient target computation above.
(blueprint: new-lem-coef-tower-trace-counit-assembly).
-/
theorem coefTowerTraceRectification_counit_step (hl : l ≠ D.p)
    (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ)
    (e : ∀ n : ℕ,
      (coefTraceEvaluation l E n).obj (coefTraceDualizingTower l E D X Q) ≅
        coefTraceFiniteValue l E D X n)
    (hEval : ∀ {m n : ℕ} (h : n ≤ m),
      (coefTraceTransition l E h).app (coefTraceDualizingTower l E D X Q) ≫ (e n).hom =
        (e m).hom ≫ coefTraceFiniteTransition l E D X h) :
    ∀ {m n : ℕ} (h : n ≤ m),
      (coefTraceTransition l E h).app (coefTraceDualizingTower l E D X Q) ≫
          (e n).hom ≫ coefTraceFiniteCounit l E D X n ≫
            (coefTraceTargetIso l E D n).hom =
        (e m).hom ≫ coefTraceFiniteCounit l E D X m ≫
          (coefTraceTargetIso l E D m).hom ≫
            (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (coefTraceRing l E)) 0).map
              (coefTraceQuotientMap l E h) := by
  intro m n h
  exact counitSquareAssembly _ _ _ _ _ _ _ _ _ _ (hEval h)
    (coefTraceFiniteCounit_transition_square l E D X hl h)
    (coefTraceTargetTransition_quotient l E D h)
/-- Evaluation of the strict quotient-semilinear dualizing compact-support tower,
including every quotient transition and the actual finite exceptional counits.
Source: blueprint prop-coef-integral-dualizing, proof paragraph 2
(blueprint: lem-coef-tower-trace-rectification).
Proof: finiteDualizingCoefficientComparisons gives the counit-defined finite
comparison, its identity and cocycle, and its tensor--restriction adjunct. The
hypothesis identifies the given strict complex with precisely that tower.
On the ringed sequence site evaluation is exact. Derive proper image and point
sections separately; simultaneous resolutions and exact scalar restriction give
finite compact support at every level, naturally for all quotient-semilinear
arrows. The finiteDualizingOrigin comparison identifies each term with the
recorded finite exceptional object. The resulting transition is the projection
transpose Res(F_n u) Res(c) eta_(F_m omega_m), as in coefTraceFiniteTransition.
For counits use epsilon_n F_n(u) = T(epsilon_m) c^(-1). After cancellation,
naturality of eta gives Res(T epsilon_m) eta = eta_(A_m) epsilon_m. The unit at
A_m is the quotient A_m to A_n, as proved in coefTraceTargetTransition_quotient.
Apply point sections and exact restriction to R. This proves the second square
with actual counits into A_n[0]. No map of complexes is inferred from equality
only in the derived category, and no test object K is used anywhere. -/
theorem coefTowerTraceRectification (hl : l ≠ D.p)
    (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n)
    (hQ : ∀ {m n : ℕ} (h : n ≤ m),
      (coefficientSequenceDerivedTransition.{u, u} l E X h).app (coefTraceInput l E X Q) ≫
          (normalizedDVRRes.{u, u} l E X h).map (eQ n).hom =
        (eQ m).hom ≫ integralDualizingExceptionalTransition l E D X hl h) :
    ∃ e : ∀ n : ℕ,
      (coefTraceEvaluation l E n).obj (coefTraceDualizingTower l E D X Q) ≅
        coefTraceFiniteValue l E D X n,
      (∀ {m n : ℕ} (h : n ≤ m),
        (coefTraceTransition l E h).app (coefTraceDualizingTower l E D X Q) ≫ (e n).hom =
          (e m).hom ≫ coefTraceFiniteTransition l E D X h) ∧
      (∀ {m n : ℕ} (h : n ≤ m),
        (coefTraceTransition l E h).app (coefTraceDualizingTower l E D X Q) ≫
            (e n).hom ≫ coefTraceFiniteCounit l E D X n ≫
              (coefTraceTargetIso l E D n).hom =
          (e m).hom ≫ coefTraceFiniteCounit l E D X m ≫
            (coefTraceTargetIso l E D m).hom ≫
              (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (coefTraceRing l E)) 0).map
                (coefTraceQuotientMap l E h)) := by
  obtain ⟨e, he⟩ := coefTowerTraceRectification_evaluation_step l E D X hl Q eQ hQ
  refine ⟨e, he, ?_⟩
  exact coefTowerTraceRectification_counit_step l E D X hl Q e he

end WeilConjectures
