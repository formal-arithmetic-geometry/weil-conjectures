/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.AdicNormalizedPurity.AdicNormalizedPuritySystems
import all WeilConjectures.SmoothPurity.AdicNormalizedPurity.AdicNormalizedPuritySystems
import all WeilConjectures.SmoothPurity.Adic.AdicPuritySourceFiniteness
import all WeilConjectures.SmoothPurity.Adic.AdicPuritySourceReduction
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import all Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionOfPurity
import WeilConjectures.SmoothPurity.AdicNormalizedPurity.AdicActualSystemsNormalized
import WeilConjectures.SmoothPurity.AdicNormalizedPurity.AdicExceptionalNormalizationMate
import WeilConjectures.SmoothPurity.Normalized.NormalizedDVRTowerEvaluationFull
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityNaturality
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteCoefficientSmoothPurity

/-! # Normalized finite purity and its lift between actual strict towers

Source: blueprint, sec-smooth-purity/sk-thm-purity-transport, integral reconstruction;
current transport proof Step 1 and det-sp-tower-gamma, referenced by the coefficient-change
proof. (blueprint: lem-pur-adic-normalized-purity-lift).

The source is the strict reduction of Lf* K(d)[2d]. The target is the actual exceptional
coefficient system before its derived limit. All evaluation maps and quotient comparisons
below are composites of the recorded canonical maps. Natural number n means exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.AdicNormalizedPurity

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

universe a b va vb

private theorem normalized_comparison_isIso
    {A : Type a} [Category.{va} A] {B : Type b} [Category.{vb} B]
    {F : A ⥤ B} {R S : B ⥤ A} (adj : F ⊣ R) (e : S ≅ R)
    {M M' : A} {N N' : B} (t : M ⟶ S.obj N) (r : F.obj M' ⟶ N')
    (hM : M = M') (hN : N = N')
    (ht : HEq (adj.homEquiv _ _ r) (t ≫ e.hom.app N))
    (hn : ∀ P : B, Function.Bijective (fun v : N ⟶ P ↦ t ≫ S.map v)) :
    IsIso r := by
  subst M' N'
  have ht := eq_of_heq ht
  apply isIso_of_coyoneda_map_bijective
  intro P
  have he : Function.Bijective
      (fun v : M ⟶ S.obj P ↦ v ≫ e.hom.app P) := by
    constructor
    · intro x y hxy
      exact (cancel_mono (e.hom.app P)).mp hxy
    · intro x
      exact ⟨x ≫ e.inv.app P, by simp⟩
  have hc := he.comp (hn P)
  have hw : (fun v : N ⟶ P ↦ (adj.homEquiv _ P) (r ≫ v)) =
      (fun v : N ⟶ P ↦ (t ≫ S.map v) ≫ e.hom.app P) := by
    funext v
    rw [adj.homEquiv_naturality_right, ht]
    simp only [Category.assoc, e.hom.naturality]
  change Function.Bijective (fun v : N ⟶ P ↦ (t ≫ S.map v) ≫ e.hom.app P) at hc
  rw [← hw] at hc
  exact hc.of_comp_left (adj.homEquiv _ P).injective

private theorem heq_postcompose
    {A : Type a} [Category.{va} A] {B : Type b} [Category.{vb} B]
    {R S : B ⥤ A} (e : S ≅ R) {M M' : A} {N N' : B}
    (hM : M = M') (hN : N = N') (t : M ⟶ S.obj N) (t' : M' ⟶ S.obj N')
    (ht : HEq t t') : HEq (t ≫ e.hom.app N) (t' ≫ e.hom.app N') := by
  subst M' N'
  cases ht
  rfl

private theorem transpose_square
    {A : Type a} [Category.{va} A] {B : Type b} [Category.{vb} B]
    {F : A ⥤ B} {R S : B ⥤ A} (adj : F ⊣ R) (e : S ≅ R)
    {U V : A} {U' V' : B} (g : U ⟶ V) (g' : U' ⟶ V')
    (u : F.obj U ⟶ U') (v : F.obj V ⟶ V')
    (tu : U ⟶ S.obj U') (tv : V ⟶ S.obj V')
    (hu : adj.homEquiv _ _ u = tu ≫ e.hom.app U')
    (hv : adj.homEquiv _ _ v = tv ≫ e.hom.app V')
    (hs : F.map g ≫ v = u ≫ g') : g ≫ tv = tu ≫ S.map g' := by
  apply (cancel_mono (e.hom.app V')).mp
  calc
    (g ≫ tv) ≫ e.hom.app V' = g ≫ adj.homEquiv _ _ v := by rw [hv]; simp
    _ = adj.homEquiv _ _ (F.map g ≫ v) :=
      (adj.homEquiv_naturality_left g v).symm
    _ = adj.homEquiv _ _ (u ≫ g') := congrArg _ hs
    _ = (tu ≫ e.hom.app U') ≫ R.map g' := by
      rw [adj.homEquiv_naturality_right, hu]
    _ = (tu ≫ S.map g') ≫ e.hom.app V' := by
      simp only [Category.assoc, e.hom.naturality]

universe c vc am an vm vn

private theorem tower_tau_transport
    {A : Type a} [Category.{va} A]
    {T : Type c} [Category.{vc} T]
    {M : Type am} [Category.{vm} M] {N : Type an} [Category.{vn} N]
    (Fm Fn : T ⥤ A) (t : Fm ⟶ Fn)
    (R : N ⥤ M) (Cm : M ⥤ A) (Cn : N ⥤ A) (e : R ⋙ Cm ≅ Cn)
    {Z Z' : T} {P P' : M} {Q Q' : N}
    (em : Fm.obj Z ⟶ Cm.obj P) (en : Fn.obj Z ⟶ Cn.obj Q)
    (em' : Fm.obj Z' ⟶ Cm.obj P') (en' : Fn.obj Z' ⟶ Cn.obj Q')
    (tau : P ⟶ R.obj Q) (tau' : P' ⟶ R.obj Q')
    (hZ : Z = Z') (hP : P = P') (hQ : Q = Q')
    (hem : HEq em em') (hen : HEq en en') (htau : HEq tau tau')
    (ht : t.app Z ≫ en = em ≫ Cm.map tau ≫ e.hom.app Q) :
    t.app Z' ≫ en' = em' ≫ Cm.map tau' ≫ e.hom.app Q' := by
  subst Z' P' Q'
  cases hem
  cases hen
  cases htau
  exact ht

private theorem lifted_evaluations
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K)
    (U V : NormalizedDVRTower C.l E X D C.different)
    (hU : U.tower = sourceTower D C E f d K)
    (hV : V.tower = targetTower D C E f K)
    (heval : ∀ n : ℕ,
      HEq (U.M n) (purAdicFiniteArrow D C E f d K hK n).left ∧
      HEq (V.M n) (purAdicFiniteArrow D C E f d K hK n).right ∧
      HEq (U.evaluationIso n).hom (sourceEvaluation D C E f d K hK n) ∧
      HEq (V.evaluationIso n).hom (targetEvaluation D C E f d K hK n).hom)
    (htau : ∀ {m n : ℕ} (h : n ≤ m),
      HEq (U.tau h) (purAdicFiniteSourceTransition D C E f d K hK h) ∧
      HEq (V.tau h) (exceptionalTransition D C E f d K hK h))
    (hsquare : ∀ n : ℕ,
      (normalizedDVRResCompleted C.l E X D C.different (n + 1)).map
          (purAdicFiniteArrow D C E f d K hK (n + 1)).hom ≫
        targetRestrictedTransition D C E f d K hK (Nat.le_succ n) =
      sourceRestrictedTransition D C E f d K hK (Nat.le_succ n) ≫
        (normalizedDVRResCompleted C.l E X D C.different n).map
          (purAdicFiniteArrow D C E f d K hK n).hom) :
    ∃ G : sourceTower D C E f d K ⟶ targetTower D C E f K,
      ∀ n : ℕ,
        (normalizedDVRTowerEvaluation C.l E X D C.different n).map G ≫
          (targetEvaluation D C E f d K hK n).hom =
        sourceEvaluation D C E f d K hK n ≫
          (normalizedDVRResCompleted C.l E X D C.different n).map
            (purAdicFiniteArrow D C E f d K hK n).hom := by
  have hsource {m n : ℕ} (h : n ≤ m) :
      (normalizedDVRTowerTransition C.l E X D C.different h).app
          (sourceTower D C E f d K) ≫ sourceEvaluation D C E f d K hK n =
        sourceEvaluation D C E f d K hK m ≫
          sourceRestrictedTransition D C E f d K hK h := by
    dsimp only [sourceRestrictedTransition]
    exact tower_tau_transport
      (normalizedDVRTowerEvaluation C.l E X D C.different m)
      (normalizedDVRTowerEvaluation C.l E X D C.different n)
      (normalizedDVRTowerTransition C.l E X D C.different h)
      (normalizedDVRRes C.l E X h)
      (normalizedDVRResCompleted C.l E X D C.different m)
      (normalizedDVRResCompleted C.l E X D C.different n)
      (normalizedDVRResCompletedComp C.l E X D C.different h)
      _ _ _ _ _ _ hU
      (eq_of_heq (heval m).1) (eq_of_heq (heval n).1)
      (heval m).2.2.1 (heval n).2.2.1 (htau h).1 (U.tower_tau h)
  have htarget {m n : ℕ} (h : n ≤ m) :
      (normalizedDVRTowerTransition C.l E X D C.different h).app
          (targetTower D C E f K) ≫ (targetEvaluation D C E f d K hK n).hom =
        (targetEvaluation D C E f d K hK m).hom ≫
          targetRestrictedTransition D C E f d K hK h := by
    dsimp only [targetRestrictedTransition]
    exact tower_tau_transport
      (normalizedDVRTowerEvaluation C.l E X D C.different m)
      (normalizedDVRTowerEvaluation C.l E X D C.different n)
      (normalizedDVRTowerTransition C.l E X D C.different h)
      (normalizedDVRRes C.l E X h)
      (normalizedDVRResCompleted C.l E X D C.different m)
      (normalizedDVRResCompleted C.l E X D C.different n)
      (normalizedDVRResCompletedComp C.l E X D C.different h)
      _ _ _ _ _ _ hV
      (eq_of_heq (heval m).2.1) (eq_of_heq (heval n).2.1)
      (heval m).2.2.2 (heval n).2.2.2 (htau h).2 (V.tower_tau h)
  let a (n : ℕ) := sourceEvaluation D C E f d K hK n ≫
    (normalizedDVRResCompleted C.l E X D C.different n).map
      (purAdicFiniteArrow D C E f d K hK n).hom ≫
        (targetEvaluation D C E f d K hK n).inv
  have ha (n : ℕ) : a (n + 1) ≫
      (normalizedDVRTowerTransition C.l E X D C.different (Nat.le_succ n)).app
        (targetTower D C E f K) =
      (normalizedDVRTowerTransition C.l E X D C.different (Nat.le_succ n)).app
        (sourceTower D C E f d K) ≫ a n := by
    apply (cancel_mono (targetEvaluation D C E f d K hK n).hom).mp
    dsimp only [a]
    simp only [Category.assoc, htarget, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]
    rw [← Category.assoc _ (sourceEvaluation D C E f d K hK n), hsource]
    simp only [Category.assoc, hsquare]
  obtain ⟨G, hG⟩ := normalizedDVRTowerEvaluation_full C.l E X D C.different
    (sourceTower D C E f d K) (targetTower D C E f K) a ha
  refine ⟨G, fun n ↦ ?_⟩
  rw [hG]
  dsimp only [a]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem finite_square
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) {m n : ℕ} (h : n ≤ m) :
    ((purAdicFiniteSetting D C E m).finiteReduction (n + 1) (Nat.succ_pos n)
      (Nat.add_le_add_right h 1) X).map (purAdicFiniteArrow D C E f d K hK m).hom ≫
        exceptionalNormalization D C E f d K hK h =
      purAdicFiniteSourceNormalization D C E f d K hK h ≫
        (purAdicFiniteArrow D C E f d K hK n).hom := by
  have hs := (purAdicFiniteSourceNormalization_existsUnique D C E f d K hK h).choose_spec.1
  rcases hs with ⟨e, q, he, hq, ht⟩
  cases eq_of_heq he
  cases eq_of_heq hq
  have ht := eq_of_heq ht
  change purAdicFiniteSourceNormalization D C E f d K hK h = _ at ht
  rw [ht]
  dsimp only [exceptionalNormalization, purAdicFiniteArrow, Arrow.mk_left, Arrow.mk_hom]
  rw [← Category.assoc,
    (purAdicFiniteSetting D C E m).finiteReductionOfPurity (n + 1) (Nat.succ_pos n)
      (Nat.add_le_add_right h 1) f d
      ((scalarReductionDerivedExtension C.l E Y m).obj K)
      (purAdicReductionFiniteTor D C E Y K hK m), Category.assoc]
  have hn := ((purAdicFiniteSetting D C E n).smoothPurityMap_naturality_choice_independence
    f d _ _ ((purAdicFiniteSetting D C E m).finiteReduction_preserves_ctf
      (n + 1) (Nat.succ_pos n) (Nat.add_le_add_right h 1) Y _
      (purAdicReductionFiniteTor D C E Y K hK m))
    (purAdicReductionFiniteTor D C E Y K hK n)
    (purAdicQuotientNormalization D C E Y h K)).1
  simpa only [Category.assoc, PurityFiniteSetting.compositionExceptional,
    PurityFiniteSetting.compositionShiftedPullback, PurityFiniteSetting.compositionTwistShift,
    Functor.comp_map, Functor.flip_obj_map] using
    congrArg (fun v ↦ ((purAdicFiniteSetting D C E m).finiteReductionSourceComparison
      (n + 1) (Nat.succ_pos n) (Nat.add_le_add_right h 1) f d
      ((scalarReductionDerivedExtension C.l E Y m).obj K)).hom ≫ v) hn

/-- Finite purity is invertible, compatible with quotient normalizations, and lifts
between the actual normalized strict source and exceptional towers. The equalities
of tower objects retain the systems used in reduction and in defining Rf! K. The
heterogeneous equalities fix their finite objects, evaluation maps, and transitions
without arbitrary endpoint identifications. Only existence of the lift is asserted.

Source: reconstruction proof, compatible comparisons and morphism of normalized systems;
current blueprint transport proof Step 1 and det-sp-tower-gamma
(blueprint: lem-pur-adic-normalized-purity-lift).

Proof plan:
1. Integral constructibility and finite Tor amplitude give finite-Tor constructible
reductions with common bounds. The strict reduction construction and
lem-pur-adic-source-finiteness-reductions identify its finite evaluations by b^U_n.
Conjugating its quotient comparisons gives purAdicFiniteSourceNormalization and its
identity and quotient cocycles, hence the normalized source tower.
2. Retain the actual integralExceptionalSystem. Apply lem-sf-proetale-constructible-origin
at each level and lem-pur-coefficient-system-derived-comparison to its bounded-below input.
The actual right adjoint of lem-pur-etale-coefficient-system-adjoint preserves normalization
and lower bounds. Transport back by exact inverse image and restrict to R_X. This is the
specified targetTower, with its original transitions and canonical targetEvaluation.
3. Its normalization agrees with exceptionalNormalization: both are the adjunction mate
of the same compact-support coefficient comparison followed by the counit. Injectivity
of the Hom bijection, using lem-coef-finite-exceptional and thm-pur-finite-reduction-of-purity,
identifies them. The quotient cocycle follows from the input cocycle and naturality.
4. Apply thm-pur-finite-coefficient-smooth-purity to K_n at every positive exponent.
5. Paste thm-pur-finite-reduction-of-purity with naturality in the input normalization
from prop-pur-smooth-purity-naturality-cover. This gives rho^V red(g_m) = g_n rho^U.
6. Under the tensor-restriction adjunction, transition equals Res(rho) followed after
the unit. Unit naturality transposes the preceding equality to transition compatibility.
Restriction to R_X gives exactly the successive equation in the conclusion.
7. Apply lem-pur-normalized-dvr-tower-evaluation-full (the independent-universe form of
lem-weil-pbc-sequential-tower-evaluation-full) on the pro-etale site
to these actual strict towers and the conjugated restricted finite maps. The successive
equation supplies its hypothesis, yielding G with the specified evaluations. No uniqueness,
natural selection, common stratification or integral local model is used. -/
theorem normalized_purity_lift
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) :
    (∀ n : ℕ, IsIso (purAdicFiniteArrow D C E f d K hK n).hom) ∧
    (∀ {m n : ℕ} (h : n ≤ m),
      IsIso (purAdicFiniteSourceNormalization D C E f d K hK h) ∧
      IsIso (exceptionalNormalization D C E f d K hK h) ∧
      HEq (((purAdicFiniteSetting D C E m).finiteReductionAdjunction (n + 1)
        (Nat.succ_pos n) (Nat.add_le_add_right h 1) X).homEquiv _ _
          (exceptionalNormalization D C E f d K hK h))
        (exceptionalTransition D C E f d K hK h ≫
          (purAdicQuotientRestrictionIso D C E X h).hom.app _) ∧
      ((purAdicFiniteSetting D C E m).finiteReduction (n + 1) (Nat.succ_pos n)
        (Nat.add_le_add_right h 1) X).map (purAdicFiniteArrow D C E f d K hK m).hom ≫
          exceptionalNormalization D C E f d K hK h =
        purAdicFiniteSourceNormalization D C E f d K hK h ≫
          (purAdicFiniteArrow D C E f d K hK n).hom) ∧
    (∃ U V : NormalizedDVRTower C.l E X D C.different,
      U.tower = sourceTower D C E f d K ∧
      V.tower = targetTower D C E f K ∧
      (∀ n : ℕ,
        HEq (U.M n) (purAdicFiniteArrow D C E f d K hK n).left ∧
        HEq (V.M n) (purAdicFiniteArrow D C E f d K hK n).right ∧
        HEq (U.evaluationIso n).hom (sourceEvaluation D C E f d K hK n) ∧
        HEq (V.evaluationIso n).hom (targetEvaluation D C E f d K hK n).hom) ∧
      (∀ {m n : ℕ} (h : n ≤ m),
        HEq (U.tau h) (purAdicFiniteSourceTransition D C E f d K hK h) ∧
        HEq (V.tau h) (exceptionalTransition D C E f d K hK h))) ∧
    (∀ n : ℕ,
      (normalizedDVRResCompleted C.l E X D C.different (n + 1)).map
          (purAdicFiniteArrow D C E f d K hK (n + 1)).hom ≫
        targetRestrictedTransition D C E f d K hK (Nat.le_succ n) =
      sourceRestrictedTransition D C E f d K hK (Nat.le_succ n) ≫
        (normalizedDVRResCompleted C.l E X D C.different n).map
          (purAdicFiniteArrow D C E f d K hK n).hom) ∧
    (∃ G : sourceTower D C E f d K ⟶ targetTower D C E f K,
      ∀ n : ℕ,
        (normalizedDVRTowerEvaluation C.l E X D C.different n).map G ≫
          (targetEvaluation D C E f d K hK n).hom =
        sourceEvaluation D C E f d K hK n ≫
          (normalizedDVRResCompleted C.l E X D C.different n).map
            (purAdicFiniteArrow D C E f d K hK n).hom) := by
  have hsystems := actual_systems_normalized D C E f d K hK
  obtain ⟨U, V, hU, hV, heval, htau⟩ := hsystems
  have hnorm : ∀ {m n : ℕ} (h : n ≤ m),
      IsIso (purAdicFiniteSourceNormalization D C E f d K hK h) ∧
      IsIso (exceptionalNormalization D C E f d K hK h) := by
    intro m n h
    let adj := (purAdicFiniteSetting D C E m).finiteReductionAdjunction (n + 1)
      (Nat.succ_pos n) (Nat.add_le_add_right h 1) X
    let e := purAdicQuotientRestrictionIso D C E X h
    have hu : HEq (adj.homEquiv _ _
        (purAdicFiniteSourceNormalization D C E f d K hK h))
        (purAdicFiniteSourceTransition D C E f d K hK h ≫ e.hom.app _) := by
      dsimp only [purAdicFiniteSourceTransition, e, adj]
      simp only [Category.assoc, Iso.inv_hom_id_app]
      exact (HEq.rfl).trans (heq_of_eq (Category.comp_id _).symm)
    have hv := exceptional_normalization_mate D C E f d K hK h
    constructor
    · exact normalized_comparison_isIso adj e (U.tau h) _
        (eq_of_heq (heval m).1) (eq_of_heq (heval n).1)
        (hu.trans (heq_postcompose e (eq_of_heq (heval m).1)
          (eq_of_heq (heval n).1) _ _ (htau h).1).symm) (U.normalization h)
    · exact normalized_comparison_isIso adj e (V.tau h) _
        (eq_of_heq (heval m).2.1) (eq_of_heq (heval n).2.1)
        (hv.trans (heq_postcompose e (eq_of_heq (heval m).2.1)
          (eq_of_heq (heval n).2.1) _ _ (htau h).2).symm) (V.normalization h)
  have htransition : ∀ {m n : ℕ} (h : n ≤ m),
      (purAdicFiniteArrow D C E f d K hK m).hom ≫
          exceptionalTransition D C E f d K hK h =
        purAdicFiniteSourceTransition D C E f d K hK h ≫
          (normalizedDVRRes C.l E X h).map
            (purAdicFiniteArrow D C E f d K hK n).hom := by
    intro m n h
    apply transpose_square
      ((purAdicFiniteSetting D C E m).finiteReductionAdjunction (n + 1)
        (Nat.succ_pos n) (Nat.add_le_add_right h 1) X)
      (purAdicQuotientRestrictionIso D C E X h)
      _ _ (purAdicFiniteSourceNormalization D C E f d K hK h)
      (exceptionalNormalization D C E f d K hK h)
    · dsimp only [purAdicFiniteSourceTransition]
      simp only [Category.assoc, Iso.inv_hom_id_app]
      exact (Category.comp_id _).symm
    · exact eq_of_heq (exceptional_normalization_mate D C E f d K hK h)
    · exact finite_square D C E f d K hK h
  have hrestricted : ∀ n : ℕ,
      (normalizedDVRResCompleted C.l E X D C.different (n + 1)).map
          (purAdicFiniteArrow D C E f d K hK (n + 1)).hom ≫
        targetRestrictedTransition D C E f d K hK (Nat.le_succ n) =
      sourceRestrictedTransition D C E f d K hK (Nat.le_succ n) ≫
        (normalizedDVRResCompleted C.l E X D C.different n).map
          (purAdicFiniteArrow D C E f d K hK n).hom := by
    intro n
    dsimp only [targetRestrictedTransition, sourceRestrictedTransition]
    rw [← Category.assoc, ← Functor.map_comp, htransition, Functor.map_comp]
    simp only [Category.assoc]
    exact congrArg
      (fun z ↦ (normalizedDVRResCompleted C.l E X D C.different (n + 1)).map
        (purAdicFiniteSourceTransition D C E f d K hK (Nat.le_succ n)) ≫ z)
      ((normalizedDVRResCompletedComp C.l E X D C.different
        (Nat.le_succ n)).hom.naturality (purAdicFiniteArrow D C E f d K hK n).hom)
  refine ⟨?_, ?_, ⟨U, V, hU, hV, heval, htau⟩, hrestricted, ?_⟩
  · intro n
    exact (purAdicFiniteSetting D C E n).isIso_smoothPurityMap f d
      ((scalarReductionDerivedExtension C.l E Y n).obj K)
      (purAdicReductionFiniteTor D C E Y K hK n)
  · intro m n h
    exact ⟨(hnorm h).1, (hnorm h).2,
      exceptional_normalization_mate D C E f d K hK h, finite_square D C E f d K hK h⟩
  · exact lifted_evaluations D C E f d K hK U V hU hV heval htau hrestricted

end WeilConjectures.AdicNormalizedPurity
