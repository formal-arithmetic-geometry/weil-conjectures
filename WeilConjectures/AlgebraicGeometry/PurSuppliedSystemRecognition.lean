/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurIntegralRepresentingPairData
import WeilConjectures.AlgebraicGeometry.CoefficientSingleDegreeEvaluationFaithfulness

/-! # Coordinate representing families

Source: blueprint integral adjunction, coordinate Hom chain and actual counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] WeilConjectures.integralExceptionalSystemDerived
attribute [-instance] WeilConjectures.integralExceptionalLevelDerived
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules
open WeilConjectures AlgebraicGeometry.Scheme
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
private theorem component_hom_ext
    {W : Scheme.{u}} {O : Type (u + 1)} [CommRing O] {t : O}
    {M N : BrownTowerComparison.ProSystem W O t} (f g : M ⟶ N)
    (h : ∀ n, f.app n = g.app n) : f = g := by
  change CoefficientSystem.Hom (J := Scheme.ProEt.topology W) M N at f g
  have hh : f.app = g.app := funext h
  cases f
  cases g
  cases hh
  rfl

private theorem concentrated_of_evaluations
    {W : Scheme.{u}} {O : Type (u + 1)} [CommRing O] {t : O}
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology W) (O := O) (ell := t))
    (K : DerivedCategory (BrownTowerComparison.ProSystem W O t)) (r : ℤ)
    (hK : ∀ n, ((P.evaluation n).obj K).IsGE r ∧
      ((P.evaluation n).obj K).IsLE r) : K.IsGE r ∧ K.IsLE r := by
  let ev (n : ℕ) := coefficientEvaluation (J := Scheme.ProEt.topology W)
    (O := O) (ell := t) n
  have hlim (n : ℕ) : PreservesFiniteLimits (ev n) :=
    (coefficientEvaluation_exact (J := Scheme.ProEt.topology W) (O := O) (ell := t) n).1
  have hcol (n : ℕ) : PreservesFiniteColimits (ev n) :=
    (coefficientEvaluation_exact (J := Scheme.ProEt.topology W) (O := O) (ell := t) n).2
  let ei (n : ℕ) : P.evaluation n ≅ (ev n).mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (BrownTowerComparison.ProSystem W O t) (.up ℤ))
      (DerivedCategory.Q ⋙ P.evaluation n)
      (DerivedCategory.Q ⋙ (ev n).mapDerivedCategory)
      (P.evaluation n) (ev n).mapDerivedCategory
      (P.evaluationFactors n ≪≫ (ev n).mapDerivedCategoryFactors.symm)
  let hi (n : ℕ) (q : ℤ) :
      P.evaluation n ⋙ DerivedCategory.homologyFunctor _ q ≅
        DerivedCategory.homologyFunctor _ q ⋙ ev n :=
    Functor.isoWhiskerRight (ei n) (DerivedCategory.homologyFunctor _ q) ≪≫
      ((ev n).mapDerivedCategoryHomologyFunctorIso q).symm
  have hz (q : ℤ) (hq : q ≠ r) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply component_hom_ext
    intro n
    have hk : IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((P.evaluation n).obj K)) := by
      rcases lt_or_gt_of_ne hq with hqr | hrq
      · exact (DerivedCategory.isGE_iff _ _).1 (hK n).1 q hqr
      · exact (DerivedCategory.isLE_iff _ _).1 (hK n).2 q hrq
    have hn := hk.of_iso ((hi n q).app K).symm
    exact hn.eq_of_src _ _
  exact ⟨(DerivedCategory.isGE_iff K r).2 (fun q hq ↦ hz q (ne_of_lt hq)),
    (DerivedCategory.isLE_iff K r).2 (fun q hq ↦ hz q (ne_of_gt hq))⟩

private theorem normalized_single_iso
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) (r : ℤ) [K.IsGE r] [K.IsLE r] :
    ∃ e : K ≅ (DerivedCategory.singleFunctor C r).obj
        ((DerivedCategory.homologyFunctor C r).obj K),
      (DerivedCategory.homologyFunctor C r).map e.hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C r).hom.app
          ((DerivedCategory.homologyFunctor C r).obj K) = 𝟙 _ := by
  obtain ⟨M, ⟨e⟩⟩ := K.exists_iso_singleFunctor_obj_of_isGE_of_isLE r
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso C r
  let c := (DerivedCategory.homologyFunctor C r).mapIso e ≪≫ ε.app M
  let δ := e ≪≫ (DerivedCategory.singleFunctor C r).mapIso c.symm
  refine ⟨δ, ?_⟩
  have hn := ε.hom.naturality c.inv
  simp only [Functor.comp_map, Functor.id_map] at hn
  dsimp only [δ, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [Functor.map_comp, Category.assoc, hn]
  simpa only [c, Iso.trans_hom, Functor.mapIso_hom, Category.assoc, Iso.app_hom,
    Functor.id_obj] using c.hom_inv_id

private theorem single_map_transformation
    {C B : Type*} [Category* C] [Category* B] [Abelian C] [Abelian B]
    {F G : C ⥤ B} [F.Additive] [G.Additive] (τ : F ⟶ G) (r : ℤ) (M : C) :
    (τ.mapHomologicalComplex (.up ℤ)).app
        ((HomologicalComplex.single C (.up ℤ) r).obj M) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) r).hom.app M =
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) r).hom.app M ≫
      (HomologicalComplex.single B (.up ℤ) r).map (τ.app M) := by
  ext i
  by_cases hi : i = r
  · subst hi
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]
    exact (τ.naturality_assoc _ _).symm
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_tgt _ _

private theorem single_map_composition
    {C B A : Type*} [Category* C] [Category* B] [Category* A]
    [Abelian C] [Abelian B] [Abelian A]
    (F : C ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (r : ℤ) (M : C) :
    (G.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) r).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) r).hom.app (F.obj M) =
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app
        ((HomologicalComplex.single C (.up ℤ) r).obj M) ≫
      (HomologicalComplex.singleMapHomologicalComplex (F ⋙ G) (.up ℤ) r).hom.app M := by
  ext i
  by_cases hi : i = r
  · subst hi
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app,
      Functor.comp_map, Category.id_comp, Functor.map_comp, Category.assoc,
      ← G.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    exact (Category.id_comp _).symm
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_tgt _ _

section SingleEvaluation
variable {W : Scheme.{u}} {O : Type (u + 1)} [CommRing O] {t : O}
  (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2}
    (J := Scheme.ProEt.topology W) (O := O) (ell := t)) (r : ℤ)
local notation "Sys" => BrownTowerComparison.ProSystem W O t
local notation "ev" => coefficientEvaluation (J := Scheme.ProEt.topology W)
  (O := O) (ell := t)
local notation "res" => coefficientRestriction (J := Scheme.ProEt.topology W) O t
local notation "s" => DerivedCategory.singleFunctor
local notation "sc" => HomologicalComplex.single

private def evaluation_single_iso (n : ℕ) (M : Sys) :
    (P.evaluation n).obj ((s Sys r).obj M) ≅ (s _ r).obj ((ev n).obj M) :=
  (P.evaluationFactors n).app ((sc Sys (.up ℤ) r).obj M) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (ev n) (.up ℤ) r).app M)

private def restriction_single_iso {m n : ℕ} (h : n ≤ m)
    (M : coefficientLevelModules (J := Scheme.ProEt.topology W) O t n) :
    (P.scalar h).restriction.obj ((s _ r).obj M) ≅ (s _ r).obj ((res h).obj M) :=
  (P.scalar h).restrictionFactors.app ((sc _ (.up ℤ) r).obj M) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (res h) (.up ℤ) r).app M)

private theorem evaluation_single_naturality (n : ℕ) {M N : Sys} (a : M ⟶ N) :
    (P.evaluation n).map ((s Sys r).map a) ≫ (evaluation_single_iso P r n N).hom =
      (evaluation_single_iso P r n M).hom ≫ (s _ r).map ((ev n).map a) := by
  have hn := (P.evaluationFactors n).hom.naturality ((sc Sys (.up ℤ) r).map a)
  have hs := (HomologicalComplex.singleMapHomologicalComplex (ev n) (.up ℤ) r).hom.naturality a
  dsimp only [evaluation_single_iso, Iso.trans_hom, Functor.mapIso_hom]
  change _ ≫ _ ≫ _ = _ ≫ _
  erw [reassoc_of% hn]
  rw [← DerivedCategory.Q.map_comp]
  erw [hs]
  rw [DerivedCategory.Q.map_comp]
  simp only [Category.assoc, Iso.app_hom]
  rfl

private theorem restriction_single_naturality {m n : ℕ} (h : n ≤ m)
    {M N : coefficientLevelModules (J := Scheme.ProEt.topology W) O t n} (a : M ⟶ N) :
    (P.scalar h).restriction.map ((s _ r).map a) ≫
        (restriction_single_iso P r h N).hom =
      (restriction_single_iso P r h M).hom ≫ (s _ r).map ((res h).map a) := by
  have hn := (P.scalar h).restrictionFactors.hom.naturality
    ((sc _ (.up ℤ) r).map a)
  have hs := (HomologicalComplex.singleMapHomologicalComplex (res h) (.up ℤ) r).hom.naturality a
  dsimp only [restriction_single_iso, Iso.trans_hom, Functor.mapIso_hom]
  erw [reassoc_of% hn]
  rw [← DerivedCategory.Q.map_comp]
  erw [hs]
  rw [DerivedCategory.Q.map_comp]
  simp only [Category.assoc, Iso.app_hom]
  rfl

private theorem transition_single {m n : ℕ} (h : n ≤ m) (M : Sys) :
    (P.transition h).app ((s Sys r).obj M) ≫
        (P.scalar h).restriction.map (evaluation_single_iso P r n M).hom ≫
        (restriction_single_iso P r h ((ev n).obj M)).hom =
      (evaluation_single_iso P r m M).hom ≫
        (s _ r).map ((P.strictTransition h).app M) := by
  have hn := (P.scalar h).restrictionFactors.hom.naturality
    ((HomologicalComplex.singleMapHomologicalComplex (ev n) (.up ℤ) r).hom.app M)
  have ht := P.transition_rep h ((sc Sys (.up ℤ) r).obj M)
  have hs := single_map_transformation (P.strictTransition h) r M
  have hc := single_map_composition (ev n) (res h) r M
  simp only [evaluation_single_iso, restriction_single_iso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  erw [reassoc_of% ht]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  erw [hc]
  have hid : (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ev n ⋙ res h)) (.up ℤ)).inv.app
      ((sc Sys (.up ℤ) r).obj M) = 𝟙 _ := rfl
  rw [hid, Category.id_comp, ← Category.assoc, hs, DerivedCategory.Q.map_comp]
  simp only [Category.assoc]
  rfl

set_option maxHeartbeats 1200000 in
-- The transition calculation elaborates the full coefficient-system interface.
private theorem lift_single_family (M N : Sys)
    (p : ∀ n, (P.evaluation n).obj ((s Sys r).obj M) ⟶
      (P.evaluation n).obj ((s Sys r).obj N))
    (hp : ∀ (m n : ℕ) (h : n ≤ m),
      (P.transition h).app ((s Sys r).obj M) ≫ (P.scalar h).restriction.map (p n) =
        p m ≫ (P.transition h).app ((s Sys r).obj N)) :
    ∃ f : M ⟶ N, ∀ n, (P.evaluation n).map ((s Sys r).map f) = p n := by
  classical
  let a (n : ℕ) : (ev n).obj M ⟶ (ev n).obj N := (s _ r).preimage
    ((evaluation_single_iso P r n M).inv ≫ p n ≫
      (evaluation_single_iso P r n N).hom)
  have ha (n : ℕ) :
      (evaluation_single_iso P r n M).hom ≫ (s _ r).map (a n) =
        p n ≫ (evaluation_single_iso P r n N).hom := by
    dsimp only [a]
    rw [Functor.map_preimage]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hc (n : ℕ) : a (n + 1) ≫ N.transition n =
      M.transition n ≫ (res (Nat.le_succ n)).map (a n) := by
    apply (s _ r).map_injective
    apply (cancel_epi (evaluation_single_iso P r (n + 1) M).hom).1
    simp only [Functor.map_comp]
    have htM := transition_single P r (Nat.le_succ n) M
    have htN := transition_single P r (Nat.le_succ n) N
    rw [P.transitionsNormalized.2.1] at htM htN
    calc
      _ = p (n + 1) ≫ (evaluation_single_iso P r (n + 1) N).hom ≫
          (s _ r).map (N.transition n) := by rw [← Category.assoc, ha, Category.assoc]
      _ = p (n + 1) ≫ (P.transition (Nat.le_succ n)).app ((s Sys r).obj N) ≫
          (P.scalar (Nat.le_succ n)).restriction.map
            (evaluation_single_iso P r n N).hom ≫
          (restriction_single_iso P r (Nat.le_succ n) ((ev n).obj N)).hom := by
        rw [← htN]
      _ = (P.transition (Nat.le_succ n)).app ((s Sys r).obj M) ≫
          (P.scalar (Nat.le_succ n)).restriction.map (p n) ≫
          (P.scalar (Nat.le_succ n)).restriction.map
            (evaluation_single_iso P r n N).hom ≫
          (restriction_single_iso P r (Nat.le_succ n) ((ev n).obj N)).hom := by
        rw [← Category.assoc, ← Category.assoc, ← hp]
        simp only [Category.assoc]
      _ = (P.transition (Nat.le_succ n)).app ((s Sys r).obj M) ≫
          (P.scalar (Nat.le_succ n)).restriction.map
            (evaluation_single_iso P r n M).hom ≫
          (P.scalar (Nat.le_succ n)).restriction.map ((s _ r).map (a n)) ≫
          (restriction_single_iso P r (Nat.le_succ n) ((ev n).obj N)).hom := by
        rw [← Functor.map_comp_assoc, ← ha, Functor.map_comp]
        simp only [Category.assoc]
      _ = (P.transition (Nat.le_succ n)).app ((s Sys r).obj M) ≫
          (P.scalar (Nat.le_succ n)).restriction.map
            (evaluation_single_iso P r n M).hom ≫
          (restriction_single_iso P r (Nat.le_succ n) ((ev n).obj M)).hom ≫
          (s _ r).map ((res (Nat.le_succ n)).map (a n)) := by
        rw [restriction_single_naturality]
      _ = _ := by rw [reassoc_of% htM]
  let f : M ⟶ N := { app := a, comm := hc }
  refine ⟨f, fun n ↦ ?_⟩
  apply (cancel_mono (evaluation_single_iso P r n N).hom).1
  rw [evaluation_single_naturality]
  exact ha n

private theorem system_iso_of_components {M N : Sys} (f : M ⟶ N)
    (hf : ∀ n, IsIso (f.app n)) : IsIso f := by
  let := hf
  let g : N ⟶ M :=
    { app := fun n ↦ inv (f.app n)
      comm := fun n ↦ by
        apply (cancel_epi (f.app (n + 1))).1
        simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
        rw [f.comm]
        simp only [Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id]
        change _ = _ ≫ (res (Nat.le_succ n)).map (𝟙 _)
        rw [CategoryTheory.Functor.map_id, Category.comp_id] }
  refine ⟨g, ?_, ?_⟩
  · apply component_hom_ext
    intro n
    exact IsIso.hom_inv_id _
  · apply component_hom_ext
    intro n
    exact IsIso.inv_hom_id _

end SingleEvaluation

namespace WeilConjectures.PurIntegralRepresentingPair
open PurIntegralSupportComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)
  (G : EtaleTowerBrownAdjunction S) (H : BrownTowerComparison.FiniteEvaluation S G)
  (D : BrownTowerComparison.TransportData S G H)

set_option maxHeartbeats 1200000 in
-- The supplied geometric data has a large derived-system interface.
/-- The supplied evaluations and transition squares determine the normalized
whole-system comparison, in either recognition mode.
Source: blueprint sk-prop-sp-integral-adjunction, recognition in its Hom chain;
Stacks 06XS and 08J5 (blueprint: lem-pur-supplied-system-recognition).

Proof: in the first mode use the specified isomorphism; normalization fixes it.
In the second mode the level maps are isomorphisms between objects concentrated
in the common degree r. The exact evaluation homology comparisons detect that
both whole systems are concentrated in r. Conjugating H^r of each level map by
these comparisons gives the components of a strict-system map; cohomology of the
supplied transition squares gives its transition condition. Component inverses
satisfy that condition as well, so it is an isomorphism. Normalize the two shifted
heart identifications to induce the identity on H^r, then conjugate the single
image of this cohomology isomorphism by those identifications. Exact-functor
compatibility and full faithfulness of the shifted heart give its prescribed
evaluations. They also prove uniqueness of its hom, hence of the isomorphism.
No faithfulness on maps of arbitrary unbounded derived systems is used. -/
theorem suppliedSystemRecognition
    (RX : CoefficientDerivedSystemCalculus l E X)
    (RY : CoefficientDerivedSystemCalculus l E Y)
    (L : CondensedERealization.Integral l E Y)
    (A : Supplied l E RX RY S G H D L) :
    ∃! theta : A.system ≅
        (brown l E S G H D).obj ((reduction l E Y RY).obj L.obj),
      (∀ n, (D.siteX.proEvaluation.evaluation n).map theta.hom =
        levelMap l E RY S G H D L A.system A.phi n) ∧
      SingleDegreeNormalization l E RX RY S G H D L A theta := by
  classical
  cases hrec : A.recognition with
  | inl z =>
    refine ⟨z.val, ⟨z.property, ?_⟩, ?_⟩
    · simp only [SingleDegreeNormalization, hrec]
    · intro theta htheta
      simpa only [SingleDegreeNormalization, hrec] using htheta.2
  | inr z =>
    let P := D.siteX.proEvaluation
    let N := (brown l E S G H D).obj ((reduction l E Y RY).obj L.obj)
    let psi (n : ℕ) : (P.evaluation n).obj A.system ≅ (P.evaluation n).obj N :=
      A.phi n ≪≫ (D.evaluation n).symm.app ((reduction l E Y RY).obj L.obj)
    have hpsi (n : ℕ) : (psi n).hom =
        levelMap l E RY S G H D L A.system A.phi n := rfl
    have hN (n : ℕ) : ((P.evaluation n).obj N).IsGE z.val ∧
        ((P.evaluation n).obj N).IsLE z.val := by
      let := (z.property n).1
      let := (z.property n).2
      exact ⟨DerivedCategory.TStructure.t.isGE_of_iso (psi n) z.val,
        DerivedCategory.TStructure.t.isLE_of_iso (psi n) z.val⟩
    obtain ⟨hVge, hVle⟩ := concentrated_of_evaluations P A.system z.val z.property
    obtain ⟨hNge, hNle⟩ := concentrated_of_evaluations P N z.val hN
    let := hVge
    let := hVle
    let := hNge
    let := hNle
    obtain ⟨deltaV, hdV⟩ := normalized_single_iso A.system z.val
    obtain ⟨deltaN, hdN⟩ := normalized_single_iso N z.val
    let p (n : ℕ) := (P.evaluation n).map deltaV.inv ≫ (psi n).hom ≫
      (P.evaluation n).map deltaN.hom
    have hp (m n : ℕ) (h : n ≤ m) :
        (P.transition h).app _ ≫ (P.scalar h).restriction.map (p n) =
          p m ≫ (P.transition h).app _ := by
      dsimp only [p]
      simp only [Functor.map_comp, Category.assoc]
      have hv := (P.transition h).naturality deltaV.inv
      have hn := (P.transition h).naturality deltaN.hom
      dsimp only [Functor.comp_map] at hv hn
      rw [← reassoc_of% hv]
      change _ ≫ ((P.transition h).app A.system ≫ _ ≫ _) = _
      rw [reassoc_of% (show (P.transition h).app A.system ≫
          (P.scalar h).restriction.map (psi n).hom =
          (psi m).hom ≫ (P.transition h).app N from A.transition m n h)]
      rw [hn]
    obtain ⟨a, ha⟩ := lift_single_family P z.val
      ((DerivedCategory.homologyFunctor _ z.val).obj A.system)
      ((DerivedCategory.homologyFunctor _ z.val).obj N) p hp
    have hai (n : ℕ) : IsIso (a.app n) := by
      have hn := ha n
      have hs := evaluation_single_naturality P z.val n a
      rw [hn] at hs
      have heq : (DerivedCategory.singleFunctor _ z.val).map (a.app n) =
          (evaluation_single_iso P z.val n _).inv ≫ p n ≫
            (evaluation_single_iso P z.val n _).hom := by
        apply (cancel_epi (evaluation_single_iso P z.val n _).hom).1
        simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
        exact hs.symm
      have : IsIso ((DerivedCategory.singleFunctor _ z.val).map (a.app n)) := by
        rw [heq]
        dsimp only [p]
        infer_instance
      exact isIso_of_reflects_iso (a.app n) (DerivedCategory.singleFunctor _ z.val)
    let := system_iso_of_components a hai
    let theta := deltaV ≪≫
      (DerivedCategory.singleFunctor _ z.val).mapIso (asIso a) ≪≫ deltaN.symm
    have heval (n : ℕ) : (P.evaluation n).map theta.hom =
        levelMap l E RY S G H D L A.system A.phi n := by
      dsimp only [theta, Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.symm_hom]
      rw [Functor.map_comp, Functor.map_comp, ha]
      simp only [p, Category.assoc]
      rw [← Functor.map_comp, deltaN.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.comp_id]
      rw [← Functor.map_comp_assoc, deltaV.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
      exact hpsi n
    refine ⟨theta, ⟨heval, ?_⟩, ?_⟩
    · simp only [SingleDegreeNormalization, hrec]
      exact ⟨asIso a, deltaV, deltaN, hdV, hdN, rfl⟩
    · intro theta' htheta'
      apply Iso.ext
      exact singleDegreeEvaluation_hom_ext X _ _ P A.system N z.val z.property hN
        (fun n ↦ (htheta'.1 n).trans (heval n).symm)

end WeilConjectures.PurIntegralRepresentingPair
