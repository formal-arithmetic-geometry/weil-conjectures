/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExceptionalSystemLaws
import WeilConjectures.CategoryTheory.ExchangeMateCube
import WeilConjectures.SecSmoothPurity.ReductionCompatibilities
import WeilConjectures.SecSmoothPurity.ReductionExceptionalChart
import WeilConjectures.SecSmoothPurity.ReductionExceptionalConservativity

/-! # Finite evaluations of the exceptional coefficient transpose

Only the finite comparison and mixed quotient step are asserted here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExceptionalSystem

open FieldShriekSystem
variable (P : PurityFiniteSetting.{u})

attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] FieldShriekSystem.coefficientMap FieldShriekSystem.comparison
attribute [local irreducible] FieldShriekSystem.iso supportEvaluation
attribute [local irreducible] scalarExtensionFunctor
attribute [local irreducible] reductionDirectImageComparison Adjoints

private theorem mate_app_eq
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {S : C ⥤ E} {T : D ⥤ F} (adj : L ⊣ R) (adj' : L' ⊣ R')
    (q : S ⋙ L' ⟶ L ⋙ T) (K : D) :
    (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ q)).app K =
      adj'.homEquiv _ _ (q.app (R.obj K) ≫ T.map (adj.counit.app K)) := by
  apply (adj'.homEquiv _ _).symm.injective
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [Equiv.symm_apply_apply]
  exact mateEquiv_counit adj adj' (TwoSquare.mk _ _ _ _ q) K

private theorem transpose_counit
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {M : C} {K : D} (v : L.obj M ⟶ K) :
    L.map (adj.homEquiv M K v) ≫ adj.counit.app K = v :=
  (adj.homEquiv M K).symm_apply_apply v

attribute [local irreducible] Adjunction.homEquiv

private theorem ell_torsion (E : Index P) (n : ℕ) :
    ∃ a : ℕ, ∀ x : SpTowerShriek.R P.coefficients.l E.val n,
      (P.coefficients.l ^ a) • x = 0 := by
  refine ⟨n + 1, fun x ↦ ?_⟩
  have h : ((P.coefficients.l ^ (n + 1) : ℕ) :
      SpTowerShriek.R P.coefficients.l E.val n) = 0 := by
    have hz := (Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.pow_mem_pow (I := spEllIdeal P.coefficients.l E.val)
        (Ideal.subset_span (Set.mem_singleton
          (P.coefficients.l : Padic.coefficientExtensionIntegers P.coefficients.l E.val)))
        (n + 1)))
    simpa only [map_pow, map_natCast, Nat.cast_pow] using hz
  rw [nsmul_eq_mul, h, zero_mul]

private theorem cube_normalized
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      K'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ.app X) =
        θ'.app (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X))
    (E : B)
    (mF : a.obj (R.obj E) ⟶ R'.obj (b.obj E))
    (mK : c.obj (S.obj (H.obj E)) ⟶ S'.obj (d.obj (H.obj E)))
    (e : G.obj (R.obj E) ⟶ S.obj (H.obj E))
    (e' : G'.obj (R'.obj (b.obj E)) ⟶ S'.obj (H'.obj (b.obj E)))
    (he : (mateEquiv adj adjK (TwoSquare.mk _ _ _ _ θ)).app E = e)
    (he' : (mateEquiv adj' adjK' (TwoSquare.mk _ _ _ _ θ')).app (b.obj E) = e')
    (hF : (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.inv)).app E = mF)
    (hK : (mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv)).app (H.obj E) = mK) :
    c.map e ≫ mK ≫ S'.map (pH.hom.app E) =
      pG.hom.app (R.obj E) ≫ G'.map mF ≫ e' := by
  have h := exchangeMate_cube adj adjK adj' adjK' a b c d pF pG pH pK
    θ θ' hc E
  rw [he, he', hF, hK] at h
  exact h

private theorem conjugation_two
    {C : Type*} [Category C] {X₀ X₁ X₂ Y₀ Y₁ Y₂ : C}
    (s₁ : X₀ ≅ X₁) (s₂ : X₁ ≅ X₂) (t₁ : Y₀ ≅ Y₁) (t₂ : Y₁ ≅ Y₂)
    (x : X₀ ⟶ Y₀) (y : X₂ ⟶ Y₂)
    (h : x ≫ t₁.hom ≫ t₂.hom = s₁.hom ≫ s₂.hom ≫ y) :
    (s₁ ≪≫ s₂).inv ≫ x ≫ (t₁ ≪≫ t₂).hom = y := by
  apply (cancel_epi (s₁ ≪≫ s₂).hom).1
  simp only [Iso.hom_inv_id_assoc]
  simpa only [Iso.trans_hom, Category.assoc] using h

section Geometry
variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of P.field.k))] [IsSeparated f]
  (d : ℕ) [SmoothOfRelativeDimension d f] (c : Compactification f)
  (D : Models P) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
  (A : Adjoints P D c b a)

private theorem finiteSupport_isIso {E F : Index P} {n m : ℕ}
    (φ : SpTowerShriek.R P.coefficients.l E.val n →+*
      SpTowerShriek.R P.coefficients.l F.val m)
    (M : spFiniteConstructibleTorCategory X (SpTowerShriek.R P.coefficients.l E.val n)) :
    IsIso ((reductionDirectImageComparison φ c.i c.g).app M.obj) := by
  classical
  let : Fintype P.field.k₀ := Fintype.ofFinite P.field.k₀
  have : Fact P.field.p.Prime := ⟨P.field.prime⟩
  have : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using
      P.field.card_base.trans P.field.cardinality_eq)
  have : CharP P.field.k P.field.p := charP_of_injective_algebraMap' P.field.k₀ P.field.p
  have hb : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X _)) i).obj M.obj)} := by
    obtain ⟨a, b, _, hab⟩ := M.property.1
    apply (Set.finite_Icc a b).subset
    intro i hi
    exact ⟨le_of_not_gt (fun h ↦ hi (hab i (Or.inl h))),
      le_of_not_gt (fun h ↦ hi (hab i (Or.inr h)))⟩
  exact (reductionDirectImage_isIso P.coefficients.l P.field.p P.field.prime.pos
    (Ne.symm P.coefficients.different) P.field.k f c.i c.g c.comm.symm
    (ell_torsion P E n) (ell_torsion P F m) φ M.obj hb
    M.property.2.1 M.property.2.2).1

private def finiteSupportComparison {E F : Index P} {n m : ℕ}
    (φ : SpTowerShriek.R P.coefficients.l E.val n →+*
      SpTowerShriek.R P.coefficients.l F.val m) :
    reductionCtfCompactSupport _ c.i c.g (A.finite E n).closed ⋙
      reductionCtfScalar φ Y (a.finiteScalar E F n m φ Y (.inr rfl)) ≅
    reductionCtfScalar φ X (a.finiteScalar E F n m φ X (.inl rfl)) ⋙
      reductionCtfCompactSupport _ c.i c.g (A.finite F m).closed :=
  NatIso.ofComponents (fun M ↦ by
    exact ObjectProperty.isoMk _
      (@asIso _ _ _ _ ((reductionDirectImageComparison φ c.i c.g).app M.obj)
        (finiteSupport_isIso P c φ M))) (by
        intro M N v
        apply ObjectProperty.hom_ext
        exact (reductionDirectImageComparison φ c.i c.g).naturality v.hom)

private def finiteComparison {E F : Index P} {n m : ℕ}
    (φ : SpTowerShriek.R P.coefficients.l E.val n →+*
      SpTowerShriek.R P.coefficients.l F.val m) :
    (A.finite E n).right ⋙
        reductionCtfScalar φ X (a.finiteScalar E F n m φ X (.inl rfl)) ⟶
      reductionCtfScalar φ Y (a.finiteScalar E F n m φ Y (.inr rfl)) ⋙
        (A.finite F m).right :=
  (mateEquiv (A.finite E n).adj (A.finite F m).adj
    (TwoSquare.mk _ _ _ _ (finiteSupportComparison P c D b a A φ).inv)).natTrans

attribute [local irreducible] finiteComparison

set_option maxHeartbeats 800000 in
-- Comparing finite transposes checks the dependent subcategory coordinates.
private theorem finiteComparison_app {E F : Index P} {n m : ℕ}
    (φ : SpTowerShriek.R P.coefficients.l E.val n →+*
      SpTowerShriek.R P.coefficients.l F.val m)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R P.coefficients.l E.val n)) :
    (finiteComparison P c D b a A φ).app K = finiteComponent P D c b a A φ K := by
  unfold finiteComparison
  refine (mate_app_eq (A.finite E n).adj (A.finite F m).adj
    (finiteSupportComparison P c D b a A φ).inv K).trans ?_
  unfold finiteComponent
  apply congrArg ((A.finite F m).adj.homEquiv _ _)
  apply ObjectProperty.hom_ext
  rfl

private theorem finiteComponent_counit {E F : Index P} {n m : ℕ}
    (φ : SpTowerShriek.R P.coefficients.l E.val n →+*
      SpTowerShriek.R P.coefficients.l F.val m)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R P.coefficients.l E.val n)) :
    (reductionCompactSupport _ c.i c.g).map (finiteComponent P D c b a A φ K).hom ≫
      ((A.finite F m).adj.counit.app
        ((reductionCtfScalar φ Y (a.finiteScalar E F n m φ Y (.inr rfl))).obj K)).hom =
      @inv _ _ _ _ ((reductionDirectImageComparison φ c.i c.g).app
        ((A.finite E n).right.obj K).obj) (A.finiteIso E F n m φ K) ≫
      (scalarExtensionFunctor φ Y).map ((A.finite E n).adj.counit.app K).hom := by
  unfold finiteComponent
  have ht := transpose_counit (A.finite F m).adj
    (M := (reductionCtfScalar φ X (a.finiteScalar E F n m φ X (.inl rfl))).obj
      ((A.finite E n).right.obj K))
    (K := (reductionCtfScalar φ Y (a.finiteScalar E F n m φ Y (.inr rfl))).obj K)
    (ObjectProperty.homMk
      (@inv _ _ _ _ ((reductionDirectImageComparison φ c.i c.g).app
        ((A.finite E n).right.obj K).obj) (A.finiteIso E F n m φ K) ≫
        (scalarExtensionFunctor φ Y).map ((A.finite E n).adj.counit.app K).hom))
  exact congrArg (fun z ↦ z.hom) ht

attribute [local irreducible] finiteComponent

set_option maxHeartbeats 800000 in
-- Congruence uses the ambient arrow equality without dependent substitution.
private theorem finiteComparison_counit_direct {E F : Index P} {n m : ℕ}
    (φ : SpTowerShriek.R P.coefficients.l E.val n →+*
      SpTowerShriek.R P.coefficients.l F.val m)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R P.coefficients.l E.val n)) :
    (reductionCompactSupport _ c.i c.g).map ((finiteComparison P c D b a A φ).app K).hom ≫
      ((A.finite F m).adj.counit.app
        ((reductionCtfScalar φ Y (a.finiteScalar E F n m φ Y (.inr rfl))).obj K)).hom =
      @inv _ _ _ _ ((reductionDirectImageComparison φ c.i c.g).app
        ((A.finite E n).right.obj K).obj) (A.finiteIso E F n m φ K) ≫
      (scalarExtensionFunctor φ Y).map ((A.finite E n).adj.counit.app K).hom := by
  have he := congrArg (fun z ↦ z.hom) (finiteComparison_app P c D b a A φ K)
  have ht := congrArg (fun z ↦ (reductionCompactSupport _ c.i c.g).map z ≫
    ((A.finite F m).adj.counit.app
      ((reductionCtfScalar φ Y (a.finiteScalar E F n m φ Y (.inr rfl))).obj K)).hom) he
  exact ht.trans (finiteComponent_counit P c D b a A φ K)

set_option maxHeartbeats 800000 in
-- The counit comparison retains both finite adjunctions and preservation witnesses.
private theorem finiteComparison_counit {E F : Index P} {n m : ℕ}
    (φ : SpTowerShriek.R P.coefficients.l E.val n →+*
      SpTowerShriek.R P.coefficients.l F.val m)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R P.coefficients.l E.val n)) :
    (reductionDirectImageComparison φ c.i c.g).app ((A.finite E n).right.obj K).obj ≫
      (reductionCompactSupport _ c.i c.g).map
        ((finiteComparison P c D b a A φ).app K).hom ≫
      ((A.finite F m).adj.counit.app
        ((reductionCtfScalar φ Y (a.finiteScalar E F n m φ Y (.inr rfl))).obj K)).hom =
      (scalarExtensionFunctor φ Y).map ((A.finite E n).adj.counit.app K).hom := by
  have := A.finiteIso E F n m φ K
  have hc := finiteComparison_counit_direct P c D b a A φ K
  have hn := congrArg (fun z ↦
    (reductionDirectImageComparison φ c.i c.g).app ((A.finite E n).right.obj K).obj ≫ z) hc
  exact hn.trans (IsIso.hom_inv_id_assoc _ _)

set_option maxHeartbeats 800000 in
-- The chart and conservativity APIs carry the full finite realization data.
include d in
private theorem finiteComponent_isIso {E F : Index P} {n m : ℕ}
    (φ : SpTowerShriek.R P.coefficients.l E.val n →+*
      SpTowerShriek.R P.coefficients.l F.val m)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R P.coefficients.l E.val n)) :
    IsIso (finiteComponent P D c b a A φ K) := by
  classical
  let : Fintype P.field.k₀ := Fintype.ofFinite P.field.k₀
  have : Fact P.field.p.Prime := ⟨P.field.prime⟩
  have : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using
      P.field.card_base.trans P.field.cardinality_eq)
  have : CharP P.field.k P.field.p := charP_of_injective_algebraMap' P.field.k₀ P.field.p
  have hc := reductionExceptional_chartEquation P.coefficients.l P.field.p
    P.field.prime.pos P.coefficients.different.symm P.field.k f d c.i c.g c.comm.symm
    (ell_torsion P E n) (ell_torsion P F m) φ
    (A.finite E n).closed (A.finite F m).closed
    (a.finiteScalar E F n m φ X (.inl rfl)) (a.finiteScalar E F n m φ Y (.inr rfl))
    (A.finite E n).right (A.finite F m).right (A.finite E n).adj (A.finite F m).adj
    (A.finite E n).realization (A.finite F m).realization
    (finiteComparison P c D b a A φ) (A.finiteIso E F n m φ)
    (finiteComparison_counit_direct P c D b a A φ)
  have hi := reductionExceptional_components_isIso P.coefficients.l P.field.p
    P.field.prime.pos P.coefficients.different.symm P.field.k f d c.i c.g c.comm.symm
    (ell_torsion P E n) (ell_torsion P F m) φ
    (A.finite E n).closed (A.finite F m).closed
    (a.finiteScalar E F n m φ X (.inl rfl)) (a.finiteScalar E F n m φ Y (.inr rfl))
    (A.finite E n).right (A.finite F m).right (A.finite E n).adj (A.finite F m).adj
    (A.finite E n).realization (A.finite F m).realization
    (finiteComparison P c D b a A φ) hc K
  exact (congrArg IsIso (finiteComparison_app P c D b a A φ K)).mp hi

set_option maxHeartbeats 800000 in
-- Composition checks dependent preservation witnesses at three coefficient levels.
include d in
private theorem finiteComposite_eq {E F L : Index P} {n m r : ℕ}
    (φ : SpTowerShriek.R P.coefficients.l E.val n →+*
      SpTowerShriek.R P.coefficients.l F.val m)
    (ψ : SpTowerShriek.R P.coefficients.l F.val m →+*
      SpTowerShriek.R P.coefficients.l L.val r)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R P.coefficients.l E.val n)) :
    HEq (finiteComposite P D c b a A φ ψ K)
      (finiteComponent P D c b a A (ψ.comp φ) K).hom := by
  have hc := reductionCompatibilities_composition P.field P.coefficients.l
    P.coefficients.different f d c (ell_torsion P E n) (ell_torsion P F m) φ
    (ell_torsion P L r) ψ
    (A.finite E n).closed (A.finite F m).closed (A.finite L r).closed
    (a.finiteScalar E F n m φ X (.inl rfl)) (a.finiteScalar E F n m φ Y (.inr rfl))
    (a.finiteScalar F L m r ψ X (.inl rfl)) (a.finiteScalar F L m r ψ Y (.inr rfl))
    (a.finiteScalar E L n r (ψ.comp φ) X (.inl rfl))
    (a.finiteScalar E L n r (ψ.comp φ) Y (.inr rfl))
    (A.finite E n).right (A.finite E n).adj
    (A.finite F m).right (A.finite F m).adj
    (A.finite L r).right (A.finite L r).adj
    (finiteComparison P c D b a A φ) (finiteComparison_counit P c D b a A φ)
    (finiteComparison P c D b a A ψ) (finiteComparison_counit P c D b a A ψ)
    (finiteComparison P c D b a A (ψ.comp φ))
    (finiteComparison_counit P c D b a A (ψ.comp φ)) K
  apply heq_of_eq
  have h := congrArg (fun z ↦
    (scalarExtensionFunctor_composition φ ψ X).inv.app ((A.finite E n).right.obj K).obj ≫ z)
    hc
  have ht := h.trans (Iso.inv_hom_id_app_assoc (scalarExtensionFunctor_composition φ ψ X)
    ((A.finite E n).right.obj K).obj
    ((finiteComparison P c D b a A (ψ.comp φ)).app K).hom)
  simp only [finiteComposite, finiteComparison_app] at ht ⊢
  -- The kernel checks the inferred equality in the displayed full-subcategory coordinates.
  run_tac Lean.Elab.Tactic.withMainContext do
    let some hd := (← Lean.getLCtx).findFromUserName? `ht
      | Lean.throwError "missing composite equality"
    (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

set_option maxHeartbeats 800000 in
-- The coefficient square transports maps with dependent finite coefficient types.
include d in
private theorem component_mixed : mixedLaw P D c b a A := by
  unfold mixedLaw
  intro E F h m n v K
  constructor
  · exact finiteComposite_eq P d c D b a A _ _ K
  · have hs := finiteComposite_eq P d c D b a A
      (SpTowerCalculus.quotient P.coefficients.l E.val v)
      ((D.coefficients E F h).quotient m) K
    exact hs.trans (congr_arg_heq
      (fun φ ↦ (finiteComponent P D c b a A φ K).hom)
      (b.coefficientSquare E F h m n v).symm)

private def supportComparison {E F : Index P} (h : E ≤ F) :
    support P D c a E ⋙ scalar P D a h Y ≅ scalar P D a h X ⋙ support P D c a F :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ ((FieldShriekSystem.iso P D c b h).app M))
    (fun v ↦ by
      apply ObjectProperty.hom_ext
      exact (FieldShriekSystem.iso P D c b h).hom.naturality v)

private def scalarEvaluationIso {E F : Index P} (h : E ≤ F)
    (T : Scheme.{u}) (hT : T = X ∨ T = Y) (n : ℕ) :
    scalar P D a h T hT ⋙ level P D a F T n hT ≅
      level P D a E T n hT ⋙ reductionCtfScalar ((D.coefficients E F h).quotient n)
        T (a.finiteScalar E F n n ((D.coefficients E F h).quotient n) T hT) :=
  by
    refine NatIso.ofComponents (fun K ↦ ?_) ?_
    · exact ObjectProperty.isoMk _
        (X := (level P D a F T n hT).obj ((scalar P D a h T hT).obj K))
        (Y := (reductionCtfScalar ((D.coefficients E F h).quotient n) T
          (a.finiteScalar E F n n ((D.coefficients E F h).quotient n) T hT)).obj
            ((level P D a E T n hT).obj K))
        ((b.scalarEvaluation E F h T n).iso.app K.obj)
    · intro K L v
      apply ObjectProperty.hom_ext
      exact (b.scalarEvaluation E F h T n).iso.hom.naturality v.hom

private theorem inverse_triple {C : Type*} [Category C] {A B C' D E F : C}
    (a : A ≅ B) (b : B ≅ C') (c : C' ≅ D)
    (d : A ≅ E) (e : E ≅ F) (f : F ≅ D)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom ≫ f.hom) :
    c.inv ≫ b.inv ≫ a.inv = f.inv ≫ e.inv ≫ d.inv := by
  have hi : a ≪≫ b ≪≫ c = d ≪≫ e ≪≫ f := Iso.ext h
  simpa only [Iso.trans_inv, Category.assoc] using congrArg Iso.inv hi

set_option maxHeartbeats 800000 in
-- The four comparison isomorphisms retain their dependent evaluation coordinates.
private theorem evaluationCube {E F : Index P} (h : E ≤ F) (n : ℕ)
    (M : N P D E X) :
    (reductionCtfCompactSupport _ c.i c.g (A.finite F n).closed).map
        ((scalarEvaluationIso P c D b a h X (.inl rfl) n).inv.app M) ≫
      (A.leftEvaluation F n).inv.app ((scalar P D a h X).obj M) ≫
      (level P D a F Y n).map ((supportComparison P c D b a h).inv.app M) =
    (finiteSupportComparison P c D b a A ((D.coefficients E F h).quotient n)).inv.app
        ((level P D a E X n).obj M) ≫
      (reductionCtfScalar ((D.coefficients E F h).quotient n) Y
        (a.finiteScalar E F n n ((D.coefficients E F h).quotient n) Y (.inr rfl))).map
          ((A.leftEvaluation E n).inv.app M) ≫
      (scalarEvaluationIso P c D b a h Y (.inr rfl) n).inv.app
        ((support P D c a E).obj M) := by
  have he₀ := A.leftNormalized E n M
  have hf₀ := A.leftNormalized F n ((scalar P D a h X).obj M)
  -- Read both normalizations as equalities; the kernel checks the two arrow types agree.
  run_tac Lean.Elab.Tactic.withMainContext do
    let mut g ← Lean.Elab.Tactic.getMainGoal
    for (src, dst) in [(`he₀, `he), (`hf₀, `hf)] do
      let some hd := (← Lean.getLCtx).findFromUserName? src
        | Lean.throwError "missing left normalization"
      let some (α, x, _, y) := (← Lean.instantiateMVars hd.type).heq?
        | Lean.throwError "left normalization is not a heterogeneous equality"
      let v := Lean.mkApp4 (Lean.mkConst ``eq_of_heq [← Lean.Meta.getLevel α]) α x y hd.toExpr
      let t := Lean.mkApp3 (Lean.mkConst ``Eq [← Lean.Meta.getLevel α]) α x y
      g ← Prod.snd <$> (← g.assert dst t v).intro1P
    Lean.Elab.Tactic.replaceMainGoal [g]
  have hl := congrArg (fun z ↦
    (SpTowerShriek.Ev P.coefficients.l F.val Y n).map
        ((FieldShriekSystem.comparison P D h c).app M.obj) ≫ z ≫
      (reductionCompactSupport (SpTowerShriek.R P.coefficients.l F.val n) c.i c.g).map
        ((b.scalarEvaluation E F h X n).iso.hom.app M.obj)) hf
  have hr := congrArg (fun z ↦
    (b.scalarEvaluation E F h Y n).iso.hom.app
        ((SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj M.obj) ≫
      (scalarExtensionFunctor ((D.coefficients E F h).quotient n) Y).map z ≫
      (reductionDirectImageComparison ((D.coefficients E F h).quotient n) c.i c.g).app
        ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj M.obj)) he
  have hh := hl.trans ((b.evaluation E F h n M.obj).trans hr.symm)
  have hi := inverse_triple
    ((level P D a F Y n).mapIso ((supportComparison P c D b a h).app M))
    ((A.leftEvaluation F n).app ((scalar P D a h X).obj M))
    ((reductionCtfCompactSupport _ c.i c.g (A.finite F n).closed).mapIso
      ((scalarEvaluationIso P c D b a h X (.inl rfl) n).app M))
    ((scalarEvaluationIso P c D b a h Y (.inr rfl) n).app
      ((support P D c a E).obj M))
    ((reductionCtfScalar ((D.coefficients E F h).quotient n) Y
      (a.finiteScalar E F n n ((D.coefficients E F h).quotient n) Y (.inr rfl))).mapIso
      ((A.leftEvaluation E n).app M))
    ((finiteSupportComparison P c D b a A ((D.coefficients E F h).quotient n)).app
      ((level P D a E X n).obj M)) (by
      apply ObjectProperty.hom_ext
      -- The lifted maps have exactly the displayed ambient underlying arrows.
      run_tac Lean.Elab.Tactic.withMainContext do
        let some hd := (← Lean.getLCtx).findFromUserName? `hh
          | Lean.throwError "missing normalized evaluation square"
        (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
        Lean.Elab.Tactic.replaceMainGoal [])
  -- The inverse cube is the displayed one up to the components of mapIso and app.
  run_tac Lean.Elab.Tactic.withMainContext do
    let some hd := (← Lean.getLCtx).findFromUserName? `hi
      | Lean.throwError "missing inverse evaluation square"
    (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

private theorem normalized_mate_app
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {S : C ⥤ E} {T : D ⥤ F} (adj : L ⊣ R) (adj' : L' ⊣ R')
    (q : L ⋙ T ≅ S ⋙ L') (r : R ⋙ S ≅ T ⋙ R')
    (h : AdjunctionEvaluationNormalized adj adj' q r) (K : D) :
    (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ q.inv)).app K = r.hom.app K := by
  unfold AdjunctionEvaluationNormalized at h
  exact congrArg (fun z ↦ z.app K) h

attribute [local irreducible] component sourceEvaluation targetEvaluation

set_option maxHeartbeats 800000 in
-- Identify the whole-system transpose before instantiating the four-adjunction cube.
private theorem wholeComparison_app {E F : Index P} (h : E ≤ F) (K : N P D E Y) :
    (mateEquiv (A.adj E) (A.adj F)
      (TwoSquare.mk _ _ _ _ (supportComparison P c D b a h).inv)).app K =
      component P D c b a A h K := by
  have hm := mate_app_eq (A.adj E) (A.adj F)
    (supportComparison P c D b a h).inv K
  -- The kernel checks the defining ambient transpose of the lifted maps.
  run_tac Lean.Elab.Tactic.withMainContext do
    let some hd := (← Lean.getLCtx).findFromUserName? `hm
      | Lean.throwError "missing whole-system mate identity"
    (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

set_option maxHeartbeats 800000 in
-- Open the packaged finite mate once, keeping its subcategory coordinates fixed.
private theorem finiteMate_app {E F : Index P} {n m : ℕ}
    (φ : SpTowerShriek.R P.coefficients.l E.val n →+*
      SpTowerShriek.R P.coefficients.l F.val m)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R P.coefficients.l E.val n)) :
    (mateEquiv (A.finite E n).adj (A.finite F m).adj
      (TwoSquare.mk _ _ _ _ (finiteSupportComparison P c D b a A φ).inv)).app K =
      finiteComponent P D c b a A φ K := by
  simpa only [finiteComparison] using finiteComparison_app P c D b a A φ K

set_option maxHeartbeats 800000 in
-- The generic cube specializes to four specified exceptional adjunctions.
private theorem rightEvaluationCube {E F : Index P} (h : E ≤ F) (n : ℕ)
    (K : N P D E Y) :
    (level P D a F X n).map (component P D c b a A h K) ≫
        (A.evaluation F n).hom.app ((scalar P D a h Y).obj K) ≫
        (A.finite F n).right.map
          ((scalarEvaluationIso P c D b a h Y (.inr rfl) n).hom.app K) =
      (scalarEvaluationIso P c D b a h X (.inl rfl) n).hom.app ((A.right E).obj K) ≫
        (reductionCtfScalar ((D.coefficients E F h).quotient n) X
          (a.finiteScalar E F n n ((D.coefficients E F h).quotient n) X (.inl rfl))).map
            ((A.evaluation E n).hom.app K) ≫
        finiteComponent P D c b a A ((D.coefficients E F h).quotient n)
          ((level P D a E Y n).obj K) := by
  have h₁ := evaluationCube P c D b a A h n
  have h₂ := wholeComparison_app P c D b a A h K
  have h₃ := finiteMate_app P c D b a A ((D.coefficients E F h).quotient n)
    ((level P D a E Y n).obj K)
  have h₄ := normalized_mate_app _ _ _ _ (A.counit E n) K
  have h₅ := normalized_mate_app _ _ _ _ (A.counit F n) ((scalar P D a h Y).obj K)
  -- Each hypothesis is passed to the cube as is; the kernel checks its displayed type.
  have hr := cube_normalized (A.adj E) (A.adj F)
    (A.finite E n).adj (A.finite F n).adj
    (level P D a E X n) (level P D a E Y n)
    (level P D a F X n) (level P D a F Y n)
    (A.leftEvaluation E n) (scalarEvaluationIso P c D b a h X (.inl rfl) n)
    (scalarEvaluationIso P c D b a h Y (.inr rfl) n) (A.leftEvaluation F n)
    (supportComparison P c D b a h).inv
    (finiteSupportComparison P c D b a A ((D.coefficients E F h).quotient n)).inv
    (by run_tac Lean.Elab.Tactic.withMainContext do
      let some hd := (← Lean.getLCtx).findFromUserName? `h₁
        | Lean.throwError "missing evaluation cube"
      (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
      Lean.Elab.Tactic.replaceMainGoal []) K
    ((A.evaluation E n).hom.app K)
    ((A.evaluation F n).hom.app ((scalar P D a h Y).obj K))
    (component P D c b a A h K)
    (finiteComponent P D c b a A ((D.coefficients E F h).quotient n)
      ((level P D a E Y n).obj K))
    (by run_tac Lean.Elab.Tactic.withMainContext do
      let some hd := (← Lean.getLCtx).findFromUserName? `h₂
        | Lean.throwError "missing whole-system mate"
      (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
      Lean.Elab.Tactic.replaceMainGoal [])
    (by run_tac Lean.Elab.Tactic.withMainContext do
      let some hd := (← Lean.getLCtx).findFromUserName? `h₃
        | Lean.throwError "missing finite mate"
      (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
      Lean.Elab.Tactic.replaceMainGoal [])
    (by run_tac Lean.Elab.Tactic.withMainContext do
      let some hd := (← Lean.getLCtx).findFromUserName? `h₄
        | Lean.throwError "missing source counit normalization"
      (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
      Lean.Elab.Tactic.replaceMainGoal [])
    (by run_tac Lean.Elab.Tactic.withMainContext do
      let some hd := (← Lean.getLCtx).findFromUserName? `h₅
        | Lean.throwError "missing target counit normalization"
      (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
      Lean.Elab.Tactic.replaceMainGoal [])
  run_tac Lean.Elab.Tactic.withMainContext do
    let some hd := (← Lean.getLCtx).findFromUserName? `hr
      | Lean.throwError "missing evaluated cube"
    (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

set_option maxHeartbeats 800000 in
-- Keep the four coordinate isomorphisms separate during the final conjugation.
private theorem component_evaluation : evaluationLaw P D c b a A := by
  unfold evaluationLaw
  intro E F h n K
  have hc := rightEvaluationCube P c D b a A h n K
  have hc' := congrArg (fun z ↦ z.hom) hc
  let s₁ := (b.scalarEvaluation E F h X n).iso.app ((A.right E).obj K).obj
  let s₂ := (scalarExtensionFunctor ((D.coefficients E F h).quotient n) X).mapIso
    ((spFiniteConstructibleTor X (SpTowerShriek.R P.coefficients.l E.val n)).ι.mapIso
      ((A.evaluation E n).app K))
  let t₁ := (spFiniteConstructibleTor X (SpTowerShriek.R P.coefficients.l F.val n)).ι.mapIso
    ((A.evaluation F n).app ((scalar P D a h Y).obj K))
  let t₂ := (spFiniteConstructibleTor X (SpTowerShriek.R P.coefficients.l F.val n)).ι.mapIso
    ((A.finite F n).right.mapIso (ObjectProperty.isoMk _
      (X := (level P D a F Y n).obj ((scalar P D a h Y).obj K))
      (Y := (reductionCtfScalar ((D.coefficients E F h).quotient n) Y
        (a.finiteScalar E F n n ((D.coefficients E F h).quotient n) Y (.inr rfl))).obj
          ((level P D a E Y n).obj K))
      ((b.scalarEvaluation E F h Y n).iso.app K.obj)))
  have hh :
      (SpTowerShriek.Ev P.coefficients.l F.val X n).map
          (component P D c b a A h K).hom ≫ t₁.hom ≫ t₂.hom =
        s₁.hom ≫ s₂.hom ≫
          (finiteComponent P D c b a A ((D.coefficients E F h).quotient n)
            ((level P D a E Y n).obj K)).hom := by
    -- Each restricted map has exactly the underlying arrow of the ambient cube.
    run_tac Lean.Elab.Tactic.withMainContext do
      let some hd := (← Lean.getLCtx).findFromUserName? `hc'
        | Lean.throwError "missing evaluated mate cube"
      (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
      Lean.Elab.Tactic.replaceMainGoal []
  have result := conjugation_two s₁ s₂ t₁ t₂
    ((SpTowerShriek.Ev P.coefficients.l F.val X n).map (component P D c b a A h K).hom)
    (finiteComponent P D c b a A ((D.coefficients E F h).quotient n)
      ((level P D a E Y n).obj K)).hom hh
  -- The two composites are the specified sourceEvaluation and targetEvaluation.
  run_tac Lean.Elab.Tactic.withMainContext do
    let some hd := (← Lean.getLCtx).findFromUserName? `result
      | Lean.throwError "missing conjugated mate equality"
    (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

end Geometry

/-- Evaluation of the actual exceptional transpose is the finite coefficient mate;
that finite mate is invertible and its two mixed quotient composites agree.
This makes no assertion about unit, counit, naturality, composition or identity of
whole-system comparisons, or invertibility of a whole-system arrow.

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2),
finite evaluations and the square of quotient and field coefficient maps.
(blueprint: lem-route-field-exceptional-finite-compatibility).

Proof: Apply evaluation at n to the defining counit equation of component. The
AdjunctionEvaluationNormalized equation of A identifies the tower counit with the
finite counit, while b.scalarEvaluation and b.evaluation identify scalar extension
and the compact-support comparison. A.leftNormalized fixes the same left evaluation
coordinate. Thus the evaluated arrow, conjugated by sourceEvaluation and
targetEvaluation, has the counit transpose defining finiteComponent. Injectivity of
the finite adjunction Hom bijection proves evaluationLaw. The finite adjoints retain
their ordinary-etale counit realizations. Apply reductionExceptional_chartEquation
to these adjoints and the actual finite mate, then apply
reductionExceptional_components_isIso. The counit identity identifies this mate
with finiteComponent, proving the last assertion.
For mixedLaw apply reductionCompatibilities_composition to the field map followed
by the quotient map and to the quotient map followed by the field map. The
finiteComponent counit equations discharge the comparison hypotheses. Both composites
are the direct comparison by injectivity of transposition. The residue-class formula
in D.coefficients proves equality of the two ring maps; transport along that equality
gives the second HEq. The scalar associators are exactly those in finiteComposite.
Equal levels and identity field extensions use the same associators and unitors;
quotient maps need not be flat. All these equalities are in finite derived categories. -/
theorem field_exceptional_finite_compatibility
    (X Y : Scheme.{u}) [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d f] [IsSeparated f] (c : Compactification f)
    (D : Models P) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) :
    evaluationLaw P D c b a A ∧ mixedLaw P D c b a A ∧
      ∀ (E F : Index P) (h : E ≤ F) (n : ℕ)
        (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R P.coefficients.l E.val n)),
        IsIso (finiteComponent P D c b a A ((D.coefficients E F h).quotient n) K) := by
  exact ⟨component_evaluation P c D b a A, component_mixed P d c D b a A,
    fun E F h n K ↦ finiteComponent_isIso P d c D b a A _ K⟩

end AlgebraicGeometry.ProEtale.FieldExceptionalSystem
