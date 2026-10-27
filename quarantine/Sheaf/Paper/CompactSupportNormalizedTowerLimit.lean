/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y8
-/
module

public import Sheaf.Paper.CompactSupportFiniteAction
public import Sheaf.Paper.CoefficientRingedSequenceSite
import all Sheaf.Paper.CompactSupportRepresentativeIndependence

/-! # Normalized total limit of the chosen compact-support tower

Source: Bhatt--Scholze Definition 6.7.6; the strict-tower realization of
lem-weil-compact-support-representative-independence.
(blueprint: lem-pod-compact-support-normalized-tower-limit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [local irreducible] HasDerivedCategory.standard
attribute [instance 5000] WeilConjectures.integralTowerHasDerivedCategory

universe u uC vC uD vD uV vV uW vW
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem whiskeredComparison_heq
    {C : Type uC} {D : Type uD} {V : Type uV} {W : Type uW}
    [Category.{vC} C] [Category.{vD} D] [Category.{vV} V] [Category.{vW} W]
    (i : C ⥤ D) (T : D ⥤ V) {RF L : V ⥤ W} {F : C ⥤ W}
    (γ : F ≅ i ⋙ T ⋙ RF) (ζ : RF ≅ L)
    {Ev : V ⥤ W} (p : L ⟶ Ev) (π : RF ⟶ Ev)
    (hp : ζ.hom ≫ p = π) (K : C) {B : W}
    (e : Ev.obj (T.obj (i.obj K)) ⟶ B) {α : Type vW} (r : α)
    (hr : HEq (γ.hom.app K ≫ π.app (T.obj (i.obj K)) ≫ e) r) :
    HEq ((γ ≪≫ Functor.isoWhiskerLeft i (Functor.isoWhiskerLeft T ζ)).hom.app K ≫
      p.app (T.obj (i.obj K)) ≫ e) r := by
  change HEq ((γ.hom.app K ≫ ζ.hom.app (T.obj (i.obj K))) ≫
    p.app (T.obj (i.obj K)) ≫ e) r
  have h := congrArg (fun a ↦ a.app (T.obj (i.obj K))) hp
  dsimp only [NatTrans.comp_app] at h
  rw [← Category.assoc,
    Category.assoc (γ.hom.app K) (ζ.hom.app (T.obj (i.obj K)))
      (p.app (T.obj (i.obj K))), h, Category.assoc]
  exact hr

private theorem rightDerived_transport
    {C D H : Type*} [Category C] [Category D] [Category H]
    (L : C ⥤ D) (F : C ⥤ H) (W : MorphismProperty C) [L.IsLocalization W]
    (RF RF' : D ⥤ H) (η : F ⟶ L ⋙ RF) (η' : F ⟶ L ⋙ RF')
    (hr : RF = RF') (hη : HEq η η')
    (hd : RF'.IsRightDerivedFunctor η' W) : RF.IsRightDerivedFunctor η W := by
  subst RF'
  cases eq_of_heq hη
  exact hd

private theorem normalizedLimitComparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : Scheme.{u})
    (RF : coefficientSequenceRestrictedDerived l E Y ⥤
      DerivedCategory (scalarReductionSource l E Y))
    (η : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤
        scalarReductionSource l E Y).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF)
    (hd : RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso _ (.up ℤ)))
    (π : ∀ n : ℕ, RF ⟶ pbcTowerEvaluation Y
      (completedIntegralCommRingSheafUnrestricted l E Y) n)
    (hπ : ∀ (n : ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ℤ),
      η.app I ≫ (π n).app (DerivedCategory.Q.obj I) ≫
          (coefficientConstantTowerEvaluationFactors l E Y n).hom.app I =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (lim.π (Opposite.op n)) (.up ℤ)).app I)) :
    ∃ ζ : RF ≅ coefficientConstantTowerLimit l E Y,
      ∀ n, ζ.hom ≫ coefficientConstantTowerProjection l E Y n = π n := by
  let := hd
  let U := (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤ scalarReductionSource l E Y)
  have := canonicalDerivedUnit_isDerived U
  let ζ : RF ≅ coefficientConstantTowerLimit l E Y :=
    Functor.rightDerivedUnique RF U.rightDerivedFunctor η (canonicalDerivedUnit U)
      (HomologicalComplex.quasiIso _ (.up ℤ))
  have hz (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ℤ) :
      η.app I ≫ ζ.hom.app (DerivedCategory.Q.obj I) = (canonicalDerivedUnit U).app I := by
    dsimp only [ζ, coefficientConstantTowerLimit, U]
    simpa only [Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom, Iso.refl_hom,
      Category.id_comp, NatTrans.id_app] using
      Functor.rightDerivedNatTrans_app RF U.rightDerivedFunctor η
        (canonicalDerivedUnit U) (HomologicalComplex.quasiIso _ (.up ℤ)) (𝟙 _) I
  refine ⟨ζ, fun n ↦ ?_⟩
  apply NatTrans.ext
  funext K
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  have := hI
  have hu : IsIso ((canonicalDerivedUnit U).app I) := by
    dsimp [canonicalDerivedUnit]
    infer_instance
  have : IsIso (η.app I ≫ ζ.hom.app (DerivedCategory.Q.obj I)) := by
    rw [hz]
    exact hu
  have : IsIso (η.app I) := IsIso.of_isIso_comp_right _ (ζ.hom.app _)
  have hq : (ζ.hom ≫ coefficientConstantTowerProjection l E Y n).app
        (DerivedCategory.Q.obj I) = (π n).app (DerivedCategory.Q.obj I) := by
    apply (cancel_epi (η.app I)).1
    apply (cancel_mono
      ((coefficientConstantTowerEvaluationFactors l E Y n).hom.app I)).1
    simp only [NatTrans.comp_app, ← Category.assoc, hz]
    have hpr := (coefficientConstantTowerProjection_exists l E Y n).choose_spec.1 I
    change (coefficientConstantTowerProjection l E Y n).app
      (DerivedCategory.Q.obj I) ≫
        (coefficientConstantTowerEvaluationFactors l E Y n).hom.app I = _ at hpr
    rw [Category.assoc, Category.assoc, hpr,
      ← Category.assoc, canonicalDerivedUnit_objIso U I, Category.id_comp]
    exact (hπ n I).symm
  apply (cancel_mono ((coefficientConstantTowerEvaluation l E Y n).map e.hom)).1
  rw [← (ζ.hom ≫ coefficientConstantTowerProjection l E Y n).naturality, hq]
  simpa only [coefficientConstantTowerEvaluation, pbcTowerEvaluation] using
    (π n).naturality e.hom

/-- The published integral action is the normalized coefficient total limit of its
chosen strict tower, retaining its original Roos projections.
Source: Bhatt--Scholze Definition 6.7.6; blueprint raw-rational reconstruction step 3.
(blueprint: lem-pod-compact-support-normalized-tower-limit).

Proof: project the integral realization from sfCompactSupportFiniteRealization.
Its specification supplies the chosen tower, its evaluation isomorphisms, and a
comparison gamma to its right-derived total limit RF with the required Roos
projections. The equalities hT and he identify exactly that tower and those
isomorphisms; no levelwise choices are changed. Both RF and
coefficientConstantTowerLimit are right-derived functors of ordinary inverse limit.
The uniqueness comparison of right-derived functors is normalized by their units.
On a K-injective strict tower its composite with each coefficient limit projection
is the original RF projection, by the two unit-projection equations. The uniqueness
of coefficientConstantTowerProjection extends this equation to all derived towers.
Whisker the comparison by T and the constructible inclusion and compose with gamma.
Substituting the projection equation in gamma's normalization proves the displayed
Roos equation, without uniqueness of a bare cone in a triangulated category. -/
theorem compactSupportNormalizedTowerLimit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (K₀ : Type u) [Field K₀] (hk : IsUnit (l : K₀))
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (T : DerivedCategory (scalarReductionSource l E X) ⥤
      coefficientSequenceRestrictedDerived l E Y)
    (e : ∀ n : ℕ, T ⋙ coefficientConstantTowerEvaluation l E Y n ≅
      compactSupportRestrictedLevel l E c n)
    (hT : T = Classical.choose (Classical.choose_spec (Classical.choose_spec
      (exists_compactSupportReductionTower l E K₀ X Y f hk c))).2.2)
    (he : HEq e (Classical.choose (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (exists_compactSupportReductionTower l E K₀ X Y f hk c))).2.2).2).2)) :
    ∃ ρ : sfCompactSupportFiniteIntegralFunctor l K₀ hk c E ⋙
        (sfIntegralConstructible l E Y).ι ≅
      (sfIntegralConstructible l E X).ι ⋙ T ⋙ coefficientConstantTowerLimit l E Y,
      ∀ (C : sfIntegralConstructibleCategory l E X) (n : ℕ),
        HEq (ρ.hom.app C ≫
            (coefficientConstantTowerProjection l E Y n).app (T.obj C.obj) ≫
              (e n).hom.app C.obj)
          (Classical.choose (Classical.choose_spec
            (exists_isDerivedLimit_and_iso (sfCompactSupportTerm l E c C.obj)
              (sfCompactSupportTransition l E c C.obj)).1) ≫
            Pi.π (sfCompactSupportTerm l E c C.obj) n) := by
  classical
  let H := exists_compactSupportRepresentativeComparison l E K₀ hk X Y f c
  let Tr := H.choose
  let er := H.choose_spec.choose
  let HR := H.choose_spec.choose_spec.2.2
  let RF := HR.choose
  let η := HR.choose_spec.choose
  let HP := HR.choose_spec.choose_spec.2.2
  let π := HP.choose
  have hTr := H.choose_spec.choose_spec.1
  have her := H.choose_spec.choose_spec.2.1
  have hF : SfCompactSupportFiniteRealizationSpec l K₀ hk c E
      (sfCompactSupportFiniteIntegralFunctor l K₀ hk c E) := by
    unfold sfCompactSupportFiniteIntegralFunctor
    exact (sfCompactSupportFiniteRealization l K₀ hk c E).choose_spec
  let γType := sfCompactSupportFiniteIntegralFunctor l K₀ hk c E ⋙
    (sfIntegralConstructible l E Y).ι ≅
      (sfIntegralConstructible l E X).ι ⋙ Tr ⋙ RF
  -- Project the large realization predicate without re-elaborating its telescope.
  run_tac Lean.Elab.Tactic.withMainContext do
    let mut h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `hF) none
    let mut ty ← Lean.Meta.inferType h
    for right in [true, true, true, false] do
      ty ← Lean.Meta.whnf ty
      let args := ty.getAppArgs
      unless ty.isAppOfArity ``And 2 do
        throwError "expected a realization conjunct"
      h := Lean.mkAppN (Lean.mkConst (if right then ``And.right else ``And.left))
        #[args[0]!, args[1]!, h]
      ty := args[if right then 1 else 0]!
    ty ← Lean.Meta.whnf ty
    unless ty.isAppOfArity ``Exists 2 do
      throwError "expected the normalized realization isomorphism"
    let args := ty.getAppArgs
    let levels := [← Lean.Meta.getLevel args[0]!]
    let witness := Lean.mkAppN (Lean.mkConst ``Exists.choose levels)
      #[args[0]!, args[1]!, h]
    let spec := Lean.mkAppN (Lean.mkConst ``Exists.choose_spec levels)
      #[args[0]!, args[1]!, h]
    let gtype ← Lean.Elab.Term.elabTerm (Lean.mkIdent `γType) none
    let (gvar, goal) ← (← (← Lean.Elab.Tactic.getMainGoal).define `γ
      gtype witness).intro1P
    let (_, goal) ← goal.note `hγ spec (args[1]!.beta #[Lean.mkFVar gvar])
    Lean.Elab.Tactic.replaceMainGoal [goal]
  let hR := @ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u + 1}
    Y.ProEt inferInstance (ProEt.topology Y) inferInstance inferInstance
    ((adicLisseForget Y).obj (completedIntegralCommRingSheafUnrestricted l E Y))
    (fun U a b ↦ @mul_comm
      ((completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U) inferInstance a b)
    (scalarReductionSourceDerived l E Y)
    (pbcTowers_hasDerivedCategory Y (completedIntegralCommRingSheafUnrestricted l E Y))
  have hr : RF = hR.choose := HR.choose_spec.choose_spec.1
  have hη : HEq η hR.choose_spec.choose := HR.choose_spec.choose_spec.2.1
  have hd : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso _ (.up ℤ)) :=
    rightDerived_transport DerivedCategory.Q _
      (HomologicalComplex.quasiIso _ (.up ℤ)) RF hR.choose η hR.choose_spec.choose hr hη
      hR.choose_spec.choose_spec.1
  have hπ := HP.choose_spec.1
  -- The arguments have already been typed by the recorded realization. Construct
  -- the application directly, avoiding repeated reduction of its large telescope.
  run_tac Lean.Elab.Tactic.withMainContext do
    let eE ← Lean.Elab.Term.elabTerm (Lean.mkIdent `E) none
    let .succ level := (← Lean.Meta.getLevel eE).normalize
      | throwError "expected a coefficient type universe"
    let mut app := Lean.mkConst ``normalizedLimitComparison [level]
    let mut ty ← Lean.Meta.inferType app
    let mut names := [`l, `E, `Y, `RF, `η, `hd, `π, `hπ]
    while let .forallE _ domain body bi := ty do
      let arg ← if bi.isInstImplicit then Lean.Meta.synthInstance domain else do
        let name :: rest := names | throwError "unexpected comparison parameter"
        names := rest
        Lean.Elab.Term.elabTerm (Lean.mkIdent name) none
      app := Lean.mkApp app arg
      ty := body.instantiate1 arg
    unless names.isEmpty do
      throwError "missing comparison parameter"
    let (_, goal) ← (← Lean.Elab.Tactic.getMainGoal).note `hlim app ty
    Lean.Elab.Tactic.replaceMainGoal [goal]
  let ζ := hlim.choose
  have hζ := hlim.choose_spec
  have hTrT : Tr = T := hTr.trans hT.symm
  clear hT
  subst T
  have he' : HEq er e := her.trans he.symm
  have heq : er = e := eq_of_heq he'
  subst e
  let ρ := γ ≪≫ Functor.isoWhiskerLeft (sfIntegralConstructible l E X).ι
    (Functor.isoWhiskerLeft Tr ζ)
  refine ⟨ρ, fun C n ↦ ?_⟩
  let i := (sfIntegralConstructible l E X).ι
  let p := coefficientConstantTowerProjection l E Y n
  let pn := π n
  have hpn := hζ n
  have hγn := hγ C n
  -- All terms already have their types. Avoid re-solving the large inferred
  -- category telescope; the completed application is checked by the kernel.
  run_tac Lean.Elab.Tactic.withMainContext do
    let localTerm (name : Lean.Name) :=
      Lean.Elab.Term.elabTerm (Lean.mkIdent name) none
    let i ← localTerm `i
    let t ← localTerm `Tr
    let rf ← localTerm `RF
    let gamma ← localTerm `γ
    let zeta ← localTerm `ζ
    let p ← localTerm `p
    let pn ← localTerm `pn
    let hpn ← localTerm `hpn
    let k ← localTerm `C
    let hr ← localTerm `hγn
    let args (label : String) (e : Lean.Expr) (size : Nat) := do
      let a := e.getAppArgs
      unless a.size = size do
        throwError "{label}: expected {size} arguments, got {a.size}"
      pure a
    let it ← args "inclusion" (← Lean.Meta.whnf (← Lean.Meta.inferType i)) 4
    let tt ← args "tower" (← Lean.Meta.whnf (← Lean.Meta.inferType t)) 4
    let rt ← args "derived limit" (← Lean.Meta.whnf (← Lean.Meta.inferType rf)) 4
    let gt ← args "realization" (← Lean.Meta.whnf (← Lean.Meta.inferType gamma)) 4
    let zt ← args "limit comparison" (← Lean.Meta.whnf (← Lean.Meta.inferType zeta)) 4
    let pt ← args "limit projection" (← Lean.Meta.whnf (← Lean.Meta.inferType p)) 6
    let ht ← args "Roos equation" (← Lean.Meta.whnf (← Lean.Meta.inferType hr)) 4
    let outer := ht[1]!.getAppArgs
    unless outer.size > 0 do throwError "expected the outer Roos composite"
    let inner := outer.back!.getAppArgs
    unless inner.size > 0 do throwError "expected the inner Roos composite"
    let e := inner.back!
    let et := (← Lean.Meta.inferType e).getAppArgs
    unless et.size > 0 do throwError "expected a projection morphism type"
    let catLevels (inst : Lean.Expr) := do
      let ty ← Lean.Meta.whnf (← Lean.Meta.inferType inst)
      let ls := ty.getAppFn.constLevels!
      unless ls.length = 2 do throwError "expected two category universes"
      pure ls
    let ci ← catLevels it[1]!
    let di ← catLevels it[3]!
    let vi ← catLevels tt[3]!
    let wi ← catLevels rt[3]!
    let levels := [("vC", ci[0]!), ("uC", ci[1]!),
      ("vD", di[0]!), ("uD", di[1]!), ("vV", vi[0]!), ("uV", vi[1]!),
      ("vW", wi[0]!), ("uW", wi[1]!)]
    let info ← Lean.getConstInfo ``whiskeredComparison_heq
    let us ← info.levelParams.mapM fun name ↦ do
      match levels.lookup name.toString with
      | some level => pure level
      | none => throwError "unexpected comparison universe {name}"
    let app := Lean.mkAppN (Lean.mkConst ``whiskeredComparison_heq us)
      #[it[0]!, it[2]!, tt[2]!, rt[2]!, it[1]!, it[3]!, tt[3]!, rt[3]!,
        i, t, rf, zt[3]!, gt[2]!, gamma, zeta, pt[5]!, p, pn, hpn, k,
        et.back!, e, ht[2]!, ht[3]!, hr]
    (← Lean.Elab.Tactic.getMainGoal).assign app
    Lean.Elab.Tactic.replaceMainGoal []

end WeilConjectures
