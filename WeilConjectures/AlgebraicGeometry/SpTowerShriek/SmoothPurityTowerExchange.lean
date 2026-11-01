/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData

/-! # Exchange invertibility for normalized coefficient towers

Source: blueprint operations proof (2b)
(blueprint: lem-sp-tower-exchange-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerShriek

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

private theorem witness_transport_isIso (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback h f' f g) (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (alpha : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
      L.obj ≅ N) : IsIso (compactExchangeTransportAtWitness Λ sq c L N alpha) := by
  rw [(compactSupport_exchange_transport Λ sq c).2 L N alpha]
  exact isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app Λ sq c N
    ⟨L.obj, L.property, ⟨alpha⟩⟩

private abbrev sheafLevel (T : Scheme.{u})
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  SemilinearSections.D.{u + 1, u, u + 1} (ProEt.topology T) A

private abbrev reductionSheafLevel (T : Scheme.{u})
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  @DerivedCategory (proEtaleRingModules T A) _
    (SemilinearSections.moduleAbelian (ProEt.topology T) A)
    (reductionModulesHasDerivedCategory T A)

private abbrev standardSheafLevel (T : Scheme.{u})
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  @DerivedCategory (SheafOfModules.{u + 1} (SemilinearSections.ring (ProEt.topology T) A)) _
    (SheafOfModules.instAbelian (SemilinearSections.ring (ProEt.topology T) A))
    (@HasDerivedCategory.standard _ _
      (SheafOfModules.instAbelian (SemilinearSections.ring (ProEt.topology T) A)))

private abbrev canonicalSheafLevel (T : Scheme.{u})
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  @DerivedCategory (SheafOfModules.{u + 1} (SemilinearSections.ring (ProEt.topology T) A)) _
    (SheafOfModules.instAbelian (SemilinearSections.ring (ProEt.topology T) A))
    (@HasDerivedCategory.standard _ _
      (SheafOfModules.instAbelian (SemilinearSections.ring (ProEt.topology T) A)))

private abbrev semilinearSheafCategory (T : Scheme.{u})
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) : Category (sheafLevel T A) :=
  @instCategoryDerivedCategory _ _
    (SemilinearSections.moduleAbelian (ProEt.topology T) A)
    (SemilinearSections.hasDerived (ProEt.topology T) A)

private abbrev standardSheafCategory (T : Scheme.{u})
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) : Category (standardSheafLevel T A) :=
  @instCategoryDerivedCategory _ _
    (SemilinearSections.moduleAbelian (ProEt.topology T) A)
    (@HasDerivedCategory.standard _ _
      (SemilinearSections.moduleAbelian (ProEt.topology T) A))

private abbrev reductionSheafCategory (T : Scheme.{u})
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) : Category (reductionSheafLevel T A) :=
  @instCategoryDerivedCategory (proEtaleRingModules T A) _
    (SemilinearSections.moduleAbelian (ProEt.topology T) A)
    (reductionModulesHasDerivedCategory T A)

private abbrev canonicalSheafCategory (T : Scheme.{u})
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) : Category (canonicalSheafLevel T A) :=
  @instCategoryDerivedCategory _ _
    (SheafOfModules.instAbelian (SemilinearSections.ring (ProEt.topology T) A))
    (HasDerivedCategory.standard _)

private theorem realization_isIso_app (T U : Scheme.{u})
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (B : Sheaf (ProEt.topology U) CommRingCat.{u + 1}) :
    letI : Category (sheafLevel T A) := standardSheafCategory T A
    letI : Category (sheafLevel U B) := canonicalSheafCategory U B
    ∀ {F G : sheafLevel T A ⥤ sheafLevel U B} (alpha : F ⟶ G)
      {M N : sheafLevel T A} (_e : @Iso _ (reductionSheafCategory T A) M N)
      (_hM : IsIso (alpha.app M)), IsIso (alpha.app N) := by
  letI := standardSheafCategory T A
  letI := canonicalSheafCategory U B
  intro F G alpha M N e hM
  let e' : M ≅ N := e
  exact (NatTrans.isIso_app_iff_of_iso alpha e').1 hM

private theorem finite_p_iso :
    @IsIso (reductionSheafLevel Y' (B l E Y' n))
      (reductionSheafCategory Y' (B l E Y' n)) _ _ ((comparisonFiniteRealization l E b Y' n).map
      (compactExchangeTransportAtWitness (ULift.{u + 1, u} (R l E n)) sq c L N alpha)) := by
  letI := reductionSheafCategory Y' (B l E Y' n)
  let : Finite (ULift.{u + 1, u} (R l E n)) :=
    Equiv.ulift.finite_iff.mpr (b.finite n)
  have hi := witness_transport_isIso (ULift.{u + 1, u} (R l E n)) sq c L N alpha
  exact (comparisonFiniteRealization l E b Y' n).map_isIso _

private theorem finite_q_iso :
    @IsIso (reductionSheafLevel Y' (B l E Y' n))
      (reductionSheafCategory Y' (B l E Y' n)) _ _
      ((comparisonFiniteF l E b coordinates (c.ofIsPullback sq) n).hom.app
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
        h).leftDerivedFunctor.obj N)) := by
  letI := reductionSheafCategory Y' (B l E Y' n)
  exact NatIso.hom_app_isIso (comparisonFiniteF l E b coordinates (c.ofIsPullback sq) n) _

private theorem finite_r_iso :
    @IsIso (reductionSheafLevel Y' (B l E Y' n))
      (reductionSheafCategory Y' (B l E Y' n)) _ _ ((finiteF l E b (c.ofIsPullback sq) n).map
      ((comparisonFinitePull l E b h n).hom.app N)) := by
  letI := reductionSheafCategory Y' (B l E Y' n)
  have hi := NatIso.hom_app_isIso (comparisonFinitePull l E b h n) N
  exact (finiteF l E b (c.ofIsPullback sq) n).map_isIso _

private theorem finite_s_iso :
    @IsIso (reductionSheafLevel Y' (B l E Y' n))
      (reductionSheafCategory Y' (B l E Y' n)) _ _ ((comparisonFinitePull l E b g n).hom.app
      ((rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c).obj N)) := by
  letI := reductionSheafCategory Y' (B l E Y' n)
  exact NatIso.hom_app_isIso (comparisonFinitePull l E b g n) _

private theorem finite_t_iso :
    @IsIso (reductionSheafLevel Y' (B l E Y' n))
      (reductionSheafCategory Y' (B l E Y' n)) _ _
      ((proEtaleConstantRingDerivedPullback (R l E n) g).map
      ((comparisonFiniteF l E b coordinates c n).hom.app N)) := by
  letI := reductionSheafCategory Y' (B l E Y' n)
  have hi := NatIso.hom_app_isIso (comparisonFiniteF l E b coordinates c n) N
  exact (proEtaleConstantRingDerivedPullback (R l E n) g).map_isIso _

private theorem tower_q_iso :
    @IsIso (SemilinearSections.D.{u + 1, u, u + 1}
      (ProEt.topology Y') (B l E Y' n))
      (semilinearSheafCategory Y' (B l E Y' n)) _ _
    ((Fcomparison l E b o (c.ofIsPullback sq) n).hom.app
      ((pull l E b (o.geometry h)).obj K)) := by
  exact NatIso.hom_app_isIso (Fcomparison l E b o (c.ofIsPullback sq) n) _

private theorem tower_r_iso :
    @IsIso (SemilinearSections.D.{u + 1, u, u + 1}
      (ProEt.topology Y') (B l E Y' n))
      (semilinearSheafCategory Y' (B l E Y' n)) _ _
    ((finiteF l E b (c.ofIsPullback sq) n).map
      (((o.geometry h).pullEvaluation n).hom.app K)) := by
  have hi := NatIso.hom_app_isIso ((o.geometry h).pullEvaluation n) K
  exact (finiteF l E b (c.ofIsPullback sq) n).map_isIso _

private theorem tower_s_iso :
    @IsIso (SemilinearSections.D.{u + 1, u, u + 1}
      (ProEt.topology Y') (B l E Y' n))
      (semilinearSheafCategory Y' (B l E Y' n)) _ _
    (((o.geometry g).pullEvaluation n).hom.app ((F l E b o c).obj K)) := by
  exact NatIso.hom_app_isIso ((o.geometry g).pullEvaluation n) _

private theorem tower_t_iso :
    @IsIso (SemilinearSections.D.{u + 1, u, u + 1}
      (ProEt.topology Y') (B l E Y' n))
      (semilinearSheafCategory Y' (B l E Y' n)) _ _
    ((proEtaleConstantRingDerivedPullback (R l E n) g).map
      ((Fcomparison l E b o c n).hom.app K)) := by
  have hi := NatIso.hom_app_isIso (Fcomparison l E b o c n) K
  exact (proEtaleConstantRingDerivedPullback (R l E n) g).map_isIso _

private def finite_exchange_at_witness (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o) (coordinates : StrictFiniteCoordinates l E b)
    (_finite : StrictFiniteExchangeComparisons l E b o levels coordinates)
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback h f' f g) (c : Compactification f) (n : ℕ)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))))
    (N : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))))
    (alpha : (comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) X).mapDerivedCategory.obj
      L.obj ≅ N) := by
  have hp := finite_p_iso l E b sq c n L N alpha
  have hq := finite_q_iso l E b coordinates sq c n N
  have hr := finite_r_iso l E b sq c n N
  have hs := finite_s_iso l E b (g := g) c n N
  have ht := finite_t_iso l E b coordinates (g := g) c n N
  have word := _finite sq c n L N alpha
  run_tac Lean.Elab.Tactic.withMainContext do
    let wl ← Lean.Meta.getLocalDeclFromUserName `word
    let wt ← Lean.instantiateMVars wl.type
    let wa := wt.getAppArgs
    let lhs := wa[1]!
    let rhs := wa[2]!
    let la := lhs.getAppArgs
    let ra := rhs.getAppArgs
    let ta := ra[6]!.getAppArgs
    let cat := la[1]!.getAppArgs.back!
    let ct ← Lean.Meta.inferType cat
    let .const _ lvls := ct.getAppFn | throwError "expected Category constant"
    let isoFn := Lean.mkAppN (Lean.mkConst ``CategoryTheory.IsIso lvls)
      #[la[0]!, cat, la[2]!, la[4]!]
    let motive := Lean.mkLambda `v .default wa[0]! (Lean.mkApp isoFn (.bvar 0))
    let eqIso ← Lean.Meta.mkAppM ``congrArg #[motive, Lean.mkFVar wl.fvarId]
    let hLeft ← Lean.Meta.synthInstance (Lean.mkApp isoFn lhs)
    let hRight ← Lean.Meta.mkAppM ``Eq.mp #[eqIso, hLeft]
    let hs ← Lean.Meta.getLocalDeclFromUserName `hs
    let ht ← Lean.Meta.getLocalDeclFromUserName `ht
    let cancel := Lean.mkConst ``CategoryTheory.IsIso.of_isIso_comp_left lvls
    let hTail := Lean.mkAppN cancel #[la[0]!, cat, ra[2]!, ra[3]!, ra[4]!,
      ra[5]!, ra[6]!, Lean.mkFVar hs.fvarId, hRight]
    let pr := Lean.mkAppN cancel #[la[0]!, cat, ta[2]!, ta[3]!, ta[4]!,
      ta[5]!, ta[6]!, Lean.mkFVar ht.fvarId, hTail]
    let goal ← Lean.Elab.Tactic.getMainGoal
    let tp ← Lean.Meta.inferType pr
    unless ← Lean.Meta.isDefEq (← goal.getType) tp do
      throwError "Cannot infer the native result type"
    goal.assign pr
    Lean.Elab.Tactic.replaceMainGoal []



-- The imported operators use several definitionally equal presentations of the
-- same derived categories. Abstract the five functors and the exchange transformation
-- before comparing these presentations, so the kernel sees variables rather than
-- unfolding the concrete derived functors. Each resulting bridge is proved below
-- by `intro ...; exact hv`; this code only constructs its ordinary Lean type.

private meta def collectBridgeAtoms (native nominal : Lean.Expr) :
    Lean.MetaM (Array Lean.Expr) := do
  let pa := native.getAppArgs
  let extract := fun (source : Lean.Expr) => Id.run do
    let sa := source.getAppArgs
    if sa.size != 6 then return none
    let inner := sa[5]!.getAppArgs
    if inner.size != 6 then return none
    let composite := inner[4]!
    if !composite.isAppOfArity ``CategoryTheory.Functor.comp 8 then return none
    let ca := composite.getAppArgs
    return some #[ca[7]!, sa[4]!, ca[6]!]
  let some data := (extract pa[2]!).orElse (fun _ => extract nominal.getAppArgs[2]!)
    | throwError "Expected a composite realization in one of the sources"
  let actualF := data[0]!
  let actualG := data[1]!
  let actualEa := data[2]!
  let actualV := pa[4]!
  let _actualVType ← Lean.Meta.inferType actualV
  let rec gatherFunctor : Nat → Lean.Expr → Array Lean.Expr → Array Lean.Expr
    | 0, _, acc => acc
    | fuel + 1, f, acc =>
      if f.isAppOfArity ``CategoryTheory.Functor.comp 8 then
        let aa := f.getAppArgs
        gatherFunctor fuel aa[7]! (gatherFunctor fuel aa[6]! acc)
      else if acc.contains f then acc else acc.push f
  let rec gatherObject : Nat → Lean.Expr → Array Lean.Expr → Array Lean.Expr
    | 0, _, acc => acc
    | fuel + 1, obj, acc =>
      if obj.isAppOfArity ``CategoryTheory.Functor.obj 6 then
        let aa := obj.getAppArgs
        gatherObject fuel aa[5]! (gatherFunctor 100 aa[4]! acc)
      else acc
  let mut atoms := #[actualF, actualG, actualEa]
  atoms := gatherObject 100 pa[3]! atoms
  atoms := gatherObject 100 nominal.getAppArgs[3]! atoms
  let va := _actualVType.getAppArgs
  unless va.size == 4 do throwError "Expected an ordinary morphism type: {_actualVType}"
  atoms := gatherObject 100 va[2]! atoms
  atoms := gatherObject 100 va[3]! atoms
  unless atoms.size == 5 do
    throwError "Expected five atomic functors, got {atoms.size}: {atoms}"
  return atoms

private def named_origin_realization (b : Base l E) (T : Scheme.{u}) (n : ℕ)
    (K : D l E T) (origin : Origin l E b T n K) :
    @Iso (reductionSheafLevel T (B l E T n)) (reductionSheafCategory T (B l E T n))
      ((comparisonFiniteRealization l E b T n).obj origin.level.obj)
      ((Ev l E T n).obj K) := origin.realization

private theorem finite_origin_input_bridge
    (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o) (coordinates : StrictFiniteCoordinates l E b)
    (_finite : StrictFiniteExchangeComparisons l E b o levels coordinates)
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback h f' f g) (c : Compactification f) (n : ℕ)
    (K : D l E X) (origin : Origin l E b X n K) :
    literal_source_bridge%
      (finite_exchange_at_witness l E b o levels coordinates _finite sq c n
        origin.witness.complex origin.level.obj origin.witness.iso),
      (argument_type% (realization_isIso_app X Y' (B l E X n) (B l E Y' n)
        (comparisonLevelExchange l E b o levels sq c n)
      (named_origin_realization l E b X n K origin))) := by
  intro F₁ G₁ Ea G₂ F₂ v hv
  exact hv

private def finite_exchange_at_origin
    (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o) (coordinates : StrictFiniteCoordinates l E b)
    (_finite : StrictFiniteExchangeComparisons l E b o levels coordinates)
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback h f' f g) (c : Compactification f) (n : ℕ)
    (K : D l E X) (origin : Origin l E b X n K) := by
  have hn := finite_exchange_at_witness l E b o levels coordinates _finite sq c n
    origin.witness.complex origin.level.obj origin.witness.iso
  have hm := finite_origin_input_bridge l E b o levels coordinates _finite sq c n K origin
    (finiteF l E b c n) (proEtaleConstantRingDerivedPullback (R l E n) g)
    (comparisonFiniteRealization l E b X n)
    (proEtaleConstantRingDerivedPullback (R l E n) h)
    (finiteF l E b (c.ofIsPullback sq) n) _ hn
  exact realization_isIso_app X Y' (B l E X n) (B l E Y' n)
    (comparisonLevelExchange l E b o levels sq c n)
      (named_origin_realization l E b X n K origin) hm

end AlgebraicGeometry.ProEtale.SpTowerShriek
