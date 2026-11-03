/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! Descent statement for the prescribed finite tensor pullback square. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerShriek

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

/-- Naturality transports a two-variable equality from flat K-flat representatives. -/
private theorem flatPairDescent
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [IsGrothendieckAbelian.{v₁} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory.{w₁} C]
    {D : Type*} [Category* D] {F G : DerivedCategory C × DerivedCategory C ⥤ D}
    (α β : F ⟶ G)
    (hrep : ∀ P Q : CochainComplex C ℤ,
      ((HomologicalComplex.quasiIso C (.up ℤ)).kFlat P ∧
        ∀ i, ObjectProperty.flat (P.X i)) →
      ((HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q ∧
        ∀ i, ObjectProperty.flat (Q.X i)) →
      α.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        β.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
    (M N : DerivedCategory C) : α.app (M, N) = β.app (M, N) := by
  obtain ⟨P, p, hp, hPflat, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage M)
  obtain ⟨Q, q, hq, hQflat, hQ⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage N)
  let eP := asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso M
  let eQ := asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso N
  apply (cancel_epi (F.map (eP.prod eQ).hom)).mp
  rw [α.naturality, β.naturality, hrep P Q ⟨hP, hPflat⟩ ⟨hQ, hQflat⟩]

/-- The proposition expressing the prescribed finite tensor square.

This isolates the categorical descent step from the representative calculation.
-/
def strictFiniteTensorPullbackSquareStatement (b : Base l E)
    (o : Operations l E b) (levels : ComparisonLevels l E b o)
    (tensor : ∀ (T : Scheme.{u}) (n : ℕ),
      SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) T ⋙ comparisonFiniteRealization l E b T n ≅
        ((comparisonFiniteRealization l E b T n).prod
          (comparisonFiniteRealization l E b T n)) ⋙
            comparisonLevelTensor l E b T n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))) : Prop :=
  (comparisonFiniteRealization l E b X n).map
      (((leftDerivedUpperStarTensorComparison
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f).app M).app N) ≫
    (tensor X n).hom.app
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
          f).leftDerivedFunctor.obj M,
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
          f).leftDerivedFunctor.obj N) ≫
    (comparisonLevelTensor l E b X n).map
      (Prod.mkHom ((comparisonFinitePull l E b f n).hom.app M)
        ((comparisonFinitePull l E b f n).hom.app N)) =
  (comparisonFinitePull l E b f n).hom.app
      ((SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
        (ULift.{u + 1, u} (R l E n)) Y).obj (M, N)) ≫
    (proEtaleConstantRingDerivedPullback (R l E n) f).map
      ((tensor Y n).hom.app (M, N)) ≫
    (levels.tensorPullback f n).hom.app
      ((comparisonFiniteRealization l E b Y n).obj M,
        (comparisonFiniteRealization l E b Y n).obj N)

private meta def foldConcreteProjection (e : Expr) : MetaM Expr := do
  let .proj name i x := e.getAppFn | return e
  let env ← getEnv
  let some info := getStructureInfo? env name | return e
  let some field := getProjFnForField? env name (info.fieldNames[i]!) | return e
  return mkAppN (← mkAppM field #[x]) e.getAppArgs

private meta def normalizeConcreteShape (e : Expr) : MetaM Expr := do
  let names := [``SheafOfModules.OpenTensorNormalization.finiteTensor,
    ``leftDerivedUpperStarDerivedTensor, ``derivedTensorLeftDerivedUpperStar,
    ``Functor.uncurry, ``Functor.postcompose₂, ``Functor.whiskeringLeft₂,
    ``Functor.whiskeringLeft, ``Functor.whiskeringRight, ``Functor.comp,
    ``Functor.prod, ``Functor.whiskerLeft, ``Functor.whiskerRight, ``NatTrans.prod]
  let thms := names.foldl (·.addDeclToUnfoldCore ·) {}
  let ctx ← Simp.mkContext { zetaDelta := true } (simpTheorems := #[thms])
  return (← dsimp e ctx).1

private meta def concreteInstanceCongr (cache : IO.Ref (Std.HashMap Expr Expr))
    : Nat → MVarId → MetaM (List MVarId)
  | 0, g => pure [g]
  | n + 1, g => do
    let type ← instantiateMVars (← g.getType)
    let saved ← cache.get
    if let some proof := saved[type]? then
      g.assign proof
      return []
    let gs ← g.withContext do
      let t ← instantiateMVars (← g.getType)
      if t.isForall then
        let (_, g) ← g.intro1
        return ← concreteInstanceCongr cache n g
      let g ← if t.isEq then do
        let gs ← g.apply (← mkConstWithFreshMVarLevels ``eq_of_heq)
        pure gs.head!
      else pure g
      let t ← instantiateMVars (← g.getType)
      let some (_, a, _, b) := t.heq? | return [g]
      if a == b then
        g.hrefl
        return []
      if ← g.proofIrrelHeq then return []
      let a' ← foldConcreteProjection a
      let b' ← foldConcreteProjection b
      if a' != a || b' != b then
        let g ← g.change (← mkHEq a' b')
        return ← concreteInstanceCongr cache n g
      if a.isApp && b.isApp && a.getAppFn == b.getAppFn &&
          a.getAppNumArgs == b.getAppNumArgs then
        let c ← mkHCongrWithArity a.getAppFn a.getAppNumArgs
        let proof ← forallTelescope c.type fun xs t => do
          let proof := mkAppN c.proof xs
          if t.isEq then
            mkLambdaFVars xs (← mkAppM ``heq_of_eq #[proof])
          else
            pure c.proof
        let gs ← g.apply proof
        return (← gs.mapM (concreteInstanceCongr cache n)).flatten
      let a' ← withReducible (whnf a)
      let b' ← withReducible (whnf b)
      if a' != a || b' != b then
        let g ← g.change (← mkHEq a' b')
        return ← concreteInstanceCongr cache n g
      try
        g.hrefl
        return []
      catch _ => return [g]
    if gs.isEmpty then
      let proof ← instantiateMVars (mkMVar g)
      cache.modify (·.insert type proof)
    return gs

private meta def representativeCongr : TacticM Unit := do
  withMainContext do
    let goal ← getMainGoal
    let some h := (← getLCtx).findFromUserName? `h | throwError "Missing representative square"
    let ht ← instantiateMVars (← inferType h.toExpr)
    let gt ← instantiateMVars (← goal.getType)
    let ht ← normalizeConcreteShape ht
    let gt ← normalizeConcreteShape gt
    let e ← mkFreshExprMVar (← mkEq ht gt) .syntheticOpaque
    let cache ← IO.mkRef ({} : Std.HashMap Expr Expr)
    let gs ← concreteInstanceCongr cache 100 e.mvarId!
    unless gs.isEmpty do
      for g in gs.take 10 do logInfo m!"Remaining representative conversion: {← g.getType}"
      throwError "Representative congruence is incomplete"
    closeMainGoal `representativeCongr (← mkAppM ``Eq.mp #[← instantiateMVars e, h.toExpr])

private meta def explicitCongr : TacticM Unit := do
  withMainContext do
    let goal ← getMainGoal
    let t ← instantiateMVars (← goal.getType)
    let some (_, a, b) := t.eq? | throwError "Expected equality"
    let a ← deltaExpand a (· == ``SheafOfModules.OpenTensorNormalization.finiteTensor)
    let b ← deltaExpand b (· == ``SheafOfModules.OpenTensorNormalization.finiteTensor)
    let e ← mkFreshExprMVar (← mkHEq a b) .syntheticOpaque
    let cache ← IO.mkRef ({} : Std.HashMap Expr Expr)
    let gs ← concreteInstanceCongr cache 100 e.mvarId!
    unless gs.isEmpty do
      for g in gs.take 10 do logInfo m!"Remaining: {← g.getType}"
      throwError "Incomplete congruence"
    closeMainGoal `explicitCongr (← mkAppM ``eq_of_heq #[← instantiateMVars e])

private theorem uncurryPostcompose
    {C D : Type*} [Category* C] [Category* D]
    (T : C ⥤ C ⥤ C) (G : C ⥤ D) :
    Functor.uncurry.obj T ⋙ G =
      Functor.uncurry.obj ((Functor.postcompose₂.obj G).obj T) := by
  refine Functor.hext
    (F := Functor.uncurry.obj T ⋙ G)
    (G := Functor.uncurry.obj ((Functor.postcompose₂.obj G).obj T)) (fun _ ↦ rfl) ?_
  intro X Y a
  apply heq_of_eq
  dsimp [Functor.uncurry, Functor.postcompose₂, Functor.whiskeringRight]
  rw [G.map_comp]

private theorem uncurryPrecompose
    {C D : Type*} [Category* C] [Category* D]
    (T : D ⥤ D ⥤ D) (G : C ⥤ D) :
    Functor.uncurry.obj ((((Functor.whiskeringLeft₂ D).obj G).obj G).obj T) =
      G.prod G ⋙ Functor.uncurry.obj T := by
  apply Functor.hext (fun _ ↦ rfl)
  intro X Y a
  rfl

private def transportComponents
    {C D : Type*} [Category* C] [Category* D]
    {F F' G G' : C ⥤ D} (hF : F' = F) (hG : G = G') (a : F ⟶ G) : F' ⟶ G' :=
  eqToHom hF ≫ a ≫ eqToHom hG

private theorem transportComponents_app_heq
    {C D : Type*} [Category* C] [Category* D]
    {F F' G G' : C ⥤ D} (hF : F' = F) (hG : G = G') (a : F ⟶ G) (Z : C) :
    HEq ((transportComponents hF hG a).app Z) (a.app Z) := by
  subst hF
  subst hG
  simp only [transportComponents, eqToHom_refl, Category.comp_id, Category.id_comp]
  rfl

private abbrev squareSource (b : Base l E) {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  SheafOfModules.OpenTensorNormalization.finiteTensor
      (ULift.{u + 1, u} (R l E n)) Y ⋙
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f).leftDerivedFunctor ⋙
    comparisonFiniteRealization l E b X n

private abbrev squareTarget (b : Base l E) {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  ((comparisonFiniteRealization l E b Y n ⋙
    proEtaleConstantRingDerivedPullback (R l E n) f).prod
    (comparisonFiniteRealization l E b Y n ⋙
      proEtaleConstantRingDerivedPullback (R l E n) f)) ⋙ comparisonLevelTensor l E b X n

private def concreteNativeComparison (b : Base l E) {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    SheafOfModules.OpenTensorNormalization.finiteTensor
        (ULift.{u + 1, u} (R l E n)) Y ⋙
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f).leftDerivedFunctor ⟶
    ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f).leftDerivedFunctor.prod
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f).leftDerivedFunctor) ⋙
      SheafOfModules.OpenTensorNormalization.finiteTensor
        (ULift.{u + 1, u} (R l E n)) X := by
  let d := Functor.uncurry.map (leftDerivedUpperStarTensorComparison
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f)
  refine transportComponents ?_ ?_ d
  · dsimp only [leftDerivedUpperStarDerivedTensor]
    rw [← uncurryPostcompose]
    run_tac explicitCongr
  · dsimp only [derivedTensorLeftDerivedUpperStar]
    rw [uncurryPrecompose]
    run_tac explicitCongr

private meta def nativeComponentProof : TacticM Unit := do
  withMainContext do
    let goal ← getMainGoal
    let t ← instantiateMVars (← goal.getType)
    let some (_, lhs, _, rhs) := t.heq? | throwError "Expected component compatibility"
    let lhs ← foldConcreteProjection lhs
    let args := lhs.getAppArgs
    let z := args.back!
    let a := args[args.size - 2]!
    let a ← deltaExpand a (· == ``concreteNativeComparison)
    let rec reduceLets : Nat → Expr → Expr
      | 0, e => e
      | n + 1, e =>
        match e with
        | .letE _ _ v b _ => reduceLets n (b.instantiate1 v)
        | .mdata _ e => reduceLets n e
        | _ =>
          let e' := e.headBeta
          if e' != e then reduceLets n e' else e
    let a := reduceLets 20 a
    unless a.getAppFn.isConstOf ``transportComponents do
      throwError "Expected the constructed endpoint transport"
    let aa := a.getAppArgs
    let h ← mkAppM ``transportComponents_app_heq
      #[aa[aa.size - 3]!, aa[aa.size - 2]!, aa.back!, z]
    let ht ← instantiateMVars (← inferType h)
    let some (_, _, _, middle) := ht.heq? | throwError "Expected transported component"
    let middle ← withReducible (whnf middle)
    let et ← normalizeConcreteShape (← mkHEq middle rhs)
    let e ← mkFreshExprMVar et .syntheticOpaque
    let cache ← IO.mkRef ({} : Std.HashMap Expr Expr)
    let gs ← concreteInstanceCongr cache 100 e.mvarId!
    unless gs.isEmpty do
      for g in gs.take 10 do logInfo m!"Remaining component: {← g.getType}"
      throwError "Component congruence is incomplete"
    closeMainGoal `nativeComponent (← mkAppM ``HEq.trans #[h, ← instantiateMVars e])

private theorem concreteNativeComparison_app (b : Base l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M N : DerivedCategory (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))) :
    (concreteNativeComparison l E b f n).app (M, N) =
      (((leftDerivedUpperStarTensorComparison
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f).app M).app N) := by
  apply eq_of_heq
  run_tac nativeComponentProof

private def concreteLeft (b : Base l E)
    (tensor : ∀ (T : Scheme.{u}) (n : ℕ),
      SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) T ⋙ comparisonFiniteRealization l E b T n ≅
        ((comparisonFiniteRealization l E b T n).prod
          (comparisonFiniteRealization l E b T n)) ⋙
            comparisonLevelTensor l E b T n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    squareSource l E b f n ⟶ squareTarget l E b f n := by
  let G := (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
    f).leftDerivedFunctor
  let H := comparisonFiniteRealization l E b X n
  let S' := comparisonLevelTensor l E b X n
  let c := comparisonFinitePull l E b f n
  let base : squareSource l E b f n ⟶ squareTarget l E b f n :=
    Functor.whiskerRight (concreteNativeComparison l E b f n) H ≫
      Functor.whiskerLeft (G.prod G) (tensor X n).hom ≫
      Functor.whiskerRight (NatTrans.prod c.hom c.hom) S'
  exact base

private def concreteRight (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o)
    (tensor : ∀ (T : Scheme.{u}) (n : ℕ),
      SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) T ⋙ comparisonFiniteRealization l E b T n ≅
        ((comparisonFiniteRealization l E b T n).prod
          (comparisonFiniteRealization l E b T n)) ⋙
            comparisonLevelTensor l E b T n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    squareSource l E b f n ⟶ squareTarget l E b f n := by
  let T := SheafOfModules.OpenTensorNormalization.finiteTensor
    (ULift.{u + 1, u} (R l E n)) Y
  let F := comparisonFiniteRealization l E b Y n
  let U := proEtaleConstantRingDerivedPullback (R l E n) f
  let c := comparisonFinitePull l E b f n
  let base : squareSource l E b f n ⟶ squareTarget l E b f n :=
    Functor.whiskerLeft T c.hom ≫ Functor.whiskerRight (tensor Y n).hom U ≫
      Functor.whiskerLeft (F.prod F) (levels.tensorPullback f n).hom
  exact base

private theorem concreteRepresentativeSquare (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o)
    (tensor : ∀ (T : Scheme.{u}) (n : ℕ),
      SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) T ⋙ comparisonFiniteRealization l E b T n ≅
        ((comparisonFiniteRealization l E b T n).prod
          (comparisonFiniteRealization l E b T n)) ⋙
            comparisonLevelTensor l E b T n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P Q : CochainComplex (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))) ℤ)
    (h : strictFiniteTensorPullbackSquareStatement l E b o levels tensor f n
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)) :
    (concreteLeft l E b tensor f n).app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      (concreteRight l E b o levels tensor f n).app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := by
  -- Resolve the small ring-instance diamonds before checking tensor components.
  let ringAgreement : (inferInstance : Ring (R l E n)) =
      (inferInstance : CommRing (R l E n)).toRing := rfl
  let liftedRingAgreement : (inferInstance : Ring (ULift.{u + 1, u} (R l E n))) =
      (inferInstance : CommRing (ULift.{u + 1, u} (R l E n))).toRing := rfl
  dsimp only [strictFiniteTensorPullbackSquareStatement, concreteLeft, concreteRight,
    NatTrans.comp_app, Functor.whiskerLeft, Functor.whiskerRight, NatTrans.prod,
    Functor.prod_obj, Functor.comp_obj] at h ⊢
  simp only [concreteNativeComparison_app] at h ⊢
  dsimp only [SheafOfModules.OpenTensorNormalization.finiteTensor,
    leftDerivedUpperStarDerivedTensor, derivedTensorLeftDerivedUpperStar,
    Functor.uncurry, Functor.postcompose₂, Functor.whiskeringLeft₂,
    Functor.whiskeringLeft, Functor.whiskeringRight, Functor.comp, Functor.prod] at h ⊢
  run_tac representativeCongr

private theorem concretePairDescent (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o)
    (tensor : ∀ (T : Scheme.{u}) (n : ℕ),
      SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) T ⋙ comparisonFiniteRealization l E b T n ≅
        ((comparisonFiniteRealization l E b T n).prod
          (comparisonFiniteRealization l E b T n)) ⋙
            comparisonLevelTensor l E b T n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (hrep : ∀ P Q : CochainComplex (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))) ℤ,
      finiteScalarFlatRepresentatives Y (R l E n) P →
      finiteScalarFlatRepresentatives Y (R l E n) Q →
      (concreteLeft l E b tensor f n).app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        (concreteRight l E b o levels tensor f n).app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
    (M N : DerivedCategory (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))) :
    (concreteLeft l E b tensor f n).app (M, N) =
      (concreteRight l E b o levels tensor f n).app (M, N) := by
  -- Resolve the small ring-instance diamonds before checking tensor components.
  let ringAgreement : (inferInstance : Ring (R l E n)) =
      (inferInstance : CommRing (R l E n)).toRing := rfl
  let liftedRingAgreement : (inferInstance : Ring (ULift.{u + 1, u} (R l E n))) =
      (inferInstance : CommRing (ULift.{u + 1, u} (R l E n))).toRing := rfl
  exact flatPairDescent (concreteLeft l E b tensor f n)
    (concreteRight l E b o levels tensor f n) hrep M N

private theorem concreteSquareOfPaths (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o)
    (tensor : ∀ (T : Scheme.{u}) (n : ℕ),
      SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) T ⋙ comparisonFiniteRealization l E b T n ≅
        ((comparisonFiniteRealization l E b T n).prod
        (comparisonFiniteRealization l E b T n)) ⋙
            comparisonLevelTensor l E b T n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M N : DerivedCategory (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))))
    (h : (concreteLeft l E b tensor f n).app (M, N) =
      (concreteRight l E b o levels tensor f n).app (M, N)) :
      (comparisonFiniteRealization l E b X n).map
          (((leftDerivedUpperStarTensorComparison
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f).app M).app N) ≫
        (tensor X n).hom.app
          ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
              f).leftDerivedFunctor.obj M,
            (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
              f).leftDerivedFunctor.obj N) ≫
        (comparisonLevelTensor l E b X n).map
          (Prod.mkHom ((comparisonFinitePull l E b f n).hom.app M)
            ((comparisonFinitePull l E b f n).hom.app N)) =
      (comparisonFinitePull l E b f n).hom.app
          ((SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
            (ULift.{u + 1, u} (R l E n)) Y).obj (M, N)) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) f).map
          ((tensor Y n).hom.app (M, N)) ≫
        (levels.tensorPullback f n).hom.app
          ((comparisonFiniteRealization l E b Y n).obj M,
            (comparisonFiniteRealization l E b Y n).obj N) := by
  -- Resolve the small ring-instance diamonds before checking tensor components.
  let ringAgreement : (inferInstance : Ring (R l E n)) =
      (inferInstance : CommRing (R l E n)).toRing := rfl
  let liftedRingAgreement : (inferInstance : Ring (ULift.{u + 1, u} (R l E n))) =
      (inferInstance : CommRing (ULift.{u + 1, u} (R l E n))).toRing := rfl
  dsimp only [strictFiniteTensorPullbackSquareStatement, concreteLeft, concreteRight,
    NatTrans.comp_app, Functor.whiskerLeft, Functor.whiskerRight, NatTrans.prod,
    Functor.prod_obj, Functor.comp_obj] at h ⊢
  simp only [concreteNativeComparison_app] at h ⊢
  dsimp only [SheafOfModules.OpenTensorNormalization.finiteTensor,
    leftDerivedUpperStarDerivedTensor, derivedTensorLeftDerivedUpperStar,
    Functor.uncurry, Functor.postcompose₂, Functor.whiskeringLeft₂,
    Functor.whiskeringLeft, Functor.whiskeringRight, Functor.comp, Functor.prod] at h ⊢
  exact h

/-- Representative squares descend through the two derived-category variables.
Source: blueprint operations proof (2), final localization and replacement step.
(blueprint: new-lem-sp-strict-finite-tensor-pullback-square-descent).

Proof: by CochainComplex.exists_quasiIso_flat_kFlat (Stacks 06YS) every derived
object is isomorphic to Q of a flat-term K-flat complex; choose such replacements
in both variables, apply the
representative equality to their images in the derived category, and use the
universal property of the localization together with naturality of every
comparison map. The replacement maps are inverted by the left-derived
functors, so the resulting equality is the displayed square for arbitrary
objects. This is independent of the calculation of the representative square.
-/
theorem strictFiniteTensorPullbackSquare_descent (b : Base l E)
    (o : Operations l E b) (levels : ComparisonLevels l E b o)
    (tensor : ∀ (T : Scheme.{u}) (n : ℕ),
      SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) T ⋙ comparisonFiniteRealization l E b T n ≅
        ((comparisonFiniteRealization l E b T n).prod
          (comparisonFiniteRealization l E b T n)) ⋙
            comparisonLevelTensor l E b T n)
    (hrep : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
      (P Q : CochainComplex (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))) ℤ),
      WeilConjectures.finiteScalarFlatRepresentatives Y (R l E n) P →
      WeilConjectures.finiteScalarFlatRepresentatives Y (R l E n) Q →
      strictFiniteTensorPullbackSquareStatement l E b o levels tensor f n
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)) :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
      (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))),
      (comparisonFiniteRealization l E b X n).map
          (((leftDerivedUpperStarTensorComparison
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f).app M).app N) ≫
        (tensor X n).hom.app
          ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
              f).leftDerivedFunctor.obj M,
            (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
              f).leftDerivedFunctor.obj N) ≫
        (comparisonLevelTensor l E b X n).map
          (Prod.mkHom ((comparisonFinitePull l E b f n).hom.app M)
            ((comparisonFinitePull l E b f n).hom.app N)) =
      (comparisonFinitePull l E b f n).hom.app
          ((SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
            (ULift.{u + 1, u} (R l E n)) Y).obj (M, N)) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) f).map
          ((tensor Y n).hom.app (M, N)) ≫
        (levels.tensorPullback f n).hom.app
          ((comparisonFiniteRealization l E b Y n).obj M,
            (comparisonFiniteRealization l E b Y n).obj N) := by
  intro X Y f n M N
  exact concreteSquareOfPaths l E b o levels tensor f n M N
    (concretePairDescent l E b o levels tensor f n
      (fun P Q hP hQ ↦ concreteRepresentativeSquare l E b o levels tensor f n P Q
        (hrep f n P Q hP hQ)) M N)

end AlgebraicGeometry.ProEtale.SpTowerShriek
