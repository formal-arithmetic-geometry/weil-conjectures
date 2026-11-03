/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictFiniteTensorPullbackSquare

/-! Open mate after the transported open comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

set_option maxHeartbeats 2000000 in
-- Explicit comparison congruences are checked within this declaration.
set_option maxHeartbeats 2000000 in
-- Explicit comparison congruences are checked within this declaration.
set_option maxHeartbeats 2000000 in
-- Explicit comparison congruences are checked within this declaration.
set_option maxHeartbeats 2000000 in
-- Explicit comparison congruences are checked within this declaration.
set_option maxHeartbeats 2000000 in
-- Explicit comparison congruences are checked within this declaration.
set_option maxHeartbeats 2000000 in
-- Explicit comparison congruences are checked within this declaration.
private meta partial def conversionCongruence
    (cache : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr))
    (congrCache : IO.Ref (Std.HashMap (Lean.Expr × Nat) Lean.Meta.CongrTheorem))
    (a b : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← Lean.Meta.mkHEqRefl a
  if let some h := (← cache.get).get? (a, b) then return h
  let compute : Lean.MetaM Lean.Expr := do
    if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
      return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
    let reduce (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
      if let .letE _ _ v body _ := e then return some (body.instantiate1 v)
      if e.getAppFn.isFVar then
        let decl ← e.getAppFn.fvarId!.getDecl
        if let some value := decl.value? then
          return some (Lean.mkAppN value e.getAppArgs)
      let projection ← match e.getAppFn with
        | .proj n i major => pure (some (n, i, major, e.getAppArgs))
        | .const name _ => do
          match (← Lean.getProjectionFnInfo? name) with
          | none => pure none
          | some info => do
            let args := e.getAppArgs
            if args.size < info.numParams + 1 then pure none else do
              let major := args[info.numParams]!
              let ty ← Lean.Meta.whnf (← Lean.Meta.inferType major)
              pure (some (ty.getAppFn.constName!, info.i, major,
                args.extract (info.numParams + 1) args.size))
        | _ => pure none
      if let some (n, i, major, args) := projection then
        let structural := #[``CategoryTheory.Iso.symm, ``CategoryTheory.Iso.trans,
          ``CategoryTheory.Functor.mapIso, ``CategoryTheory.Iso.app,
          ``CategoryTheory.Functor.comp, ``CategoryTheory.Iso.refl]
        if major.getAppFn.isConst && structural.contains major.getAppFn.constName! then
          if let some major' ← Lean.Meta.unfoldDefinition? major
              (ignoreTransparency := true) then
            let major' ← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf major')
            let field := Lean.Expr.proj n i major'
            let field := (← field.reduceProjStruct?).getD field
            return some (Lean.mkAppN field args).headBeta
      if let .proj n i major := e.getAppFn then
        let env ← Lean.getEnv
        let some info := Lean.getStructureInfo? env n | throwError "unknown structure {n}"
        let some proj := Lean.getProjFnForField? env n info.fieldNames[i]! |
          throwError "unknown projection of {n}"
        let majorType ← Lean.Meta.whnf (← Lean.Meta.inferType major)
        unless majorType.getAppFn.isConstOf n do
          throwError "unexpected projection type {majorType}"
        let head := Lean.mkAppN (Lean.mkConst proj majorType.getAppFn.constLevels!)
          (majorType.getAppArgs.push major)
        return some (Lean.mkAppN head e.getAppArgs)
      if e.headBeta != e then return some e.headBeta
      if let some e' ← e.reduceProjStruct? then return some e'
      return none
    if let some a' ← reduce a then
      return ← conversionTrans (← conversionReduction a a')
        (← conversionCongruence cache congrCache a' b)
    if let some b' ← reduce b then
      return ← conversionTrans (← conversionCongruence cache congrCache a b')
        (← conversionSymm (← conversionReduction b b'))
    let mut congruenceError : Option Lean.Exception := none
    let sameHead := a.getAppFn == b.getAppFn ||
      (a.getAppFn.isConst && b.getAppFn.isConst &&
        a.getAppFn.constName! == b.getAppFn.constName!)
    if sameHead && a.isApp && a.getAppNumArgs == b.getAppNumArgs then
      try
        let aa := a.getAppArgs
        let bb := b.getAppArgs
        let key := (a.getAppFn, aa.size)
        let ct ← match (← congrCache.get).get? key with
          | some ct => pure ct
          | none => do
            let ct ← if a.getAppFn.hasFVar then
                Lean.Meta.mkHCongrWithArity a.getAppFn aa.size
              else Lean.Meta.withLCtx {} {} <|
                Lean.Meta.mkHCongrWithArity a.getAppFn aa.size
            let proof ← Lean.Meta.mkAuxTheorem ct.type ct.proof
              (kind? := `_finiteCongruence)
            let ct := { ct with proof := proof }
            congrCache.modify fun m => m.insert key ct
            pure ct
        let mut args := #[]
        for i in [:aa.size] do
          let h ← conversionCongruence cache congrCache aa[i]! bb[i]!
          let h ← if ct.argKinds[i]! == .eq then conversionToEq h else pure h
          args := args ++ #[aa[i]!, bb[i]!, h]
        let h := Lean.mkAppN ct.proof args
        return ← if (← Lean.Meta.inferType h).isHEq then pure h else conversionOfEq h
      catch err => congruenceError := some err
    if (← Lean.Meta.isClass? (← Lean.Meta.inferType a)).isSome then
      return ← conversionReduction a b
    let a' ← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf a)
    let a' ← match (← reduce a') with
      | some v => pure v
      | none => pure a'
    if a' != a then
      return ← conversionTrans (← conversionReduction a a')
        (← conversionCongruence cache congrCache a' b)
    let b' ← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf b)
    let b' ← match (← reduce b') with
      | some v => pure v
      | none => pure b'
    if b' != b then
      return ← conversionTrans (← conversionCongruence cache congrCache a b')
        (← conversionSymm (← conversionReduction b b'))
    if let some a' ← Lean.Meta.unfoldDefinition? a (ignoreTransparency := true) then
      let a' ← match (← reduce a') with
        | some v => pure v
        | none => pure a'
      if a' != a then
        return ← conversionTrans (← conversionReduction a a')
          (← conversionCongruence cache congrCache a' b)
    if let some b' ← Lean.Meta.unfoldDefinition? b (ignoreTransparency := true) then
      let b' ← match (← reduce b') with
        | some v => pure v
        | none => pure b'
      if b' != b then
        return ← conversionTrans (← conversionCongruence cache congrCache a b')
          (← conversionSymm (← conversionReduction b b'))
    if a.isLambda && b.isLambda then return ← conversionReduction a b
    if let some err := congruenceError then throw err
    throwError "Unmatched finite comparison expressions: {a} versus {b}"
  let h ← compute
  let ty ← Lean.Meta.mkHEq a b
  let h ← Lean.Meta.mkAuxTheorem ty h
    (zetaDelta := true) (kind? := `_finiteCongruence)
  cache.modify fun m => m.insert (a, b) h
  return h

set_option maxHeartbeats 2000000 in
-- Explicit comparison congruences are checked within this declaration.
private lemma transport_adjunct
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (a' : L' ⊣ R') (e : C ⥤ C') (d : D ⥤ D')
    (left : L ⋙ d ≅ e ⋙ L') (right : R ⋙ e ≅ d ⋙ R')
    (hu : ∀ K, e.map (a.unit.app K) ≫ right.hom.app (L.obj K) ≫
      R'.map (left.hom.app K) = a'.unit.app (e.obj K))
    {K : C} {M : D} (f : L.obj K ⟶ M) :
    a'.homEquiv _ _ (left.inv.app K ≫ d.map f) =
      e.map (a.homEquiv _ _ f) ≫ right.hom.app M := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← hu]
  simp only [Functor.map_comp, Category.assoc]
  rw [← R'.map_comp_assoc]
  simp only [Iso.hom_inv_id_app]
  apply congrArg (e.map (a.unit.app K) ≫ ·)
  simpa using (right.hom.naturality f).symm

private lemma projection_transport
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (a' : L' ⊣ R') (e : C ⥤ C') (d : D ⥤ D')
    (left : L ⋙ d ≅ e ⋙ L') (right : R ⋙ e ≅ d ⋙ R')
    (hu : ∀ K, e.map (a.unit.app K) ≫ right.hom.app (L.obj K) ≫
      R'.map (left.hom.app K) = a'.unit.app (e.obj K))
    (T : C × C ⥤ C) (S : D × D ⥤ D)
    (T' : C' × C' ⥤ C') (S' : D' × D' ⥤ D')
    (t : T ⋙ e ≅ e.prod e ⋙ T') (s : S ⋙ d ≅ d.prod d ⋙ S')
    (mu : S ⋙ R ≅ R.prod R ⋙ T) (mu' : S' ⋙ R' ≅ R'.prod R' ⋙ T')
    (hsq : ∀ M N, e.map (mu.hom.app (M, N)) ≫
      t.hom.app (R.obj M, R.obj N) ≫ T'.map (Prod.mkHom
        (right.hom.app M) (right.hom.app N)) =
      right.hom.app (S.obj (M, N)) ≫ R'.map (s.hom.app (M, N)) ≫
        mu'.hom.app (d.obj M, d.obj N))
    (K : C) (M : D) (N : D') (beta : d.obj M ⟶ N)
    (p : L.obj (T.obj (K, R.obj M)) ≅ S.obj (L.obj K, M))
    (hp : a.homEquiv _ _ p.hom =
      T.map (Prod.mkHom (a.unit.app K) (𝟙 _)) ≫ mu.inv.app (L.obj K, M))
    (q : S'.obj (L'.obj (e.obj K), N) ≅ L'.obj (T'.obj (e.obj K, R'.obj N)))
    (hq : a'.homEquiv _ _ q.inv =
      T'.map (Prod.mkHom (a'.unit.app (e.obj K)) (𝟙 _)) ≫
        mu'.inv.app (L'.obj (e.obj K), N)) :
    d.map p.inv ≫ left.hom.app _ ≫ L'.map
        (t.hom.app (K, R.obj M) ≫ T'.map (Prod.mkHom (𝟙 _)
          (right.hom.app M ≫ R'.map beta))) =
      s.hom.app (L.obj K, M) ≫ S'.map (Prod.mkHom (left.hom.app K) beta) ≫
        q.hom := by
  dsimp only [Functor.comp_obj, Prod.fst, Prod.snd] at *
  have hsi : e.map (mu.inv.app (L.obj K, M)) ≫
      right.hom.app (S.obj (L.obj K, M)) ≫
      R'.map (s.hom.app (L.obj K, M)) ≫ mu'.hom.app (d.obj (L.obj K), d.obj M) =
      t.hom.app (R.obj (L.obj K), R.obj M) ≫
        T'.map (Prod.mkHom (right.hom.app (L.obj K)) (right.hom.app M)) := by
    rw [← cancel_epi (e.map (mu.hom.app (L.obj K, M)))]
    simp only [← e.map_comp_assoc, Iso.hom_inv_id_app]
    erw [e.map_id, Category.id_comp]
    exact (hsq (L.obj K) M).symm
  have hf : left.inv.app _ ≫ d.map p.hom ≫ s.hom.app (L.obj K, M) ≫
      S'.map (Prod.mkHom (left.hom.app K) beta) =
      L'.map (t.hom.app (K, R.obj M) ≫ T'.map (Prod.mkHom (𝟙 _)
        (right.hom.app M ≫ R'.map beta))) ≫ q.inv := by
    apply (a'.homEquiv _ _).injective
    rw [← Category.assoc (left.inv.app _) (d.map p.hom)]
    rw [a'.homEquiv_naturality_right (left.inv.app _ ≫ d.map p.hom),
      transport_adjunct a a' e d left right hu, hp,
      a'.homEquiv_naturality_left]
    dsimp only [Functor.comp_obj, Prod.fst] at *
    rw [hq]
    simp only [Functor.map_comp, Category.assoc]
    rw [← cancel_mono (mu'.hom.app (L'.obj (e.obj K), N))]
    have hn := mu'.hom.naturality (Prod.mkHom (left.hom.app K) beta)
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj] at hn
    simp only [Category.assoc]
    rw [hn, reassoc_of% hsi]
    simp only [Iso.inv_hom_id_app]
    have ht := t.hom.naturality (Prod.mkHom (a.unit.app K) (𝟙 (R.obj M)))
    dsimp only [Functor.comp_map, Functor.prod_map] at ht
    rw [reassoc_of% ht]
    erw [e.map_id, Category.comp_id]
    simp only [← T'.map_comp, prod_comp, Category.id_comp, Category.comp_id]
    apply congrArg (t.hom.app (K, R.obj M) ≫ ·)
    apply congrArg T'.map
    apply Prod.hom_ext
    · simpa only [prod_comp, Category.id_comp, Category.assoc] using hu K
    · simp
  rw [← cancel_epi (d.map p.hom), ← cancel_mono q.inv]
  simp only [← d.map_comp_assoc, p.hom_inv_id,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← hf]
  simp only [← Category.assoc, Iso.hom_inv_id_app]
  simp only [d.map_id, Category.id_comp, Category.assoc]
  erw [Category.id_comp]

section Native
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [ProEtale.UpperStarPreservesFlat A]
open AlgebraicGeometry.ProEtale
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
private def nativePullTensor :
    Functor.uncurry.obj (derivedTensor A Y) ⋙ (upperStar A j).leftDerivedFunctor ≅
      ((upperStar A j).leftDerivedFunctor.prod (upperStar A j).leftDerivedFunctor) ⋙
        Functor.uncurry.obj (derivedTensor A X) :=
  NatIso.ofComponents (fun Z ↦ leftDerivedUpperStarTensorIso A j Z.1 Z.2) (by
    intro Z W f
    have h := (Functor.uncurry.map (leftDerivedUpperStarTensorComparison A j)).naturality f
    dsimp [Functor.uncurry, leftDerivedUpperStarDerivedTensor,
      derivedTensorLeftDerivedUpperStar, Functor.whiskeringLeft₂, Functor.postcompose₂,
      Functor.whiskeringLeft, Functor.whiskeringRight] at h ⊢
    simpa only [Functor.map_comp, leftDerivedUpperStarTensorIso_hom] using h)
omit [IsOpenImmersion j] in
private lemma nativePullTensor_hom
    (M N : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    (nativePullTensor A j).hom.app (M, N) =
      ((leftDerivedUpperStarTensorComparison A j).app M).app N := by
  exact leftDerivedUpperStarTensorIso_hom A j M N

private def nativeProjection
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (M : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    (openImmersionLowerShriek A j).mapDerivedCategory.obj
        ((Functor.uncurry.obj (derivedTensor A X)).obj
          (K, (upperStar A j).leftDerivedFunctor.obj M)) ≅
      (Functor.uncurry.obj (derivedTensor A Y)).obj
        ((openImmersionLowerShriek A j).mapDerivedCategory.obj K, M) where
  hom := ((derivedOpenImmersionLowerShriekProjectionIso A j).hom.app K).app M
  inv := ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app M
  hom_inv_id := by
    change ((derivedOpenImmersionLowerShriekProjectionIso A j).hom.app K).app M ≫
      ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app M = 𝟙 _
    have h := congrArg (fun t ↦ t.app K)
      (derivedOpenImmersionLowerShriekProjectionIso A j).hom_inv_id
    exact congrArg (fun t ↦ t.app M) h
  inv_hom_id := by
    change ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app M ≫
      ((derivedOpenImmersionLowerShriekProjectionIso A j).hom.app K).app M = 𝟙 _
    have h := congrArg (fun t ↦ t.app K)
      (derivedOpenImmersionLowerShriekProjectionIso A j).inv_hom_id
    exact congrArg (fun t ↦ t.app M) h

private lemma native_mate
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (M : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).ofNatIsoRight
      (upperStar A j).leftDerivedFunctorIsoMapDerivedCategory.symm).homEquiv _ _
        (((derivedOpenImmersionLowerShriekProjectionIso A j).hom.app K).app M) =
      (Functor.uncurry.obj (derivedTensor A X)).map
          (Prod.mkHom (((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).ofNatIsoRight
            (upperStar A j).leftDerivedFunctorIsoMapDerivedCategory.symm).unit.app K) (𝟙 _)) ≫
        (nativePullTensor A j).inv.app
          ((openImmersionLowerShriek A j).mapDerivedCategory.obj K, M) := by
  rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  rw [derivedOpenImmersionLowerShriekProjectionIso_hom]
  unfold derivedOpenImmersionLowerShriekProjectionMap
  rw [Adjunction.projectionMap_app_app, Equiv.apply_symm_apply]
  dsimp [Adjunction.projectionMapTranspose, mapDerivedCategoryUpperStarDerivedTensorIso,
    nativePullTensor, leftDerivedUpperStarTensorIso, leftDerivedUpperStarIsoMapDerivedCategory]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_hom]
  rw [(derivedTensor A X).map_comp]
  simp only [NatTrans.comp_app]
  erw [((derivedTensor A X).obj _).map_id]
  simp only [Category.id_comp, Category.assoc]

attribute [local irreducible] nativePullTensor

private lemma native_projection_transport
    {C' : Type u₃} {D' : Type u₄} [Category.{v₃} C'] [Category.{v₄} D']
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} (a' : L' ⊣ R')
    (e : DerivedCategory (Sheaf (ProEt.topology X) A) ⥤ C')
    (d : DerivedCategory (Sheaf (ProEt.topology Y) A) ⥤ D')
    (left : (openImmersionLowerShriek A j).mapDerivedCategory ⋙ d ≅ e ⋙ L')
    (right : (upperStar A j).leftDerivedFunctor ⋙ e ≅ d ⋙ R')
    (hu : ∀ K, e.map
      (((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).ofNatIsoRight
        (upperStar A j).leftDerivedFunctorIsoMapDerivedCategory.symm).unit.app K) ≫
      right.hom.app ((openImmersionLowerShriek A j).mapDerivedCategory.obj K) ≫
      R'.map (left.hom.app K) = a'.unit.app (e.obj K))
    (T' : C' × C' ⥤ C') (S' : D' × D' ⥤ D')
    (t : Functor.uncurry.obj (derivedTensor A X) ⋙ e ≅ e.prod e ⋙ T')
    (s : Functor.uncurry.obj (derivedTensor A Y) ⋙ d ≅ d.prod d ⋙ S')
    (mu' : S' ⋙ R' ≅ R'.prod R' ⋙ T')
    (hsq : ∀ M N, e.map
        (((leftDerivedUpperStarTensorComparison A j).app M).app N) ≫
      t.hom.app ((upperStar A j).leftDerivedFunctor.obj M,
        (upperStar A j).leftDerivedFunctor.obj N) ≫
      T'.map (Prod.mkHom (right.hom.app M) (right.hom.app N)) =
      right.hom.app ((Functor.uncurry.obj (derivedTensor A Y)).obj (M, N)) ≫
      R'.map (s.hom.app (M, N)) ≫ mu'.hom.app (d.obj M, d.obj N))
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (M : DerivedCategory (Sheaf (ProEt.topology Y) A))
    (N : D') (beta : d.obj M ⟶ N)
    (q : S'.obj (L'.obj (e.obj K), N) ≅
      L'.obj (T'.obj (e.obj K, R'.obj N)))
    (hq : a'.homEquiv _ _ q.inv =
      T'.map (Prod.mkHom (a'.unit.app (e.obj K)) (𝟙 _)) ≫
        mu'.inv.app (L'.obj (e.obj K), N)) :
    d.map (((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app M) ≫
      left.hom.app
        (((derivedTensorWhiskeringRightLeftDerivedUpperStar A j).obj K).obj M) ≫
      L'.map (t.hom.app (K, (upperStar A j).leftDerivedFunctor.obj M) ≫
        T'.map (Prod.mkHom (𝟙 _) (right.hom.app M ≫ R'.map beta))) =
      s.hom.app ((openImmersionLowerShriek A j).mapDerivedCategory.obj K, M) ≫
        S'.map (Prod.mkHom (left.hom.app K) beta) ≫ q.hom := by
  have h := projection_transport
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).ofNatIsoRight
      (upperStar A j).leftDerivedFunctorIsoMapDerivedCategory.symm)
    a' e d left right hu
    (Functor.uncurry.obj (derivedTensor A X))
    (Functor.uncurry.obj (derivedTensor A Y)) T' S' t s
    (nativePullTensor A j) mu'
    (by intro P Q; rw [nativePullTensor_hom]; exact hsq P Q)
    K M N beta (nativeProjection A j K M)
    (by
      simpa only [nativeProjection, Functor.uncurry,
        derivedTensorWhiskeringLeftOpenImmersionLowerShriek,
        derivedTensorWhiskeringRightLeftDerivedUpperStar, Functor.postcompose₂,
        Functor.whiskeringLeft₂, Functor.whiskeringLeft, Functor.whiskeringRight,
        Functor.comp_obj, Functor.id_obj] using native_mate A j K M)
    q hq
  simpa only [nativeProjection, Functor.uncurry,
    derivedTensorWhiskeringLeftOpenImmersionLowerShriek,
    derivedTensorWhiskeringRightLeftDerivedUpperStar, Functor.postcompose₂,
    Functor.whiskeringLeft₂, Functor.whiskeringLeft, Functor.whiskeringRight,
    Functor.comp_obj, Functor.id_obj] using h

end Native

private lemma finite_projection_transport
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [ProEtale.UpperStarPreservesFlat (ModuleCat.{u + 1} Λ)]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {C' : Type u₃} {D' : Type u₄} [Category.{v₃} C'] [Category.{v₄} D']
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} (a' : L' ⊣ R')
    (e : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⥤ C')
    (d : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ⥤ D')
    (left : (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory ⋙ d ≅ e ⋙ L')
    (right : (upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor ⋙ e ≅ d ⋙ R')
    (hu : ∀ K, e.map
      (((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} Λ) j).ofNatIsoRight
        (upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctorIsoMapDerivedCategory.symm).unit.app
          K) ≫
      right.hom.app ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj K) ≫
      R'.map (left.hom.app K) = a'.unit.app (e.obj K))
    (T' : C' × C' ⥤ C') (S' : D' × D' ⥤ D')
    (t : SheafOfModules.OpenTensorNormalization.finiteTensor Λ X ⋙ e ≅ e.prod e ⋙ T')
    (s : SheafOfModules.OpenTensorNormalization.finiteTensor Λ Y ⋙ d ≅ d.prod d ⋙ S')
    (mu' : S' ⋙ R' ≅ R'.prod R' ⋙ T')
    (hsq : ∀ M N, e.map
        (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) j).app M).app N) ≫
      t.hom.app ((upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.obj M,
        (upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.obj N) ≫
      T'.map (Prod.mkHom (right.hom.app M) (right.hom.app N)) =
      right.hom.app ((SheafOfModules.OpenTensorNormalization.finiteTensor Λ Y).obj (M, N)) ≫
      R'.map (s.hom.app (M, N)) ≫ mu'.hom.app (d.obj M, d.obj N))
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (M : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (N : D') (beta : d.obj M ⟶ N)
    (q : S'.obj (L'.obj (e.obj K), N) ≅
      L'.obj (T'.obj (e.obj K, R'.obj N)))
    (hq : a'.homEquiv _ _ q.inv =
      T'.map (Prod.mkHom (a'.unit.app (e.obj K)) (𝟙 _)) ≫
        mu'.inv.app (L'.obj (e.obj K), N)) :
    d.map (((derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} Λ) j).inv.app K).app M) ≫
      left.hom.app
        (((derivedTensorWhiskeringRightLeftDerivedUpperStar (ModuleCat.{u + 1} Λ) j).obj K).obj M) ≫
      L'.map (t.hom.app (K, (upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.obj M) ≫
        T'.map (Prod.mkHom (𝟙 _) (right.hom.app M ≫ R'.map beta))) =
      s.hom.app ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj K, M) ≫
        S'.map (Prod.mkHom (left.hom.app K) beta) ≫ q.hom := by
  exact native_projection_transport (ModuleCat.{u + 1} Λ) j
    a' e d left right hu T' S' t s mu' hsq K M N beta q hq

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard
  Padic Padic.coefficientExtensionIntegers
  comparisonFiniteOpen comparisonFinitePull
  comparisonLevelOpenAdjunction
  DerivedCategory instCategoryDerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  Functor.leftDerivedFunctor Functor.leftAdjoint sfIntrinsicModuleEquivalence
  derivedTensor upperStar

-- The fixed statement names hunit inside a forall; the proof introduces and uses it.
set_option linter.unusedVariables false in
set_option maxHeartbeats 2000000 in
-- Check the explicit conversion congruences for the large derived-functor word.
/-- The transported open projection, for an open immersion and arbitrary
second input, equals the normalized `levels.openTensor` map. No compactification
or pullback compositor occurs. The unit square is an explicit earlier hypothesis.
Source: blueprint operations proof (2), open mate comparison.
(blueprint: new-lem-sp-strict-finite-open-projection-open-mate).
Proof: apply the open adjunction Hom equivalence to the inverse maps. Transport
its unit by hunit. The pinned tensor pullback square identifies the mixed tensor
restriction map. The equation levels.openTensor_mate gives the same transpose;
injectivity identifies the inverse maps and cancellation gives the forward maps.
For beta use naturality in the second input, which follows by transposing and
using naturality of the tensor pullback and unit. This works for arbitrary open
immersions and all complexes, including zero objects and empty schemes. -/
theorem strictFiniteOpenProjectionOpenMate (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o)
    (tensor : ∀ (T : Scheme.{u}) (n : ℕ),
      SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) T ⋙ comparisonFiniteRealization l E b T n ≅
        ((comparisonFiniteRealization l E b T n).prod
          (comparisonFiniteRealization l E b T n)) ⋙
            comparisonLevelTensor l E b T n)
    (hpin : (∀ (T : Scheme.{u}) (n : ℕ),
    ∃ e : SheafOfModules.OpenTensorNormalization.FiniteRealization.{u}
        (ULift.{u + 1, u} (R l E n)) T (B l E T n)
        (comparisonFiniteConstantSection l E T n),
    ∃ t : AlgebraicGeometry.Scheme.ProjectionRestriction.TensorModel.{u} (B l E T n),
    ∃ d : SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
        (ULift.{u + 1, u} (R l E n)) T ⋙ e.derived ≅
          (e.derived.prod e.derived) ⋙ t.functor,
      HEq e.equivalence (sfIntrinsicModuleEquivalence T (R l E n)) ∧
      HEq e.underlying (comparisonFiniteUnderlying l E b T n) ∧
      HEq t.functor (comparisonLevelTensor l E b T n) ∧
      ComparisonFiniteTensorRepresentative l E b T n t ∧ HEq d (tensor T n) ∧
      Nonempty (@SheafOfModules.OpenTensorNormalization.FiniteTensorPin.{u}
        (ULift.{u + 1, u} (R l E n)) _ _ T (B l E T n)
        (comparisonFiniteConstantSection l E T n) e t d))) :
    ∀ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ)
      (hunit : ∀ K : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))),
    (comparisonFiniteRealization l E b X n).map
      (((derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) j).ofNatIsoRight
          (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
            j).leftDerivedFunctorIsoMapDerivedCategory.symm).unit.app K) ≫
      (comparisonFinitePull l E b j n).hom.app
        ((openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) j).mapDerivedCategory.obj K) ≫
      (proEtaleConstantRingDerivedPullback (R l E n) j).map
        ((comparisonFiniteOpen l E b j n).hom.app K) =
      (comparisonLevelOpenAdjunction l E b j n).unit.app
        ((comparisonFiniteRealization l E b X n).obj K))
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))))
      (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))))
      (N : proEtaleDerivedCategory Y (R l E n))
      (beta : (comparisonFiniteRealization l E b Y n).obj M ⟶ N),
      (comparisonFiniteRealization l E b Y n).map
        (((derivedOpenImmersionLowerShriekProjectionIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) j).inv.app K).app M) ≫
      (comparisonFiniteOpen l E b j n).hom.app
        (((derivedTensorWhiskeringRightLeftDerivedUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) j).obj K).obj M) ≫
      (sfIntrinsicDerivedOpen (R l E n) j).map
        ((tensor X n).hom.app
          (K, (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
            j).leftDerivedFunctor.obj M) ≫
          (comparisonLevelTensor l E b X n).map
            (Prod.mkHom (𝟙 _) ((comparisonFinitePull l E b j n).hom.app M ≫
              (proEtaleConstantRingDerivedPullback (R l E n) j).map beta))) =
      (tensor Y n).hom.app
        ((openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) j).mapDerivedCategory.obj K, M) ≫
      (comparisonLevelTensor l E b Y n).map
        (Prod.mkHom ((comparisonFiniteOpen l E b j n).hom.app K) beta) ≫
      (levels.openTensor j n ((comparisonFiniteRealization l E b X n).obj K) N).hom  := by
  intro X Y j _ n hunit K M N beta
  have H := finite_projection_transport (ULift.{u + 1, u} (R l E n)) j
    (C' := proEtaleDerivedCategory X (R l E n))
    (D' := proEtaleDerivedCategory Y (R l E n))
    (L' := sfIntrinsicDerivedOpen (R l E n) j)
    (R' := proEtaleConstantRingDerivedPullback (R l E n) j)
    (comparisonLevelOpenAdjunction l E b j n)
    (comparisonFiniteRealization l E b X n) (comparisonFiniteRealization l E b Y n)
    (comparisonFiniteOpen l E b j n) (comparisonFinitePull l E b j n)
    (by
      intro P
      have HU := hunit P
      run_tac Lean.Elab.Tactic.withMainContext do
        let h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `HU) none
        exactByConversion h)
    (comparisonLevelTensor l E b X n) (comparisonLevelTensor l E b Y n)
    (tensor X n) (tensor Y n) (levels.tensorPullback j n)
    (by
      intro P Q
      have HS := strictFiniteTensorPullbackSquare l E b o levels tensor hpin j n P Q
      run_tac Lean.Elab.Tactic.withMainContext do
        let h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `HS) none
        exactByConversion h)
    K M N beta
    (levels.openTensor j n ((comparisonFiniteRealization l E b X n).obj K) N)
    (by
      have HQ := levels.openTensor_mate j n ((comparisonFiniteRealization l E b X n).obj K) N
      run_tac Lean.Elab.Tactic.withMainContext do
        let h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `HQ) none
        exactByConversion h)
  run_tac Lean.Elab.Tactic.withMainContext do
    let h ← Lean.Elab.Term.elabTerm (Lean.mkIdent `H) none
    exactByConversion h

end AlgebraicGeometry.ProEtale.SpTowerShriek
