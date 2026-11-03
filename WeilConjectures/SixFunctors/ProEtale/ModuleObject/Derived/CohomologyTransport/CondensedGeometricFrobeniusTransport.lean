/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Lean.Meta.CongrTheorems
public import Mathlib.Logic.Function.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar

/-! # Condensed cohomology transport for geometric Frobenius

Source: latest blueprint, `def-weil-global-geometric-frobenius`, the first
isomorphism in each displayed ordinary and compact-support composite
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport).

The geometric-fibre square is constructed from the finite-field datum and the
published geometric Frobenius.  The transport laws are stated on the existing
canonical derived exchanges and compactification comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

/-- The semilinear square attached to geometric Frobenius on a finite-field fibre.
Source: Deligne, Weil II (1.1.7), pp. 150--151
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
def geometricFrobeniusGeometry (D : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [IsSeparated Y₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    Geometry D.k := by
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let Y := (D.geometricFiber Y₀).left
  let aY : Y ⟶ Spec (.of D.k) := (D.geometricFiber Y₀).hom
  let γ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
  let b : Spec (.of D.k) ≅ Spec (.of D.k) :=
    Scheme.Spec.mapIso γ.toRingEquiv.toCommRingCatIso.op
  let gY : Y ⟶ Y := (D.geometricFrobenius Y₀).hom
  have w : gY ≫ aY = aY ≫ b.hom := by
    dsimp [gY, aY, b, WeilConjectures.FiniteFieldDatum.geometricFrobenius,
      WeilConjectures.FiniteFieldDatum.galoisMap,
      WeilConjectures.FiniteFieldDatum.geometricFiber]
    exact (D.galoisMap_projections Y₀.hom γ).2
  letI : IsSeparated aY := by
    dsimp [aY, WeilConjectures.FiniteFieldDatum.geometricFiber]
    apply MorphismProperty.pullback_snd
    infer_instance
  letI : LocallyOfFiniteType aY := by
    dsimp [aY, WeilConjectures.FiniteFieldDatum.geometricFiber]
    apply MorphismProperty.pullback_snd
    infer_instance
  letI : QuasiCompact aY := by
    dsimp [aY, WeilConjectures.FiniteFieldDatum.geometricFiber]
    apply MorphismProperty.pullback_snd
    infer_instance
  exact
    { X := Y
      X' := Y
      a := aY
      a' := aY
      b := b
      h := ⟨gY, (D.geometricFrobenius Y₀).inv,
        (D.geometricFrobenius Y₀).hom_inv_id, (D.geometricFrobenius Y₀).inv_hom_id⟩
      comm := w
      separated := inferInstance
      finiteType := inferInstance
      quasiCompact := inferInstance
      separated' := inferInstance
      finiteType' := inferInstance
      quasiCompact' := inferInstance }

/-- The actual proper/open diagram obtained by reindexing along an isomorphism.
The middle scheme is unchanged; this models base change along the base automorphism.
Source: the compact-support first arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
def frobeniusReindexedSquare {k : Type u} [Field k] (q : Geometry k)
    (c : Compactification q.a) :
    CompactificationReindexing.Square c (reindex q.b.hom q.h.hom q.comm c)
      q.h.hom q.b.hom where
  middle := 𝟙 c.Z
  openSquare := by
    let : IsIso (𝟙 c.Z) := IsIso.id c.Z
    apply IsPullback.of_horiz_isIso
    exact ⟨by
      simp [reindex, Compactification.precomp, Compactification.postcomp,
        Compactification.copy]⟩
  properSquare := ⟨by
    simp [reindex, Compactification.precomp, Compactification.postcomp,
      Compactification.copy]⟩

/-- Canonically normalized comparison and compact exchange data for one fixed square.
Only compactifications of its two structure maps occur. No transport theorem for an
arbitrary semilinear square is included in this type.
Source: the compact-support first arrow of `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
structure FrobeniusTransportData {k : Type u} [Field k] (q : Geometry k) where
  pull_constructible : ∀ M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory,
    boundedConstructible (condensedRingObj Λ q.X') ((L Λ q.h.hom).obj M.obj)
  sourceCompare : ∀ c d : Compactification q.a, bc Λ q.X ⋙ C Λ c ≅ bc Λ q.X ⋙ C Λ d
  targetCompare : ∀ c d : Compactification q.a', bc Λ q.X' ⋙ C Λ c ≅ bc Λ q.X' ⋙ C Λ d
  source_refinement : ∀ (c d z : Compactification q.a)
    (r : z.Refinement c) (t : z.Refinement d)
    (M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory),
    (sourceCompare c d).hom.app M ≫ (CompactificationReindexing.refinement Λ t).app M.obj =
      (CompactificationReindexing.refinement Λ r).app M.obj
  target_refinement : ∀ (c d z : Compactification q.a')
    (r : z.Refinement c) (t : z.Refinement d)
    (M : (boundedConstructible (condensedRingObj Λ q.X')).FullSubcategory),
    (targetCompare c d).hom.app M ≫ (CompactificationReindexing.refinement Λ t).app M.obj =
      (CompactificationReindexing.refinement Λ r).app M.obj
  source_identity : ∀ c : Compactification q.a, sourceCompare c c = Iso.refl _
  target_identity : ∀ c : Compactification q.a', targetCompare c c = Iso.refl _
  source_cocycle : ∀ c d z : Compactification q.a,
    sourceCompare c d ≪≫ sourceCompare d z = sourceCompare c z
  target_cocycle : ∀ c d z : Compactification q.a',
    targetCompare c d ≪≫ targetCompare d z = targetCompare c z
  exchange : ∀ (c : Compactification q.a) (d : Compactification q.a'),
    bc Λ q.X ⋙ C Λ c ⋙ L Λ q.b.hom ≅ bc Λ q.X ⋙ L Λ q.h.hom ⋙ C Λ d
  exchange_normalization : ∀ (c : Compactification q.a) (d : Compactification q.a')
    (M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory),
    (exchange c d).hom.app M =
      (CompactificationReindexing.squareExchange Λ (frobeniusReindexedSquare q c)).app M.obj ≫
        (targetCompare (reindex q.b.hom q.h.hom q.comm c) d).hom.app
          ⟨(L Λ q.h.hom).obj M.obj, pull_constructible M⟩

/-- The compact-support transport is insertion followed by evaluation of the exchange.
Its exchange is fixed by the proper/open reindexing and common-refinement normalization.
Source: the formula t_{!,g,M} = Γ_s(e_{!,g,M}) ∘ iota in the assigned node
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
def frobeniusCompactTransport {k : Type u} [Field k] [IsAlgClosed k] (q : Geometry k)
    (S : FrobeniusTransportData Λ q) (c : Compactification q.a) (d : Compactification q.a')
    (M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory) :
    (Γ Λ (Spec (.of k))).obj ((C Λ c).obj M.obj) ⟶
      (Γ Λ (Spec (.of k))).obj ((C Λ d).obj ((L Λ q.h.hom).obj M.obj)) :=
  (insertion Λ q.b.hom).hom.app ((C Λ c).obj M.obj) ≫
    (Γ Λ (Spec (.of k))).map ((S.exchange c d).hom.app M)

/-- The transport conclusions for this square, on the specified maps in D(Λ(*)).
The two naturality equations quantify over all ambient derived morphisms between
bounded constructible objects. Homology uses the actual maps in every integer degree.
Source: the two first arrows in `def-weil-global-geometric-frobenius`
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
structure FrobeniusTransportLaws {k : Type u} [Field k] [IsAlgClosed k] (q : Geometry k)
    (S : FrobeniusTransportData Λ q) : Prop where
  ordinary_exchange_iso : ∀ M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory,
    IsIso ((ordinary Λ q.h.hom q.a' q.a q.b.hom q.comm).app M.obj)
  ordinary_iso : ∀ M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory,
    IsIso (ordinaryTransport Λ q M.obj)
  compact_iso : ∀ (c : Compactification q.a) (d : Compactification q.a')
    (M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory),
    IsIso (frobeniusCompactTransport Λ q S c d M)
  ordinary_naturality : ∀
    (M N : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory) (f : M ⟶ N),
    (Γ Λ (Spec (.of k))).map ((R Λ q.a).map f.hom) ≫ ordinaryTransport Λ q N.obj =
      ordinaryTransport Λ q M.obj ≫
        (Γ Λ (Spec (.of k))).map ((R Λ q.a').map ((L Λ q.h.hom).map f.hom))
  compact_naturality : ∀ (c : Compactification q.a) (d : Compactification q.a')
    (M N : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory) (f : M ⟶ N),
    (Γ Λ (Spec (.of k))).map ((C Λ c).map f.hom) ≫
        frobeniusCompactTransport Λ q S c d N =
      frobeniusCompactTransport Λ q S c d M ≫
        (Γ Λ (Spec (.of k))).map ((C Λ d).map ((L Λ q.h.hom).map f.hom))
  compactification_independent : ∀ (c d : Compactification q.a)
    (c' d' : Compactification q.a')
    (M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory),
    (Γ Λ (Spec (.of k))).map ((S.sourceCompare c d).hom.app M) ≫
        frobeniusCompactTransport Λ q S d d' M =
      frobeniusCompactTransport Λ q S c c' M ≫
        (Γ Λ (Spec (.of k))).map ((S.targetCompare c' d').hom.app
          ⟨(L Λ q.h.hom).obj M.obj, S.pull_constructible M⟩)
  homology_iso : ∀ (c : Compactification q.a) (d : Compactification q.a')
    (M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory) (i : ℤ),
    IsIso ((DerivedCategory.homologyFunctor _ i).map (ordinaryTransport Λ q M.obj)) ∧
      IsIso ((DerivedCategory.homologyFunctor _ i).map
        (frobeniusCompactTransport Λ q S c d M))

/-- Compose an exchange with a comparison on a full subcategory. -/
private def assembleExchange {A B C D : Type*} [Category A] [Category B]
    [Category C] [Category D] (i : A ⥤ B) (h : B ⥤ C) (F : B ⥤ D) (b : D ⥤ D)
    (g g' : C ⥤ D) (P : ObjectProperty C) (hp : ∀ x, P ((i ⋙ h).obj x))
    (e : F ⋙ b ≅ h ⋙ g) (t : P.ι ⋙ g ≅ P.ι ⋙ g') :
    i ⋙ F ⋙ b ≅ i ⋙ h ⋙ g' :=
  Functor.isoWhiskerLeft i e ≪≫ Functor.isoWhiskerLeft (P.lift (i ⋙ h) hp) t

private theorem assembleExchange_hom {A B C D : Type*} [Category A] [Category B]
    [Category C] [Category D] (i : A ⥤ B) (h : B ⥤ C) (F : B ⥤ D) (b : D ⥤ D)
    (g g' : C ⥤ D) (P : ObjectProperty C) (hp : ∀ x, P ((i ⋙ h).obj x))
    (e : F ⋙ b ≅ h ⋙ g) (t : P.ι ⋙ g ≅ P.ι ⋙ g') (x : A) :
    (assembleExchange i h F b g g' P hp e t).hom.app x =
      e.hom.app (i.obj x) ≫ t.hom.app ⟨h.obj (i.obj x), hp x⟩ := by
  rfl

/-- Congruence of dependent function spaces under heterogeneous equality of their families. -/
private theorem modelPiHEq {α α' : Sort v} {β : α → Sort w} {β' : α' → Sort w}
    (hα : α = α') (hβ : HEq β β') : HEq (∀ x, β x) (∀ x, β' x) := by
  cases hα
  cases hβ
  exact HEq.rfl

/-- Apply heterogeneous equal functions to heterogeneous equal arguments. -/
private theorem modelAppHEq {α α' : Sort v} {β : α → Sort w} {β' : α' → Sort w}
    {f : ∀ x, β x} {f' : ∀ x, β' x} {x : α} {x' : α'}
    (hα : α = α') (hβ : HEq β β') (hf : HEq f f') (hx : HEq x x') :
    HEq (f x) (f' x') := by
  cases hα
  cases hβ
  cases hf
  cases hx
  exact HEq.rfl

/-- Equality transport preserves its argument heterogeneously. -/
private theorem modelCastHEq {α β : Sort v} (h : α = β) (x : α) :
    HEq (Eq.mp h x) x := by
  cases h
  exact HEq.rfl

/-- Dependent equality elimination preserves the transported data heterogeneously. -/
private theorem modelRecHEq {α : Sort v} {a : α}
    {motive : (b : α) → a = b → Sort w} (z : motive a rfl) {b : α} (h : a = b) :
    HEq (Eq.rec (motive := motive) z h) z := by
  cases h
  exact HEq.rfl

private theorem modelNdrecHEq {α : Sort v} {a : α}
    {motive : α → Sort w} (z : motive a) {b : α} (h : a = b) :
    HEq (Eq.ndrec (motive := motive) z h) z := by
  cases h
  exact HEq.rfl

/-- Syntactic equality allowing the kernel's inexpensive universe-level equality. -/
private def modelSame : Nat → Expr → Expr → MetaM Bool
  | 0, a, b => pure (a == b)
  | n + 1, a, b => do
    if a == b then return true
    match a, b with
    | .mdata _ a, b => modelSame n a b
    | a, .mdata _ b => modelSame n a b
    | .sort u, .sort v => isLevelDefEq u v
    | .const na us, .const nb vs =>
      if na != nb || us.length != vs.length then return false
      for u in us, v in vs do
        unless ← isLevelDefEq u v do return false
      return true
    | .app f x, .app g y =>
      if !(← modelSame n f g) then return false
      modelSame n x y
    | .lam _ t b _, .lam _ t' b' _
    | .forallE _ t b _, .forallE _ t' b' _ =>
      if !(← modelSame n t t') then return false
      modelSame n b b'
    | .proj s i x, .proj s' i' y =>
      if s != s' || i != i' then return false
      modelSame n x y
    | _, _ => return false

private def modelHead (e : Expr) : MetaM Expr := do
  let mut e ← instantiateMVars e
  for _ in [:20] do
    let old := e
    match e with
    | .mdata _ b => e := b
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .fvar id =>
      let d ← id.getDecl
      if let some v := d.value? then
        if !(← isProp d.type) then e := v
    | _ =>
      match e.getAppFn with
      | .fvar id =>
        let d ← id.getDecl
        if let some v := d.value? then
          if !(← isProp d.type) then e := mkAppN v e.getAppArgs |>.headBeta
      | .proj name idx b =>
        let mode := if name == ``CategoryTheory.Functor || name == ``NatTrans || name == ``Iso then
          TransparencyMode.default else TransparencyMode.instances
        if let some v ← withTransparency mode <| project? b idx then
          e := mkAppN v e.getAppArgs |>.headBeta
      | .const fn _ =>
        if let some pi ← getProjectionFnInfo? fn then
          let args := e.getAppArgs
          if args.size > pi.numParams then
            let mode := if fn == ``Functor.obj || fn == ``Functor.map ||
                fn == ``NatTrans.app || fn == ``Iso.hom || fn == ``Iso.inv then
              TransparencyMode.default else TransparencyMode.instances
            if let some v ← withTransparency mode <| project? args[pi.numParams]! pi.i then
              e := mkAppN v (args.extract (pi.numParams + 1) args.size) |>.headBeta
      | _ => e := e.headBeta
    if e == old then break
  return e

private def modelProjection (name : Name) (idx : Nat) (b : Expr) : MetaM Expr := do
  let env ← getEnv
  let info := (getStructureInfo? env name).get!
  let fn := (getProjFnForField? env name (info.fieldNames[idx]!)).get!
  let type ← whnf (← inferType b)
  let .const _ us := type.getAppFn | throwError "Expected a model structure: {b}"
  return mkAppN (mkConst fn us) (type.getAppArgs.push b)

/-- Construct congruence explicitly, retaining separate proof arguments until proof irrelevance. -/
private def modelHEq (cache : IO.Ref (Std.HashMap (Expr × Expr) Expr))
    (cc : IO.Ref (Std.HashMap (Expr × Nat) CongrTheorem)) :
    Nat → Expr → Expr → MetaM Expr
  | 0, a, b => throwError "Model congruence exceeded its depth: {a} versus {b}"
  | n + 1, a, b => do
    let a ← modelHead a
    let b ← modelHead b
    let key := (a, b)
    let memo ← cache.get
    if let some h := memo[key]? then return h
    let h ← do
      if ← modelSame 256 a b then return ← mkHEqRefl a
      if (← isProof a) && (← isProof b) then
        if ← modelSame 256 (← inferType a) (← inferType b) then
          return ← mkHEqRefl a
        return ← mkAppM ``proof_irrel_heq #[a, b]
      if a.isAppOfArity ``Eq.mp 4 then
        let args := a.getAppArgs
        let h ← mkAppM ``modelCastHEq #[args[2]!, args[3]!]
        let h' ← modelHEq cache cc n args[3]! b
        return ← mkAppM ``HEq.trans #[h, h']
      if b.isAppOfArity ``Eq.mp 4 then
        let args := b.getAppArgs
        let h ← mkAppM ``modelCastHEq #[args[2]!, args[3]!]
        let h ← mkAppM ``HEq.symm #[h]
        let h' ← modelHEq cache cc n a args[3]!
        return ← mkAppM ``HEq.trans #[h', h]
      if a.isAppOfArity ``Eq.rec 6 then
        let args := a.getAppArgs
        let h ← mkAppOptM ``modelRecHEq (args.map some)
        let h' ← modelHEq cache cc n args[3]! b
        return ← mkAppM ``HEq.trans #[h, h']
      if b.isAppOfArity ``Eq.rec 6 then
        let args := b.getAppArgs
        let h ← mkAppOptM ``modelRecHEq (args.map some)
        let h ← mkAppM ``HEq.symm #[h]
        let h' ← modelHEq cache cc n a args[3]!
        return ← mkAppM ``HEq.trans #[h', h]
      if a.isAppOfArity ``Eq.ndrec 6 then
        let args := a.getAppArgs
        let h ← mkAppOptM ``modelNdrecHEq (args.map some)
        let h' ← modelHEq cache cc n args[3]! b
        return ← mkAppM ``HEq.trans #[h, h']
      if b.isAppOfArity ``Eq.ndrec 6 then
        let args := b.getAppArgs
        let h ← mkAppOptM ``modelNdrecHEq (args.map some)
        let h ← mkAppM ``HEq.symm #[h]
        let h' ← modelHEq cache cc n a args[3]!
        return ← mkAppM ``HEq.trans #[h', h]
      for d in ← getLCtx do
        if let some (_, x, _, y) := d.type.heq? then
          if x == a && y == b then return d.toExpr
        if let some (_, x, y) := d.type.eq? then
          if x == a && y == b then return ← mkAppM ``heq_of_eq #[d.toExpr]
      if let .proj name idx x := a.getAppFn then
        let f ← modelProjection name idx x
        return ← modelHEq cache cc n (mkAppN f a.getAppArgs) b
      if let .proj name idx x := b.getAppFn then
        let f ← modelProjection name idx x
        return ← modelHEq cache cc n a (mkAppN f b.getAppArgs)
      if a.isApp && b.isApp && (← modelSame 256 a.getAppFn b.getAppFn) &&
          a.getAppNumArgs == b.getAppNumArgs then
        let ck := (a.getAppFn, a.getAppNumArgs)
        let thm ← match (← cc.get).get? ck with
          | some thm => pure thm
          | none => do
            let thm ← if a.getAppFn.isConst then
              withLCtx {} {} <| mkHCongrWithArity a.getAppFn a.getAppNumArgs
              else mkHCongrWithArity a.getAppFn a.getAppNumArgs
            let proof ← mkAuxTheorem thm.type thm.proof (kind? := `_frobeniusCongruence)
            let thm := { thm with proof := proof }
            cc.modify (·.insert ck thm)
            pure thm
        unless thm.argKinds.size == a.getAppNumArgs do
          throwError "Overapplied model function: {a.getAppFn}"
        let mut args := #[]
        for x in a.getAppArgs, y in b.getAppArgs, kind in thm.argKinds do
          let h ← modelHEq cache cc n x y
          let h ← if kind == CongrArgKind.eq then mkAppM ``eq_of_heq #[h] else pure h
          args := args.push x |>.push y |>.push h
        let h := mkAppN thm.proof args
        if (← inferType h).isEq then return ← mkAppM ``heq_of_eq #[h]
        return h
      if a.isApp && b.isApp && a.getAppFn != b.getAppFn then
        if let .const fn _ := a.getAppFn then
          if (← getProjectionFnInfo? fn).isNone then
            if let some a' ← unfoldDefinition? a then return ← modelHEq cache cc n a' b
        if let .const fn _ := b.getAppFn then
          if (← getProjectionFnInfo? fn).isNone then
            if let some b' ← unfoldDefinition? b then return ← modelHEq cache cc n a b'
      if a.isLambda != b.isLambda then
        let other := if a.isLambda then b else a
        if let .forallE name domain _ bi ← whnf (← inferType other) then
          let expanded ← withLocalDecl name bi domain fun x =>
            mkLambdaFVars #[x] (mkApp other x)
          if a.isLambda then return ← modelHEq cache cc n a expanded
          return ← modelHEq cache cc n expanded b
      if let .app f x := a then
        if let .app g y := b then
          unless a.getAppFn.isFVar && b.getAppFn.isFVar do
            throwError "Unaligned model heads: {a.getAppFn} / {b.getAppFn}\n{a} / {b}"
          let .forallE na α body bi ← whnf (← inferType f) |
            throwError "Expected function: {f}"
          let .forallE nb α' body' bj ← whnf (← inferType g) |
            throwError "Expected function: {g}"
          let hd ← modelHEq cache cc n α α'
          let hd ← mkAppM ``eq_of_heq #[hd]
          let hβ ← modelHEq cache cc n (.lam na α body bi) (.lam nb α' body' bj)
          let hf ← modelHEq cache cc n f g
          let hx ← modelHEq cache cc n x y
          return ← mkAppM ``modelAppHEq #[hd, hβ, hf, hx]
      match a, b with
      | .lam _ α body _, .lam _ α' body' _ =>
        let hd ← modelHEq cache cc n α α'
        let hd ← mkAppM ``eq_of_heq #[hd]
        withLocalDeclD `x α fun x =>
          withLocalDeclD `y α' fun y => do
            withLocalDeclD `hxy (← mkHEq x y) fun hxy => do
              let h ← modelHEq cache cc n (body.instantiate1 x) (body'.instantiate1 y)
              let hp ← mkLambdaFVars #[x, y, hxy] h
              mkAppM ``Function.hfunext #[hd, hp]
      | .forallE na α body bi, .forallE nb α' body' bj =>
        let hd ← modelHEq cache cc n α α'
        let hd ← mkAppM ``eq_of_heq #[hd]
        let hf ← modelHEq cache cc n (.lam na α body bi) (.lam nb α' body' bj)
        mkAppM ``modelPiHEq #[hd, hf]
      | .sort _, .sort _ =>
        if ← isDefEq a b then return ← mkHEqRefl a
        throwError "Different model universes: {a} / {b}"
      | _, _ =>
        if let some a' ← unfoldDefinition? a then return ← modelHEq cache cc n a' b
        if let some b' ← unfoldDefinition? b then return ← modelHEq cache cc n a b'
        throwError "Unmatched model expressions: {a} / {b}"
    let h ← if a == b then pure h else
      mkAuxTheorem (← mkHEq a b) h (zetaDelta := true) (kind? := `_frobeniusEquality)
    cache.modify (·.insert key h)
    return h

private def reindexRefinement {k : Type u} [Field k] (q : Geometry k)
    {c d : Compactification q.a} (r : c.Refinement d) :
    (reindex q.b.hom q.h.hom q.comm c).Refinement
      (reindex q.b.hom q.h.hom q.comm d) where
  hom := r.hom
  i_hom := by
    change (q.h.hom ≫ c.i) ≫ r.hom = q.h.hom ≫ d.i
    rw [Category.assoc, r.i_hom]
  hom_g := by
    change r.hom ≫ (d.g ≫ inv q.b.hom) = c.g ≫ inv q.b.hom
    rw [← Category.assoc, r.hom_g]

private theorem reindex_refinement_exchange {k : Type u} [Field k] (q : Geometry k)
    {c d : Compactification q.a} (r : c.Refinement d) (K : D Λ q.X) :
    (CompactificationReindexing.P Λ q.b.hom).map
        ((CompactificationReindexing.refinement Λ r).app K) ≫
        (CompactificationReindexing.squareExchange Λ (frobeniusReindexedSquare q c)).app K =
      (CompactificationReindexing.squareExchange Λ (frobeniusReindexedSquare q d)).app K ≫
        (CompactificationReindexing.refinement Λ (reindexRefinement q r)).app
          ((CompactificationReindexing.P Λ q.h.hom).obj K) := by
  let : IsIso (frobeniusReindexedSquare q c).middle := IsIso.id _
  let : IsIso (frobeniusReindexedSquare q d).middle := IsIso.id _
  exact CompactificationReindexing.refinement_cube Λ r (reindexRefinement q r)
    (frobeniusReindexedSquare q c) (frobeniusReindexedSquare q d)
    (by
      change r.hom ≫ 𝟙 d.Z = 𝟙 c.Z ≫ r.hom
      simp only [Category.comp_id, Category.id_comp]) K

private theorem comparison_square {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {a b z : A} {a' b' z' : B}
    (f : a ⟶ b) (r : a ⟶ z) (t : b ⟶ z)
    (f' : a' ⟶ b') (r' : a' ⟶ z') (t' : b' ⟶ z') [Mono t']
    (e₁ : F.obj a ⟶ a') (e₂ : F.obj b ⟶ b') (e₃ : F.obj z ⟶ z')
    (hr : F.map r ≫ e₃ = e₁ ≫ r') (ht : F.map t ≫ e₃ = e₂ ≫ t')
    (hf : f ≫ t = r) (hf' : f' ≫ t' = r') :
    F.map f ≫ e₂ = e₁ ≫ f' := by
  apply (cancel_mono t').1
  rw [Category.assoc, ← ht, ← Category.assoc, ← F.map_comp, hf, hr,
    Category.assoc, hf']

private theorem exchange_comparison {k : Type u} [Field k] (q : Geometry k)
    (S : FrobeniusTransportData Λ q)
    (hiso : ∀ {c d : Compactification q.a'} (r : c.Refinement d)
      (M : (boundedConstructible (condensedRingObj Λ q.X')).FullSubcategory),
      IsIso ((CompactificationReindexing.refinement Λ r).app M.obj))
    (c d z : Compactification q.a) (r : z.Refinement c) (t : z.Refinement d)
    (M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory) :
    (L Λ q.b.hom).map ((S.sourceCompare c d).hom.app M) ≫
        (CompactificationReindexing.squareExchange Λ (frobeniusReindexedSquare q d)).app
          M.obj =
      (CompactificationReindexing.squareExchange Λ (frobeniusReindexedSquare q c)).app
          M.obj ≫
        (S.targetCompare (reindex q.b.hom q.h.hom q.comm c)
          (reindex q.b.hom q.h.hom q.comm d)).hom.app
            ⟨(L Λ q.h.hom).obj M.obj, S.pull_constructible M⟩ := by
  let M' : (boundedConstructible (condensedRingObj Λ q.X')).FullSubcategory :=
    ⟨(L Λ q.h.hom).obj M.obj, S.pull_constructible M⟩
  have := hiso (reindexRefinement q t) M'
  refine comparison_square (L Λ q.b.hom)
    ((S.sourceCompare c d).hom.app M)
    ((CompactificationReindexing.refinement Λ r).app M.obj)
    ((CompactificationReindexing.refinement Λ t).app M.obj)
    ((S.targetCompare _ _).hom.app M')
    ((CompactificationReindexing.refinement Λ (reindexRefinement q r)).app M'.obj)
    ((CompactificationReindexing.refinement Λ (reindexRefinement q t)).app M'.obj)
    ((CompactificationReindexing.squareExchange Λ (frobeniusReindexedSquare q c)).app M.obj)
    ((CompactificationReindexing.squareExchange Λ (frobeniusReindexedSquare q d)).app M.obj)
    ((CompactificationReindexing.squareExchange Λ (frobeniusReindexedSquare q z)).app M.obj)
    ?_ ?_ ?_ ?_
  · transport_exact (reindex_refinement_exchange Λ q r M.obj)
  · transport_exact (reindex_refinement_exchange Λ q t M.obj)
  · transport_exact (S.source_refinement c d z r t M)
  · transport_exact (S.target_refinement _ _ _ (reindexRefinement q r)
      (reindexRefinement q t) M')

private theorem transport_laws {k : Type u} [Field k] [IsAlgClosed k] (q : Geometry k)
    (S : FrobeniusTransportData Λ q)
    (hiso : ∀ {c d : Compactification q.a'} (r : c.Refinement d)
      (M : (boundedConstructible (condensedRingObj Λ q.X')).FullSubcategory),
      IsIso ((CompactificationReindexing.refinement Λ r).app M.obj)) :
    FrobeniusTransportLaws Λ q S := by
  have ho : IsIso (ordinary Λ q.h.hom q.a' q.a q.b.hom q.comm) := by
    have : (L Λ q.b.hom).IsEquivalence := by
      unfold L moduleObjectDerivedPullback
      infer_instance
    have : (L Λ q.h.hom).IsEquivalence := by
      unfold L moduleObjectDerivedPullback
      infer_instance
    exact Adjunction.isIso_exchangeRight_of_isEquivalence
      (derivedUpperStarLowerStarAdjunction Λ q.a)
      (derivedUpperStarLowerStarAdjunction Λ q.a') (square Λ q.h.hom q.a' q.a q.b.hom q.comm)
  have hoi (M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory) :
      IsIso (ordinaryTransport Λ q M.obj) := by
    unfold ordinaryTransport t
    infer_instance
  have hci (c : Compactification q.a) (d : Compactification q.a')
      (M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory) :
      IsIso (frobeniusCompactTransport Λ q S c d M) := by
    unfold frobeniusCompactTransport
    infer_instance
  refine ⟨fun _ ↦ inferInstance, hoi, hci, ?_, ?_, ?_, ?_⟩
  · intro M N f
    let e : R Λ q.a ⋙ Γ Λ (Spec (.of k)) ⟶
        L Λ q.h.hom ⋙ R Λ q.a' ⋙ Γ Λ (Spec (.of k)) :=
      Functor.whiskerLeft (R Λ q.a) (insertion Λ q.b.hom).hom ≫
        Functor.whiskerRight (ordinary Λ q.h.hom q.a' q.a q.b.hom q.comm)
          (Γ Λ (Spec (.of k)))
    exact e.naturality f.hom
  · intro c d M N f
    let e : bc Λ q.X ⋙ C Λ c ⋙ Γ Λ (Spec (.of k)) ⟶
        bc Λ q.X ⋙ L Λ q.h.hom ⋙ C Λ d ⋙ Γ Λ (Spec (.of k)) :=
      Functor.whiskerLeft (bc Λ q.X ⋙ C Λ c) (insertion Λ q.b.hom).hom ≫
        Functor.whiskerRight (S.exchange c d).hom (Γ Λ (Spec (.of k)))
    exact e.naturality f
  · intro c d c' d' M
    let M' : (boundedConstructible (condensedRingObj Λ q.X')).FullSubcategory :=
      ⟨(L Λ q.h.hom).obj M.obj, S.pull_constructible M⟩
    have hcoc (x y z : Compactification q.a') :
        (S.targetCompare x y).hom.app M' ≫ (S.targetCompare y z).hom.app M' =
          (S.targetCompare x z).hom.app M' := by
      exact congrArg (fun e ↦ e.hom.app M') (S.target_cocycle x y z)
    have he :
        (L Λ q.b.hom).map ((S.sourceCompare c d).hom.app M) ≫
            (S.exchange d d').hom.app M =
          (S.exchange c c').hom.app M ≫ (S.targetCompare c' d').hom.app M' := by
      rw [S.exchange_normalization, S.exchange_normalization,
        ← Category.assoc, exchange_comparison Λ q S hiso c d (Compactification.inf c d)
          (Compactification.infFst c d) (Compactification.infSnd c d) M]
      simp only [Category.assoc]
      change _ ≫ (S.targetCompare _ _).hom.app M' ≫
          (S.targetCompare _ _).hom.app M' =
        _ ≫ (S.targetCompare _ _).hom.app M' ≫ (S.targetCompare _ _).hom.app M'
      rw [hcoc, hcoc]
    have hi := (insertion Λ q.b.hom).hom.naturality ((S.sourceCompare c d).hom.app M)
    change (Γ Λ (Spec (.of k))).map ((S.sourceCompare c d).hom.app M) ≫
        (insertion Λ q.b.hom).hom.app ((C Λ d).obj M.obj) =
      (insertion Λ q.b.hom).hom.app ((C Λ c).obj M.obj) ≫
        (Γ Λ (Spec (.of k))).map
          ((L Λ q.b.hom).map ((S.sourceCompare c d).hom.app M)) at hi
    unfold frobeniusCompactTransport
    rw [← Category.assoc, hi, Category.assoc, ← Functor.map_comp,
      he, Functor.map_comp, Category.assoc]
  · intro c d M i
    have := hoi M
    have := hci c d M
    exact ⟨inferInstance, inferInstance⟩

private theorem comparison_data_rational (k : Type u) [Field k] [IsAlgClosed k]
    (ell : ℕ) [Fact ell.Prime] [Fact (ringChar k ≠ ell)]
    (hΛ : Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj.{u} ell) ∨
      ∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj.{u} E.1)) (q : Geometry k) :
    ∃ S : FrobeniusTransportData Λ q, FrobeniusTransportLaws Λ q S := by
  letI sourceOver : q.X.Over (Spec (.of k)) := ⟨q.a⟩
  letI targetOver : q.X'.Over (Spec (.of k)) := ⟨q.a'⟩
  letI pointOver : (Spec (.of k)).Over (Spec (.of k)) := ⟨𝟙 _⟩
  let : q.a.IsOver (Spec (.of k)) := ⟨by
    dsimp only [CategoryTheory.over, sourceOver, pointOver]
    exact Category.comp_id _⟩
  let : q.a'.IsOver (Spec (.of k)) := ⟨by
    dsimp only [CategoryTheory.over, targetOver, pointOver]
    exact Category.comp_id _⟩
  let : LocallyOfFiniteType (q.X ↘ Spec (.of k)) := q.finiteType
  let : QuasiCompact (q.X ↘ Spec (.of k)) := q.quasiCompact
  let : LocallyOfFiniteType (q.X' ↘ Spec (.of k)) := q.finiteType'
  let : QuasiCompact (q.X' ↘ Spec (.of k)) := q.quasiCompact'
  obtain ⟨σ, hσ, hσid, hσcomp, _⟩ :=
    CompactificationReindexing.condensed_compactification_reindexing Λ ell hΛ k q.a
  obtain ⟨τ, hτ, hτid, hτcomp, _⟩ :=
    CompactificationReindexing.condensed_compactification_reindexing Λ ell hΛ k q.a'
  have hp (M : (boundedConstructible (condensedRingObj Λ q.X)).FullSubcategory) :
      boundedConstructible (condensedRingObj Λ q.X') ((L Λ q.h.hom).obj M.obj) :=
    boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ q.h.hom M.obj M.property
  have hsq (c : Compactification q.a) :
      IsIso (CompactificationReindexing.squareExchange Λ (frobeniusReindexedSquare q c)) := by
    let : IsIso (frobeniusReindexedSquare q c).middle := IsIso.id _
    exact (CompactificationReindexing.square_isIso Λ (frobeniusReindexedSquare q c)
      ⟨q.comm⟩).2
  let S : FrobeniusTransportData Λ q :=
    { pull_constructible := hp
      sourceCompare := σ
      targetCompare := τ
      source_refinement := by transport_exact hσ
      target_refinement := by transport_exact hτ
      source_identity := by transport_exact hσid
      target_identity := by transport_exact hτid
      source_cocycle := by transport_exact hσcomp
      target_cocycle := by transport_exact hτcomp
      exchange := fun c d ↦ by
        have := hsq c
        let Q := boundedConstructible (condensedRingObj Λ q.X')
        have hp' : ∀ M, Q ((bc Λ q.X ⋙ L Λ q.h.hom).obj M) := by
          transport_exact hp
        let ec : C Λ c ⋙ L Λ q.b.hom ≅
            L Λ q.h.hom ⋙ C Λ (reindex q.b.hom q.h.hom q.comm c) := by
          transport_exact
            (asIso (CompactificationReindexing.squareExchange Λ (frobeniusReindexedSquare q c)))
        let tc : Q.ι ⋙ C Λ (reindex q.b.hom q.h.hom q.comm c) ≅ Q.ι ⋙ C Λ d := by
          transport_exact (τ (reindex q.b.hom q.h.hom q.comm c) d)
        exact assembleExchange (bc Λ q.X) (L Λ q.h.hom) (C Λ c) (L Λ q.b.hom)
          (C Λ (reindex q.b.hom q.h.hom q.comm c)) (C Λ d) Q hp' ec tc
      exchange_normalization := by
        intro c d M
        rw [assembleExchange_hom]
        transport_congr }
  refine ⟨S, transport_laws Λ q S ?_⟩
  intro c d r M
  exact CompactificationReindexing.rational_refinement_isIso Λ ell hΛ k r M.obj M.property

private theorem comparison_data (k : Type u) [Field k] [IsAlgClosed k]
    (ell : ℕ) [Fact ell.Prime] [Fact (ringChar k ≠ ell)]
    (E : PadicAlgCl.FiniteIntermediateField ell) (closure : Bool) (q : Geometry k) :
    ∃ S : FrobeniusTransportData (coefficient.{u} ell E closure) q,
      FrobeniusTransportLaws (coefficient.{u} ell E closure) q S := by
  apply comparison_data_rational (coefficient.{u} ell E closure) k ell ?_ q
  cases closure
  · exact Or.inr ⟨E, rfl⟩
  · exact Or.inl rfl

/-- Geometric Frobenius preserves bounded constructibility and gives the two specified
natural scalar-linear isomorphisms of derived cohomology objects. Exact terminal
sections identify the derived evaluation with evaluation applied termwise.

Source: latest blueprint, `def-weil-global-geometric-frobenius`, the first isomorphism
in each displayed ordinary and compact-support composite
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport).

Proof:
1. The published geometric-fibre Frobenius is an automorphism over Spec(γ), with
   g_Y;a_Y = a_Y;Spec(γ). Its exact inverse image preserves bounded constructible
   complexes; this assertion needs no Weil structure on M.
2. The ordinary exchange is the unit/compositor/counit mate of this square.
   Inverse images along its horizontal isomorphisms are equivalences, so this
   specified mate is invertible and natural.
3. Reindex a compactification along the base automorphism. On its proper part use
   the ordinary exchange and on its open part the inverse open-adjunction mate.
   The finite-extension and finite-subextension-valued algebraic-closure comparison
   theorem gives invertible proper refinements on bounded constructible inputs.
   Compare to the target compactification through a common refinement. Refinement
   normalization, independence and cocycle identify these maps for every choice.
4. Terminal evaluation on the algebraically closed point is exact. Restriction
   along b gives the insertion map and preserves the constant scalars Λ(*), by
   the monoidal pullback-from-point comparison. The maps are therefore linear.
   Compose insertion with evaluation of the two exchanges. Their naturality gives
   the displayed naturality equations, and refinement descent gives independence.
5. Apply the ordinary homology functor in every i : ℤ to these derived
   isomorphisms. It preserves the inverse equations and yields both H^i transports.
-/
theorem geometricFrobeniusCohomologyTransport
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀)))
    [IsSeparated Y₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ F.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (closure : Bool) :
    letI : IsAlgClosed F.k := IsAlgClosure.isAlgClosed F.k₀
    let Λ := coefficient.{u} ell E closure
    let q := geometricFrobeniusGeometry F Y₀
    (sections Λ (Spec (.of F.k))).PreservesHomology ∧
      IsIso (sections Λ (Spec (.of F.k))).rightDerivedFunctorUnit ∧
      ∃ S : FrobeniusTransportData Λ q, FrobeniusTransportLaws Λ q S := by
  sorry

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

set_option maxHeartbeats 0 in
-- Repeated native derived-functor endpoints need more elaboration heartbeats.
end AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport
