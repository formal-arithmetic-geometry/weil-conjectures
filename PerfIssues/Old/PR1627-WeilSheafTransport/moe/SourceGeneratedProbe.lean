/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import MOEStage

import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraLiftOfStr
import WeilConjectures.WeilSheaf.Category

/-!
# Transport of Weil sheaves to a finite extension of the base field

Let `Y` be a `k₀`-scheme and `Y'` a `k₀'`-scheme, and let `θ : Ȳ ≅ Ȳ'` be an isomorphism of
their geometric fibers intertwining the `r`-th power of the geometric Galois Frobenius of `Ȳ`
with that of `Ȳ'`, `θ ≫ Fr' = Frʳ ≫ θ`. A pro-étale Weil sheaf `(K, φ)` on `Y` gives the
pro-étale Weil sheaf `(θ_* K, φ_r)` on `Y'`, whose Weil structure is the `r`-fold iterate of
`φ` (`AlgebraicGeometry.ProEtaleWeilSheaf.frobeniusPowIso`), transported along `θ`:

`Fr'^* θ_* K ≅ θ_* (Frʳ)^* K --θ_* φ_r--> θ_* K`.

## Main definitions

- `AlgebraicGeometry.ProEtaleWeilSheaf.frobeniusPowIso`: the iterated Weil structure
  `φ_m : (Frᵐ)^* K ≅ K` of a pro-étale Weil sheaf.
- `AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor`: `(K, φ) ↦ (K, φ_r)`.
- `AlgebraicGeometry.ProEtaleWeilSheaf.transport`: `(K, φ) ↦ (θ_* K, θ_* φ_r)`.

## Implementation notes

`powFunctor` is an instance of the generic `CategoryTheory.Endofunctor.IsoAlgebra.liftOfStr`, and
its lemmas and instances, together with those of `transport`, are instances of the generic ones.
Proving them directly makes the kernel compare `frobeniusPowPullback k₀ l Y r` with
`WeilSheaf.frobeniusPullback k₀ l Y`, which is slow and memory-hungry.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

noncomputable section

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]

/-- The iterated Weil structure `φ_m : (Frᵐ)^* K ≅ K` of a pro-étale Weil sheaf, the ordered
composite `(Fr^{m+1})^* K ≅ Fr^* (Frᵐ)^* K --Fr^* φ_m--> Fr^* K --φ--> K`, with `φ_0` the
identification `𝟙^* K ≅ K`; the pullback along an automorphism `g` is the pushforward along
`g⁻¹`. This is `AlgebraicGeometry.WeilSheaf.frobeniusPowIso` for all pro-étale Weil sheaves. -/
def frobeniusPowIso (K : ProEtaleWeilSheaf k₀ l Y) : (m : ℕ) →
    ((((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*ᵃ[l].obj K.carrier ≅
      K.carrier)
  | 0 => (adicLowerStarCongr l (by rw [pow_zero]; rfl)).app _ ≪≫ (adicLowerStarId l _).app _
  | m + 1 =>
    (adicLowerStarCongr l (by rw [pow_succ, Aut.mul_asIso, Iso.trans_inv])).app _ ≪≫
      (adicLowerStarComp l _ _).symm.app _ ≪≫
      (WeilSheaf.frobeniusPullback k₀ l Y).mapIso (K.frobeniusPowIso m) ≪≫ K.str

lemma _root_.AlgebraicGeometry.WeilSheaf.frobeniusPowIso_eq [Fact (ringChar k₀ ≠ l)]
    (F : WeilSheaf k₀ l Y) (m : ℕ) : F.frobeniusPowIso m = F.obj.frobeniusPowIso m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [WeilSheaf.frobeniusPowIso, frobeniusPowIso, ih]

/-- The iterated Weil structures are natural. -/
@[reassoc]
lemma frobeniusPowIso_hom_naturality {K K' : ProEtaleWeilSheaf k₀ l Y} (φ : K ⟶ K') (m : ℕ) :
    (((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*ᵃ[l].map φ.hom.f ≫
        (K'.frobeniusPowIso m).hom =
      (K.frobeniusPowIso m).hom ≫ φ.hom.f := by
  induction m with
  | zero =>
    simp only [frobeniusPowIso, Iso.trans_hom, Iso.app_hom, Category.assoc]
    erw [NatTrans.naturality_assoc, NatTrans.naturality]
    rfl
  | succ m ih =>
    have h₁ := (WeilSheaf.frobeniusPullback k₀ l Y).congr_map ih
    rw [Functor.map_comp, Functor.map_comp] at h₁
    simp only [frobeniusPowIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
      Category.assoc]
    erw [NatTrans.naturality_assoc, NatTrans.naturality_assoc, reassoc_of% h₁]
    erw [φ.hom.h]
    rfl

variable (k₀ l Y) in
/-- The pushforward `((Frᵐ)⁻¹)_* = (Frᵐ)^*` along the inverse of the `m`-th power of the
geometric Galois Frobenius. -/
abbrev frobeniusPowPullback (m : ℕ) :
    AdicSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber ⥤
      AdicSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  ((((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*ᵃ[l])

variable (k₀ l Y) in
/-- The `r`-th power of a Weil structure: `(K, φ) ↦ (K, φ_r)`, a pro-étale sheaf with an
isomorphism `(Frʳ)^* K ≅ K`. -/
def powFunctor (r : ℕ) :
    ProEtaleWeilSheaf k₀ l Y ⥤ IsoAlgebra (frobeniusPowPullback k₀ l Y r) where
  obj K := IsoAlgebra.mk K.carrier (K.frobeniusPowIso r)
  map φ := ObjectProperty.homMk
    { f := φ.hom.f
      h := frobeniusPowIso_hom_naturality φ r }

end AlgebraicGeometry.ProEtaleWeilSheaf

open Lean Lean.Meta

set_option maxHeartbeats 10000000

private def proofHead (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => s!"const {n}"
  | .proj n i _ => s!"proj {n}.{i}"
  | .fvar .. => "fvar"
  | .bvar i => s!"bvar {i}"
  | .lam .. => "lambda"
  | .forallE .. => "forall"
  | .letE .. => "let"
  | .mdata .. => "metadata"
  | _ => "other"

private def auditProofPrefix (env : Environment) (name : Name) : MetaM Unit := do
  let info ← getConstInfo name
  let value := info.value! (allowOpaque := true)
  lambdaTelescope value fun xs body => do
    let lctx ← getLCtx
    let args := body.getAppArgs
    logInfo m!"{name}: binders={xs.size}, body head={proofHead body}, args={args.size}"
    let mut appSoFar := body.getAppFn
    for i in [:args.size] do
      let arg := args[i]!
      let startArg ← IO.monoMsNow
      let argResult := Kernel.check env lctx arg
      let stopArg ← IO.monoMsNow
      let startFn ← IO.monoMsNow
      let fnResult := Kernel.check env lctx appSoFar
      let stopFn ← IO.monoMsNow
      match argResult, fnResult with
      | .ok actual, .ok fnType =>
        match Kernel.whnf env lctx fnType with
        | .ok (.forallE _ expected _ _) =>
          let startEq ← IO.monoMsNow
          let result := Kernel.isDefEq env lctx actual expected
          let stopEq ← IO.monoMsNow
          logInfo m!"{name} arg {i}: term={proofHead arg}, actual type={proofHead actual}, expected={proofHead expected}, structural={actual == expected}; own={stopArg - startArg} ms, prefix={stopFn - startFn} ms, domain={stopEq - startEq} ms, result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
        | _ => logInfo m!"{name} arg {i}: function type not Pi"
      | _, _ => logInfo m!"{name} arg {i}: argument or prefix failed"
      appSoFar := mkApp appSoFar arg

run_meta do
  let env ← getEnv
  for n in [1, 2] do
    auditProofPrefix env (Name.str `AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor s!"_proof_{n}")

set_option moe.maxDepth 0
#moe_elab (fun (x : Nat) => x)

open Lean

private def moeOuter : Expr → String
  | .app .. => "app"
  | .const n _ => s!"const:{n}"
  | .proj n i _ => s!"proj:{n}:{i}"
  | .lam .. => "lam"
  | .forallE .. => "forall"
  | .letE .. => "let"
  | .mdata .. => "mdata"
  | .fvar .. => "fvar"
  | .bvar i => s!"bvar:{i}"
  | .sort .. => "sort"
  | .lit .. => "lit"
  | .mvar .. => "mvar"

private def moeHead : Expr → String
  | .const n us => s!"{n}[{String.intercalate "," (us.map toString)}]"
  | .proj n i _ => s!"{n}.{i}"
  | e => moeOuter e

private def moeArgs : Expr → Nat
  | .app f _ => moeArgs f + 1
  | _ => 0

private def moeBinders : Expr → Nat
  | .lam _ _ b _ => moeBinders b + 1
  | .forallE _ _ b _ => moeBinders b + 1
  | _ => 0

private def moeHints : ReducibilityHints → String
  | .abbrev => "abbrev"
  | .opaque => "opaque"
  | .regular h => s!"regular:{h}"

run_meta do
  let env ← getEnv
  let decls := [
    `AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor,
    `AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor._proof_1,
    `AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor._proof_2,
    `AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor._proof_3]
  for name in decls do
    match env.find? name with
    | none => logInfo m!"MOE_META name={name} status=missing"
    | some info =>
      let value? := info.value? true
      let ty := info.type
      let value := value?.getD (.lit (.natVal 0))
      logInfo m!"MOE_META name={name} status=present kind={match info with | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque" | _ => "other"} levels={info.levelParams.length} hints={moeHints info.hints} hasValue={value?.isSome} typeOuter={moeOuter ty} typeHead={moeHead ty.getAppFn} typeArgs={moeArgs ty} typeBinders={moeBinders ty} valueOuter={moeOuter value} valueHead={moeHead value.getAppFn} valueArgs={moeArgs value} valueBinders={moeBinders value}"

private partial def firstExprDiff (a b : Expr) (path : String := "root") :
    Option (String × Expr × Expr) :=
  if a == b then none else
    match a, b with
    | .app f x, .app g y =>
      (firstExprDiff f g (path ++ "/fn")).orElse fun _ =>
        firstExprDiff x y (path ++ "/arg")
    | .lam _ da ba _, .lam _ db bb _ =>
      (firstExprDiff da db (path ++ "/domain")).orElse fun _ =>
        firstExprDiff ba bb (path ++ "/body")
    | .forallE _ da ba _, .forallE _ db bb _ =>
      (firstExprDiff da db (path ++ "/domain")).orElse fun _ =>
        firstExprDiff ba bb (path ++ "/body")
    | .letE _ ta va ba _, .letE _ tb vb bb _ =>
      (firstExprDiff ta tb (path ++ "/type")).orElse fun _ =>
        (firstExprDiff va vb (path ++ "/value")).orElse fun _ =>
          firstExprDiff ba bb (path ++ "/body")
    | .proj na ia ea, .proj nb ib eb =>
      if na == nb && ia == ib then firstExprDiff ea eb (path ++ "/expr")
      else some (path, a, b)
    | .mdata _ ea, .mdata _ eb => firstExprDiff ea eb (path ++ "/data")
    | _, _ => some (path, a, b)

run_meta do
  let env ← getEnv
  let name := `AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor._proof_2
  let info ← getConstInfo name
  let value := info.value! (allowOpaque := true)
  lambdaTelescope value fun _ body => do
    let args := body.getAppArgs
    let mut fn := body.getAppFn
    for i in [:args.size] do
      let arg := args[i]!
      if i == 1 then
        let lctx ← getLCtx
        let actual ← match Kernel.check env lctx arg with
          | .ok t => pure t
          | .error _ => throwError "proof argument check failed"
        let fnType ← match Kernel.check env lctx fn with
          | .ok t => pure t
          | .error _ => throwError "proof prefix check failed"
        let expected ← match Kernel.whnf env lctx fnType with
          | .ok (.forallE _ t _ _) => pure t
          | _ => throwError "proof prefix is not Pi"
        match firstExprDiff actual expected with
        | none => logInfo "MOE_DIFF proof_2 arg=1 none"
        | some (path, left, right) =>
          logInfo m!"MOE_DIFF proof_2 arg=1 path={path} left={left} right={right}"
      fn := mkApp fn arg

run_meta do
  let env ← getEnv
  let name := `AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor._proof_3
  let info ← getConstInfo name
  let value := info.value! (allowOpaque := true)
  lambdaTelescope value fun _ body => do
    let args := body.getAppArgs
    let mut fn := body.getAppFn
    for i in [:args.size] do
      let arg := args[i]!
      if i == 1 then
        let lctx ← getLCtx
        let actual ← match Kernel.check env lctx arg with
          | .ok t => pure t
          | .error _ => throwError "proof argument check failed"
        let fnType ← match Kernel.check env lctx fn with
          | .ok t => pure t
          | .error _ => throwError "proof prefix check failed"
        let expected ← match Kernel.whnf env lctx fnType with
          | .ok (.forallE _ t _ _) => pure t
          | _ => throwError "proof prefix is not Pi"
        match firstExprDiff actual expected with
        | none => logInfo "MOE_DIFF proof_3 arg=1 none"
        | some (path, left, right) =>
          logInfo m!"MOE_DIFF proof_3 arg=1 path={path} left={left} right={right}"
      fn := mkApp fn arg
