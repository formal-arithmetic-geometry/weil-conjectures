/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraLiftOfStr
public import WeilConjectures.WeilSheaf.Category

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

set_option pp.explicit true
set_option pp.universes true
set_option pp.maxSteps 100000

private def auditShape : Expr → String
  | .app .. => "app"
  | .const n _ => s!"const {n}"
  | .proj n i _ => s!"proj {n}.{i}"
  | .lam .. => "lambda"
  | .forallE .. => "forall"
  | .letE .. => "let"
  | .fvar .. => "fvar"
  | .bvar .. => "bvar"
  | .mdata .. => "metadata"
  | .sort .. => "sort"
  | .lit .. => "literal"
  | .mvar .. => "mvar"

private def auditHint : ReducibilityHints → String
  | .abbrev => "abbrev"
  | .opaque => "opaque"
  | .regular h => s!"regular height {h}"

private def auditDescribe (label : String) (e : Expr) : MetaM Unit := do
  let args := e.getAppArgs
  let head := e.getAppFn
  logInfo m!"{label}: outer={auditShape e}; head={auditShape head}; args={args.size}"
  match head with
  | .const n ls =>
    logInfo m!"{label}: universes {ls}"
    match (← getConstInfo n) with
    | .defnInfo d =>
      logInfo m!"{label}: definition, Kernel hint {auditHint d.hints}, body outer={auditShape d.value}, body head={auditShape d.value.getAppFn}"
    | .thmInfo _ => logInfo m!"{label}: theorem"
    | .axiomInfo _ => logInfo m!"{label}: axiom"
    | _ => logInfo m!"{label}: other declaration kind"
  | .proj n i major =>
    logInfo m!"{label}: projection {n}.{i}, major outer={auditShape major}, major head={auditShape major.getAppFn}"
  | _ => pure ()
  for i in [:min args.size 32] do
    let a := args[i]!
    logInfo m!"{label}: arg {i} outer={auditShape a}, head={auditShape a.getAppFn}"

private partial def auditFirstDiff (a b : Expr) (path : String := "root") :
    Option (String × Expr × Expr) :=
  if a == b then none else
    match a, b with
    | .app f x, .app g y =>
      (auditFirstDiff f g (path ++ ".fn")).orElse fun _ =>
        auditFirstDiff x y (path ++ ".arg")
    | .forallE _ da ba _, .forallE _ db bb _ =>
      (auditFirstDiff da db (path ++ ".domain")).orElse fun _ =>
        auditFirstDiff ba bb (path ++ ".body")
    | .lam _ da ba _, .lam _ db bb _ =>
      (auditFirstDiff da db (path ++ ".domain")).orElse fun _ =>
        auditFirstDiff ba bb (path ++ ".body")
    | .letE _ ta va ba _, .letE _ tb vb bb _ =>
      (auditFirstDiff ta tb (path ++ ".type")).orElse fun _ =>
        (auditFirstDiff va vb (path ++ ".value")).orElse fun _ =>
          auditFirstDiff ba bb (path ++ ".body")
    | .proj na ia ea, .proj nb ib eb =>
      if na == nb && ia == ib then auditFirstDiff ea eb (path ++ ".proj")
      else some (path, a, b)
    | .mdata _ ea, .mdata _ eb => auditFirstDiff ea eb (path ++ ".mdata")
    | _, _ => some (path, a, b)

private partial def auditStripLambdas (e : Expr) (n : Nat := 0) : Nat × Expr :=
  match e with
  | .lam _ _ body _ => auditStripLambdas body (n + 1)
  | _ => (n, e)

private partial def auditStripForalls (e : Expr) (n : Nat := 0) : Nat × Expr :=
  match e with
  | .forallE _ _ body _ => auditStripForalls body (n + 1)
  | _ => (n, e)

run_meta do
  let env ← getEnv
  let name := `AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor
  let info ← getConstInfo name
  let value := info.value! (allowOpaque := true)
  logInfo m!"AUDIT declaration {name}; original value and declared type read from the current environment"
  let start ← IO.monoMsNow
  let result := Kernel.check env {} value
  let stop ← IO.monoMsNow
  logInfo m!"Kernel.check(value) {stop - start} ms"
  match result with
  | .error _ => logInfo m!"value replay failed"
  | .ok inferred =>
    auditDescribe "actual inferred type" inferred
    auditDescribe "expected declared type" info.type
    let (actualBinders, actualResult) := auditStripForalls inferred
    let (expectedBinders, expectedResult) := auditStripForalls info.type
    logInfo m!"result binders actual={actualBinders}, expected={expectedBinders}"
    auditDescribe "actual result" actualResult
    auditDescribe "expected result" expectedResult
    let startEq ← IO.monoMsNow
    let equal := Kernel.isDefEq env {} inferred info.type
    let stopEq ← IO.monoMsNow
    logInfo m!"final conversion={stopEq - startEq} ms, result={match equal with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
    match auditFirstDiff inferred info.type with
    | none => logInfo m!"final type pair structurally identical"
    | some (path, a, b) =>
      logInfo m!"first structural divergence {path}"
      auditDescribe "divergence actual" a
      auditDescribe "divergence expected" b
  let (binders, body) := auditStripLambdas value
  logInfo m!"value binders {binders}"
  auditDescribe "value body" body
