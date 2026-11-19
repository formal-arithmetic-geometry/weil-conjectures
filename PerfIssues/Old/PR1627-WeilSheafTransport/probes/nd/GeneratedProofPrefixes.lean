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
