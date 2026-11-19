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

private def proofShape : Expr → String
  | .app .. => "app"
  | .const n _ => s!"const {n}"
  | .proj n i _ => s!"proj {n}.{i}"
  | .lam .. => "lambda"
  | .forallE .. => "forall"
  | .letE .. => "let"
  | .mdata .. => "metadata"
  | .fvar .. => "fvar"
  | .bvar .. => "bvar"
  | .sort .. => "sort"
  | .lit .. => "literal"
  | .mvar .. => "mvar"

private partial def stripProofBinders (e : Expr) (n : Nat := 0) : Nat × Expr :=
  match e with
  | .lam _ _ b _ => stripProofBinders b (n + 1)
  | .forallE _ _ b _ => stripProofBinders b (n + 1)
  | _ => (n, e)

run_meta do
  let env ← getEnv
  for n in [1, 2, 3] do
    let name := Name.str `AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor s!"_proof_{n}"
    if let some info := env.find? name then
      let value := info.value! (allowOpaque := true)
      let (typeBinders, resultType) := stripProofBinders info.type
      let (valueBinders, body) := stripProofBinders value
      logInfo m!"{name}: type binders={typeBinders}, result outer={proofShape resultType}, head={proofShape resultType.getAppFn}"
      logInfo m!"{name}: value binders={valueBinders}, body outer={proofShape body}, head={proofShape body.getAppFn}, args={body.getAppArgs.size}"
      let startValue ← IO.monoMsNow
      let checked := Kernel.check env {} value
      let stopValue ← IO.monoMsNow
      logInfo m!"{name}: Kernel.check value={stopValue - startValue} ms"
      match checked with
      | .error _ => logInfo m!"{name}: value check failed"
      | .ok inferred =>
        logInfo m!"{name}: inferred structurally equal to declared={inferred == info.type}"
        let startEq ← IO.monoMsNow
        let equal := Kernel.isDefEq env {} inferred info.type
        let stopEq ← IO.monoMsNow
        logInfo m!"{name}: final defeq={stopEq - startEq} ms, result={match equal with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"}"
