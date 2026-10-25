/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ContractingGraph
public import WeilConjectures.TraceFormula.GraphPieces

/-!

# The Frobenius local term on a smooth curve

Let `X` be smooth of relative dimension one over `s = Spec k`, with the model Frobenius `Φ` of a
model `X₀` over a finite field, let `m ≥ 1`, `v : LΦ_m^* K ⟶ K` an arbitrary (not necessarily
invertible) map and `x` a rational point fixed by `Φ_m`. For an open and closed subscheme `B` of
the fixed locus of the graph correspondence `(𝟙, Φ_m)` with underlying set `{x}`, the local term
of `v` along `B` is the trace of the stalk map `v_x` (blueprint `sk-p-frob`,
`thm-trf-frobenius-local-term`):
```
LT_B(v) = tr(v_x | K_x).
```
This file follows the route of blueprint `sk-rem-tf-curve-local-proof` (SGA 5, III B, §§2–4),
without nearby cycles and without Varshavsky's contracting theorem.

* The open–closed filtration `K^U = j_! Lj^* K ⟶ K ⟶ K^Z = Rx_* Lx^* K` at `x` and filtered
  trace-class additivity (`Correspondence.traceClass_ofGraph_eq_add`, blueprint
  `sk-i-additivity`) split the local term into the local terms of the closed piece and of the open
  piece. The closed piece is the proper pushforward of the point correspondence `v_x`, whose local
  term is `tr(v_x)` by proper pushforward compatibility (blueprint `sk-p-proper`) and the point
  case (blueprint `sk-p-pairing`). Hence the local term is `tr(v_x)` as soon as the open piece
  contributes zero
  (`Correspondence.localTerm_traceClass_ofGraph_eq_trace_of_restrict_eq_zero`).
* The open piece has zero stalk at `x`, and on a smooth curve the local term of a coefficient
  with zero stalk at `x` vanishes (blueprint `sk-i-curve-zero`,
  `Correspondence.restrict_traceClass_frobeniusGraph_eq_zero_of_smooth`): the local term is
  computed from the stalk at `x` of the trace morphism `𝔱 : 𝓗_c(K) ⟶ Rι_* ω_Fix`, the composite
  of evaluation and the supported restriction from the Frobenius graph to the diagonal (blueprint
  `sk-lem-tf-curve-supported-pairing`,
  `Correspondence.restrict_traceClass_eq_zero_of_upperStar_map_traceMap_eq_zero`), and this stalk
  vanishes when `K_x = 0` (blueprint `sk-lem-tf-curve-restriction-zero`,
  `Correspondence.upperStar_map_traceMap_ofGraph_eq_zero`).
* If `X` has a single point, the open piece is zero and the local term is `tr(v_x)` for every
  endomorphism (`Correspondence.localTerm_traceClass_ofGraph_eq_trace_of_subsingleton`).

## Coefficients

The blueprint carries out the local calculation with a finite `ℓ`-primary coefficient ring `A`,
on the classical étale models. The trace classes of this chapter are only defined with
coefficients `ℚ̄_ℓ`; the statements here are the `ℚ̄_ℓ`-forms. The vanishing of the supported
restriction is a vanishing of a morphism before any trace is taken, and the `ℚ̄_ℓ`-form follows
from the finite forms by the integral models of blueprint `sk-lem-tf-rational-model`: a morphism
of perfect `𝒪_E`-complexes whose reductions modulo every `π_E^n` vanish is zero, since
`Hom(P, Q) ⊗ 𝒪_E/π_E^n ↪ Hom(P, Q ⊗ 𝒪_E/π_E^n)`.

## Main statements

- `ProEtale.CondensedRing.Correspondence.localTerm_traceClass_frobeniusGraph_eq_trace_of_smooth`:
  the Frobenius local term on a smooth curve (blueprint `sk-p-frob`).
- `ProEtale.CondensedRing.Correspondence.localTerm_traceClass_frobeniusGraph_eq_zero_of_smooth`:
  the Frobenius local vanishing on a smooth curve (blueprint `sk-i-curve-zero`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

/-! ### The local term through the stalk of the trace morphism -/

/-- **The local term through the supported restriction** (blueprint
`sk-lem-tf-curve-supported-pairing`, `det-tf-supported-restriction-local-term`): the restriction
of the trace class `Tr_c(u)` to an open subscheme `j : B ⟶ Fix(c)` only depends on the pullback
along `B ⟶ C` of the composite `ũ ≫ 𝔱` of the mate of `u` and the trace morphism
`𝔱 : 𝓗_c(K) ⟶ Rι_* ω_Fix(c)`. In particular it vanishes if the pullback of `𝔱` along `B ⟶ C`
does, whatever the coefficient map `u`: in the blueprint, the pullback of `𝔱` to the strict
localization at a fixed point is evaluation composed with the supported restriction `ρ_{a,b}`
from the graph to the diagonal. -/
theorem restrict_traceClass_eq_zero_of_upperStar_map_traceMap_eq_zero (c : Correspondence ℓ K)
    (F : c.FixedLocus) {B : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
    [IsSeparated B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left]
    (h : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (j ≫ F.ι)).map
      (c.traceMap F) = 0) :
    (c.traceClass F).restrict j = 0 :=
  sorry

/-! ### Reduction to the open piece -/

/-- **The local term at a fixed point modulo the open piece** (blueprint `sk-p-frob`, proof:
the open–closed filtration at `x`, filtered trace-class additivity `sk-i-additivity`, proper
pushforward `sk-p-proper` and the point case `sk-p-pairing`): let `x` be a rational point fixed by
`h` and `B` an open and closed subscheme of the fixed locus of the graph correspondence `(𝟙, h)`,
proper over `s`, with underlying set `{x}`. If the trace class of the open piece
`u^U = [j]_! (v|_U)` on `K^U = j_! Lj^* K` restricts to zero on `B`, the local term of `v` along
`B` is the trace of the stalk map `v_x`. -/
theorem localTerm_traceClass_ofGraph_eq_trace_of_restrict_eq_zero (h : X ⟶ X)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
    (F : (ofGraph K h v).FixedLocus) (x : RationalPoint X) (hx : x ≫ h = x)
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint x ((Category.comp_id x).trans hx.symm)).left.base (default : Spec (.of k))})
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)]
    (hU : (F.traceClassWithCoeff _ (graphOpenPieceCoeff K v hx ≫
      (boundedConstructibleUpperShriekId ℓ X).inv.app _)).restrict j = 0) :
    ((ofGraph K h v).traceClass F).localTerm j = trace (graphStalkMap K h v x hx) :=
  sorry

/-- **The local term on a one-point scheme**: if `X` has a single point, the open piece at a
fixed rational point `x` is zero, and the local term of the graph correspondence `(𝟙, h)` along
an open and closed subscheme `B` of the fixed locus with underlying set `{x}` is the trace of the
stalk map `v_x`. -/
theorem localTerm_traceClass_ofGraph_eq_trace_of_subsingleton [Subsingleton X.left] (h : X ⟶ X)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
    (F : (ofGraph K h v).FixedLocus) (x : RationalPoint X) (hx : x ≫ h = x)
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint x ((Category.comp_id x).trans hx.symm)).left.base (default : Spec (.of k))})
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)] :
    ((ofGraph K h v).traceClass F).localTerm j = trace (graphStalkMap K h v x hx) :=
  sorry

/-! ### The curve case -/

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} {Φ : X ⟶ X}

/-- **The supported restriction is zero for Frobenius** (blueprint
`sk-lem-tf-curve-restriction-zero`; SGA 5, III B, §§2–4): let `X` be smooth of relative dimension
one over the algebraically closed field `k`, with the model Frobenius `Φ` of a model over a finite
field, `m ≥ 1`, and let `x` be a rational point fixed by `Φ_m` with `K_x = 0`. For an open and
closed subscheme `B` of the fixed locus of the graph correspondence `(𝟙, Φ_m)` with underlying set
`{x}`, the pullback along `B ⟶ X` of the trace morphism `𝔱 : 𝓗_c(K) ⟶ Rι_* ω_Fix` vanishes.

This is the `ℚ̄_ℓ`-form of the blueprint statement: the pullback of `𝔱` to `B ≅ {x}` is the
stalk at `x`, that is the value on the strict localization `T` of `X ⨯ X` at `(x, x)`, of the
composite of the supported restriction `ρ_{a,b} : RΓ_a(T, P) ⟶ RΓ_x(b, b^* P)` from the
transposed Frobenius graph `a` to the diagonal `b`, `P = (D_X K ⊠ K)|_T`, with evaluation
`b^* P ⟶ ω_X`; the blueprint shows `ρ_{a,b} = 0` in `D(A)` for every finite `ℓ`-primary ring
`A` (localization to the punctured diagonal, covers of degree prime to `ℓ`, and the blowup
argument of `sk-lem-tf-blowup-restriction`), and the `ℚ̄_ℓ`-form follows by the integral models
of `sk-lem-tf-rational-model`. The coefficient map `v` plays no role: `𝔱` only depends on the
correspondence and on `K`. -/
theorem upperStar_map_traceMap_ofGraph_eq_zero [IsAlgClosed k]
    [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint x ((Category.comp_id x).trans hx.symm)).left.base (default : Spec (.of k))})
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (j ≫ F.ι)).map
      ((ofGraph K (frobeniusIterate Φ m) v).traceMap F) = 0 :=
  sorry

/-- **Frobenius local vanishing on a smooth curve**, trace classes (blueprint `sk-i-curve-zero`):
let `X` be smooth of relative dimension one over the algebraically closed field `k`, with the
model Frobenius `Φ` of a model over a finite field, `m ≥ 1`, `v : LΦ_m^* K ⟶ K` arbitrary and `x`
a rational point fixed by `Φ_m` with `K_x = 0`. Then the trace class of the graph correspondence
`(𝟙, Φ_m)` with coefficient `v` restricts to zero on every open and closed subscheme `B` of the
fixed locus with underlying set `{x}`: the supported restriction vanishes
(`upperStar_map_traceMap_ofGraph_eq_zero`, blueprint `sk-lem-tf-curve-restriction-zero`), so
its composite with the mate of `v` does
(`restrict_traceClass_eq_zero_of_upperStar_map_traceMap_eq_zero`, blueprint
`sk-lem-tf-curve-supported-pairing`). -/
theorem restrict_traceClass_frobeniusGraph_eq_zero_of_smooth [IsAlgClosed k]
    [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint x ((Category.comp_id x).trans hx.symm)).left.base (default : Spec (.of k))})
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)) :
    ((ofGraph K (frobeniusIterate Φ m) v).traceClass F).restrict j = 0 :=
  restrict_traceClass_eq_zero_of_upperStar_map_traceMap_eq_zero _ F j
    (upperStar_map_traceMap_ofGraph_eq_zero hΦ hm v F x hx j hB hK)

/-- **Frobenius local vanishing on a smooth curve** (blueprint `sk-i-curve-zero`): in the
situation of `restrict_traceClass_frobeniusGraph_eq_zero_of_smooth`, if `K_x = 0` the local term
`LT_B(v)` is zero. No invertibility of `v` is assumed. -/
theorem localTerm_traceClass_frobeniusGraph_eq_zero_of_smooth [IsAlgClosed k]
    [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint x ((Category.comp_id x).trans hx.symm)).left.base (default : Spec (.of k))})
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)) :
    ((ofGraph K (frobeniusIterate Φ m) v).traceClass F).localTerm j = 0 := by
  rw [BorelMooreSection.localTerm,
    restrict_traceClass_frobeniusGraph_eq_zero_of_smooth hΦ hm v F x hx j hB hK]
  exact BorelMooreSection.integral_zero

/-- **The Frobenius local term on a smooth curve** (blueprint `sk-p-frob`,
`thm-trf-frobenius-local-term`): let `X` be smooth of relative dimension one over the
algebraically closed field `k`, with the model Frobenius `Φ` of a model over a finite field,
`m ≥ 1`, `v : LΦ_m^* K ⟶ K` an arbitrary (not necessarily invertible) map and `x` a rational point
fixed by `Φ_m`. For an open and closed subscheme `B` of the fixed locus of the graph
correspondence `(𝟙, Φ_m)`, proper over `s`, with underlying set `{x}`, the local term of `v`
along `B` is the trace of the stalk map `v_x` on `K_x`. No local constancy of `K` at `x` is
assumed.

The open–closed filtration at `x` and filtered trace-class additivity reduce this to the point
and to the open piece (`localTerm_traceClass_ofGraph_eq_trace_of_restrict_eq_zero`), whose stalk
at `x` vanishes, so that it contributes zero by the Frobenius local vanishing
(`restrict_traceClass_frobeniusGraph_eq_zero_of_smooth`, blueprint `sk-i-curve-zero`). -/
theorem localTerm_traceClass_frobeniusGraph_eq_trace_of_smooth [IsAlgClosed k]
    [SmoothOfRelativeDimension 1 X.hom] [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    {m : ℕ} (hm : 1 ≤ m)
    (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (frobeniusIterate Φ m)).obj K ⟶ K)
    (F : (ofGraph K (frobeniusIterate Φ m) v).FixedLocus) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint x ((Category.comp_id x).trans hx.symm)).left.base (default : Spec (.of k))})
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)] :
    ((ofGraph K (frobeniusIterate Φ m) v).traceClass F).localTerm j =
      trace (graphStalkMap K (frobeniusIterate Φ m) v x hx) :=
  sorry

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
