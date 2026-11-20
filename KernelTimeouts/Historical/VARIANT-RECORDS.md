# Common experiment records (§9)

All records use Lean `leanprover/lean4:v4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, the historical module imports, and the same
consumer obligation. Times are wall-clock measurements; `>` means the bounded run was
terminated. Proof-free and `sorry` values are diagnostic controls only.

## A0 — original `abbrev`

```text
HISTORICAL KERNEL EXPERIMENT
Case: Slow Derived Tensor; Variant: A0
Original commit: bdab171985a
Exact operation: Kernel.isDefEq(inferred type, declared type), both orientations
Exact pair: @tensorObj (DerivedCategory ...) _ inferInstance K L versus
  @tensorObj (DerivedMonoidal DerivedCategory.Qh ...) _ inferInstance K L
Local context: A, X, K, L and the monoidal/abelian/flat-resolution instances
Time: 49,867 ms forward / 50,279 ms reverse; value check 1 ms
Representation: abbrev hint; same tensorObj head, derived monoidal instance differs
Footprint: additive Hom and Functor/NatTrans unfolds in one parent conversion
Interpretation: H1/P1 strongly supported; exact lazy-delta branch inferred
Confidence: confirmed phase; strongly supported mechanism
```

## A1 — ordinary `def`

```text
HISTORICAL KERNEL EXPERIMENT
Case: Slow Derived Tensor; Variant: A1
Original commit: bdab171985a, declaration-kind scratch control
Exact operation: same final conversion and same instance consumer
Local context: unchanged from A0
Time: source control is fast in the regular-definition family; standalone timing was not
  retained because the detached scratch lacked the root generated module artifact
Representation: def/regular hint; body and consumer unchanged
Footprint: no new mathematical data; expected shared regular head
Interpretation: closest valid control for the hint dimension; no timing extrapolation claimed
Confidence: source-level control confirmed; standalone measurement incomplete
```

## A2 — `@[reducible] def`

```text
HISTORICAL KERNEL EXPERIMENT
Case: Slow Derived Tensor; Variant: A2
Original commit: 428569e1ce1
Exact operation: original isLeftDerivedFunctor₂ consumer
Time: direct module check 2.20 s; minute-scale conversion absent
Representation: reducible regular definition; same body and arguments
Footprint: deep derived/localization descent no longer dominates
Interpretation: causal alignment control for H1
Confidence: confirmed
```

## A3 — exposed body

```text
HISTORICAL KERNEL EXPERIMENT
Case: Slow Derived Tensor; Variant: A3
Original commit: 195ac97d078 diagnostic source
Exact operation: tensorObj final conversion
Time: A0 path returns; diagnostic same-head kernel reduces it to seconds
Representation: consumer sees the expanded body rather than a stable regular head
Footprint: Hom-level additive reductions reappear
Interpretation: exposure is the trigger; internal reduction order inferred
Confidence: strongly supported
```

## B00 — inline diagram, inferred instance

```text
HISTORICAL KERNEL EXPERIMENT
Case: Derived-Completion Cone; Variant: B00
Original commit: 9ba4d01f55c
Exact operation: final inferred/declaration conversion for := sorry
Exact pair: inferred Cone (quotPowFunctor J I ⋙ tensorLeft K) type versus declared type
Local context: J, I, R, K and inferred derived MonoidalCategory
Time: >600 s; type check 3 ms, value check 3 ms
Representation: inline diagram; concrete proof-carrying monoidal instance
Footprint: 36 proof-position proposition comparisons; 337 shared / 6217 unshared nodes
Interpretation: H2 baseline; H3 is fan-out within the parent
Confidence: confirmed phase; strongly supported cause
```

## B10 — named diagram

```text
HISTORICAL KERNEL EXPERIMENT
Case: Derived-Completion Cone; Variant: B10
Original commit: fe5f5d78f1c
Exact operation: same cone declaration conversion
Time: approximately 17 s including elaboration
Representation: named diagram head applied to J, I, K; instance remains inferred in body
Footprint: proof-laden instance is checked in the body and not rebuilt in the declared type
Interpretation: B2 comparison boundary
Confidence: confirmed causal control
```

## B01 — explicit instance

```text
HISTORICAL KERNEL EXPERIMENT
Case: Derived-Completion Cone; Variant: B01
Original source: diagnostic explicit-instance control
Exact operation: inline cone final conversion
Time: 18 s
Representation: one local MonoidalCategory variable used on both sides
Footprint: concrete instance construction is removed from the comparison pair
Interpretation: B1.5 instance-sharing control
Confidence: confirmed
```

## B11 — named diagram plus explicit instance

```text
HISTORICAL KERNEL EXPERIMENT
Case: Derived-Completion Cone; Variant: B11
Original commit: fe5f5d78f1c
Exact operation: real cone term and complete remaining API
Time: 5.3 s for the API with diagnostic values; 9.5 s with the real cone term
Representation: named diagram and shared local derived MonoidalCategory
Footprint: no minute-scale final conversion; body check remains finite
Interpretation: interacting comparison boundaries
Confidence: confirmed
```

## B-D0..B-D4 diagram representation controls

```text
HISTORICAL KERNEL EXPERIMENT
Case: Derived-Completion Cone; Variants: B-D0, B-D1, B-D2, B-D3, B-D4
Exact operation: same Cone declaration and same inferred instance
Pairs: inline expression; named abbrev; named def; named reducible def; expanded body
Times: D0 >600 s; D1 approximately 17 s; D2/D3 fast named-boundary family; D4 timeout path
Representation: only the diagram boundary changes; consumer and proof abstraction fixed
Interpretation: naming/sharing is causal; no cache claim is made
Confidence: D0/D1/D4 confirmed; D2/D3 structurally controlled
```
