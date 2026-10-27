# moduleObjectDerivedExchange_exact_normalization

## Reason

The proof uses the actual canonical K-flat comparison, compositor and adjunction.
Their signatures expose `(upperStar Λ f).leftDerivedFunctor`; the published shift
instance is indexed by the definitionally equal `moduleObjectDerivedPullback Λ f`.
A private local bridge supplies exactly that existing instance. A proved private
exchange/mate equation permits equality transport before evaluating components and
avoids expanding concrete derived constructions inside `NatTrans.app`.

## Old

The canonical public pullback shift instance was already

```lean
instance moduleObjectDerivedPullbackCommShift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (moduleObjectDerivedPullback Λ f).CommShift ℤ :=
  Functor.CommShift.ofIso (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ
```

The three public theorem proofs were `sorry`. There was no private local bridge or
component equation API.

## New

Every public definition body, including the displayed instance, is verbatim unchanged.
The bridge is private and scoped to the shift-proof section, which ends before public
theorem statements:

```lean
@[instance_reducible]
private noncomputable def pullback_commShift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar Λ f).leftDerivedFunctor.CommShift ℤ :=
  moduleObjectDerivedPullbackCommShift Λ f

attribute [local instance] pullback_commShift
```

The private `exchange_eq_mate` equation is proved by `rfl` at the natural-transformation
level. The ambient assertion is transported along it as a whole; the general restriction
proof uses `congrArg` on component evaluation and composes equalities. For the bounded
proof, the three named base-change steps are identified with the existing
`Adjunction.squareExchange` presentation, giving its counit equation. The underlying
restricted counit is identified by `Adjunction.map_restrictFullyFaithful_counit_app`.
Private object and map equations, together with the square-component hypothesis,
identify this with the ambient counit equation. Injectivity of the inverse ambient
adjunction hom equivalence gives component equality. A proved private helper treats
both transformations and square comparisons as parameters; the small full-subcategory
lift and inclusion definitions are explicitly reduced before the final comparison.
The actual restricted constructions remain unchanged.
Proof-local attributes expose `Over.forget`, `Comma.fst`, and the named functor wrappers,
while keeping `mateEquiv`, lifted adjunctions, the derived-functor constructors,
`upperStar`, `lowerStar`, the published adjunction, and the square comparison folded.
The preservation predicate is also locally reducible, so rewriting can see its
function type. Explicit `@H` arguments suppress automatic implicit lambdas at the
final helper boundary, keeping the preservation proof identical in the constructions. `Adjunction.homEquiv` is locally kept folded outside the final explicit counit rewrite.
These attributes affect no importer. No public instance is added or
reprioritized. Explicit object
and square annotations restate the existing inferred types. The public import list is
unchanged; six unused private imports are removed as listed in the report.

## Users

Only the assigned module changes. Its public data and statement meanings are preserved,
so no forced consumer adaptation is required. Unfinished DAG parents retain the same
interface. No adopted source-library file changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DerivedExchangeExactNormalization | R3 | Three proofs and private helpers. |

## Status

landed 20261022T144114-L-1500271 2026-10-22 (merge of deliver/R3/Sheaf.Paper.DerivedExchangeExactNormalization)
