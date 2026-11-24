# Slow Derived Tensor: round-two direct measurements

## 8.1 Exact roots and environment

Lean is 4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), Mathlib is
`0df444a360eaa60ab8c11dca51a86af692955474`, the original consumer is
`bdab171985a`, and the regular-alias control is `428569e1ce1`. The new
traces use the READY4.2 observational kernel instrumentation, with a
3600-second limit and at most one Lean process at a time. No kernel
decision logic was changed.

| Root | Comparison | Result | Recursive calls | Instrumented kernel time |
| --- | --- | --- | ---: | ---: |
| R0 | standalone `tensorObj`, forward | true | 6,239,533 | 63,400.227 ms |
| R1 | same standalone pair, reverse | true | 6,239,533 | 69,134.061 ms |
| R2 | full original consumer, forward | true | 14,378,617 | 154,390.907 ms |
| R3 | full regular-alias consumer, forward | true | 428 | 5.322 ms |

R0/R1 and R2 are roots 2912/2913 and 3234 in the retained original
trace. R3 is root 496 in the control trace. An independently timed R0
provider argument has 6,269,622 calls and 69,814.952 ms. Its tensor
application arguments 0/1/2 took 2,947/1/74,925 ms in that process;
argument 2 is the `MonoidalCategory` provider. The root applications
share `MonoidalCategoryStruct.tensorObj`; provider sizes are 1,785/11,973.

The earlier uninstrumented baseline remains 46--52 s for the standalone
comparison, 119,953/127,832 ms for original full-consumer directions,
and 2/2 ms for the regular control. Instrumented times have overhead and
are not pooled with baseline times. All new Kernel results are `true`.

## 8.2 First expensive `MonoidalCategory` field (H1)

The historical Environment lists `MonoidalCategory` as the parent
projection `toMonoidalCategoryStruct` followed by ten coherence fields.
`MonoidalCategoryStruct` fields, in order, are `tensorObj`, `whiskerLeft`,
`whiskerRight`, `tensorHom`, `tensorUnit`, `associator`, `leftUnitor`,
and `rightUnitor`. The constructor has two parameters before those
fields, so constructor argument 2 is **field index 0, `tensorObj`**.

The exact two field expressions have hashes `3864345625/2761921257`,
sizes `60,951/38,555`, and are not pointer equal. Both render as:

```lean
fun X₁ X₂ =>
  ((DerivedMonoidal.bifunctor DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A)
      (ComplexShape.up ℤ))).obj X₁).obj X₂
```

The rendered form hides distinct instance terms; hashes and sizes refer
to the actual expressions. Fresh standalone replay of that exact pair
returned `true` in 6,239,530 calls and 62,825.143 ms instrumented kernel
time (67,036 ms probe wall time). The constructor pair costs 6,269,620
calls and 77,998.114 ms in a separate instrumented run. Direct children
are `DerivedMonoidal` binder domains 0 and 1, followed by dependent-body
`Functor.obj`; that body subtree accounts for essentially all 62.825 s.
`DerivedMonoidal.bifunctor` is an intermediate definition in the field
value, not itself a direct structure field.

## 8.3 `Functor.leftDerived₂` components (H2)

The source defines `DerivedMonoidal.bifunctor` through
`Functor.leftDerived₂`, whose body is
`curry.obj ((uncurry.obj F).totalLeftDerived (L₁.prod L₂) (W₁.prod W₂))`.
The new field replay follows `Functor.obj` through
`curriedTensor_hasLeftDerivedFunctor₂`, its proposition type, and an
exposed `Functor.mk`. The direct trace does not emit a distinct
`Functor.leftDerived₂` head because it has already reduced before this
comparison.

| Path below exposed `Functor.mk` | Direct calls | Inclusive subtree time in same field run |
| --- | ---: | ---: |
| constructor argument 7 | 1 | 42,620.446 ms |
| constructor argument 5 | 1 | 18,734.497 ms |
| constructor argument 6 | 1 | 842.450 ms |

The three times are sibling inclusive subtrees and are not summed with
their parents. They expose `Functor.uncurry._proof_3`, composition and
localization descendants, and `Functor.uncurry._proof_2`, respectively.
The retained trace does not provide complete component field metadata,
so a full outer/inner `obj`/`map`/law, `NatTrans.app`, naturality,
localization, and Hom-additive exclusive table is **Unknown**.

The same field run's aggregate labels were:

| Label | Calls | Comparison-exclusive | Reduction-exclusive |
| --- | ---: | ---: | ---: |
| M0 | 1 | 0.037 ms | 0 |
| M1 | 4,436,634 | 40,991.932 ms | 21,671.143 ms |
| M2 | 815 | 13.131 ms | 6.895 ms |
| Matched | 1,802,080 | 142.004 ms | 0 |

These are measured implementation labels from the same run. READY4.2
labels M1 by matching first-divergence hashes or path prefixes; it does
not verify that a child pair is the reduction image of the original
mismatch. Thus these are provisional lineage shares, not a validated
§3.5 M1/M2/Matched proof. Global reduction counters cannot be assigned
to semantic components from this trace.

## 8.4 Original mismatch propagation

The original application mismatch is its `MonoidalCategory` argument.
The trace enters `MonoidalCategoryStruct.mk`, then `tensorObj`, the
lambda-body `Functor.obj`, `curriedTensor_hasLeftDerivedFunctor₂`, its
proposition type, and the exposed functor constructor. Measured branches
include dependent-body, `second_whnf`, projection, application argument,
and proposition-type comparison.

In the field replay, provisional M1-to-M1 edges include 996,371
projection children (16,473.387 ms), 1,867,041 application-argument
children (12,823.821 ms), 729,927 application-function children
(3,731.174 ms), and 308,968 `second_whnf` children (3,564.292 ms).
These are disjoint branch buckets from the same run. The raw per-call
trace captures the first 36,623 of 6,239,530 calls; later work is
aggregate only. Exact reduction-image lineage through all descendants is
not demonstrable from these records.

## 8.5 `abbrev` / regular decision trace (H3)

Both full-consumer roots first compare `Functor.IsLeftDerivedFunctor₂`.
In R2, with the `.abbrev` alias, its next child is an
`application/function-head` comparison of `Functor.IsLeftDerivedFunctor`.
In R3, with the `@[reducible] def` control, its next child is a
`lazy_delta/argument[20]` comparison of
`MorphismProperty.IsMultiplicative.toContainsIdentities`. This is the
first recorded branch divergence. R2 continues to 14,378,617 calls and
154,390.907 ms; R3 stops at 428 calls and 5.322 ms, with no provider
subtree. `DerivedMonoidal` itself remains a regular definition.

The standalone tensor comparison remains expensive under the regular
control (6,267,703 calls in its forward trace). The full consumer avoids
the deep obligation, while the isolated tensor root still demands it.
The raw reduction records do not retain the unfolded constant and hint
for the particular branch, so that detail is **Unknown**.

## 8.6 Evidence grading and remaining instrumentation

**Demonstrated:** exact historical roots and results; field index/name
`MonoidalCategoryStruct.tensorObj`; actual field hashes/sizes and replay
cost; per-call IDs, parents, depths and branches for captured calls;
same-run aggregate lineage labels; and R2/R3's first different child
branch.

**Strongly supported:** the expensive tensor field descends through
dependent functor/proposition comparisons; the regular proposition
boundary prevents the full consumer from reaching it.

**Unknown:** complete exclusive calls/time per semantic `leftDerived₂`
component, verified reduction-image M1 lineage, projection names,
unfolded constants/hints, and component-owned reductions. The available
READY4.2 schema caps raw events in serial order and emits path-prefix
aggregates, but does not retain expensive-subtree-selected dumps or
semantic-component counters. Closing these requires a scratch rebuild
that records constructor/projection metadata, expression size/pointer
equality, reduction constant/hint/kind, and per-component counters.

### Round 1 → Round 2

H1 moved from Unknown to measured field 0 and exact standalone replay.
H3 moved from timing inference to an observed first branch divergence.
H2 moved from saved path guesses to new same-run subtree and provisional
lineage measurements; its full semantic partition and verified M1
lineage remain Unknown.

### Answers to §9

1. First expensive field: inherited `MonoidalCategoryStruct.tensorObj`,
   field 0, constructor argument 2; replay 6,239,530 calls / 62.825 s.
2. `DerivedMonoidal.bifunctor` is an intermediate definition in that
   field value, not a direct field.
3. The field enters binder domains, then dependent-body `Functor.obj`,
   followed by `second_whnf`, projection, and proposition branches.
4. Actual paths include exposed functor arguments 7, 5, and 6, with
   uncurry-law and localization/composition descendants.
5. Their same-run sibling subtree times are 42.620 s, 18.734 s, and
   0.842 s; complete semantic call partitions remain Unknown.
6. Frequent reductions occur inside the field root, but ownership and
   validated M1 lineage are not recorded.
7. Provisional whole-field labels are 4,436,634 M1, 815 M2, and
   1,802,080 Matched calls; strict §3.5 verification remains Unknown.
8. R2 first descends via `application/function-head` to
   `IsLeftDerivedFunctor`; R3 first takes `lazy_delta/argument[20]`.
9. R3 has 428 calls and avoids the provider; standalone tensor remains
   expensive.
10. Remaining exact measurements require the additional instrumentation
    described in §8.6.

## Audit note

The exact `tensorObj` field replay and the R2/R3 first-branch observation
support the demonstrated field and branch facts. The regular-alias result is
an API-level counterfactual, not an M0-preserving cut; the standalone field
remains expensive. The `leftDerived₂` component shares and strict M1 lineage
remain **U**, so no component-level claim is promoted to D or S.
