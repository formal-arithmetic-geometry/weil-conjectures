# Slow Derived Tensor

## Scope and environment

The exact historical consumer is `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor`
in `bdab171985a` (18 September 2026). The kernel probes were added in `195ac97d078`; the
workaround landed in `428569e1ce1`. Both use Lean `leanprover/lean4:v4.33.1` and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. The target module imports the derived-category
monoidal and étale-sheaf modules shown in the historical `Tensor.lean` source.

The timings below are direct measurements unless labelled `inferred` or `control`. They are
wall-clock kernel probe times; the process also pays the fixed import/elaboration cost.

## A1.1 Declaration-kind matrix

The body, parameters, instance consumer, and proof are unchanged. The historical patch
changes exactly these declarations in `LeftDerivedTwo`, `LeftDerivedThree`, and
`LeftDerivedFour`:

```lean
-- A0
abbrev IsLeftDerivedFunctor₂ : Prop := body

-- A2
@[reducible] def IsLeftDerivedFunctor₂ : Prop := body
```

The corresponding `HasLeftDerivedFunctor₂/₃/₄` declarations receive the same change.

| Variant | Declaration hint | `Kernel.check(value)` | final `isDefEq` | Evidence |
| --- | --- | ---: | ---: | --- |
| A0, original `abbrev` | `def/abbrev` | 1 ms | 131,963 ms forward; 121,742 ms reverse | direct probe |
| A1, ordinary `def` | `def/regular` | fast value check | fast module control | historical control shape; exact standalone timing not retained |
| A2, `@[reducible] def` | regular definition with reducible transparency | fast | seconds including imports | direct successful control build |
| A3, explicitly exposed body | no useful named boundary | fast locally | returns to the A0 expensive path | direct probe behavior; same-head diagnostic |

The ordinary-`def` row is a declaration-kind control: it verifies the body and consumer are
unchanged and exposes the regular hint. The historical fix used the annotated form because
it preserves the intended elaboration behavior for downstream users. A3 is the explicit-body
probe used by the debug harness; it is not a library replacement.

The performance change therefore correlates with the declaration hint, not with a different
mathematical proposition. It is not valid to identify `abbrev`, ordinary `def`, and
`@[reducible] def` without checking the hint in the target Lean version.

## A1.2 Exact comparison boundary

The smallest reproducer is the historical `test_tensorObj_kernelProbe`:

```lean
@tensorObj (DerivedCategory (Sheaf X.smallEtaleTopology A)) _ inferInstance K L
=
@tensorObj (DerivedMonoidal DerivedCategory.Qh
  (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)))
  _ inferInstance K L
```

Direct expression inspection shows the same outer application head,
`CategoryTheory.MonoidalCategoryStruct.tensorObj`, with the category, structure, and
instance arguments carrying the representation difference. `Kernel.check(value)` is 1 ms;
the final equality conversion is about 50 s in both directions. The full consumer has outer
head `Functor.IsLeftDerivedFunctor` after unfolding the proposition alias; its nested
derived-functor arguments contain the same tensor/monoidal comparison and additional
localization fields.

The probe's high-level head list is:

```text
MonoidalCategoryStruct.tensorObj
DerivedMonoidal
MonoidalCategory.ofBifunctor
DerivedMonoidal.bifunctor
Functor.leftDerived₂
DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
DerivedCategory.Qh / DerivedCategory.Q
```

The corresponding argument comparisons are cheap when performed independently. The
expensive path begins when an `abbrev` boundary is unfolded and the kernel descends through
the derived/localization implementation. This supports the shared-head explanation, while
the exact internal lazy-delta branch is an inference from the controlled declaration-kind
change, not a kernel trace.

## A1.3 Exposure controls

| Exposure | Result | Interpretation |
| --- | --- | --- |
| original A0 pair | 49.9 s on the tensor probe | baseline |
| left-only one-step exposure | no independent type-correct parent probe; exposing only one dependent side changes the obligation | not a valid one-factor measurement |
| right-only one-step exposure | same limitation | not a valid one-factor measurement |
| both sides at first common `tensorObj` representation | the direct tensor probe remains expensive until the derived monoidal instance path is aligned | the body is not the only issue |
| shared regular definition head | fast control | high-level head prevents the pathological descent |
| explicit body / diagnostic same-head relaxation | expensive path returns; a diagnostic kernel accepting the same-head shortcut reduces it to seconds | supports H1 |

The invalid one-sided controls are recorded explicitly because the tensor equality is
dependent: changing only one category/instance argument no longer measures the original
consumer. `@[no_expose]` controls on `DerivedMonoidal.bifunctor` and `.counit` did not help,
which rules out a simple lower-level opacity boundary.

## A1.4 Directionality and consumer controls

The tensor probe is almost symmetric: 49,867 ms forward versus 50,279 ms reverse. The full
consumer is also similar in both directions: 131,963 ms versus 121,742 ms. This rules out a
simple left-only reduction-order accident. Replacing the consumer by the narrowly
parameterized tensor helper preserves the same concrete derived-category arguments and
retains the 50 s conversion, so the cost is tied to the representation boundary rather than
the instance registration wrapper.

## Reduction footprint and classification

The diagnostic counters are downstream symptoms, not a trace of decision order. The tensor
probe reports approximately 743k `AddGroup.toSubNegMonoid`, 711k `Preadditive.homGroup`,
674k `AddCommGroup.toAddGroup`, 658k `Functor.obj`, and 542k `NatTrans.app` unfolds. The
regular-definition control removes the minute-scale conversion and the corresponding deep
derived/localization descent. A custom diagnostic kernel that permits the same-head shortcut
reduces the probe to a few seconds, which is the strongest reduction-footprint control.

**R1/R2:** The exact cost site is the final inferred-type/declaration conversion; the first
useful boundary is the same `tensorObj`/derived-functor head. The initial mismatch is a
representation bundle (derived monoidal category and dependent functor fields), not one
mathematical data argument.

**R3/R4:** The exposed tree is `tensorObj → DerivedMonoidal.bifunctor → leftDerived₂ →
localization/quotient functors → NatTrans/Functor fields → Hom additive structures`. One
parent conversion dominates; counters show many reductions inside it rather than many
independent declaration checks.

**R5/R6:** Aligning the declaration kind removes the expensive path while preserving the
consumer. The counters and custom-kernel control shrink with it. Explicitly exposing the
body restores the path. This is a causal control for the high-level boundary, although the
kernel's exact lazy-delta action remains inferred.

**R7:** Classification **P1/H1**, confidence **strongly supported** (the exact shared-head
decision is not directly traced); repeated comparison is not the primary explanation.
Remaining unexplained cost: the precise recursive pair and lazy-delta choice inside the
derived localization machinery.

## §6/§7 controls

| Control | Result |
| --- | --- |
| `debug.skipKernelTC` | removes the delay: kernel phase confirmed |
| RHS theorem alone | under 0.1 s: proof construction is not the cause |
| explicit target with `sorry` | under 0.1 s: written type alone is not the cause |
| explicit `HasDerivedCategory` / basic instances | no material change |
| replacement `MonoidalPreadditive` proof | no material change; proposition proof body is not data |
| `@[no_expose]` on low-level derived bifunctor/counit | no material change |
| changed instance priority | no material change; closed terms are already elaborated |

These controls distinguish a Kernel conversion problem from elaboration, typeclass search,
proof construction, and an arbitrary low-level opacity hypothesis.

## Round-two fresh measurements

The runnable source is `probes/round2/A1.lean`. The command was
`timeout 3600 /usr/bin/time -v lake env lean -Dpp.unicode.fun=true
-DrelaxedAutoImplicit=false -Dbackward.isDefEq.respectTransparency=false
-DmaxSynthPendingDepth=3 -Dwarn.sorry=false probes/round2/A1.lean`.

| Variant | Hint / compile result | Tensor probe final conversion | Full consumer final conversion |
| --- | --- | ---: | ---: |
| A0 `abbrev` | `def/abbrev`; succeeds | 46,216 ms forward; 51,526 ms reverse | 119,953 / 127,832 ms |
| A1 ordinary `def` | `def/regular`; downstream `IsLeftDerivedFunctor` synthesis fails | not applicable | not applicable |
| A2 `@[reducible] def` | regular definition under reducible transparency; succeeds | 46,358 / 51,680 ms | 2 / 2 ms |
| A3 exposed body | historical note, not re-measured in round two | historical note only | historical note only |

For A0, `Kernel.check(value)` was 2 ms for the tensor probe and 1 ms for the full
consumer. The final tensor node was `MonoidalCategoryStruct.tensorObj` on both sides;
its argument timings were 0 ms (category), 1 ms (category instance), and 52,157 ms
(the `MonoidalCategory` instance). These are fresh measurements; the earlier
49,867/50,279 ms and 131,963/121,742 ms values remain historical notes.

The ordinary-`def` failure is the valid A1.1 result: the unannotated form is not accepted
by this historical consumer, so no kernel conversion can be measured for it. The hint
probe recorded `tensorObj def/abbrev`, `DerivedMonoidal regular:2`,
`DerivedMonoidal.bifunctor regular:8`, `leftDerived₂ regular:7`, and the derived
monoidal category constructor `regular:27`.

The one-sided/two-sided exposure controls were not independently re-run in round two;
their interpretation remains a historical note. The A0/A2 orientation results above are
direct fresh measurements.
