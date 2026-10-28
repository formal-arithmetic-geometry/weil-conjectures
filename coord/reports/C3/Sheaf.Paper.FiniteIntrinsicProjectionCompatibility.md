## What changed

Repaired the disputed universal tensor-family statement in
`Sheaf.Paper.FiniteIntrinsicProjectionCompatibility`. The theorem now uses the explicitly
constructed `canonicalFiniteIntrinsicTensorComparison`. Its sole caller,
`Sheaf.Paper.FiniteIntrinsicProjectionRealization`, retains its exact public signature and
supplies this family directly.

Added the canonical comparison as a genuine construction, exposing the balanced-tensor,
K-flat descent and coefficient-counit composite already used inside the existing pointwise
existence proof. Added explicit fixed proper/open subwords and a midpoint coordinate comparison.
The midpoint uses only tensor, open, pullback and direct-image realizations; it does not use
a projection map, its inverse, or a witness from mere existence.

The fixed-factorization and final compatibility proofs use ordinary kernel-checked congruence to compare the
definitionally equal coefficient-instance paths, following `FiniteProjectionFromDescent`.
The combining proof pastes complementary proper and open/compositor equations, applies the
proved fixed-factorization and constructible-conjugation identities, and obtains the full
compatibility equation. This is a decomposition with real Lean composition, not a renamed
copy of the original obligation.

Validation: the final import-order compile passed for the canonical construction (11.2 s),
coordinates (40.2 s), open factor (14.1 s), proper factor (12.3 s), compatibility (18.7 s),
parent realization (9.0 s), and its unchanged direct consumer
`Sheaf.Paper.IntegralProjectionSystemEvaluation` (22.3 s). The temporary unchanged consumer
copy was removed after testing. The parent statement matches the shared source byte for byte.
All six delivered Lean signatures match their node records (attributes are recorded in Lean), and no dependency cycle passes
through a delivered node. Change record:
`coord/changes/C3-finite-intrinsic-projection-normalization.md`.

## Proved and sorry left

Original item: one hole,
`WeilConjectures.IntegralProjectionReduction.finiteIntrinsicProjectionCompatibility`.
The original arbitrary-family assertion is false and is not counted as proved. Its corrected
canonical-family statement has a complete combining proof. Zero holes remain in the item.

Two holes added, both named public theorems with their complete argument in their docstrings:

- `WeilConjectures.IntegralProjectionReduction.finiteIntrinsicProjectionProperFactor`
  (`lem-sf-finite-intrinsic-projection-proper-factor`). This compares the proper counit factor
  only, before the open tensor map or pullback compositor.
- `WeilConjectures.IntegralProjectionReduction.finiteIntrinsicProjectionOpenFactor`
  (`lem-sf-finite-intrinsic-projection-open-factor`). This compares the open tensor map and
  pullback compositor only; the proper projection does not occur.

All definitions are explicit and have no sorry. The coordinate theorems `fixed_factorization`
and `component_factorization`, the generic pasting lemma, and the parent existential assembly
are proved. This delivery is a statement repair and decomposition; it is not a net decrease
in the target-closure hole count.

## No longer needed

Removed the proof-only import `Sheaf.Paper.FiniteIntrinsicTensorRealization` from the parent.
Its node `new-sf-finite-intrinsic-tensor-realization` and sole lower wrapper
`Sheaf.Paper.FiniteIntrinsicTensorComponent` / `lem-sf-finite-intrinsic-tensor-component`
are no longer needed by this route: the comparison is supplied by construction, not by
choosing from their unnormalized Nonempty assertions. Both modules and all declarations
remain in the repository. The normalized scalar tensor realization and finite K-flat tensor
model remain needed and are imported by the canonical construction.

No existing public import is removed. No other module is withdrawn. The old proof dependencies
`def-weil-proetale-inverse-image`, `def-pur-finite-pullback-tensor-construction`,
`def-sf-constructible-projection-mates`, and `def-sf-integral-projection-evaluation-factors`
remain needed by the construction and factor obligations; they are not pruned from the
mathematical route, only replaced by the precise factor dependencies on the assigned node.

## Where the brief, the DAG or earlier work was wrong

The previous split applied compatibility to an arbitrary independent family of tensor
isomorphisms. Objectwise naturality alone does not supply compatibility with geometric maps
or their adjunction units. The assigned module itself recorded this defect. Specifying the
canonical balanced-tensor construction repairs it without adding a hypothesis to the parent's
existential statement or changing any target.
For a concrete obstruction to the old assertion, take odd finite coefficients and
p: Y ⊔ Y → Y with constant degree-zero inputs. The projection is the nonzero canonical
A² ⊗ A → A². Negating the tensor comparison at X = Y ⊔ Y while retaining the one at Y
negates only one side of the required equation. The old assertion cannot hold for both
families. This uses a finite proper map and bounded constructible finite-Tor inputs.

The server queue read at the start lists this as a disputed route item; the older rework row
mentions a quarantined import of `IntegralNormalizedFamily`. The current source is present
and does not import that module directly. No quarantine archive or attachment is deleted.

Edge cases were checked at the level of the constructions: exponent m=0 is still the positive
coefficient exponent one; all coordinate arrows are existing isomorphism components; zero
inputs and empty schemes use the same maps; identity and empty opens use the actual open
unit, and no finite-Tor assumption on K or separated structure-map assumption is added.
The proper equation contains no open projection. The open equation contains no proper
projection. Thus neither is the full obligation under a different name.

The blueprint search found no separate intrinsic-projection statement and no matching scalar
tensor statement (the scalar query's one result is a purity statement). The ancestor helper
returns None on this recently created chain; the new nodes use the explicitly recorded
`fix-prop-projection-formula` ancestor already carried by its parent, with the same-map
sentence as their source. The current unit has no separately realized proof steps to bypass.

## New nodes

`def-sf-canonical-finite-intrinsic-tensor-comparison` records the explicit comparison and its
counit cancellation. It reuses the construction from the proved pointwise existence theorem;
it introduces no choice from an unnormalized existence assertion.

`def-sf-finite-intrinsic-projection-coordinates` records the fixed subwords,
the explicit midpoint and the proved fixed/component factorizations.

`lem-sf-finite-intrinsic-projection-proper-factor` records the proper counit square. Its
source is the projection mate definition (Stacks 0B56) and the normalized K-flat tensor
comparison (07A4).

`lem-sf-finite-intrinsic-projection-open-factor` records the complementary open/compositor
square. Its source is the open tensor/adjunction argument (Stacks 0E8I) and derived pullback
composition on K-flat representatives. These statements are strictly separate factors of
the argument. Searches through LeanFinder, Loogle, LeanSearch and Mathlib grep found no
project-specific comparison theorem. The proof source is the current blueprint same-map
sentence, read with the stated proper/open and scalar-realization definitions.

The additional source search found the proved `finiteScalarTensorPullbackComparison` and its
representative lemmas. Its public conclusion supplies existential compatible tensor
isomorphisms, without identifying them with the fixed canonical values. It therefore does
not directly close either factor equation here. Its representative argument is useful for
the canonical tensor/pullback square in the natural-language proofs of both new factors.

Preflight initially returned two node signature records that included `@[irreducible]`;
the records now contain the declaration signatures expected by the checker. The Lean
attributes and compiled code are unchanged. The statement-change record also preserves
the exact prior statement, statement dependencies, proof and proof dependencies.

## Forced adaptations

`Sheaf.Paper.FiniteIntrinsicProjectionRealization` (unclaimed). The original proof ended with
`finiteIntrinsicProjectionCompatibility m S e f c K L U V k l`, which no longer elaborates once
the item's binder `e` is removed (the item's statement was STATEMENT-DISPUTED and is repaired).
Changed lines: the proof body now supplies `canonicalFiniteIntrinsicTensorComparison m` as the
witness and applies `finiteIntrinsicProjectionCompatibility m S`; the now unused proof-only
`import Sheaf.Paper.FiniteIntrinsicTensorRealization` is dropped. The public statement is
unchanged byte for byte. (Reviewer, 2026-10-28: two file-level `set_option
backward.isDefEq.respectTransparency…` lines the delivery also added were not needed, the
module compiles without them, and are withdrawn.)

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CanonicalFiniteIntrinsicTensorComparison": "e75b8329d801125944fbd81264e2ed2ed0a8986e", "Sheaf.Paper.FiniteIntrinsicProjectionCompatibility": "dbf86386a3ea78fe387e1487d070039d362c3bbd", "Sheaf.Paper.FiniteIntrinsicProjectionCoordinates": "0c74ceb61885e2120a488f54a3cbfb5d8a152799", "Sheaf.Paper.FiniteIntrinsicProjectionOpenFactor": "2f03d6315a21a489c466c94a749f51d09ef25b21", "Sheaf.Paper.FiniteIntrinsicProjectionProperFactor": "2ea1412c6b6e72524be925b5eadf5ad240fc1ab4", "Sheaf.Paper.FiniteIntrinsicProjectionRealization": "77caa7c36dfbc528594f3cb0d71679e37502a989"}, "results": {"Sheaf.Paper.IntegralProjectionSystemEvaluation": {"hash": "0c8f6093cbf98ec3662932678954f803590a9d56", "status": "OK"}}, "seconds": 29, "time": "2026-10-28T11:38:01+0800", "transitive": 0, "version": 1}
```

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
