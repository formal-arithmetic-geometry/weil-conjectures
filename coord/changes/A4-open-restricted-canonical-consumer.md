# AlgebraicGeometry.SingleComplexBaseChange.exists_open_restricted_comparison_transport

## Reason

Retire the redundant historical Sheaf import path after migrating its sole live
consumer to the canonical, fully proved adopted theorem. W6 already restored
the historical module as a re-export in landing 20261021T162130-L-292211, just
before the A4 claim. The present delivery goes beyond rebasing that repair:
it removes the consumer's dependency on the wrapper and withdraws the wrapper.
The item is also listed in coord/retire-items.tsv with this canonical replacement.

The theorem itself remains in WeilConjectures without any edit. Its DAG node,
canonical Lean attachment, both mathematical proof dependencies, and its parent's
use of that node remain. This withdraws a module, not the mathematical result.
The adopted proof still constructs literal restricted representative data and
specializes the comparison-square theorem. No unit route is bypassed.

## Old

The item's complete current source is:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonComposition
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonTransport

/-! # Comparison on the literal restriction of a complex

Source: Stacks Project, Tag 0DJ8, locality of equation-bc; Tag 0DJ9.
(blueprint: lem-pc-open-restricted-comparison-transport).

Re-export the adopted source proof at the historical module path. Its K-flat
predicate `IsKFlatTensor` has the same defining acyclic-test-complex formula as
`IsAcyclicTensorKFlat`, retained through the public naturality import. The
comparison maps, representative data and derived-composition transport agree.
-/

@[expose] public section
```

The sole live consumer's dependency line is:

```lean
import Sheaf.AlgebraicGeometry.OpenRestrictedComparisonTransport
```

## New

Withdraw lean/Sheaf/AlgebraicGeometry/OpenRestrictedComparisonTransport.lean
via deleted.txt. The delivery tool installs its standard empty module stub.
The sole consumer instead has:

```lean
import WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonTransport
```

Every other line of the consumer, including its signature and proof, is unchanged.
Its public naturality import already retains the legacy IsAcyclicTensorKFlat
predicate. The original transport's canonical IsKFlatTensor spelling is
definitionally the same predicate. Its original composition-map public import
is already public in the canonical transport provider. No instance or notation
needed by the consumer is lost. A separate scratch signature check applies the
canonical theorem to the entire historical signature with the legacy predicate.

No theorem is removed from WeilConjectures. No statement, definition, universe,
hypothesis, conclusion or target meaning changes. All parent dependency edges
are retained, including any unfinished proofs referencing this result. The
item's node already points at the canonical provider, so no detachment is needed.
The parent node records its direct use of the canonical provider; the item node
records the wrapper withdrawal in proof_origin. No DAG node is withdrawn.

## Users

The read-only tools/downstream.py query reports exactly one downstream module.
A source import search of lean/ and quarantine/ finds the same parent and its
archived copy. The live parent has no current holder. Its archived copy is a
historical snapshot, not a second live compilation unit; it is left intact.
A full JSON dependency scan finds just this parent's node as a mathematical
consumer. The unit sk-thm-picard-semicon realizes sk-thm-picard-semicon and
thm-pc-semicontinuity-base-change, neither changed here.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OpenRestrictedComparisonTransport | A4 | Withdraw redundant re-export; zero local declarations. |
| Sheaf.AlgebraicGeometry.OpenComparisonIntoPullbackTransport | unclaimed | Replace one private import; identical complete theorem and proof. |
| WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonTransport | unclaimed | Canonical complete theorem preserved verbatim. |

## Status

landed 20261021T165746-L-2238838 2026-10-21 (merge of deliver/A4/Sheaf.AlgebraicGeometry.OpenRestrictedComparisonTransport)
