## What changed

Restored the quarantined item from its archive, preserving both public declarations and
all three public imports. Replaced the proof of
`AlgebraicGeometry.Etale.etaleOpenScalarProjection` by a categorical pasting argument.
The proof factors `compactOpenProjection` into the local ordered open projection and
the pullback compositor, uses its separately stated scalar compatibility, and pastes
using tensor and open-map naturality.
No existing statement, definition body, instance, attribute, or public import changes.

Added `Sheaf.Paper.EtaleOrderedOpenProjectionScalar`, containing the explicit local
ordered open projection and its scalar square. This is the open-immersion part of the
argument before inserting a composite pullback. It has no compactification, proper map,
or compactification pullback comparison. The parent proof supplies these additional
steps; the new theorem is not the compactification statement renamed.

Added `Sheaf.Paper.EtaleScalarPullbackCompactification` for the compositor
transport, isolated after profiling the item. Its proof plan uses the existing
exact-composition theorem; this transport remains a named obligation.

The parent imports the two new modules privately. Its node records the actual factorization, compositor transport and pasting.

Validation: `lcompile.py --all` compiled all three modules successfully. The final
combining proof was also profiled independently at 26.6 seconds. Removed diagnostic
files and profiler settings before delivery.

## Proved and sorry left

Closed the textual hole in `AlgebraicGeometry.Etale.etaleOpenScalarProjection`
(node `lem-pur-etale-open-scalar-projection`). Its combining proof is complete.

Added two holes. First: `AlgebraicGeometry.Etale.etaleOrderedOpenProjectionScalar`
(node `lem-pur-etale-ordered-open-projection-scalar`). Its docstring gives the full
normalization, inversion and signed-symmetry proof and covers empty opens, zero
objects and zero rings. No hypotheses of flatness, boundedness, coefficient finiteness
or quasi-compactness are introduced.

Second: `AlgebraicGeometry.Etale.scalarPullback_compactification`
(node `lem-pur-etale-scalar-pullback-compactification`). This is the tensor-free
exact-to-derived composition transport. Its full naturality and inversion proof
is in its docstring. Attempts to elaborate the transport exceeded the file budget.

This is a decomposition: one upper hole closed, two strictly smaller holes added, net
one additional hole. The factorization and all tensor and open-map naturality glue
are proved here. There are no holes in definitions or private
helpers. The original item contained one hole and the delivered item contains zero.

## No longer needed

No existing import is removed and no module is withdrawn. No global pruning of a
module is claimed.

The parent's original direct dependency on
`lem-sfb-ringed-derived-monoidal-comparisons` is unnecessary: the proof uses the
already specialized, normalized `scalarPullback_composition` rather than choosing
an abstract ringed comparison system.

The mixed open scalar/tensor comparisons, open coefficient normalization and K-flat
resolution dependencies now belong to the local-square node, where they are still
needed. They are not claimed as globally pruned. The parent's remaining direct
dependencies are recorded exactly in its updated `proof_deps`.

## Where the brief, the DAG or earlier work was wrong

The item source was absent from `lean/` and listed in `coord/rework.tsv`; its archive
was used for restoration. Its Lean attachment and mathematical dependencies are
preserved. No deletion or withdrawal is inferred from quarantine.

The original proof plan described exact-to-derived transport and final pasting
only in prose. The final pasting is now explicit Lean; the transport has its own
precise statement. The normalized local
open-immersion square remains a named mathematical obligation; no false or weakened
statement was used to replace it.

## New nodes

`lem-pur-etale-ordered-open-projection-scalar` records the scalar square for the
ordered open projection at an arbitrary ambient input T, before any compactification
pullback is inserted. Its source is the open projection and scalar balancing argument
in Stacks 0E8I, 0GL6 and 07A4, extracted from steps 1 and 2 of the parent node. It uses
the existing mixed scalar/open equation and normalization statements. The definition
is a real composition of the canonical signed swaps and inverse open projection.
The node has its Lean attachment, complete proof in words and three search records.
No existing interface change requires a change record.

`lem-pur-etale-scalar-pullback-compactification` records scalar compatibility
of the canonical compactification pullback compositor. It contains no tensor or open
projection formula. Its proof plan transports the existing exact composition identity,
uses naturality to cancel comparison factors, and takes inverses of equal isomorphisms.
This node introduces the second split hole.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
