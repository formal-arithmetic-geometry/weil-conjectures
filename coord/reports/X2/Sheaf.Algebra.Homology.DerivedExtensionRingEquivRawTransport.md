## What changed

Retired `Sheaf.Algebra.Homology.DerivedExtensionRingEquivRawTransport`, as listed in
`coord/retire-items.tsv` under the human's 2026-10-20 retirement hand-off. Its
`ModuleCat.exists_raw_transport` duplicates a proved upstream theorem with fewer
parameters. The module is withdrawn through `deleted.txt`; its node
`lem-pc-derived-extension-ring-equiv-raw-transport` now records the exact official
signature, module and file, with an explanation of the legacy specialization.
No upstream Lean file changes.

The entire legacy signature was derived from the upstream theorem in
`scratchpad/LegacyTransportCompatibility.lean`: introduce the old parameters and
termwise isomorphism, unpack `exists_raw_transport eB`, and return the functor,
factorization isomorphism and `True`. The verification file compiled through
`lcompile.py`; its theorem and the upstream theorem use only `propext`,
`Classical.choice`, and `Quot.sound`. The official consumer
`WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivRawCounit` was compiled
unchanged, including an axiom check with the same three axioms.

Change record:
`coord/changes/X2-retire-derived-extension-ring-equiv-raw-transport.md`.

## Proved and sorry left

The item contained zero `sorry` before this repair. It introduces no holes and
closes no holes: 0 of 0 proved; 0 split off. No `sorry` remains in the withdrawn
module. The original transport theorem is preserved mathematically by the
stronger, already proved official `ModuleCat.exists_raw_transport`; the complete
legacy specialization was also checked in Lean. This is a retirement repair,
not a claim of a newly closed proof hole.

## No longer needed

Pruned module: `Sheaf.Algebra.Homology.DerivedExtensionRingEquivRawTransport`.
Its public import of
`WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel` and private
import of `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` disappear with
the duplicate. The upstream theorem retains its own required imports.

There are zero direct or transitive importers of the old Sheaf module. A scan of
both library roots and quarantine sources found no imports to migrate. The sole
DAG parent, `lem-pc-derived-extension-ring-equiv-raw-counit`, already records
`WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivRawCounit`. That module
already imports the official transport and applies its current API. The parent
dependency remains valid through the repointed transport node; no DAG node or
unit step is removed. The upstream transport's source import closure has no
Sheaf modules or duplicate twins. No other module or dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

This is a zero-hole retirement item, rather than the deep outstanding proof
suggested by the generic brief. The retirement table's historical Sheaf counit
consumer has already been retired; its node and official replacement use the
simplified upstream theorem. The transport node alone still pointed at the
unneeded legacy copy. The upstream result drops unused R-side and derived
scalar-extension parameters and replaces `exists q, True` by `Nonempty`; the
compiled specialization verifies the original conclusion without any change to
the mathematical statement or the unit route.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
