## What changed

Restored `Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparison` from its
quarantine archive, as assigned in `coord/rework.tsv`. Added exactly one line:
`public import Sheaf.Algebra.Homology.KFlat`. The public theorem signature uses
that module's `IsAcyclicTensorKFlat` predicate; private proof imports cannot
provide it to the signature. All other source lines are unchanged.

The unmodified archive fails through `lcompile.py` with the recorded invalid-field
error at line 102 and a cascading unsolved goal. The repaired file compiles without
diagnostics in 7.2 seconds. The proof constructs scalar extension from
`exists_baseDerivedExtension_linear`, applies the existing comparison isomorphism,
proves stalk-counit invertibility using the K-flat stalk criterion, and applies
the proved private homology calculation. All these dependencies remain imported.
The final `lcompile.py --all` check also passes, in 7.0 seconds.
An isolated scratch importer, with only a public import of the restored module,
also compiles and sees both `CochainComplex.IsAcyclicTensorKFlat` and the original
theorem (10.9 seconds for its sandbox dependency, 2.0 seconds for the importer).

Change record: `coord/changes/P4-stalk-derived-extension-kflat-public-import.md`.

## Proved and sorry left

This is a visibility repair of a module with zero textual holes: 0 holes closed,
0 holes added, 0 split off, 0 left. The existing complete proofs of
`AlgebraicGeometry.SingleComplexBaseChange.exists_stalkDerivedExtensionComparison`
and private `homology_comparison` are unchanged. No new declaration is introduced.
This does not assert that every transitive proof dependency is sorry-free.

## No longer needed

None. No import, declaration, node, module, Lean attachment or dependency is
removed or withdrawn. Both original public imports and every proof import remain
needed for the unchanged signature or proof. The quarantine archive is retained.

## Where the brief, the DAG or earlier work was wrong

The item is a listed quarantine repair, rather than a remaining proof hole.
Its previously completed proof needs an explicit public dependency after the
upstream synchronization. This is the same visibility distinction already repaired
in the comparison-isomorphism modules; changing the K-flat hypothesis is unnecessary.

The existing DAG node and `sk-thm-picard-semicon` unit record need no modification:
the statement and proof route are unchanged. Searches of the current source and
Mathlib found generic `leftDerivedNatIso` and ordinary stalk-pullback isomorphisms;
they give no reason to replace this already completed proof.

The only archived direct consumer is
`Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality`. Its application at
line 112 uses the identical theorem signature and computation; it needs no forced
adaptation. Its own rework assignment and dependencies are preserved. The upstream
source library and all target statements are untouched.
`tools/downstream.py --allow-missing --uses` reports zero live downstream modules
and zero live uses; the archived consumer was checked separately in the source.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
