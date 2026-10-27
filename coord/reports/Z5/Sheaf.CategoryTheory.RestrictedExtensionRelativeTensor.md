## What changed

Proved `CategoryTheory.Mod.exists_restrictedExtension_relativeTensor` in
`Sheaf.CategoryTheory.RestrictedExtensionRelativeTensor`, preserving its full statement.
The direct proof adapts the already proved private `scalarTensorIso` comparison and
its normalization/naturality lemmas from `Sheaf.CategoryTheory.FiniteFreeScalarCoordinates`.
Those helpers are private and cannot be imported as an API; the argument here uses
only the existing public coequalizer and action API, without abelianness or freeness.

The two defining coequalizers give maps in both directions. Cancelling their
projections proves inverse identities. Cancelling the tensor of the extension
projection proves linearity; `Mod.isoMk` supplies the inverse module morphism.
Cancelling the extension projection also proves naturality, and `NatIso.ofComponents`
assembles the desired natural isomorphism with both normalizations.

Updated the item's DAG proof, proof dependencies and proof origin to match this
argument. Updated the declaration's proof explanation accordingly. All public imports
and all declaration signatures are unchanged. The item compiled via `lcompile.py`.

## Proved and sorry left

Closed 1 hole:
`CategoryTheory.Mod.exists_restrictedExtension_relativeTensor`
(node `lem-sfb-restricted-extension-relative-tensor`).

Added 0 holes. Remaining holes in delivered Lean files: 0. No statements split off.
The proof uses the existing sheaf tensor structure and preservation instances;
this report does not claim those dependencies have no transitive holes.

## No longer needed

Removed the proof-only import `Sheaf.CategoryTheory.EquivariantCoequalizerComparison`.
Removed `lem-sfb-equivariant-coequalizer-comparison` from this node's `proof_deps`
and `tool_uses`: explicit coequalizer descents and cancellation give the comparison
without constructing an auxiliary module-valued source functor or natural balancing
pair. That general lemma remains available to its other consumers; no file is withdrawn.
All other declared proof dependencies remain needed. No public imports were removed.
No unit statement or unit proof step is bypassed.

The stronger underlying-object comparison in
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars` is not imported:
its ambient hypotheses are unnecessary, and it does not supply the module-valued
comparison required here. `FiniteFreeScalarCoordinates` is read for its existing
proof, not imported: no finite-power construction enters the result.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect in the statement was found. The DAG's general equivariant
comparison is a valid but longer route. The existing private proof in
`FiniteFreeScalarCoordinates` already gives the required argument from the public
module-object API, including linearity and naturality. Direct adaptation avoids
new nodes and the general comparison dependency.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
