## What changed

Repair of returned head `50296683e15`: removed the inherited
`set_option warn.sorry false` command. The landing hole scanner matched the `sorry`
component of that option name and reported it as an unattributed hole at line 31.
The option is unnecessary now that the theorem is proved. The actual hole scanner
now reports zero markers and zero scanner warnings for both delivered modules.
All theorem statements, proof bodies, public imports and DAG dependencies are retained.
The repaired assigned module compiled remotely in 14.9 seconds; the unchanged refinement
module passed the cached compile check. The assigned theorem signature also matches current
main byte-for-byte.

Proved `AlgebraicGeometry.exists_geometricallyConnected_fibre_neighbourhood` without changing
its statement or public imports. The proof applies the existing affine fibre-open reduction,
affine elementary étale multisection, and finite locally free multisection connected-open
statements. A proved private helper identifies the initial restricted fibre with its prescribed
open, including the structure map to the residue-field spectrum.

Added `Sheaf.AlgebraicGeometry.Morphisms.ConnectedOpenEtaleRefinement` with
`AlgebraicGeometry.exists_affine_etale_refinement_of_connected_open`. This isolates the final
open-image restriction, quasi-compactness, residue-field compatibility, and equality of the
embedded special fibre. Its proof uses Mathlib and the already proved definition/API of
`Scheme.Hom.fiberMap`; it invokes none of the three existence statements above.

Updated the item's proof steps and dependencies to follow this Lean assembly. No existing
module besides the assigned item is changed. No existing definition or statement is changed.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.exists_geometricallyConnected_fibre_neighbourhood`
(node `lem-trf-geometrically-connected-fibre-open-spreading`). Its proof uses the existing
stated dependencies, as intended by stage 3.

Validation: both final files compiled remotely without warnings, in import order. The
refinement module took 6.6 seconds and the assigned module took 19.6 seconds, both below
the 60-second per-file limit. The original theorem signature was compared byte-for-byte
and is unchanged; the DAG attachment of the new statement matches its Lean signature.

Added zero holes. The new theorem
`AlgebraicGeometry.exists_affine_etale_refinement_of_connected_open`
(node `lem-trf-connected-open-etale-refinement`) and every private helper are proved.
There are no `sorry` statements left in the delivered modules.

## No longer needed

Removed these seven redundant proof imports from the assigned module:

- `WeilConjectures.AlgebraicGeometry.FibreCohenMacaulayLocus`
- `Sheaf.AlgebraicGeometry.Morphisms.CohenMacaulayClosedPointSlice`
- `Sheaf.TraceFormula.FlatLFPCMLocusFibreDense`
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`
- `WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteAtPoint`
- `WeilConjectures.AlgebraicGeometry.FinitePiecePersistence`
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`

The first six belong to earlier construction steps, supplied here by the existing affine
reduction and multisection packages. The finite-locally-free predicate is already publicly
imported by the packages using it. These removals do not claim that the corresponding source
modules or mathematical dependencies can be withdrawn globally.

Removed the item's obsolete direct `tool_uses` entries for
`lem-sbc-fibre-cohen-macaulay-locus-open`,
`lem-weil-pbc-etale-local-finite-at-point-elementary`, and
`lem-weil-pbc-elementary-etale-finite-piece-persistence`: these steps occur inside the
multisection package, not in this assembly. The previous final-step dependencies are now
accounted for by the refinement node. `lem-weil-pbc-quasi-compact-morphism-preimage-qc-open` is not separately invoked:
compactness follows from `quasiCompact_of_compactSpace`, base change, and
`QuasiCompact.compactSpace_of_compactSpace`. No module is withdrawn and no unit route
is bypassed.

## Where the brief, the DAG or earlier work was wrong

The return identified an unattributed hole at line 31. Reproducing the landing scanner
confirmed that this was the inherited warning-suppression option, not a proof hole.
Removing that command repairs the reported failure without changing a proof.

No mathematical statement correction was necessary. The existing declarations support the
planned argument. The previously implicit final base-change glue needs explicit projection
identities and image calculations; these are now proved. In particular the argument does not
assume that points of a scheme fibre product are determined by their two coordinates.

Edge cases: geometric connectedness makes the distinguished fibre nonempty. In the refinement
lemma this is assumed separately and transported across the specified fibre isomorphism.
An empty final fibre is excluded by choosing the affine base inside the open image. The
original base need not be Noetherian or quasi-separated: quasi-compactness is established over
the affine intermediate base, which is quasi-separated. No reducedness is needed in the final
refinement after the connected open has already been constructed.

## New nodes

`lem-trf-connected-open-etale-refinement` records the final paragraph of Stacks Tag 055W,
`lemma-fibre-geometrically-connected-reduced`. It starts with an already constructed compact
open immersion inducing an isomorphism on the distinguished fibre and having geometrically
connected nonempty fibres. It proves affine shrinking and the precise embedded fibre equality.
It is a proper subargument of the item: it constructs neither the initial lift of the fibre
open, nor the multisection, nor the connected open. Its complete Lean proof adds no new hole.
The node includes source, proof steps, dependencies, Lean attachment, and three kinds of search.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
