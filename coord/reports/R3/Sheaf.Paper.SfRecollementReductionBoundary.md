## What changed

Proved `WeilConjectures.sfRecollementReductionBoundary` in
`Sheaf.Paper.SfRecollementReductionBoundary`, preserving every existing statement,
definition and public import. Three proved private helpers establish preservation
of the counit and unit, distinguishedness with the specified transported tensor
shift, and finite shifted orthogonality. The main proof applies the existing BBD
triangle-morphism extension theorem with the prescribed three vertex maps and
packages them using `Triangle.isoMk`.

Added proof-only imports of `Sheaf.Paper.SfOpenClosedTriangleAllStages`,
`WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension`, and
`Sheaf.Algebra.Homology.DerivedScalarExtensionCounitShift`. Updated the item's
node proof, proof dependencies and proof origin to the argument actually used.
The already-proved naturality theorem is preserved verbatim.

Validation: the complete Lean proof compiled without errors or warnings through
`lcompile.py` (26.6 seconds). Delivery performs the required final compile and
preflight checks on the packet.

## Proved and sorry left

Closed the one remaining hole:
`WeilConjectures.sfRecollementReductionBoundary`
(node `lem-sf-recollement-reduction-boundary`).
There are zero `sorry` declarations left in the delivered module, zero new holes,
and zero split-off statements. The three private helpers are fully proved.
`WeilConjectures.sfRecollementReductionBoundary_naturality` was already proved
by the earlier P3 delivery and is not counted as a newly closed hole.

The proof uses existing dependency declarations; this is not a claim that every
transitive dependency is already free of `sorry`.

## No longer needed

The proof does not directly use `lem-pur-derived-change-of-rings`
(`Sheaf.SecSmoothPurity.OrdinaryDerivedChangeOfRings`), or
`lem-fix-operation-reduction`
(`Sheaf.Paper.BasicOperationsCoefficientReduction`). Its scalar-extension
exactness comes from the counit-normalized derived-extension theorem and its
unit/counit compatibility comes directly from the specified operation datum.
Removed those two obsolete entries from the node's top-level `tool_uses` list.
Their statement dependencies and declarations remain: the theorem still names
the same specified operations, and other consumers may need these results.
The current live module had no proof-only imports, so no live import is removed.

The original separate transported-boundary construction and subsequent uniqueness
identification are unnecessary: the existing triangle-morphism extension theorem
produces the third square for the prescribed outer maps directly. No node or
module is withdrawn, and no blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The current live source has one hole, rather than the two described in its old
stage-2 review: P3 had already proved naturality before this worker started.
The original node's abstract change-of-rings assertion alone did not identify the
specific transported shift structure appearing in the Lean statement. The proof
uses `SheafOfModules.derivedScalarExtension_counitShift` and the uniqueness of the
counit-compatible shift, then transports triangulatedness through
`PurCompactSupport.finiteReductionIso`; hence it uses exactly that structure.
The finite all-stages theorem is transported through the datum's finite
normalization isomorphisms before applying orthogonality. No statement or
definition repair was needed.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
