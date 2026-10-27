## What changed

Proved `AlgebraicGeometry.affine_etale_relation_separated_locally_quasi_finite`
in `Sheaf.AlgebraicGeometry.AffineEtaleRelationSeparatedQuasiFinite` without changing
its statement. Added private proof imports of
`Sheaf.AlgebraicGeometry.AffineSquareMonomorphismAbsoluteSeparated` and
`Sheaf.AlgebraicGeometry.MonomorphismFiniteTypeComposite`. Updated the theorem's
proof description to the current DAG's three-step assembly.

The canonical affine presentation `U.left.isoSpec` instantiates the affine-square
lemma. Its absolute-separatedness conclusion makes `R.left` separated, and
Mathlib's separated cancellation supplies separatedness of both projections.
Étaleness supplies local finite type and open diagonals, so the existing
unramified-to-quasi-finite theorem gives both projection conclusions. The relation
map followed by the first projection equals `s.left`; the existing monomorphism
composite theorem then gives its separatedness and local quasi-finiteness.

Read Stacks `spaces.tex`, `lemma-presentation-quasi-compact` (Tag 0265), opening
two proof paragraphs and first representability step. The given equivalence-relation
hypothesis is unnecessary for these geometric conclusions; it is retained verbatim.
The argument uses no separatedness of the base or quasi-compactness of the relation.
The current unit route is preserved. A theorem-local unused-variable linter option
preserves the original named hypothesis without an irrelevant use in the proof.

The sandbox proof compiled successfully through `lcompile.py`; `deliver3.py` runs
the final compile and declaration checks on the submitted version.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.affine_etale_relation_separated_locally_quasi_finite`
(node `lem-trf-affine-etale-relation-separated-lqf`).
No sorry remains in the item, and no holes are added or split off.
The proof uses the existing stated dependencies
`AlgebraicGeometry.affine_square_monomorphism_absolute_separated` and
`AlgebraicGeometry.Scheme.Hom.monomorphism_properties_of_locallyOfFiniteType_comp`,
whose proofs remain their separate items. The unramified quasi-finiteness theorem
is already proved. This delivery closes the assembly hole; it does not claim that
all transitive dependencies are sorry-free.

## No longer needed

Removed the direct private import
`Sheaf.AlgebraicGeometry.UnramifiedMorphism`: the proof constructs the finite-type
and open-diagonal conjunction directly, and does not refer to `IsUnramified`.
That module is still needed by `MonomorphismFiniteTypeComposite`, so it is not
withdrawn or globally pruned. All public imports are retained.
All seven proof dependencies of the current node are used, directly or through
the associated definitions and Mathlib instances. No DAG node or module is pruned.
No source-library declaration or import is changed.

## Where the brief, the DAG or earlier work was wrong

The item's old five-step docstring predates the current reviewed three-step DAG
assembly. It is now aligned with that DAG. The DAG itself needs no change.
No mathematical statement or definition required repair, and no new nodes were needed.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
