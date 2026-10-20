## What changed

Proved `CochainComplex.exists_canonicalTruncationFiltration` in
`lean/Sheaf/Algebra/Homology/CanonicalTruncationFiltration.lean`, preserving its complete
statement and all existing public imports. Private constructions give the good-truncation
filtration, its canonical step isomorphisms, and the filtration-preserving lift of any chain map.
Private proofs establish the finite bounds and the restriction of chain homotopies.

The graded-piece isomorphism is obtained by applying `cokernel.mapIso` to the canonical
subobject representatives and the inclusion supplied by
`CochainComplex.exists_upperTruncationStepSES`. Its coordinates, comparison quasi-isomorphism,
and naturality give the corresponding filtration assertions. Naturality and two-out-of-three
prove invariance under quasi-isomorphisms. This follows all five steps of the existing DAG plan;
no node or public interface changes are needed.

The boundedness proof takes `q = max m n`, `a = -q`, and `b = -m + 1`, ensuring `a < b`
even when the supplied bounds are reversed for the zero complex. The homotopy proof uses the
inverse of the target truncation inclusion below the cutoff; otherwise its component vanishes
by degree support or by the homotopy's support condition. These arguments also cover a single
module in one degree and a two-term complex with zero or invertible differential.

Local linter options on the theorem preserve the original unused boundedness binders and allow
rewriting between the chosen cokernel/subobject representatives without changing any global
option. The public theorem statement was compared verbatim with the original and is identical.

## Proved and sorry left

Closed: `CochainComplex.exists_canonicalTruncationFiltration`
(node `lem-kun-canonical-truncation-filtration`). Original holes: 1; closed: 1; added: 0;
remaining in the item: 0. No new modules or split-off statements.

The module compiles through `lcompile.py` with no errors or warnings. Axiom and delivery checks
are recorded by the required delivery tool.

## No longer needed

Removed the redundant direct proof imports
`Sheaf.Algebra.Homology.FilteredComplexSubquotients` and
`WeilConjectures.CategoryTheory.Abelian.Filtration`. Their definitions remain available through
the unchanged public imports and are still used, so neither module nor its DAG node is pruned.
No planned proof dependency is bypassed. All three existing public imports are retained:
finite filtered module complexes supply the statement interfaces, the upper-truncation theorem
supplies the graded comparisons, and the embedding supplement supplies the monic inclusions
and their invertible components below the cutoff.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. The five-step plan is realized without new holes.
The finite-bounds proof explicitly allows the zero complex to be supplied with reversed
bounds; it does not assume the existentially supplied lower bound is at most the upper bound.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
