## What changed

Proved `AlgebraicGeometry.IsGroupoidScheme.existsUnique_invariantOpen_restriction_degree`
in `Sheaf.AlgebraicGeometry.GroupoidInvariantOpenRestrictionDegree`, preserving its signature
and all public imports. Four proved private helpers implement factorization into an inverse-image
open, descent of all groupoid laws along monomorphisms, involutivity from the groupoid laws,
and transport of finite locally free degree along an isomorphism.

The source and target restrictions use `Scheme.Hom.resLE`; the remaining three maps use
`IsOpenImmersion.lift`. Their compatibility equations imply uniqueness by monomorphism
cancellation. The restricted laws are obtained by the pullback universal property and cancellation.
Associativity applied to `(i(i(a)), i(a), a)` proves involutivity. The existing source-library
`Scheme.Hom.fiberDegree_comp_left_of_isIso` supplies the final fibre-degree equality.
Updated the item's DAG proof steps 5–7 and proof provenance to describe these details.
The complete module passed `lcompile.py` in 3.9 seconds without warnings.
A text comparison confirmed that the public theorem signature and imports are unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.IsGroupoidScheme.existsUnique_invariantOpen_restriction_degree`
(node `lem-a1-groupoid-invariant-open-restriction-degree`). No holes added, no split-off statements,
and no `sorry` remains in the delivered module. The helpers have complete proofs.

## No longer needed

None. No imports were removed or added, and no module or node is withdrawn. All eight declared
proof dependencies remain relevant to the restriction construction, monomorphism cancellation,
groupoid laws, pullbacks, and the three defining properties of finite locally free morphisms.
The existing fibre-degree API replaces a repeated explicit construction of the isomorphism of
fibres; no new intermediate theory is needed.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The DAG's involutivity step can be performed directly in the
restricted groupoid, and its final fibre-degree comparison already exists as a proved
source-library lemma. The argument imposes no extra hypotheses and includes the empty open.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
