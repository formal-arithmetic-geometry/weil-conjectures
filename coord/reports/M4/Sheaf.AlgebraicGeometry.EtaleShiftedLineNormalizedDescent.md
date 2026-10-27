## What changed

Replaced the body of
`AlgebraicGeometry.Etale.AffineLineNormalizedDescent.normalized_descent`
with a reduction to normalized-comparison existence. No existing declaration signature,
definition, declaration attribute, or public import changed. Added local elaboration
attributes and a notation scope opening are recorded in the change record below.

The complete combining proof obtains the comparison, identifies both overlap restrictions
with pullback along the common composite by naturality, and takes inverses for the inverse
clause. It proves uniqueness among arbitrary normalized global comparisons, and identifies
every normalized comparison after base change with the restriction of the global one.
For these rigidity clauses it shifts the base object to its chosen sheaf, combines
ordinary affine-line fullness with full faithfulness of the single-complex functor,
and transports endomorphism lifting back through the shift. The section compositor
identifies the lifted base endomorphism with its restriction at one; normalization
makes it the identity. Exact inverse image preserves the single-degree hypothesis
after any base change. These arguments do not need the base change to be etale.

Added `Sheaf.AlgebraicGeometry.EtaleShiftedLineComparisonExistence`, containing only the
existence and prescribed-restriction part of the original argument. It is stated for
arbitrary coefficient rings and arbitrary sheaves placed in a common degree: the fullness
argument needs neither rank one nor finite coefficients. It uses the original
shift-to-sheaves, overlap-ratio, and sheaf-gluing route; its source and complete proof in
words are in the theorem docstring and its new node. The parent node records the resulting
route. Private proof imports provide full faithfulness and compatibility with shifts.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.AffineLineNormalizedDescent.normalized_descent`
(node `lem-trf-etale-shifted-line-normalized-descent`). Its combining proof has no `sorry`.
The existing proof of `sheaf_rigidity` is preserved and is not counted as new work.

Added one hole:
`AlgebraicGeometry.Etale.exists_normalized_shifted_line_comparison`
(node `lem-trf-etale-shifted-line-comparison-existence`). This is the existence of
a normalized global comparison for arbitrary sheaves placed in a common degree, with
the specified restrictions. It asserts neither
uniqueness among arbitrary comparisons nor independence after base change nor overlap
equalities in the output. Those clauses are proved separately in the parent.

Actual packet hole count: one, all in the new existence theorem. One original hole closed
and one lower hole added: this is a decomposition, with net hole reduction zero.

## No longer needed

Removed direct proof imports from the item:
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`,
`Sheaf.AlgebraicGeometry.EtaleSheafHomFamilyGluing`,
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, and
`Mathlib.AlgebraicGeometry.Sites.MorphismProperty`.
The exactness and sheaf-gluing nodes remain needed by the new existence lemma; their work
is not pruned. The item retains affine-line fullness for its existing `sheaf_rigidity`.
The additional proof uses Mathlib's fully faithful single functor and the source
`Derived.Shift` API. Rigidity uses no tensor-invertibility construction or specialized
purity/affine-line gluing module.
No module or unit step is withdrawn, and no transitive mathematical dependency is claimed
pruned. 
## Where the brief, the DAG or earlier work was wrong

No false statement or source-library interface defect was found. Affine-line fullness
on sheaves lifts endomorphisms of pulled-back objects in any single degree. This supplies the uniqueness clauses without a tensor-invertibility
construction. Comparison existence remains a separate genuine gluing result. The empty base, empty cover, nonreduced base, and zero
coefficient ring introduce no additional hypothesis; the new node's proof explains these
cases. No source declaration or target statement was changed.

The resumed reference clock was reset by the launcher: the earlier recorded start was
2026-10-23 12:40:01 UTC, while the current `.budget.start` is 2026-10-23 15:23:33 UTC.
Resume briefs `.brief2` through `.brief5` are present. Delivery attempt 85522 reported
39 active minutes and refused the split; further proof work continued, including the
compiled fullness argument replacing tensor invertibility. No budget metadata was edited.

## New nodes

`lem-trf-etale-shifted-line-comparison-existence` states the normalized comparison-existence
part of blueprint `sk-thm-dnc`, opening paragraph and Gluing. Its Lean module is
`Sheaf.AlgebraicGeometry.EtaleShiftedLineComparisonExistence`. LeanSearch, LeanFinder,
Loogle, and grep found no matching arbitrary-base, arbitrary-cover theorem for arbitrary
sheaves in one degree. Existing
source results glue along a single surjective etale morphism; specialized normalized
comparison results additionally have field-based hypotheses. The node retains
the original affine-line-fullness, exact inverse-image, fully faithful single-complex,
cover-base-change, and sheaf-family-gluing dependencies. Its theorem is a strict existence
part of the argument, with the rigidity and independence work proved in the parent.
Both packet modules compile together through `lcompile.py --all`; the combining proof
passes kernel checking. Existing statements and definitions are unchanged. Preflight additionally required a
record for local elaboration commands; it is
`coord/changes/etale-shifted-line-local-proof-scope.md`.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
