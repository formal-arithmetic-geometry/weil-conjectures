## What changed

Filled the remaining proof in
`WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness`:
`AlgebraicGeometry.Etale.nonempty_dualizingComplex_iso_constantComplex_of_etale`.
No import was added: the required comparison is already publicly available through
`SmoothDuality.SmoothBaseChange` and `SmoothDuality.Etale`. A declaration-local
`linter.unusedSectionVars` setting preserves the existing `HasTateTwist` assumption
without an unused-section-variable warning; dropping that assumption would change
the existing public signature.

The existing theorem `isIso_compactificationEtaleComparison`
(node `lem-sf-etale-graph-comparison-isomorphism`) makes exact etale sum extension
isomorphic to compact support for the chosen compactification. The existing
`compactificationEtaleAdjunction` therefore has the same left adjoint as
`rightDerivedUpperShriekAdjunction`. `Adjunction.rightAdjointUniq` identifies their
right adjoints. Evaluate at the monoidal unit and compose with
`leftDerivedUpperStarUnitIso` to obtain the required trivial dualizing complex.
This is the etale normalization of the current blueprint locality proof, Step 1,
and the existing DAG locality proof, Step 2; it does not alter the unit route.

All existing signatures, attributes, public imports and other proofs are preserved.
The argument applies to arbitrary schemes and finite commutative coefficients;
the original theorem retains its existing Tate-twist assumption. It needs no
invertible-exponent or quasi-compactness assumption. In particular it
includes empty schemes, identity morphisms and coefficients of noninvertible characteristic.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.nonempty_dualizingComplex_iso_constantComplex_of_etale`.
Added 0 holes; split off 0 statements. There are 0 remaining textual `sorry`s in
the delivered module. The existing downstream theorem
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_of_etale`
now uses this proof in its existing tensor-formula argument.

The dependency theorem `isIso_compactificationEtaleComparison` is already proved.
This delivery does not claim that all transitive dependencies are free of sorry.

## No longer needed

None. No imports, declarations, nodes or modules are withdrawn. The proof uses the
already proved graph-comparison theorem directly, so no additional normalization,
tensor-compatibility or pro-etale transport statement is introduced for this hole.
Existing public imports remain verbatim as required by the source-library boundary.

## Where the brief, the DAG or earlier work was wrong

No node currently has this assigned module in its `lean.module` field. Its docstring
points to `lem-pur-co-smooth-etale-locality`, whose Lean attachment is the broader
pro-etale statement in `Sheaf.Paper.CohomologicalSmoothEtaleLocality`.
That node is not reassigned or rewritten: the present proof fills the ordinary
etale normalization subcase of its existing Step 2 using an existing declared
and proved dependency. No mathematical statement or definition repair was needed.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
