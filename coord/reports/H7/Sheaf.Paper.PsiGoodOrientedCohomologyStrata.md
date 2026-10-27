## What changed

Proved `PsiGoodStrata.restrictSite_properties` and
`PsiGoodStrata.vanishing_finiteLimits` in
`Sheaf.Paper.PsiGoodOrientedCohomologyStrata`. Limits are constructed componentwise
in products and comma categories. Continuity is proved from the three generating
cover types, using finite-limit preservation to commute image sieves with pullback.
All existing public declarations, definitions, signatures and public imports are preserved.

Implemented steps 1–4 of the cohomology-strata proof. Private proved helpers compare
`orgogozoModuleSections` with the fixed-ring sheaf and its AsSmall transport, prove
bounded constructibility of the degree-zero input, transport constructibility across
isomorphisms, and combine proper-surjective constructibility, Psi-good base change,
exact pullback commuting with homology, and proper-surjective descent.

The main theorem applies these helpers, extracts the existing strata, converts their
records using the supplied constructibility proofs, and applies the separate transport
lemma to each pair. Its inverse-image presentation hypothesis is discharged by Mathlib's
`Functor.sheafPullbackConstruction.sheafPullbackIso` for `restrictSite`.

Proof imports added: Mathlib comma limits, the source constructible-module predicate
comparison and zero-sheaf constructibility, and the new canonical-strata module.
No adopted source-library file is changed. No definition or existing theorem statement
is changed, so there is no change record or forced consumer adaptation.

## Proved and sorry left

Original holes: 3.

- Closed with complete proofs, without new holes for their arguments:
  `AlgebraicGeometry.OrientedNearbyCycles.PsiGoodStrata.restrictSite_properties` and
  `AlgebraicGeometry.OrientedNearbyCycles.PsiGoodStrata.vanishing_finiteLimits`.
- Reduced with a complete combining proof:
  `AlgebraicGeometry.OrientedNearbyCycles.PsiGoodStrata.exists_constructible_cohomology_strata`.
  The bounded-constructible input and the entire proper-surjective descent argument
  are proved in this module. The original theorem has no remaining `sorry`.
- Added one hole:
  `AlgebraicGeometry.OrientedConstructibleSheaf.canonical_stratum_trivializations`, node
  `lem-trf-constructible-vanishing-canonical-strata`, in
  `Sheaf.Paper.ConstructibleVanishingCanonicalStrata`.

Actual packet hole count: 1, all in that named public theorem. Item module hole count: 0.
Thus two holes are proved and the third is decomposed with one strictly simpler
presentation-comparison hole; the net hole reduction is two. No existing dependency
hole is claimed as proved. All private helpers are proved; no definition contains a hole.

The new lemma is independent of nearby cycles, Psi-goodness, proper surjections,
Noetherian hypotheses and finite presentation. It concerns one normalized stratum restriction assumed finite type locally constant,
and the canonical set inverse-image presentation; it does not assert the existence
of stratifications. Its remaining work is to identify
the algebraic module lift with the normalized sheafified Kan extension and to carry
slice constants through scalar restriction. This is a genuine part of step 5,
not the cohomology theorem renamed or a repackaging of its hypotheses.

Edge cases were checked mathematically before stating it: empty strata and the zero
coefficient ring require no chosen points; a terminal object still exists on the triple
site. Finite type over the finite coefficient ring gives finite underlying models.

## No longer needed

Removed the direct private import
`WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`: the transported
bounded-constructibility interface is already supplied by the proper-surjective input.
That source module remains a dependency through `BoundedConstructibleTransport`;
no upstream declaration or dependency is withdrawn.

No original mathematical proof dependency or module is pruned. The original five-step
route is retained. A trial `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic` import
was unnecessary and is absent from the packet. No scratch Lean module is delivered.

## Where the brief, the DAG or earlier work was wrong

The original step 5 was described as unfolding constructibility. It requires a real
presentation comparison: `IsConstructibleVanishing` precomposes by identity-base-change
normalization and sheafifies, `stratumRestriction` uses a sheafified left Kan extension,
and the conclusion uses the constant-module algebraic lift of the canonical geometric
inverse image. These are canonically isomorphic, but not definitionally the same.
The new lemma records precisely this missing comparison and its proof in words.

The degree-zero bounded-constructibility step also requires explicit scalar and AsSmall
comparisons to match the recorded `orgogozoModuleSections` interface; those comparisons
are proved here. The normalized predicate uses `Scheme.FiniteLocallyClosedStratification`, while the
item concludes with `Scheme.Stratification`, whose topological record additionally
requires constructibility. A private explicit conversion inserts the constructibility
proofs already provided by the predicate; all strata, domains and immersions are retained.
No statement is disputed and the unit route is preserved.

Lean initially overflowed while unfolding initial-object scalar restriction inside a
large transported-site expression. Abstracting the initial object and the small site
made the comparison compile; no compile limit was raised and no definition was changed.

## New nodes

`lem-trf-constructible-vanishing-canonical-strata` states the general final transport
step, in `Sheaf.Paper.ConstructibleVanishingCanonicalStrata`. Its module has one public
theorem, with a complete proof in words and one `sorry`. The node carries the exact
Lean statement, dependency list, three Mathlib search records, source references and
blueprint ancestry. Searches found no existing theorem identifying these presentations.
Sources checked online: Lu–Zheng, the constructibility definition following Theorem 4.27
(PDF index 37, printed p. 38), and Stacks Tags 03CY and 03D2. The detailed comparison
argument is marked agent-origin; it is not claimed to be a numbered lemma of the paper.

The parent node's proof and dependencies now record this comparison and the actual
source constructible-module predicate comparison used in degree zero.

Validation: `lcompile.py --all` passed for both modules, with no errors or warnings.
The compile server reported 39.8 s for the new module and 69.6 s for the item; it
returned success.
The main theorem signature was compared with its recorded node statement and matches.
All Lean lines are at most 100 characters; the packet has zero item holes and one
new named theorem hole. The delivery tool additionally checks statements, imports,
consumers and the DAG.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
