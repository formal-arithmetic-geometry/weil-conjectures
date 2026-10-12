## What changed

Replaced the sorry in `CategoryTheory.boundedFilteredComplex_canonicalPages` with
an assembly proof. The canonical construction, pinned comparisons, naturality,
finite abutment and finite stationary bounds are split into
`Sheaf.CategoryTheory.BoundedFilteredComplexPageCore`.
The first-quadrant conclusion is proved directly from Mathlib: negative filtration
indices give a cokernel of an identity; negative second indices use graded support;
homology propagates zero terms to all pages. Outside the indicated quadrant bound,
the adjacent maps vanish and zero-map short-complex homology identifies consecutive
pages. Induction composes these isomorphisms to every later page.
The original declaration signature and public imports are unchanged.

## Proved and sorry left

Closed the local hole in `CategoryTheory.boundedFilteredComplex_canonicalPages`
(the sole original sorry), node `thm-sp-spectral-object-yields-canonical-pages`; its proof contains no sorry.
All four private helpers are proved: `page_zero_of_first`, `quadrant_differentials`,
`graded_zero`, and `quadrant_later_iso`.
One sorry remains in the delivery:
`CategoryTheory.boundedFilteredComplex_pageCore`, new node
`lem-sp-bounded-filtered-page-core`. It omits the entire first-quadrant conclusion;
it is a strict component, rather than the original assertion under another name.
Holes closed: 1; holes added: 1; net: 0. This is a decomposition, not a completed
proof of the original theorem; its axiom closure still contains `sorryAx`.

## No longer needed

Removed direct proof imports of
`Sheaf.Algebra.Homology.FilteredComplexZBDescription`,
`Sheaf.CategoryTheory.ExactCouple`, `Sheaf.CategoryTheory.ExactCoupleMorphism`,
and `Sheaf.CategoryTheory.SpectralSequencePageInduction` from the parent module.
The cycle/boundary and couple theory remain dependencies of the new construction
node; they are not claimed globally pruned.
`lem-sp-page-induction` and its module
`Sheaf.CategoryTheory.SpectralSequencePageInduction` are not needed on this route:
that theorem transports an existing page-2 isomorphism, whereas the construction
uses derived couples and the quadrant argument uses direct zero-object homology.
`lem-sp-long-exact-of-triangle` is not needed on this route: Mathlib's
`HomologySequence` supplies the long exact sequences of short exact complexes,
without passing through a triangulated category. This is pruning for this item,
not a claim that other targets no longer reach either node.

## Where the brief, the DAG or earlier work was wrong

The old plan cites page-isomorphism induction as if it constructed pages; its actual
signature compares already supplied spectral sequences. The new construction node
uses the derived-couple construction instead. No statement was changed.
A scope check confirmed that Lean includes BOTH the support conclusion and the
quadrant-specific bound under the two support hypotheses. Thus there is no
statement dispute. The zero complex, filtration shifted to negative indices, and
r=t cases were checked: the first is trivial, the second is excluded only from
the quadrant assertion by its explicit hypotheses, and r=t uses page equality.
No unit statement or realized step was bypassed; the unit's realized lists are empty.
Searches: LeanSearch was unavailable (Internal Server Error); LeanFinder returned only generic zero-differential results; Loogle did not
recognize the spectral-sequence abbreviation; grep and local signature inspection
found Mathlib zero-object homology and zero-map homology data, which the proof uses.

## New nodes

`lem-sp-bounded-filtered-page-core` states only the canonical functor, pinned page
comparisons, representative equations, finite convergence and eventual stabilization.
Its source and complete representative/couple argument are in the docstring and node.
The original first-quadrant support and quantitative stabilization are omitted and
proved in the parent. No new definitions or changes to existing statements.


## Second reading by P2

1. Compared the parent module with the repository using `diff -u`, and compared
   the entire existing theorem signature as a string: byte-identical. Its existing
   docstring and five public imports are unchanged. No definition, hypothesis or
   conclusion changed; the only added public declaration is the new core theorem.
2. Compiled both modules in dependency order with `lcompile.py --all`: no errors
   or warnings. Scanned both sources: the only sorry is the named
   `CategoryTheory.boundedFilteredComplex_pageCore`; no forbidden declarations or
   hollow definitions. Scratch `#print axioms` checks show only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` for the two public theorems.
   Read each helper: zero middle terms have zero homology; equal filtration steps
   have an epimorphic inclusion and zero cokernel; the differential endpoints have
   the stated negative coordinates; zero-map homology and induction compare all
   later pages. The `r=t` induction base uses page equality, not a positive step.
3. Read the core's full signature, docstring and node. It keeps the construction,
   representative equations and finite abutment, but omits the two quadrant
   conclusions which the parent proves. This is a strict reduction with one hole
   replacing one, and no claim of net proof progress. Checked the zero complex,
   a one-step filtration concentrated at an arbitrary integer, `r=1`, and the
   stationary tail: a shifted filtration has no unconditional quadrant claim.
   At `r=1`, hφ fixes the transition to the identity by the epimorphic quotient
   projection. No extra coproduct assumption is needed for the exact-couple route.
   Read Stacks [Section 12.24](https://stacks.math.columbia.edu/tag/012K), including
   the representative formulas, Lemmas 12.24.2--4 and 12.24.11: these supply the
   construction, functoriality and finite-tail argument. The cited blueprint file
   is absent from this read-only clone; the named Stacks source is available.
   Fresh LeanFinder search for natural filtered pages and convergent cohomology
   found bounded-complex vanishing lemmas, not the core; Loogle did not know the
   project exact-couple identifier. `rg` on Sheaf and WeilConjectures found the
   pointwise Z/B theorem and associated spectral sequence, neither providing the
   core's natural functor and pinned exact-couple abutment. The upstream total
   complex theorem addresses double complexes, not this filtered-complex functor.
4. The direct Mathlib route proves the quadrant part without page-induction or
   triangle machinery. Checked the old proof_deps: exact-couple, Z/B, convergence
   and couple-morphism remain in the core's route, spectral sequence remains in
   the parent, and precisely long-exact-of-triangle and page-induction are unused
   on this route. Their item-level pruning is listed above. Read
   `dag/units/sk-prop-av-pqf-finite.json`: its statement and sole step have empty
   realized lists, which this delivery leaves unchanged. Signature imports are
   needed for quotient objects, exact-couple convergence, δ, spectral sequences
   and the full subcategory; new proof dependencies are plain imports.
5. Read both node records against the Lean: the parent's three steps match the
   core application, zero-support induction and zero-differential induction.
   The core's proof_deps are the union of its three steps; its statement and Lean
   record agree clause by clause, and its source, searches, created, blueprint,
   chapter, unit and new-module fields are present. Its representative step uses
   exactly the Z/B theorem's pinned representative comparison; the couple-morphism
   theorem supplies page naturality, not the finite convergence itself. Finiteness
   supplies the latter through the explicitly described stationary tails.

Changed in second reading: added plain imports of
`Sheaf.Algebra.Homology.FilteredComplexZBDescription` and
`Sheaf.CategoryTheory.ExactCoupleMorphism` to the core, making its stated proof
route available without re-exporting proof dependencies; inserted a blank line
between two helpers; corrected the report to explicitly count the delivery as
one-hole-for-one-hole decomposition. No mathematical proof or signature changed.
