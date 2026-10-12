## What changed

Replaced the sorry in `CategoryTheory.Functor.exists_hypercohomology_firstPage` by a
complete Lean reduction. Its signature, all hypotheses, the signed first-page differential,
and the pinned augmentation/comparison clauses are unchanged.

Added three proof imports and three separate modules:

- `Sheaf.CategoryTheory.CartanEilenbergSecondFiltration` states the second-filtration
  spectral data and finite image filtration on total cohomology, with transport along any
  supplied family of isomorphisms. It does not identify the total with a derived complex.
- `Sheaf.CategoryTheory.CartanEilenbergTotalResolution` states that the specified augmentation
  is a quasi-isomorphism and that the original injective total is K-injective. It makes no
  claim about a spectral sequence or about applying F.
- `Sheaf.CategoryTheory.CartanEilenbergMappedTotal` PROVES the finite-diagonal comparison of
  complexes, with its equation on the summand inclusions. Its proof constructs the finite
  interval of contributing indices and uses the proved source-library declarations
  `CoreHasTotal.preserves`, `mapTotalIso` and `mapExtendFunctorNatIso`.

The main proof packages the augmented total as an actual `KInjectiveResolutionChoice`,
uses clause (1) of the existing `kInjective_computes`, assembles the inverse homotopies into
`HomotopyEquiv`, applies F to this equivalence, and composes its homology isomorphism with
that of the finite-diagonal comparison. It defines w as the corresponding composite chain
map and proves both its diagonal formula and `(c n).hom = homologyMap w n`. Finally it
instantiates the total-cohomology filtration transport at this c. Thus the reduction
contains real comparison-map and cohomology calculations, rather than renaming the target.

The complete Cartan--Eilenberg hypotheses `hinjective` and `hquasi` are retained in the API,
but the first spectral sequence only needs the term resolutions. A declaration-local
unused-variable linter setting permits retaining those original binder names unchanged.
No definition or existing statement is changed; no change record is required.

## Proved and sorry left

The item's original one sorry is closed by the reduction:
`CategoryTheory.Functor.exists_hypercohomology_firstPage` (node `thm-sp-if-e1`).
The additional finite-diagonal theorem
`CategoryTheory.Functor.cartanEilenberg_mapped_total_iso`
(node `lem-sp-cartan-eilenberg-mapped-total`) is proved without sorry.

Exactly two new sorries remain, each the entire proof of its named public theorem:

- `CategoryTheory.Functor.cartanEilenberg_second_filtration`
  (`lem-sp-cartan-eilenberg-second-filtration`).
- `CategoryTheory.Functor.cartanEilenberg_total_resolution`
  (`lem-sp-cartan-eilenberg-total-resolution`).

Each has its own module, node, source and complete proof in words. The existing imported
`CategoryTheory.Functor.kInjective_computes` now has a proof in the repository; this delivery
does not alter or reprove it. The main theorem therefore remains dependent on open theorems,
although it no longer contains a direct sorry.

All four modules compile locally in import order. The delivery dry run performs the
server checks and axiom probes. Mathematical edge checks: the zero bicomplex and zero
functor yield zero comparisons; arbitrary negative b is permitted; when n<b the interval
[b,n] is empty and every diagonal term is zero; resolution degree m=0 uses the prescribed
augmentation; the sign ratio at s+1 is valid for negative as well as positive s. The
spectral helper has no horizontal cycles/boundaries injectivity assumptions: these are
needed for the other hypercohomology spectral sequence, not this row-cohomology sequence.

## No longer needed

Removed the three original ordinary proof imports:
`Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`,
`Sheaf.CategoryTheory.ExactCoupleConvergence`, and
`Sheaf.CategoryTheory.KInjectiveBridge`.
The last module's definitions are STILL used and supplied by the retained public
`KInjectiveComputes` import; it is not mathematically pruned. All original public imports
are retained to preserve the exposed interface.

The main proof no longer uses `thm-sp-spectral-object-yields` or `def-sp-convergence`.
The new spectral and resolution nodes use the degreewise cycle/boundary stabilization
argument and the page-zero filtered-complex construction instead, so
`Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence` and its exact-couple
convergence machinery are unnecessary along THIS route. This is a claim about the route
from `thm-sp-if-e1`, not about other callers in the project. No unit statement or realized
unit proof step was bypassed: the unit's realized lists are empty for this auxiliary node.

The following old direct proof dependencies are no longer direct dependencies of the
main node: `def-sp-injective-resolutions`, `def-sp-left-exact-additive`,
`thm-sp-spectral-object-yields`, and `def-sp-convergence`. The first two remain needed
by the new intermediate statements and are not pruned from the mathematical closure.
`lem-sp-kinjective-computes` and `def-sp-kinjective-bridge` remain directly used.
No other old dependency is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The plan says to apply `boundedFilteredComplex_spectralSequence` to this filtration.
Its actual signature requires `DecreasingFiltration.IsFinite` as a filtration of the
ENTIRE cochain complex: one step is top and another bottom as subcomplexes. Here the
upper bound is n+1 in degree n and is not uniformly bounded when the complex is unbounded
above. The source result needed is degreewise finite convergence, as in
[Stacks 0132](https://stacks.math.columbia.edu/tag/0132), not that global hypothesis.
The new spectral node records the precise needed argument without modifying the existing
bounded-filtration theorem or any target statement.

The direct declarations of the old dependencies also do not assemble the degree-zero
augmentation or the finite-sum F comparison for these particular extension and flip
conventions. The new total-resolution node isolates the first gap; the mapped-total module
fully closes the second using existing source-library infrastructure.

LeanSearch returned HTTP Internal Server Error for every new-node query; these searches
are recorded as unavailable, not as evidence of absence. Loogle/LeanFinder and Mathlib
source searches ran and are recorded in searches.jsonl. Blueprint searches for second
filtration, total injective, additive total, augmentation and finite diagonal found no
existing blueprint statement with the precise new conclusions. The existing generic
first-quadrant double-complex node assumes first-quadrant support and does not give the
arbitrary integer lower bound and pinned comparisons required here.

## New nodes

`lem-sp-cartan-eilenberg-second-filtration`, in
`dag/nodes/sec-abelian-varieties/lem-sp-cartan-eilenberg-second-filtration.json`, realizes
paragraph 1 of `thm-sp-if-e1`. Its theorem retains all spectral data but only concerns
ordinary total cohomology and transport along a given isomorphism. Sources: Stacks 0130,
0132, and the cycle/boundary formulas in 012K. It is strictly a part of the original result.

`lem-sp-cartan-eilenberg-total-resolution`, in
`dag/nodes/sec-abelian-varieties/lem-sp-cartan-eilenberg-total-resolution.json`, realizes
the augmentation and K-injective-total part of paragraph 2. Its proof follows the
augmented-row argument of [Stacks 0133](https://stacks.math.columbia.edu/tag/0133), then
bounded-below injectivity. It has no F, spectral sequence, or derived abutment in its
conclusion.

`lem-sp-cartan-eilenberg-mapped-total`, in
`dag/nodes/sec-abelian-varieties/lem-sp-cartan-eilenberg-mapped-total.json`, realizes the
finite-diagonal additivity sentence of paragraph 2. This node is already proved by the
new module; it leaves no additional work item. The proof source and module mapping are
recorded in its node.

## Second reading by S2

1. Compared the delivered main module against the repository with `diff -u` and read
   the complete original statement. The existing declaration signature is byte-for-byte
   unchanged, including both Cartan--Eilenberg hypotheses and all pinned comparison
   clauses. The only main-module changes are its proof, ordinary proof imports and a
   local unused-variable linter setting. No existing definition or public import changed;
   no change record is required. Verdict: passes.
2. Compiled all four modules locally in import order without errors or warnings. Searched
   all delivered Lean files for forbidden declarations and proof shortcuts: none occur.
   Exactly the two reported public intermediate theorems have `:= by sorry`; there is
   no sorry in a definition. A scratch module printing axioms shows only `propext`,
   `Classical.choice`, `Quot.sound` for `cartanEilenberg_mapped_total_iso` and the current
   `kInjective_computes`; the main theorem and the two open helpers additionally use
   `sorryAx`. The main theorem is a checked reduction, not yet an axiom-free closed target.
   Verdict: passes as a partial stage-3 delivery.
3. Read both open statements, their docstring proofs and their nodes. The spectral helper
   concerns ordinary total cohomology and its transported image filtration; the resolution
   helper concerns only the augmentation, its quasi-isomorphism and K-injectivity. Neither
   merely renames the original theorem. Checked zero rows, the zero functor, negative lower
   bounds and n<b (empty diagonal), resolution degree zero, and the sign ratio for negative
   complex degrees. A row quasi-isomorphism from the single object in degree zero gives
   precisely the augmented exact row needed by the cone argument. Independently verified
   Stacks Tags 0130, 0132, 0133 and 015J. Repeated LeanFinder, Loogle and Mathlib grep searches
   with different queries, recorded in searches.jsonl, and searched Sheaf and the upstream
   homology sources. `isKInjective_of_injective` supplies the bounded-below injective step;
   source-library total quasi-isomorphism results found in BicomplexColumns impose upper
   support bounds and do not directly give this bounded-below pinned augmentation. No
   existing declaration supplies either full helper. Closing either is substantial work,
   so neither was replaced by a speculative proof. Verdict: passes.
4. Read the reduction from the main theorem downward: it uses the proved finite-diagonal
   comparison, constructs an actual resolution choice and mapped homotopy equivalence,
   proves the diagonal equation and homology-map equation, and transports the filtration.
   Each ordinary proof import supplies a used declaration; the new helpers' public imports
   supply their signatures or required instances. Confirmed the old proof-dependency list
   against `## No longer needed`: all four removed direct dependencies are named, and the
   two definition dependencies still used downstream are distinguished from pruning.
   Read `dag/units/sk-prop-av-pqf-finite.json`: its realized statement and step lists are
   empty, so this auxiliary reduction bypasses no realized unit step. Verdict: passes.
5. Compared the existing node JSON with the repository: only `proof`, `proof_deps` and
   `proof_origin` changed. Their steps match the Lean reduction and their `uses` union is
   exactly `proof_deps`. Checked the three new nodes' statements, declaration mappings,
   source, proof, search records, blueprint provenance, creation records, chapter and unit.
   The mapped-total node records a proved finite-index comparison; the two other nodes
   match precisely the two open declarations. Verdict: passes.

Second reading changed only documentation: corrected the spectral helper's source from
Tag 012U to 0132; added the precise augmentation source 0133 to the resolution helper;
removed an unnecessary shift from the augmented-row cone description in its docstring
and node; corrected the stale report claim that `kInjective_computes` is still open.
The Lean statements and proof terms were not changed.
