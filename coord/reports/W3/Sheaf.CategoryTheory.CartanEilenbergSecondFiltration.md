## What changed

Reduced CategoryTheory.Functor.cartanEilenberg_second_filtration without changing its
signature. The combining proof establishes support by Mathlib zero-preservation and
extension-by-zero, obtains the degreewise bounded second subcomplex filtration,
identifies the row pages, then composes the stationary quotient comparisons with
page quotient comparisons after normalizing the total-degree index.

Added four modules and their nodes. CartanEilenbergRowPages has a complete combining proof: the given
rows are bundled as actual InjectiveResolution structures (no witness chosen from
an existence theorem), their cohomology comparisons use Mathlib, and the sign
correction by (r*s).negOnePow is calculated in Lean. Three smaller arguments remain
as named theorems. All original public imports are retained; the three new proof-only
imports replace three redundant direct imports.

## Proved and sorry left

Closed the item's one hole:
CategoryTheory.Functor.cartanEilenberg_second_filtration
(node lem-sp-cartan-eilenberg-second-filtration).
Also supplied a complete combining proof of the new theorem CategoryTheory.Functor.cartanEilenberg_row_pages
(node lem-sp-cartan-eilenberg-row-pages).

Added three holes, each exactly `:= by sorry` in its own module:
- HomologicalComplex₂.boundedBelow_secondFiltration
  (lem-sp-bounded-below-second-filtration): support-dependent subcomplex construction.
- CategoryTheory.Functor.secondFiltration_row_cohomology
  (lem-sp-second-filtration-row-cohomology): page computation with the raw totalization sign,
  with no augmentation, injectivity, derived-functor comparison or convergence.
- CategoryTheory.degreewiseFiltered_stable_quotient
  (lem-sp-degreewise-filtered-stable-quotient): stable cycle quotients for any degreewise
  finite filtered complex, with no spectral sequence or double complex in its statement.

This is a decomposition, not a sorry-free proof: one original hole closed, three lower
holes added (net -2). There are no holes in definitions, private helpers or the
combining proofs. The axioms still include sorryAx through these three dependencies.

## No longer needed

Removed direct proof imports Sheaf.Algebra.Homology.FilteredComplexSubquotients,
Sheaf.CategoryTheory.DoubleComplexTotal, and Sheaf.CategoryTheory.Filtration from the item.
Their declarations remain needed transitively and through the unchanged public imports;
no existing node or module is globally pruned. No unit route is bypassed: the unit's
realized lists for this mathematical argument are empty and the original four-step
filtration, row-comparison, stabilization and transport argument is retained.
The old direct proof dependencies replaced by the lower nodes are
`def-sp-double-complex-total`, `def-sp-filtered-complex-subquotients`,
`def-sp-filtration`, `def-sp-injective-resolutions`, `def-sp-left-exact-additive`,
and `lem-sp-filtered-complex-associated-spectral-sequence-construction`.
They remain used in the lower arguments or statement interfaces; only
`def-sp-cartan-eilenberg-presentation` remains a direct dependency of the combining proof.
The overbroad new import `Mathlib.Algebra.Homology.HomologySequence` was replaced from
DegreewiseFilteredStableQuotient by `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`,
which supplies exactly the homology and homologyMap declarations its signature needs.
The global bounded-filtration module BoundedFilteredComplexSpectralSequence was examined
but never imported: it demands a single finite filtration bound for the whole complex.

## Where the brief, the DAG or earlier work was wrong

The existing filteredComplex_associated_spectralSequence statement gives page-zero
and abstract page-term isomorphisms but no connecting-map characterization of d₁.
It cannot alone imply the row differential identification: arbitrary isomorphisms
with the cycle quotient do not constrain d₁. The new raw row theorem isolates that
missing computation instead of asserting it follows from the weaker interface.
DoubleComplexTotal's subcomplex and top-bound statements assume first-quadrant
support in both directions; the item allows arbitrary integer lower bound b in
complex degree. The new support lemma handles that case, including negative b.
The repository copy contains no blueprint literature files at the cited path;
Stacks Tags 012Z, 0130, 0132 and 012Q were read from their official pages.
LeanSearch returned an internal server error; the other searches ran and found no match.

Edge cases checked mathematically: for n<b all diagonal summands are zero, so top
and bottom agree and both bounds in the support lemma hold; for p>n its sum is empty;
for negative complex degrees s the integer unit exponent r*s still gives the
consecutive sign ratio; in characteristic two the sign automorphisms are identities.
For the zero complex the stationary quotient is zero and the image filtration is
finite; for a one-step filtration it gives its single homology graded piece.
For varying degreewise bounds, convergence uses only degrees n-1,n,n+1, never a
uniform upper bound. Each lower statement is strictly a part of the original argument.

## New nodes

lem-sp-bounded-below-second-filtration: subcomplex construction for a half-plane-supported
bicomplex, with its degreewise bounds; BoundedBelowSecondFiltration.lean.

lem-sp-second-filtration-row-cohomology: raw signed row page calculation, without
injective resolutions or convergence; SecondFiltrationRowCohomology.lean.

lem-sp-cartan-eilenberg-row-pages: proved injective-resolution comparison and explicit
sign cancellation; CartanEilenbergRowPages.lean.

lem-sp-degreewise-filtered-stable-quotient: stationary subquotients and transport to
any isomorphic cohomology family; DegreewiseFilteredStableQuotient.lean.

The stable-quotient source additionally includes Stacks Tag 012W, the exact degreewise
finite convergence lemma.

All inherit the item's chapter/unit and cite thm-sp-if-e1 proof paragraph 1. Node
proofs include the complete arguments also carried in their declaration docstrings.
No change record is needed: no existing statement or definition was changed.


## Second reading by W3

1. PASS. Compared the item's complete diff with the repository version and checked
   the original theorem signature byte for byte. Only its proof and proof imports
   changed. The other four modules are new; no existing definition or statement was
   changed, so no change record is required.
2. PASS, as a decomposition. All five modules compile through lcompile.py in import
   order. Explicit axiom prints show only propext, Classical.choice, Quot.sound and
   sorryAx. There are exactly the three reported whole named-theorem holes and no
   definitions, unsafe declarations or new axioms in the delivered modules.
   The row resolutions use the given data directly; existence witnesses are only
   eliminated inside theorem proofs. Neither combining theorem is sorry-free in its
   dependency closure.
3. PASS. Read all four new signatures, docstring arguments and nodes. The three
   lower holes are strictly parts of the original argument: half-plane subcomplex
   construction, signed row pages without augmentation/injectivity/convergence, and
   stationary quotients without double complexes or spectral sequences. Checked zero
   complexes, one-step filtrations, n<b (including negative b), p>n, r=0 and negative
   s. Mathlib's total signs are epsilon1=1 and epsilon2=(-1)^r after the flip; the
   sign cancellation works also in characteristic two. Stabilization needs only
   bounds in n-1,n,n+1. Independent LeanFinder, Loogle and grep searches used
   'finite filtration cohomology stationary quotients', 'HomologicalComplex₂.total'
   and 'homology.*filtration|filtration.*homology'; they found no exact replacement.
   Read the existing filtered spectral sequence and bounded canonical-page interfaces:
   the former does not specify d1, and the latter requires global finite filtration.
   The degreewise result is supported directly by
   [Stacks 012W](https://stacks.math.columbia.edu/tag/012W), with quotient formulas in
   [012Q](https://stacks.math.columbia.edu/tag/012Q); the row sign is
   [0130](https://stacks.math.columbia.edu/tag/0130).
4. PASS after repair. The proof constructs support first, bundles actual injective
   rows, calculates the sign and uses Mathlib derived-functor naturality. The three
   unresolved constructions are substantial and cannot be closed by the searched
   interfaces in a few minutes. Replaced the overbroad HomologySequence public import with ShortComplex.HomologicalComplex.
   Expanded No longer needed to enumerate every replaced old direct proof dependency;
   none is globally pruned. The unit realized lists are empty and its route is kept.
5. PASS after repair. Checked node declaration names, recorded signatures, chapter,
   unit, source, creation, blueprint and search fields; proof_deps equal the union of
   proof-step uses. Rewrote the row-pages node's proof description to match the actual
   reduction to the raw row theorem and Mathlib naturality, rather than describing
   the construction performed in its dependency. Added the precise 012W source to
   the stable-quotient node/docstring.

Second-reading changes: narrowed one import; corrected the stable-quotient
source citation; aligned the row-pages DAG proof with the code; completed the
replaced-dependency list and clarified that row-pages has a complete combining proof
with sorryAx dependencies. No hole or signature changed during the second reading.
