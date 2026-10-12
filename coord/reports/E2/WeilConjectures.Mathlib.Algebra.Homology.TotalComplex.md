## What changed

Replaced the `sorry` in `HomologicalComplex₂.exists_spectralSequence` by a complete Lean
reduction to the vertical truncation spectral object and its one-layer cohomology calculation.
The proof composes the existing spectral-object page-two isomorphism with two interval
isomorphisms, then transports the existing, proved spectral-object abutment to total cohomology.
The declaration's signature and all existing definitions are unchanged.

Added `Sheaf.Algebra.Homology.DoubleComplexVerticalWindow`, which composes Mathlib's
extension, smart truncation and restriction functors, with proved zero-morphism preservation
instances. Added two statement modules for the independent construction and calculation steps.
Updated the main node's proof route and recorded the existing general abutment theorem as a node.
All four delivered Lean modules compile locally without warnings. The universal total-existence
instance is supplied by the original proved `hasTotal_up_nat`; no definition uses `sorry`.

## Proved and sorry left

Closed hole: `HomologicalComplex₂.exists_spectralSequence` (one original hole), by reduction
to named intermediate theorems. Added holes: `HomologicalComplex₂.exists_verticalSpectralObject`
and `HomologicalComplex₂.verticalWindow_total_homology_iso` (two holes). This is a decomposition,
not an unconditional proof of the original theorem: its axiom closure still contains `sorryAx`.
The changed declarations alone have net -1 holes closed; import-closure progress must include
pruning and be measured by the maintainer's pinned sorry ledger. The underlying universal finite-diagonal instance remains the original proved instance.
Zero-morphism preservation for both smart truncation functors and their interval composition is
proved in the new definition module.

There are exactly two remaining `sorry` declarations in the delivery:

- `HomologicalComplex₂.exists_verticalSpectralObject`, node
  `lem-sp-double-complex-vertical-spectral-object`, in
  `Sheaf.Algebra.Homology.DoubleComplexVerticalSpectralObject`.
- `HomologicalComplex₂.verticalWindow_total_homology_iso`, node
  `lem-sp-double-complex-vertical-window-homology`, in
  `Sheaf.Algebra.Homology.DoubleComplexVerticalWindowHomology`.

The construction lemma asserts the cohomology of **every finite vertical truncation interval**
and of the whole interval, with the spectral-object exactness and support axioms. It contains no
spectral-sequence page calculation or abutment. The calculation lemma asserts only cohomology of
one concrete truncated total complex, and contains no spectral object or spectral sequence.
Neither is the original statement renamed or supplied as a hypothesis.

Checked the construction at empty intervals (`a=b`), intervals ending at zero or below, and
intervals with negative starting degree: extension by zero gives the expected support. Checked
the layer calculation at `p=0` and `q=0`, including the vanishing predecessor at degree zero.
The existing general abutment and first-page comparison are already proved in the source library.

## No longer needed

Removed the two proof-only imports:

- `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`, node
  `thm-sp-spectral-object-yields`.
- `Sheaf.CategoryTheory.DoubleComplexTotal`, node `def-sp-double-complex-total`.

These modules and their proof subtrees are no longer dependencies of this proof. Their separate
uses elsewhere are unaffected. The main node retains its original statement dependencies.
No existing public import was removed. The second reader also removed the redundant
`Mathlib.Algebra.Homology.HomologicalComplexAbelian` public import from the new vertical-window
module: it is already publicly imported through `Embedding.CochainComplex` ->
`Embedding.AreComplementary` -> `Embedding.TruncLEHomology`. No extra proof import remains unused.

## Where the brief, the DAG or earlier work was wrong

The existing node describes both double-complex sequences, while the existing Lean declaration
formalizes only the first sequence. This predates the delivery; neither statement was changed.
The owning unit has no realized statement or proof-step nodes, so the changed route bypasses no
realized unit step.

The imported bounded-filtered-complex theorem assumes a globally finite filtration, while
the column filtration of a general first-quadrant double complex is only finite degree by degree.
Consequently that declaration cannot simply be applied to this double complex. Its final support
condition also restricts graded cohomology to two consecutive degrees, whereas a column can have
cohomology in arbitrarily many degrees. The delivery uses the already proved general spectral-object
abutment instead and does not alter that imported theorem.

LeanSearch returned an internal server error for the searches. These attempts are recorded as
unavailable without claiming an absence verdict; Loogle, LeanFinder and source grep were also used.

## New nodes

`def-sp-double-complex-vertical-window` records the concrete composition of existing Mathlib
functors. Its data and supporting instances are fully defined and proved.

`lem-sp-double-complex-vertical-spectral-object` records construction of the vertical smart
truncation spectral object, its first-quadrant vanishing and interval cohomology comparisons.
This is the construction portion of the argument, left for a later worker.

`lem-sp-double-complex-vertical-window-homology` records the independent single-layer total
cohomology computation, with its naturality and degree-zero cases described in the proof.

`lem-sp-first-quadrant-spectral-object-abutment` attaches the already proved existing declaration
`CategoryTheory.Abelian.SpectralObject.abutsTo_E₂SpectralSequenceNat`. No new Lean declaration
or module is introduced for this existing theorem. Its proof is the existing finite image filtration
and stabilized-page calculation, read in the source module.


## Second reading by E2

1. PASS. Compared the delivered TotalComplex module against the repository with `diff -u`.
   The complete signature and docstring of `HomologicalComplex₂.exists_spectralSequence`,
   the existing `hasTotal_up_nat` instance, variables, and all public imports are unchanged.
   Only proof imports and the theorem body change. The other three Lean modules are new;
   no existing definition or target statement changes and no change record is required.
2. PASS with two reported open lemmas. Compiled all four modules in import order using
   `lcompile.py`, without errors or unexpected warnings. In a scratch copy, printed axioms
   for the original instance and theorem, the window definition and its three preservation
   instances, both new lemmas, and the existing abutment theorem. Only `propext`,
   `Classical.choice`, `Quot.sound`, and (for the original theorem and two open lemmas)
   `sorryAx` occur. The only direct sorries are the complete proofs of the two reported,
   public, named theorems. There is no hollow definition or arbitrary witness selected
   from an unproved existence theorem to define data.
3. PASS as a decomposition. Read both statements, docstring proofs and nodes. The first
   constructs interval cohomology and its exact spectral-object structure; the second
   computes only one concrete layer's total cohomology. Neither restates spectral-sequence
   existence, page computation and convergence together. Checked `a=b`, `b<=0`, `a<0`,
   and a complex supported at one vertical degree: truncation is respectively zero, zero,
   unchanged below degree zero, and supported exactly when that degree lies in `[a,b)`.
   For the layer computation, the kernel of the induced differential on opcycles is
   vertical homology. At `q=0` its incoming boundary is zero; at `p=0` the preceding
   horizontal summand is zero. The horizontal total sign is +1, matching Mathlib's
   TensorSigns convention. The bounded-below diagonal chase in the construction decreases
   the vertical degree, so it terminates. These checks reveal no false boundary case.
   Independent LeanFinder search for hypercohomology of a canonical bicomplex truncation
   tower found truncation APIs, not the construction. Loogle search combining
   `homologyFunctor` and `singleFunctor` found no direct match; source grep with
   `truncLE.*truncGE`, `truncGE.*truncLE`, and single-functor homology terms found the
   constituent APIs. Read the upstream derived-category single-layer isomorphism and
   the Sheaf truncation-hypercohomology theorem: neither supplies this totalization
   comparison, and the latter imposes Grothendieck-category hypotheses absent here.
   No duplicate statement was found. Neither remaining lemma has a minutes-long proof.
4. PASS after import cleanup. The original theorem composes the existing page-two
   isomorphism, the interval comparison, and the layer comparison; the existing proved
   first-quadrant abutment is transported by the whole-interval isomorphisms. Verified
   every old proof dependency removed is reported: `thm-sp-spectral-object-yields` and
   `def-sp-double-complex-total`, with their two imports. The replacement hypotheses do
   not impose a global finite filtration. The owning unit's `realized.statement` and
   sole `realized.steps` entry are both empty, so no realized unit route is bypassed.
   The separate mismatch between the DAG's two-sequence statement and the pre-existing
   Lean first-sequence statement is reported, not silently changed.
5. PASS. Compared the existing node: only `proof`, `proof_deps`, and `proof_origin` change.
   Its three dependencies are exactly the construction, layer calculation, and existing
   abutment used by Lean. Read all four new nodes and checked their source, creation,
   blueprint, chapter/unit, search records, Lean declaration/signature and proof fields.
   The abutment node attaches the existing theorem rather than introducing a duplicate.
   Each new holed theorem has its matching node and complete mathematical docstring.

Changes by the second reader: removed one redundant public Mathlib import from the new
vertical-window module; corrected the progress accounting to distinguish one closed original
hole from two added holes and explicitly call the delivery a decomposition; added this review.
No Lean statement, definition, proof body, or DAG route needed repair.
