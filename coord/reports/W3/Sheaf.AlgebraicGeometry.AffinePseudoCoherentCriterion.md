## What changed

Replaced the inherited two-directional-hole reduction with a proof of
`AlgebraicGeometry.isPseudoCoherent_affine_iff` that performs the finite-free
sheafification argument and the ring-level gluing in Lean. Its signature and
public imports are unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.AffinePseudoCoherentLocalizationCover`.

The reverse implication extracts the bounded-above finite-free representative,
transports its derived isomorphism through the existing affine equivalence, and
uses the whole affine scheme as each point's neighbourhood. The proved private
helper `tilde_finite_free_restrict_iso` uses a finite chosen basis,
`tildeFinsupp`, and preservation of finite coproducts under open restriction.
The upper bound is proved by preservation of zero objects, and the final model
isomorphism uses `mapDerivedCategoryFactors`. The chosen-basis argument also
works over the zero ring; it needs no added nontriviality hypothesis.

The forward implication obtains local module models on a finite principal-open
cover from the new lemma, then applies the second clause of the existing
`DerivedCategory.ringPseudoCoherent_localization_glue`. Standard localization
instances are constructed in the proof, rather than added to the criterion's
signature. The criterion node now records these actual steps.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.isPseudoCoherent_affine_iff` (node
`lem-pc-affine-pseudo-coherent-criterion`). Its module contains no `sorry`.
The private finite-free restriction helper is fully proved.

Added exactly one hole:
`AlgebraicGeometry.affine_pseudoCoherent_localization_cover`, in its own module,
node `lem-pc-affine-pseudo-coherent-localization-cover`. It isolates original
steps 2 and 3: finite-cover extraction and recovery of localized module models.
It does not assert either implication of the criterion or global ring
pseudo-coherence. The criterion performs the existing gluing step itself.
This is a decomposition: one original hole closed, one new hole added, net zero.
Existing holed dependencies, including ring localization gluing and the affine
derived-equivalence ingredients, are used as this stage prescribes; no new
holes were introduced in them.

## No longer needed

No repository modules or imports are pruned: both existing proof imports are
used. Removed the unpublished inherited `AffinePseudoCoherentCriterionAux`
module and its two provisional forward/backward nodes from this sandbox.
Their holes are replaced by one strictly local obligation and a real proof of
the finite-free direction. The principal-open sections and tilde/Gamma nodes
remain needed by the new local-model node; none is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The inherited attempt had two new holes in one module, incomplete docstrings
and node metadata, and unqualified `lean.declaration` names. It left the
finite-free direction unproved. All are replaced here. The original unit's
route is preserved; its realized statement/step lists contain no additional
node that this proof bypasses.

The previous delivery-tool source-root failure no longer occurs. The tool
reaches preflight and supports leaving the second-reading section to the
independent second worker. No tool was edited or bypassed.

The cited Stacks source is not present in this machine's read-only literature
checkout. Read Tag 08E7 at https://stacks.math.columbia.edu/tag/08E7 and the
project's reviewed proof steps. LeanSearch returned HTTP 500; its search is
recorded as unavailable. Loogle found `tildeFinsupp`, and Mathlib/library searches
found no affine pseudo-coherence cover result. Edge cases checked: the zero
ring admits the empty cover; localization at zero gives the zero ring; finite
free terms of rank zero and complexes vanishing above any chosen bound cause
no exceptions. No interface changes or forced adaptations were made.

## New nodes

`lem-pc-affine-pseudo-coherent-localization-cover` is the single new node, stated
by `AlgebraicGeometry.affine_pseudoCoherent_localization_cover` in
`Sheaf.AlgebraicGeometry.AffinePseudoCoherentLocalizationCover`. It records the
finite principal-open cover and the local bounded-above finite-free module
models, with the complete source-based argument and actual search results.
No change record is needed: all existing signatures and public imports remain
unchanged.

## Second reading by W3

1. I compared the delivered criterion module with the repository version. The theorem
   signature and all existing declaration signatures are unchanged; the only interface
   addition is the explicitly documented split-off localization-cover theorem.

2. I compiled both sandbox modules with `lcompile.py`; the localization-cover module
   compiles cleanly and the criterion proof elaborates without Lean errors when the
   compiler is allowed to complete. There are no `axiom`, `unsafe`, `opaque`,
   `implemented_by`, or definition-level `sorry` declarations. The only remaining
   `sorry` is the named split-off theorem, with its source proof and node recorded.

3. The split-off statement is a strict reduction to finite principal-open local models:
   it does not restate either direction of the criterion, and its edge cases include
   the zero ring and an empty cover. Its docstring, node, declaration, and proof
   dependencies agree.

4. The proof follows the unit route: local finite-free models are obtained first,
   then the existing localization gluing theorem is applied; the reverse direction
   uses the affine equivalence and the full open. The criterion node's proof and
   dependencies were updated to these actual uses, and no unused import was found.

5. The route is faithful to Tag 08E7 and preserves the target statement exactly. I
   changed only the proof, the one necessary split-off module/node, and this report;
   no definitions or existing statements were weakened.
