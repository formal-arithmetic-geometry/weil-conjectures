## What changed

Replaced the sorry in `AlgebraicGeometry.Etale.etalePresentation_image_filtration`
without changing its signature or either public import. The proof constructs a
factorization of each supported witness through the fixed stupid truncation using
upstream `ιStupidTrunc_naturality` and invertibility of the supported source's
truncation inclusion. Conversely, that fixed truncation is an admissible witness.
It then computes the presentation step using `H_formula`, image pushforward,
epi-mono factorization and invariance of image under an isomorphism. A proved
private helper identifies element membership in an image subobject with having a
preimage under the original group homomorphism.

Added the proof-only imports `Sheaf.AlgebraicGeometry.EtaleFilteredStepCohomology`
and `WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits`. The new module states
the remaining comparison between cohomology of one filtered total step and derived
cohomology of one fixed stupid truncation, including its inclusion square. This
comparison is a proper part of the original argument: it says nothing about the
existential predicate over arbitrary supported source complexes, whose equivalence
with the fixed-truncation range is proved in the item's module.

Both modules compile together with lcompile.py, without warnings. Removing a
trial explicit import of Mathlib.Algebra.Category.Grp.EpiMono also compiled cleanly.
No definitions, existing signatures, visibility, instances or other modules changed.
The second reader restored the original declaration docstring and added plain proof
imports of CartanEilenbergTotalResolution, CartanEilenbergMappedTotal and
KInjectiveComparisonPrinciple to the new comparison module. KInjectiveComputes is
already publicly available through the presentation interface and needs no extra import.

## Proved and sorry left

Closed the original local hole:
`AlgebraicGeometry.Etale.etalePresentation_image_filtration`
(node `lem-weil-pbc-etale-presentation-image-filtration`).

Added one hole, the whole proof of the public named theorem
`AlgebraicGeometry.Etale.etale_filtered_step_cohomology`
(node `lem-weil-pbc-etale-filtered-step-cohomology`), in the new module
`Sheaf.AlgebraicGeometry.EtaleFilteredStepCohomology`.
Its docstring and node give the restricted augmented-total resolution argument
and the compatibility with the fixed resolution comparison.

There are no sorries in the original module, no sorries in definitions and no
partial-proof sorries. This is a decomposition: one hole closed and one added,
net zero holes, with the supported-witness and image-subobject arguments now proved.
The item remains transitively dependent on the new hole.

## No longer needed

No original import was removed: both original public imports are used by the
unchanged statement. The trial explicit Mathlib.Algebra.Category.Grp.EpiMono import
was removed because its API is already available through the existing imports.

The original direct proof dependency `thm-sp-if-e1`
(`Sheaf.CategoryTheory.HypercohomologyFirstPage`) is replaced by
`lem-weil-pbc-etale-filtered-step-cohomology`. No direct proof import of that
existence theorem is needed: this statement works with a supplied presentation.
Its module remains available transitively through the presentation interface,
so no entire existing module is claimed pruned from the targets' import closure.
The filtered-step comparison still needs the existing total-resolution,
mapped-total and K-injective comparison ingredients; these have not been pruned.
No unit statement or realized proof step has been bypassed.

## Where the brief, the DAG or earlier work was wrong

The original sole proof dependency `thm-sp-if-e1` provides a spectral sequence and
resolution presentation, but its Lean signature does not identify the cohomology
of a supplied presentation's filtered step with the stupid truncation. That missing
comparison is now explicitly stated instead of assuming it follows from the
existence theorem's conclusion. The completed proof handles the rest of the
original paragraph. Related Grothendieck second-filtration comparison theorems
use canonical truncations and different indexing, and do not supply this comparison.

The inherited unit is `sk-prop-h2`, whose record has no realized nodes and whose
Kummer proof is unrelated to this newly created filtration branch. The inherited
blueprint ancestor is null (`blueprint_refs.py ancestor` prints None); the new node
preserves that ancestry with an explicit place and via list. Neither record is
silently repaired here. The rules mention coord/delivery-errors.md section I, but
this checkout has no such section.

Sources read: Stacks Tag 015J, especially proof remark (3), and Tag 0133, finite
row-resolution totalization. Edge cases checked in the comparison argument:
arbitrary negative q, n<q (empty diagonal), the zero bicomplex, q below the original
lower bound, and supported complexes with nonzero differential at q. The stupid
truncation keeps the outgoing differential at q and kills only the incoming one,
so the factorization and restricted augmentation remain chain maps. The finite
bounds concern total degree n and do not require q>=0. The comparison uses the
pinned c_formula, w_formula, aug_formula and over_K fields, not an arbitrary
isomorphism of abutment groups.

Searches used leanfinder, loogle and grep through msearch.py; LeanSearch returned
Internal Server Error and is recorded as unavailable. Blueprint searches for
stupid truncation, filtered step and 015J found only the existing definition of
truncations, not a theorem stating the remaining comparison.

## New nodes

`lem-weil-pbc-etale-filtered-step-cohomology`:
`lean/Sheaf/AlgebraicGeometry/EtaleFilteredStepCohomology.lean`, declaration
`AlgebraicGeometry.Etale.etale_filtered_step_cohomology`. It is the fixed-truncation
resolution computation and inclusion comparison required before applying the
proved supported-witness equivalence. Its three proof steps specify restriction,
finite-diagonal K-injective computation and naturality of the comparison. Existing
nodes for these ingredients are cited. No change record is needed: the item changes
only proofs and proof imports, and the new public statement is in a new module.


## Second reading by Q1

1. **Existing interface unchanged: pass.** Diffed the item against the repository
   and checked its declaration table: the existing theorem signature is byte for
   byte identical, both public imports remain, and there are no changed definitions,
   instances, visibility or target statements. The only added declaration in the
   item is a proved private membership helper. The other module is new; no change
   record is required. Restored the original theorem docstring to minimize changes.
2. **Kernel proof and holes: pass as a decomposition.** Both delivered modules
   compile through lcompile.py in import order with no warnings. Explicit
   `#print axioms` in temporary scratch copies gives propext, Classical.choice,
   Quot.sound and sorryAx for both public theorems, and only the first three for
   imageSubobject_mem_iff. There is exactly one local sorry in the delivered set,
   the entire proof of etale_filtered_step_cohomology; no forbidden declarations
   or data holes. The existential comparison is eliminated inside a proposition
   proof, not used to define data from an arbitrary unproved witness.
3. **Split statement true and strictly smaller: pass.** Read all fields of
   EtaleTermwiseHypercohomology, the total-resolution and mapped-total signatures,
   the K-injective comparison principle, and Stacks Tags 015J and 0133. Restriction
   to complex degrees s >= q is a sub-bicomplex and preserves the outgoing
   differential at q. Its diagonal is q <= s <= n with resolution degree n-s >= 0.
   The finite injective total resolves the stupid truncation. The degreewise
   secondFiltration formula after flip selects precisely these summands, including
   negative q. The fixed augmentation, over_K, w_formula and c_formula give the
   canonical inclusion square. Checked zero complexes, p < q, negative indices,
   q below the original lower bound and a nonzero outgoing boundary differential.
   The new theorem does not restate membership in images of arbitrary supported
   complexes; the item proves that factorization and the image calculation.
   Independent leanfinder search for column-subcomplex homology/brutal truncation,
   loogle search for imageSubobject and Iso, and grep for brutal/sigma truncations
   found truncation homology APIs and image transport facts, not this comparison.
   Also inspected the library's second-image/canonical-truncation comparison:
   it has different orientation, indexing and hypotheses. Closing the remaining
   comparison needs construction of restricted totals and their canonical squares;
   it is not a few-minute application of an available theorem.
4. **Top-down reduction and pruning: pass.** The proof establishes the supported
   witness equivalence directly using the upstream truncation API, then uses the
   restricted resolution computation and a genuine epi-mono image argument.
   Both original public imports are needed by the unchanged signature. The added
   Subobject.Limits import supplies the proof's image composition API. Added plain
   imports for the split theorem's planned total-resolution, mapped-total and
   K-injective comparison ingredients; its KInjectiveComputes dependency is already
   publicly imported transitively. The old sole proof_dep thm-sp-if-e1 is completely
   accounted for under No longer needed. No whole existing module is pruned.
   Inspected dag/units/sk-prop-h2.json: realized.statement and its sole realized
   step are empty; no realized node is removed or bypassed by this reduction.
5. **DAG matches Lean: pass.** The existing node's unchanged statement and Lean
   record match the item, and its three proof steps describe the supported-source
   factorization, comparison/image transport and membership helper. Its proof_deps
   is exactly the new comparison node. The new node has its source, complete proof
   plan, statement dependencies, union of proof-step uses, proof_origin, searches,
   status, creation record, inherited chapter/unit/blueprint ancestry and matching
   Lean signature. Its named theorem docstring supplies the complete mathematical
   proof. Recorded the independent searches in the new node as well.

Second-reading changes: restored the item's original docstring; added three
proof-only imports for the new node's plan; recorded independent searches and this
review. No Lean proof or statement needed repair. One original hole closed, one
strictly smaller hole added: decomposition, net zero; not a sorry-free proof.
