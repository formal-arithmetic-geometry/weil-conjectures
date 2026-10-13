## What changed
Moved the six explicit constructions, with identical names, elaborated types and visibility,
into `Sheaf.AlgebraicGeometry.RestrictedOverSingleData`, publicly reexported by the original
module. This allows two new modules to state independent unit and triangle-composition laws
without an import cycle. Proved `restrictedOverSingle_coherence` via the fully proved private canonical helper
and the generic categorical `iso_cancel_triangle`, from these two laws, including
a real cancellation proof of cone coherence using triangle composition at the cone legs.
The original theorem signature is unchanged. The second reader restored the original
`asIso h` transition-isomorphism construction, with its proved IsIso instance; its
inverse is uniquely determined by that hom. The explicit return annotations keep the same original endpoint objects. No data is chosen from an unproved theorem.
The inferred return types of the single
complex, constant diagram and cone isomorphism are now written explicitly; these name the
same objects and reduce elaboration of inverse-image constructions. Local irreducibility
attributes and a scoped transparency option keep inverse-image and comparison
implementations abstract during elaboration.

## Proved and sorry left
Closed the original hole `AlgebraicGeometry.Etale.restrictedOverSingle_coherence`.
This is a decomposition, not a sorry-free proof: two strictly smaller holes are added,
`AlgebraicGeometry.Etale.restrictedOverSingle_unit` (node
`lem-sbc-restricted-over-single-unit`) and
`AlgebraicGeometry.Etale.restrictedOverSingle_composition` (node
`lem-sbc-restricted-over-single-composition`). Each has one whole-proof `sorry` in a new
module, a source and a complete natural-language calculation. No holes remain in the item
module or in the extracted definitions. Locally, one original hole is closed and two
are added (net holes closed minus added: -1); no net proof progress is claimed.

## No longer needed
No module is pruned. The old direct proof dependencies
`lem-weil-pbc-inverse-image-composition` and
`def-sbc-raw-affine-restricted-cohomology` are replaced at the coherence node by
`lem-sbc-restricted-over-single-unit` and
`lem-sbc-restricted-over-single-composition`. Both old nodes remain needed through
the extracted data and the lower calculations; this is dependency refinement, not pruning. The original public raw-cohomology
import is retained to preserve visibility. No separate cone-naturality lemma is needed:
triangle composition and cancellation prove it directly. The preorder-only modules
`RestrictedAffineSingleTransitionLaws` and `RestrictedAffineSingleConeNaturality` were checked
and not imported; they do not specialize to the arbitrary category in this theorem.

## Where the brief, the DAG or earlier work was wrong
The plan needs explicit unit and triangle-composition calculations for an arbitrary category;
the existing restricted-affine transition statements assume a preorder. A single new theorem
restating all three coherence clauses would not be a reduction, so that attempt was discarded.
The unit route is unchanged: this is strictly a refinement below the existing coherence node.
Edge cases of the new laws include identity arrows, zero sheaves, empty schemes, and arbitrary
(non-thin) categories; the comparison-isomorphism calculations use no cofilteredness or limits.
The supplied Stacks tags contain the surrounding restriction/complex argument; their implicit
coefficient coherence is expanded by the stated inverse-image unit and associativity laws.

## New nodes
`def-sbc-restricted-over-single-data`: the unchanged explicit definitions, extracted solely to
avoid cycles. Module `Sheaf.AlgebraicGeometry.RestrictedOverSingleData`.

`lem-sbc-restricted-over-single-unit`: one-arrow identity law, with no cone or composition law.
Module `Sheaf.AlgebraicGeometry.RestrictedOverSingleUnit`.

`lem-sbc-restricted-over-single-composition`: the composition identity for one triangle in
Over W; no indexing category, unit law or cone statement. Module
`Sheaf.AlgebraicGeometry.RestrictedOverSingleComposition`.

Change record: `coord/changes/restrictedOverSingleData.md`.

## Second reading by B2

1. **Interface and meaning — PASS.** Compared the delivered item with the repository
   using diff and checked the entire existing theorem signature byte for byte. It is
   unchanged. Read the extraction change record against all six original definitions.
   Scratch Lean checks establish equality of the diagram, cone, single complex and
   constant diagram constructions, equality of the original transition hom expression,
   and pointwise equality of the cone isomorphisms and their endpoint types. The
   transition construction now uses the original `asIso h` body again. Its inverse
   is determined by the proved IsIso instance, not by any unproved existence theorem.
   Only the original direct consumer uses these names; no consumer statement is changed.

2. **Proof and axioms — PASS for the delivered modules.** Compiled all four modules
   with lcompile.py. The coherence proof first eliminates the concrete-data equalities;
   its canonical helper proves the three conjuncts from unit, triangle composition,
   and the fully proved categorical cancellation helper. There is no hole in either
   helper. The only two direct sorries are the named unit and composition theorems.
   Printed axioms for all six constructions, both lower theorems and the coherence
   theorem: the constructions use only propext, Classical.choice and Quot.sound;
   the latter three additionally use sorryAx through the reported lower holes.
   Scanned for forbidden declarations and hollow data: none.

3. **Lower statements — PASS as a decomposition.** The unit theorem asserts only
   the identity clause at one object; the composition theorem asserts one triangle
   equation, independently of an indexing diagram or cone. Neither restates the
   whole item. Its hq is the equality of the concrete composite pullback maps, supplied
   by map_comp or cone naturality in the actual applications; equality-proof choices
   are immaterial. Checked identity arrows, zero sheaves, empty schemes, empty indexing
   categories, and non-thin indexing categories: these require no extra assumptions
   or weakened conclusions. Read the proof calculations and their nodes. Independent
   leanfinder, qualified loogle and grep searches found geometric gluing cocycles and
   supporting single-complex component lemmas, not either whole comparison statement.
   Also checked repository inverse-image unit/associativity laws and the preorder-only
   restricted-affine statements. No lower hole could be closed by one of those results
   without the remaining coefficient calculation. One hole closed, two added: this
   delivery records a decomposition, not net proof progress.

4. **Route and pruning — PASS.** Cone coherence is actually derived by applying
   triangle composition to the two cone legs and cancelling the apex transition;
   no extra cone hole is introduced. The lower-law imports are proof-only. The data
   import is public because it reexports the existing constructions. The original
   raw-cohomology public import remains available. Corrected `No longer needed` to
   name both old direct proof dependencies replaced by the refinement; both still
   occur transitively, so no module is pruned. Read sk-lem-failure-field.realized:
   its statement and step entries are empty and remain untouched. No unit route is
   bypassed and no unit or chapter record is changed.

5. **Lean and nodes — PASS.** The existing node changes only lean, proof, proof_deps
   and proof_origin. Its proof describes the actual private helper and cancellation.
   The moved definitions belong to the new data node; the two public lower declarations
   have their own new modules and nodes. Checked each new node's required fields,
   source, chapter, unit, created record and blueprint ancestry, and that proof_deps
   equals the union of proof-step uses. Added independent search records to both
   lower nodes and removed stray doc-comment terminators from their proof prose.

**Second-reader changes.** Restored the original transition-hom construction with
`asIso h`, adding a transparency setting scoped to its IsIso proof to prevent
inverse-image implementation unfolding. Updated the change record to the actual code,
fixed its Users table formatting, corrected direct-dependency and net-hole accounting,
and recorded the independent searches. Kept the original theorem proof and the two
true lower statements. Scratch checks are not delivered.

**Downstream timing limitation.** The unchanged direct consumer
RestrictedOverAbelianComplexData compiled against the baseline locally in 57.6 seconds
and, on a subsequent launcher-managed fallback, against the published server build in
42.2 seconds. Additional checks against the sandbox exceeded the local 60-second
limit without a type error. The preserved constructions and their equality checks
establish the unchanged mathematical interface; the maintainer's global build must
still verify the downstream file within its limit. No consumer adaptation or limit
increase is included.
