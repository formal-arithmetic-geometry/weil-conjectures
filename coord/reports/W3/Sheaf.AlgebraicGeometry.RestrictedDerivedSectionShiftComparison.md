## What changed

Replaced the sorry in restrictedSectionPullback_shift by a reduction to two independent
parts of the stated argument. RestrictedDerivedSectionsShiftTransport handles shift
coherence for arbitrary unshifted derived morphisms. RestrictedDerivedSectionsSingle
handles the unshifted single-complex and restricted coefficient calculation.
The item applies degree-p homology to the latter, unfolds the explicit cohomology map,
and cancels the source single comparison using functoriality. The signature and
original docstring of the item are unchanged. All new imports are proof-only.

## Proved and sorry left

Closed the original hole:
AlgebraicGeometry.Etale.RawRestrictedComparison.restrictedSectionPullback_shift
(lem-sbc-restricted-derived-section-shift-comparison).
There is no sorry left in the item's module. This is a decomposition, not a complete
sorry-free proof of the mathematical result: one original hole is closed and two
new holes are added, a net change of -1 before any closure effects.

The two new holes, each the whole proof of a public named theorem, are:

- AlgebraicGeometry.Etale.RawRestrictedComparison.restrictedDerivedSections_shiftTransport
  (lem-sbc-restricted-derived-sections-shift-transport).
- AlgebraicGeometry.Etale.RawRestrictedComparison.restrictedDerivedSections_single
  (lem-sbc-restricted-derived-sections-single).

Transport has no restricted coefficient map or restricted-cohomology map in its
conclusion and permits any derived morphism f. The single comparison has no shift
parameter and no homology assertion. The item combines these distinct steps by
actual functoriality and inverse cancellation. Both statements permit noninvertible
coefficient maps, degree zero, the zero sheaf and empty restricted schemes. No data
are chosen from an unproved existence statement.

## No longer needed

No original library import is removed: RestrictedDerivedSectionZeroComparison is
still needed for its three explicit constructions. Its theorem
restrictedSectionPullback_zero is not used. The following old direct proof_deps are replaced by the two new nodes:
- def-sbc-raw-restricted-cohomology-comparison-map;
- lem-sbc-restricted-derived-section-zero-comparison;
- lem-weil-pbc-inverse-image-composition;
- prop-weil-pbc-derived-inverse-image-adjunction.
Their constructions remain used by the item or the new nodes; these are not globally
pruned nodes or modules. In particular, inverse-image composition and the derived
adjunction remain needed by the new statements. No unit statement or realized unit proof step is bypassed.

The earlier sandbox drafts RestrictedDerivedSectionsCommShift and
RestrictedDerivedSectionShiftIso are not delivered or imported. The generic
shift-transport helper and the scratch calculations are not part of the delivery.
Shift coherence and its canonical comparison alignment form one new transport node,
instead of additional separate holes.

## Where the brief, the DAG or earlier work was wrong

The previous attempt was unvalidated because its compiled dependency was missing.
That dependency is available now. The previous proof also mixed the canonical shift
structures of differently parenthesized functor composites. A generic transport
calculation compiles in isolation, but its concrete comparison with Evaluation.shiftIso
caused deep unfolding. The delivered reduction records this whole coherence step
as the shift-transport node instead of asserting the concrete alignment is proved.

Rewriting after expanding the formulas can also require default transparency:
@Etale must unfold to MorphismProperty Scheme. The final inverse cancellation uses
an explicit categorical Functor.map_id to avoid the unrelated root Functor.map_id.
No existing statement or definition was changed and no adaptation is needed.

## New nodes

lem-sbc-restricted-derived-sections-shift-transport, in
lean/Sheaf/AlgebraicGeometry/RestrictedDerivedSectionsShiftTransport.lean,
states the conjugation formula for shifted restricted section pullback and an
arbitrary derived morphism. Its source is the shift-coherence step of the parent's
Stacks 07A6 and 0D6F argument. The docstring and node give the complete proof in words.

lem-sbc-restricted-derived-sections-single, in
lean/Sheaf/AlgebraicGeometry/RestrictedDerivedSectionsSingle.lean,
states the unshifted identity in the derived category, including the localization,
composition and coefficient comparisons. Its source is the other step of the same
parent argument. The docstring and node give the complete proof in words.

No change record is needed: existing interfaces and public imports are unchanged.

## Second reading by W3

1. PASS: compared the existing module with the repository using diff, and checked
   the theorem signature and original docstring byte for byte. Only two proof-only
   imports, a local heartbeat option, and the proof body were added. No existing
   statement, definition, public import, or visibility changed; no change record
   or forced adaptation is needed.
2. PASS: all three delivered modules compile locally in import order without errors
   or warnings (13.8 s, 17.3 s, 44.2 s on the first review run). The item contains no
   sorry; the only two new sorries are the complete named theorem proofs listed
   above. No forbidden declaration or hollow definition occurs. Scratch copies
   with #print axioms show exactly propext, Classical.choice, Quot.sound and
   sorryAx for each of the three declarations; sorryAx remains through
   the explicitly reported open statements, rather than a completed target proof.
3. PASS: read both new statements and their word proofs against the definitions of
   Evaluation.singleIso, Evaluation.shiftIso, derivedSectionPullback,
   derivedRestrictionIso and the explicit coefficient/cohomology maps. Shift
   transport is the conjugation identity for an arbitrary derived morphism; it
   does not identify the coefficient map. The single theorem identifies that map
   before shifts or homology; it does not establish shift coherence. Thus each is
   a strict part of the original argument. At p=0 the shift formula is ordinary
   conjugation by the single comparisons. For f=0 and phi=0, additivity makes both
   sides zero; for the zero sheaf or empty restriction the same functorial
   identities apply. No invertibility of either morphism is used. The directions
   of all single and localization comparisons agree with their definitions.
   Independent searches used leanfinder (conjugating shift-compatible natural
   transformations), loogle (Functor.CommShift), and grep (single/derived and
   right-derived shift comparisons), plus rg of the upstream and Sheaf sources.
   Mathlib supplies individual single comparisons and general shift naturality;
   upstream supplies mapDerivedCategoryCompIso_fac, mapDerivedCategoryNatIso_fac
   and conditional right-derived shift compatibility. No exact duplicate was
   found. ExtExactFunctorCompositionComparison contains a related private single
   calculation, but its public Ext theorem does not give this derived equality.
   Neither open statement has a short direct closure from those public results.
4. PASS: the item really applies both reductions, maps the single equality by
   degree-p homology and cancels the source single isomorphism. Its imports are
   needed: the original public import supplies the unchanged signature and
   constructions, and the two ordinary imports supply the proof reductions.
   Corrected No longer needed to enumerate every replaced old direct proof_dep,
   without claiming global pruning. Read sk-lem-failure-field.json: realized has
   an empty statement list and an empty step list; no realized node is bypassed.
   The parent shifted-single route is retained as the two stated parts.
5. PASS: compared all three DAG lean.statement fields verbatim with Lean; checked
   new-node source, complete word proof, searches, status, created, blueprint,
   chapter, unit and lean metadata. Existing node changes are only proof,
   proof_deps and proof_origin. Its proof_deps are exactly the union of proof-step
   uses. Both new nodes preserve the item's chapter, unit and ancestry.

Second reading changed only excess blank lines in the item and the report's
explicit list of replaced direct dependencies, and added this review. No additional
hole was closed or added: this delivery remains a one-hole-to-two-hole decomposition,
with no globally pruned module.
