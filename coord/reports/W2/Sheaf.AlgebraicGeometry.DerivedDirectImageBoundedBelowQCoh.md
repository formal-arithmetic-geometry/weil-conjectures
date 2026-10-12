## What changed

Proved `AlgebraicGeometry.schemeDerivedDirectImage_preserves_QCoh_of_isGE` in
`Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh` without changing its signature.
The proof implements all four planned steps using the existing truncation hypercohomology
and qcqs ordinary higher-direct-image declarations. Three proved private helpers establish
that quasi-coherence contains zero, propagates to every derived page, and passes from the
graded pieces of a finite filtration to the filtered object. The last helper is stated for
an arbitrary isomorphism-invariant, extension-closed object property in an abelian category.

Replaced the proof-only import of
`WeilConjectures.AlgebraicGeometry.Cohomology.Projective` with the narrower
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`, where the ordinary
qcqs quasi-coherence theorem is stated. All public imports remain unchanged.
Updated the item's DAG proof to describe the actual comparisons and induction arguments;
the conceptual proof dependencies and the unit route remain unchanged.

Validation: the final single-file compilation passed with no warnings. The proof handles
negative first indices by zero objects, and degrees below the cohomological lower bound
by a filtration whose full and zero steps can both be index zero. No new statement or
hypothesis was introduced. The launcher dry run is the final delivery check.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.schemeDerivedDirectImage_preserves_QCoh_of_isGE`
(node `lem-pc-derived-direct-image-bounded-below-qcoh`).

Original holes closed: 1. New holes added or split off: 0. No `sorry` remains in the
item's module, and the delivery adds no other Lean module. The three private helpers
`qcoh_containsZero`, `qcoh_pages`, and `property_of_filtration` are fully proved.
This is a proof from existing declarations, some of which remain unproved in their
own modules; it is not a claim that the target's whole import closure is sorry-free.

## No longer needed

Removed direct import:
`WeilConjectures.AlgebraicGeometry.Cohomology.Projective`.
Its projective coherence statements and
`AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_of_isPullback`
are not used. No uniform cohomological dimension bound, compact target, projective
embedding, or locally Noetherian hypothesis is needed.

No entire conceptual dependency node is pruned: clause (1) of
`lem-pc-finite-support-hi` is still used through the ordinary qcqs quasi-coherence theorem;
only its uniform vanishing clauses (2) and (3) are unnecessary here. The kernel,
cokernel/image, extension, t-structure, derived-image, and hypercohomology nodes remain
needed. The proof uses the finite-page graded comparison directly, so it needs no
additional standalone page-infinity quasi-coherence or category-transfer lemma.

## Where the brief, the DAG or earlier work was wrong

The original broad `Projective` import was unnecessary for this item. The DAG's
`lem-pc-finite-support-hi` Lean record points only to its uniform-vanishing declaration
in that module, although this proof needs its quasi-coherence clause, whose existing
Lean declaration is `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage`
in `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`.
The item's proof now records this exact declaration; the dependency node's record was
not changed as part of this delivery. A future dependency-import regeneration should
retain the narrower import instead of reintroducing `Projective` for its unused bound.

Two anticipated compatibility steps require no additional lemma: the shared module
category accepts the Scheme.Modules closure theorems directly, and the right derived
functor in hypercohomology is definitionally the scheme derived direct image. No
mathematical error or unit-route departure was found.

## Second reading by W2

1. **Statements and source.** I compared the delivered theorem declaration byte for
   byte with the repository version and with node
   `lem-pc-derived-direct-image-bounded-below-qcoh`: the morphism has exactly the
   quasi-compact and quasi-separated instances, the two derived-category instances,
   the object `E`, its quasi-coherent-cohomology hypothesis, the integer lower bound
   and `[E.IsGE a]`, and the conclusion is unchanged. The source is Stacks Tag 08D5,
   part (1); the proof follows its bounded-below spectral-sequence argument.

2. **Proof correctness.** The file compiles cleanly with the launcher. The first
   comparison uses `exists_iso_Q_obj_of_isGE` and the truncation hypercohomology
   theorem; nonnegative E2 terms use
   `Scheme.Modules.isQuasicoherent_higherDirectImage`, while negative terms use the
   explicit quasi-coherent zero object. `qcoh_pages` applies the kernel and
   cokernel/image closure theorems at each successor page. The final helper performs
   a genuine descending finite-filtration induction using short exact cokernel
   sequences and extension closure. The `max 0 (n - a + 1)` bound also covers the
   edge case `n < a`, where the filtration has zero length. No partial proof,
   `sorry`, forbidden declaration, or hollow definition was introduced.

3. **Axioms and edge cases.** An axiom probe reports only the permitted axioms for
   `qcoh_containsZero` and `property_of_filtration`; `qcoh_pages` and the target
   additionally inherit `sorryAx` from existing imported declarations, including
   the exact-couple construction, cokernel/image closure, ordinary higher direct
   images, and extension closure. The kernel closure declaration itself is proved.
   The source theorem and target signatures remain
   unchanged, and the zero, negative-page, and below-bound cases are handled
   explicitly.

4. **Pruning and dependencies.** The proof-only `Projective` import was replaced by
   the narrower `DirectImage.Sections` import that supplies the declaration actually
   used. Public imports are unchanged. The node's proof steps and dependency union
   agree with the Lean proof; no conceptual unit dependency was removed, and the
   unit route remains intact.

5. **Nodes and delivery.** There are no new split-off statements or nodes, so there
   are no new docstrings or DAG records to review. The sole original target hole is
   closed, the theorem signature is byte-for-byte unchanged, and the report's
   `## Proved and sorry left` counts one hole closed and zero added.

**Changes made during second reading:** added this review record only; no Lean proof,
statement, definition, or DAG content needed repair.
