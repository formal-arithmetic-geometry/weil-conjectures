# Stage-1 report: lem-sfb-monomorphism-into-field-coproduct

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-monomorphism-into-field-coproduct.json: existing statement, now split; statement unchanged; no Mathlib match for the full assertion.
- dag/nodes/sec-six-functors-basics/lem-sfb-field-ring-epimorphism-trivial-or-iso.json: new statement-only ring lemma, unsplit; no exact Mathlib match or one-line specialization found.
- citations.json: one verbatim statement quotation for every node used in every proof step.
- report.md: this report. searches.jsonl was written by the authorized search command and retained.

## Attachments

None. Searched lean/WeilConjectures for the item id/docstring tag and for monomorphism/field/spectrum terminology. No declaration there states the full item. Its old sorry declarations, if any, would not qualify. The existing clopen-coproduct node has a Sheaf declaration, which is reused through that node, not claimed as an attachment for this item.

## WANTED

None. All sources used are available in literature/stacks-project/ and the current blueprint.

## What was wrong or incomplete

The item was statement-only, with no proof or proof dependencies. The assertion agrees with the arbitrary-disjoint-union clause of Stacks Tag 03DP, schemes.tex, lemma-mono-towards-spec-field; no statement correction is needed. I made explicit the justification for the source's sentence that the source over a single field has at most one point, rather than assuming that monomorphisms are pointwise injective by definition. I also avoided the false infinite-family replacement of a scheme coproduct by the spectrum of the product ring. Only the individual nonempty pieces are proved affine.

The inherited blueprint.from.node is null, as confirmed by tools/blueprint_refs.py ancestor. The exact inherited place and via chain are preserved. Read the current latest blueprint unit and direct-images proof (3); its current compactification route is not altered by this generic supporting lemma. This item is not the unit's key node, so no unit record is edited.

## Sources and searches

For the item I read schemes.tex, Tag 03DP, lemma-mono-towards-spec-field, including the whole proof and its explicit citation to the algebraic classification. For the new node I read algebra.tex, Tag 04VV, lemma-epimorphism-over-field, together with the preceding faithfully-flat-epimorphism lemma and the following epimorphism-injective-spec lemma. The statement in the new node translates the source's equality notation into the precise assertion that the given structural map is an isomorphism, or the target is zero. It has no proof text or proof dependencies.

The actual msearch.py queries and results are in searches.jsonl; the node records list exact query strings and actual verdicts. Two different phrasings of the ring-epimorphism question were tried before concluding absence; additional faithfully-flat and tensor-criterion searches tested more general formulations. I read Mathlib/Algebra/Category/Ring/Epi.lean:26-56 and Mathlib/Algebra/Algebra/Epi.lean:29-90. CommRingCat.epi_iff_epi supplies a tensor criterion, not the classification. RingHom.surjective_of_epi_of_finite and Algebra.isEpi_iff_surjective_algebraMap_of_finite require module finiteness, which is not assumed and would itself need proof. The algebraically closed/integral and localization hits have different hypotheses. The faithfully-flat search returned descent and injectivity results, not a direct match. No service failed in the searches used for the verdicts. An initial grep of the nonexistent RingTheory/Epimorphisms directory returned zero hits; I did not use it as evidence and followed up in the actual Algebra/Category/Ring, Algebra/Algebra and RingTheory/Flat directories. No unrun query is recorded as run.

Before creating the node, I searched the whole DAG by 04VV, epimorphism-over-field, field/epimorphism terminology and by candidate names. I also ran blueprint_refs.py searches for 04VV and epimorphism field, and searched literature/blueprint/latest for that tag/label; there is no existing node for this assertion. For the item, whole-blueprint searches for 03DP, field spectra and monomorphism field returned no matching blueprint statement. Searched the live Lean source for ring epimorphism/field terms; the hits concern sheaves or flat epimorphisms in a different argument, not this theorem.

## Not duplicates

lem-sfb-field-ring-epimorphism-trivial-or-iso vs lem-sfb-monomorphism-into-field-coproduct: the new node is the ring-theoretic input 04VV for an arbitrary commutative target; the item additionally reduces arbitrary schemes to affine field components and assembles an arbitrary coproduct. The new node does not restate the scheme item or one of its clauses.

lem-sfb-field-ring-epimorphism-trivial-or-iso vs lem-sfb-reduced-singleton-field-factorization: that node factors reduced algebraic-space maps through a specified quasi-compact field monomorphism, using the present scheme item; it does not classify epimorphisms of arbitrary commutative rings. The new node has no reducedness or algebraic-space hypotheses, and cites none of that node's dependencies.

lem-sfb-field-ring-epimorphism-trivial-or-iso vs lem-sfb-locally-separated-space-decent: that node concerns quasi-compact field representatives of algebraic-space points and is an ancestor of the item; it gives no ring-epimorphism assertion.

No existing node has source tag 04VV. The latter comparisons also distinguish the other nodes mentioning 03DP in their supporting material.

## Review by Q59

I checked delivery-errors B through E against the written files and sources. The new node introduces k, A, the unital homomorphism, its cancellation property, and the meaning of the zero ring; the only nonprimitive notion is a field and it cites def-weil-field. Its source is 04VV with the exact TeX label. It is statement-only and is strictly the algebraic input to the item's geometric proof, not a renaming of the item. There are no new definition nodes and no Mathlib leaves claimed without an exact match. The item's statement and inherited metadata are retained, and all new TeX uses single logical backslashes.

Step 1 uses the full statement of lem-weil-pbc-scheme-coproduct-family for arbitrary small I, clopen component images and covering. I opened that node and checked that it really includes all three clauses. The preimages are clopen by continuity; no finiteness is used. The open-factorization statement of lem-weil-pbc-morphism-factors-through-open-subscheme supplies f_i with exactly the required equation. The cancellation proof of monicity is written out: use monicity of m and then of j_i. The latter is the actual statement of lem-weil-pbc-open-immersion-monomorphism; it applies because j_i is an open-subscheme inclusion. Thus this step is elementary given the cited statements, not an uncited base-change theorem.

Step 2 cites def-weil-radicial-morphism for its explicit theorem (1) iff (2), not merely the name of a notion. Its statement really says that injectivity on maps from every field spectrum is equivalent to universal injectivity. I read the corresponding source morphisms.tex, Tag 01S4, lemma-universally-injective, including its proof. Monicity supplies condition (1); the identity base change gives ordinary point injectivity. def-weil-affine-spectrum explicitly states that a field spectrum has one point. The affine-opens-basis statement supplies an affine neighbourhood of the unique point when T_i is nonempty; that neighbourhood is the entire underlying open, so it is T_i itself. There is no assumption that all of T is quasi-compact or affine.

Step 3 uses the affine-spectrum node's full bijection on ring maps and scheme morphisms, including functoriality and uniqueness. I read the node, and those assertions are present in its statement. The displayed cancellation against Spec B proves that the particular structural map k_i to A_i is an epimorphism in exactly the sense of the new node. The hypotheses of 04VV are therefore met, including that k_i is a field, A_i is commutative, and maps are unital. The empty alternative is explicitly excluded using properness of prime ideals, not an unproved reducedness or finite-dimensionality assertion. The isomorphism obtained is f_i itself, so its base-field structure is retained. This is the only new non-elementary input; its future split can follow 04VV's faithfully-flat or vector-space argument.

Step 4 uses the exact statement of det-pe-finite-local-systems-type-coproduct, which quantifies over any scheme, any index type and a clopen decomposition. It has no local-system or coefficient hypothesis despite the filename. The nonempty pieces indexed by J are disjoint opens and cover T because the omitted pieces are empty. This verifies that theorem's entire hypothesis. Its coproduct universal property and the existing scheme-coproduct statement define both maps explicitly, and their two inverse equations are checked on coprojections. The equation m theta eta_j = iota_j verifies the isomorphism over D, not only as abstract schemes. I declare this other-unit node as a generic tool in split_report.tool_uses: the fact used is scheme gluing, and no unit-level route is replaced.

I checked small cases for the item: I empty forces T empty; T empty gives J empty even if I is nonempty; a singleton family recovers precisely the empty-or-field case; an infinite I and any infinite J still work since no finite product-ring description is used. For the new node, k to k and k to the zero ring realize the alternatives. The nontrivial algebra k[t] is not an epimorphic target (the evaluations t=0 and t=1 agree on k), and the dual numbers are not an epimorphic target (identity and epsilon-to-zero agree on k). Thus neither arbitrary dimension nor nilpotents are silently excluded, and they do not create counterexamples. No statement dispute was found.

Every proof dependency is the union of the steps' uses. Each citation is checked from the statement alone and quotations were copied directly into citations.json; none relies on a cited proof or a definition without the theorem actually needed. All four proof steps are shorter than 2000 characters; their combined text is under 3000 characters. The non-elementary ring input is isolated as the new node. No SGA source is used, and no Lean file, compiler, Lake command, repository mutation or launcher edit was made.

## Unfinished work

No unfinished task within this one-level split. The new node is deliberately unsplit, as required for a new supporting node. Delivery validation and push are the remaining procedural steps at report creation.
