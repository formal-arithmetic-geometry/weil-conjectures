# Stage-1 report: lem-sfb-stratum-perfect-uniform-bounds

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-stratum-perfect-uniform-bounds.json: statement node, now split in eight steps; statement and statement dependencies unchanged. Mathlib searches find no matching theorem.
- No new nodes and no new Mathlib leaves.
- citations.json: one verbatim statement quotation for each of the 29 step/node citations. The full cited statement is retained so the independent reader can check all relevant clauses.
- searches.jsonl: actual Q60 searches, with the returned results read. Earlier N5 search records in the live item are preserved.

## Attachments

None. The exact blueprint docstring tag has no match in lean/WeilConjectures. Searches for stratum uniform bounds, scalar-model cohomology and finite affine pro-etale refinement found no declaration proving every clause of this item. Existing refinement results are tools for the proof, not attachments for the item. No compiler was run.

## WANTED

None. The blueprint and the Stacks sources used are present.

## Problems found and corrections

The imported item has an empty proof. Its statement is true as written; no statement correction or STATEMENT-DISPUTED is needed. The blueprint (2) gives the local calculation but leaves the passage from local boundedness to a uniform interval implicit. This split supplies finite refinement and attained extrema, explicitly independently of the arbitrary tensor test sheaf. It also verifies the geometry of an arbitrary locally closed subscheme, with no reducedness hypothesis.

The original source discusses integral coefficients separately using derived completeness. This item and its parent now explicitly concern ordinary uncompleted module derived categories, and their constructibility definition uses finite constant scalar models. We use the existing exact-admissible-scalar-model-cohomology node for that ordinary calculation; we neither impose derived completeness nor identify the ordinary ambient category with a completed category.

## Unfinished work

None for this one-level split. Existing cited unsplit nodes remain their own queue items. In particular lem-sfb-admissible-scalar-model-cohomology is not claimed to have a finished Lean proof.

## Not duplicates

No new nodes. Before deciding to create nothing I searched the entire DAG's statement/title fields for cover refinement, admissible scalar exactness, K-flat tensor, locally closed geometry and vanishing detection, and ran blueprint_refs searches for perfect uniform, scalar perfect and Tor bounds. The existing finite-scalar-perfect-refinement and admissible-scalar-model-cohomology nodes cover exactly the local tools needed; the former does not state cohomological finite presentation or Tor bounds, and the latter does not state finite cover extraction or uniform global bounds. They are reused.

## Review by Q60

I read the current blueprint det-prop-scalar-six-ctf statement and proof, especially (2) Local models, the chapter record and sk-prop-scalar-six unit route, the constructible-local-model blueprint definition and both live constructibility definition statements. I read Stacks proetale.tex Tags 0989 (definition-fpqc-covering), 098A (lemma-recognize-proetale-covering), 098C (lemma-proetale), properties.tex Tag 01OX (lemma-immersion-into-noetherian), morphisms.tex Tag 01T6 (lemma-finite-type-noetherian), and sites-cohomology.tex Tags 06YQ (lemma-bounded-flat-K-flat), 0E8K (lemma-restriction-K-flat), and the construction preceding 06YU (definition-derived-tor). I opened every cited node and checked its statement, rather than using its proof as an additional conclusion. There are no new nodes whose source needs a separate review.

Step 1 uses finite-type-over-Noetherian with Spec k, whose Noetherian property follows because a field has only two ideals. The existing Noetherian-open-closed-finite-presentation Mathlib leaf applies to the actual factorization S closed in an open U of X, and states quasi-compactness and local finite presentation for the composite a. These imply finite type by definition. The finite-type composition tool gives S finite type over k. The separated-cancellation node explicitly says immersions are separated, and the proper-fp-permanence node explicitly gives composition of separated maps. The qcqs-over-affine tool applies to Spec k, and the finite-affine-open-cover node has only the quasi-compact hypothesis. No finite-type theorem is applied to the pro-etale covering schemes, which need not be Noetherian.

Step 2 applies finite-scalar-perfect-refinement only after splitting off the empty case. Its stated hypotheses are precisely quasi-compactness and nonemptiness together with a specified cover and specified bounded finite-projective scalar complexes. Its statement gives the retained complexes, affine refinement, representing isomorphisms, finite extrema, and splitting data. Thus no proof-only feature of that node is used. No coefficient flatness is used for this extraction.

Step 3 uses coefficient-sections-localization for the actual equivalence with the pro-etale slice, and Cartesian coefficients (1) for the canonical restricted ring identification. Admissible-scalar-model-cohomology explicitly quantifies over every scheme and every coefficient in this item's list, includes integral coefficients and torsion or zero cohomology, asserts exactness and finite presentation, and gives the required cohomology isomorphism. Restriction-kflat explicitly states exactness of module restriction. Exact-functor-preserves-homology (c) gives the cohomology comparison. The proof does not incorrectly replace Gamma_W by a constant sheaf for integral or field coefficients.

Step 4 uses the actual degreewise inclusion/projection from the refinement statement and transports their splitting identity through scalar realization. The finite direct sum/retract argument is written out for injectivity, middle exactness and surjectivity, so this is not an unsupported assertion that a definition proves flatness. The bounded-above-flat-kflat-site statement then applies directly to E_i, with no enough-points or stalk hypothesis. The zero term and rank-zero splitting are included.

Step 5 chooses a flat-term K-flat representative using precisely the existence in kflat-resolution. One-sided-tensor-normalization explicitly permits an arbitrary second complex, so N need not be flat. Restriction-kflat supplies K-flatness, slice-restriction-flat supplies termwise flatness, and localized-site-tensor-restriction supplies the natural degreewise tensor comparison on the slice. Since N is in degree zero there is one summand in each total degree: no unmentioned commutation with an infinite sum is needed. Replacing the local derived object by its bounded flat model then gives the displayed derived isomorphism. The same interval works for every N because it was fixed in Step 2.

Step 6 uses exact restriction and homology preservation already cited, then proves joint zero detection directly from the sheaf uniqueness axiom. The fpqc-covering-axioms statement gives base change of the covering, and sk-def-pe-site identifies the covering condition with weakly etale fpqc covers. This is vanishing of sheaves, not a false descent claim that maps in a derived category are zero whenever their restrictions are zero.

Step 7 reads the finite constant local model and Dctf definitions literally: finitely presented scalar cohomology models on the same cover witness constructibility on S itself, which is an allowed constructible locally closed stratum. Global boundedness and Tor amplitude were proved before applying these definitions. Step 8 checks the empty site using its empty cover, which forces every abelian sheaf to be zero. It supplies the permitted empty refinement and interval [0,0].

I checked the small cases S empty, a zero complex, zero projective summands, disjoint local degree intervals, disconnected finite covers with different local bounds, a finite nonregular ring such as Z/4 with projective scalar terms, integral torsion cohomology, and field coefficients. The proof never assumes arbitrary modules over Z/4 are projective, nor that the cohomology of a perfect complex is projective. It uses finite presentation instead. The maximum/minimum construction is invoked only for a nonempty finite family. All steps are shorter than 2000 characters; the K-flat restriction calculation is an assembly from explicitly cited statements, not a hidden new lemma. There is no SGA source and no change to the unit route. Generic tools from other units are declared in split_report.tool_uses for maintainer review.

The Mathlib hits were finite-presentation predicates, Grothendieck abelian structures, derived-category localization and support assertions, and K-projectivity; none supplies this pro-etale coefficient-model theorem or a one-line specialization giving all its clauses. Two semantic phrasings, Loogle and source grep were actually run and recorded. No unavailable service is recorded as a no-match result.
