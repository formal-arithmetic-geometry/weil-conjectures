# Stage-1 delivery: lem-wf-bounded-free-complex-projective-cohomology-splitting

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-wf-bounded-free-complex-projective-cohomology-splitting.json`: existing statement, split into eight explicit steps; Mathlib searches found individual projective splittings and resolutions, not the full statement.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `searches.jsonl`: seven searches actually run through msearch.py; their responses are retained and added to the item's inherited searches.
- `report.md`: this report. `make_split.py` is sandbox-only scratch work.

No new nodes and no new Mathlib leaves. No unit or chapter file changed.

## Attachments

None. Searches in the project source under WeilConjectures/ for the item id, its blueprint tag, projective cohomology, and bounded-complex splitting found no declaration stating the item. The homological-algebra project code concerns resolutions, monoidal constructions and comparison maps, not this decomposition. No claim is based on the upstream master's sorry declarations.

## Wanted literature

None.

## What was wrong or missing

The imported item was true, but had no proof and cited only the derived-category definition. I added the existing free-module and projective-module definitions to the statement dependencies, and attached their references to those notions without changing any mathematical hypothesis or conclusion. I made the meaning of contractible explicit. There is no STATEMENT-DISPUTED issue.

The source starts by splitting onto B^(i+1); that step needs B^(i+1) projective. The rewritten proof starts at B^(b+1)=0 and establishes the descending induction in the right order, so it never assumes the projectivity of a cycle or boundary before proving it. The coordinate maps, inverse maps, differential, contracting homotopy and final quasi-isomorphism were missing from the imported node and are now written out.

## Unfinished work

None for this one-level split. There are no new unsplit dependencies. Lean writing and compilation were outside the authorized stage and were not performed.

## Not duplicates

No new nodes were created. Whole-DAG/blueprint searches for projective cohomology, bounded splitting and splitting were read. The existing `lem-trf-field-complex-cohomology-splitting` and `new-field-complex-homotopy-normal-form` require a field (and the latter is a sheaf complex on its spectrum); neither gives this arbitrary commutative-ring statement. `lem-pc-finite-free-split-top-cancellation` assumes an already supplied section onto the top term and constructs a quasi-isomorphic shorter finite-free model; it does not state this chain-level decomposition by actual cohomology and boundary modules. They are not needed as citations. The existing `def-weil-pbc-projective-module` already states both the direct-summand-of-free and surjection-lifting characterizations, so no additional projective-splitting or retract lemma node was made.

## Review by Q93

I read the main-20261015 proof of `lem-wf-curve-finite-level-pd`, particularly the entire paragraph beginning “We record the elementary splitting argument needed here”. The item is exactly the algebra argument that paragraph needs before passing from derived duality to a degreewise pairing. I also read the unit and chapter records. This algebra sublemma changes none of their routes. I read the complete statements of all three cited nodes: `def-weil-pbc-free-module`, `def-weil-pbc-projective-module`, and `def-weil-abstract-derived-category`. For their underlying sources I checked Stacks algebra.tex, item-free-module (00C2), definition-projective (05CE), lemma-characterize-projective (05CF), including its proof, and derived.tex, section-derived-categories and definition-unbounded-derived-category (05RR/05RU). No new-node source needs review because there are no new nodes. Since the blueprint is agent-written and the explicit maps were expanded here, proof_origin.by is agent.

Step 1 uses only kernels, images, quotients, d squared zero, and the supplied term bounds. I checked B^(b+1)=0 and B^a=0; no bound on projective dimension or regularity of R is assumed. Its two surjections and their kernels are actual module maps, not an appeal to an unstated exactness theorem.

Step 2 cites the free-module definition for the basis and the projective-module statement for the free-summand and lifting characterizations. Both are explicitly in those statements. For the retract closure property I wrote the full two-line lifting construction g j for a lift of f r; no non-elementary closure theorem is hidden. Zero is covered by the empty basis. These are elementary consequences of the cited characterizations, not new DAG nodes.

Step 3 uses the projective-module statement only to lift the identity of B^(i+1) along the surjection p_i proved in step 1. Its hypothesis is the descending induction hypothesis. The formulas z+t_i(c) and (x-t_i p_i(x),p_i(x)) are inverse by p_i t_i=1; the first inverse coordinate is in the kernel. Thus Z^i is a retract of the already projective L^i, by step 2.

Step 4 uses the same cited lifting characterization with the item's hypothesis on H^i(L), and the actual quotient q_i. I checked that z-s_i q_i(z) is in B^i, and that the inverse identities follow from q_i s_i=1. The induction base is B^(b+1)=0 and the finite descent performs step 3 before step 4 at each degree. All splittings are defined before the chain calculation uses them. I marked this substantive descending induction non-elementary; it uses no black box beyond the cited characterizations.

Step 5 is direct substitution in those maps. I checked d alpha_i(u,h,c)=c and alpha_(i+1)(c,0,0)=c. Its inverse's first coordinate lies in B^i, its second in H^i, and its third in B^(i+1). Therefore these are actual chain isomorphisms, not only degreewise module isomorphisms.

Step 6 cites the derived-category definition solely for the shift convention. Its statement literally gives (K[1])^r=K^(r+1), so H^i[-i] sits in degree i. The direct-sum identification is an explicit reindexing with exactly the two adjacent disk contributions in each degree. Bounds give finitely many disks and cohomology terms; no infinite-coproduct exactness result is used.

Step 7 is elementary: the one identity map h_i^(i+1) gives h d=1 in the lower degree and d h=1 in the upper degree, with zero in all other degrees. This proves the stated contractibility and gives a contraction of their finite sum. It does not infer contractibility merely from acyclicity.

Step 8 cites the derived-category definition precisely for localization at quasi-isomorphisms. Its statement says this explicitly. The kernel and image in the displayed coordinate differential are computed directly, so projection induces the identity on cohomology in every degree and is a quasi-isomorphism. No theorem that localization preserves an infinite sum is required: S was constructed as the displayed finite sum of single-term complexes before localization.

I checked delivery-errors B through E point by point. B: the statement is self-contained with notion references; there are no statement-only new nodes, unchecked leaf claims or duplicate nodes. The search log preserves actual queries, including the unqualified Loogle identifier error and the corrected qualified query. I read the strongest hits in Mathlib: EnoughProjectives.lean:40-59 (a split epimorphism to one single-term complex), HomotopyCategory/KProjective.lean:113-124 (K-projectivity of bounded-above projective complexes), DerivedCategory/TStructure.lean:180-188 (bounded representatives), and ShortComplex/ShortExact.lean:213-218 (splitting one short exact sequence with projective quotient). None states both clauses of the item or specializes to them in one line. C: all citations use the cited statements, with per-step verbatim quotations in citations.json; elementary arguments are written out, and proof_deps is exactly the union of uses. The definitions are existing Mathlib leaves, so no off-unit theorem is used or tool-use exception needed. D: the induction and actual maps carry the proof; nothing is moved to a restatement node, and the small closure argument is fully proved rather than labelled standard. E: the ground ring is arbitrary, the modules split only after projectivity is known, and all shifts and disk indices were checked. The zero ring, zero complex, a single nonzero projective term, an identity two-term complex, and the example [Z/4 --2--> Z/4] were tested. The last example has nonprojective Z/2 cohomology and is correctly excluded; the proof never claims the necessary splittings in it. No source error was found. Each proof step is under 2000 characters, and no step hides a separate comparison lemma. No SGA source is cited.
