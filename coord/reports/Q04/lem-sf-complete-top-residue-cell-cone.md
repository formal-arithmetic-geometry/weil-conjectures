# Worker report: lem-sf-complete-top-residue-cell-cone

Group Q04; stage 1; 2026-10-21; direct delivery.

## Files written

- `dag/nodes/sec-six-functors/lem-sf-complete-top-residue-cell-cone.json`: statement, split into seven proof steps; no Mathlib match. Statement and statement dependencies unchanged. The original metadata and searches are retained; five executed Q04 searches are appended.
- `citations.json`: one verbatim quotation for every dependency cited by every numbered proof step (21 entries).
- `report.md`: this report. `searches.jsonl` is the search command's actual log. `write_split.py` is a sandbox-only construction helper, not a DAG delivery file.

There are **0 new nodes and 0 new Mathlib leaves**. All required facts already have nodes. Nothing is written to Lean, the shared repository, or the launcher, and nothing is compiled.

## Attachments

None. I searched the current `lean/WeilConjectures/` for the exact blueprint tag, top-residue terminology, residue-cell terminology and quotient-tower terminology. There is no matching declaration of this item. The broader hits include `ResidueConnectiveProjectiveOpcycles.lean` and `AffineResidueCycleHomology.lean`; I read them and they concern module opcycles or affine residue cycles, not complete pro-etale sheaf complexes with a prescribed top basis and complete cone. They do not justify an attachment.

## WANTED

None. All sources used are present locally. No prohibited SGA source is used.

## What was wrong or incomplete

The item had a statement but no proof. Its source, Stacks Tag 09C3, explicitly omits the argument that the residue cone has shorter Tor amplitude. I supplied that argument: the reduced top map is the summand inclusion under any model inducing the prescribed cohomology identifications, and its cone is the lower-degree direct sum plus an identity pair in degrees b-1,b. The homotopy is the identity from degree b to b-1 and zero in other degrees. This is an elementary calculation inside the item's proof, not a new node restating its cone clause.

There is no statement dispute. In particular the hypotheses do not include affineness, and the proof does not use affineness: the exact-evaluation theorem and split-model theorem both accept the exact epimorphism-surjectivity hypothesis stated here. Quasi-compactness is used only in the existing complete-cohomology bound. No finite-type, invertibility-on-T, or characteristic hypothesis is added.

The completeness comparison needs care: the inverse-limit coefficient sheaf is not the discrete constant sheaf R_T. I use the canonical ring identification with the pulled-back continuous integral coefficient sheaf from `det-prop-sfb-qlbar-colimit-x-integral-limit`, with its finite quotient projections, before invoking `det-pe-derived-nakayama-first-reduction`. I do not assert that an arbitrary inverse-image functor preserves inverse limits.

## Unfinished work

None for this one-level split. The existing unsplit coefficient-resolution and projective-splitting nodes remain their own items. They are cited for their statements, without borrowing constructions from their proofs. No new unsplit node is needed.

## Blueprint and searches

I read the fixed chapter record `sec-six-functors` and unit `sk-rem-sf-pf-done`. The latter is an assembly remark with no steps and this item is not its key statement; no realization fields are changed. The ancestor command returns `lem-fix-weil-operations`; the item's existing `blueprint.from` specifies the local-model extraction beneath that ancestor, via the projective-model and completed-tensor nodes. I preserve it and explain in `split_report.blueprint` how the seven steps realize the extracted old parent steps 5-6. Whole-blueprint searches for “top residue” and “projective cohomology” find no duplicate blueprint statement. A broader “derived complete” search was read and yields generic definitions and completeness results, not this cell construction.

The existing Q43 searches are retained as historical records. Q04 ran LeanFinder, Loogle, LeanSearch and grep through the required msearch command, followed by a second LeanFinder phrasing. The exact queries and returned names are in `searches.jsonl` and appended to the item's `mathlib_searches`. The results were successful searches, not unavailable services. They give generic mapping-cone definitions, projective lifting, injective factorizations, ordinary adic completion and perfectoid constructions. Their types do not state the sheaf-theoretic complete top-cell assertion. The second phrasing also finds `CochainComplex.isSplitEpi_to_singleFunctor_obj_of_projective`, whose hypothesis is an already given chain map from a bounded complex onto a single projective object; it does not lift a residue basis integrally or establish completeness of the cone. Therefore this item is not a Mathlib leaf.

## Not duplicates

No new node is created, so there are no new/existing shared-tag pairs. The DAG search by Tags 09C2 and 09C3 finds the already existing coefficient resolution, complete cohomology bounds, split residue model, top-cell attachment and parent local-model nodes. I read their statements and reused the relevant ones. The parent local-model node depends on this item and is not used as a dependency, avoiding a cycle.

## Review by Q04

I read Stacks `proetale.tex`, Tag 09C2 (`lemma-describe-constructible-complexes`), its proof of completeness bounds, and Tag 09C3 (`lemma-local-structure-constructible-complex`), including the last top-generator induction paragraph and its omitted residue-cone details. I also read `sites-cohomology.tex` Tag 0946 (`lemma-w-contractible`) for evaluation, Tag 06YY (`lemma-derived-base-change`) for exact scalar extension, and `derived.tex` Tag 064B (`lemma-morphisms-from-projective-complex`), Tag 05RS (`lemma-cohomology-homological`), Tag 014E (`definition-cone`) and Tag 05QR (`lemma-third-object-zero`). For the completion convention I read the current statements and the main-20261015 blueprint proofs of the integral-limit identification and first-reduction Nakayama result. The source's sheaf-only vanishing lemma in `proetale.tex` is not used as a substitute for complex Nakayama; the latter is exactly the cited DAG theorem. I also checked Tag 099I (`lemma-restriction-derived-complete-equivalence`) in `algebraization.tex` as background; the proof does not need to invoke that equivalence, since it identifies the two completed coefficient sheaves directly.

Step 1 uses `lem-sf-complete-residue-cohomology-bounds` only for H^(b+1)(M)=0. Its hypotheses are exactly the quasi-compactness, completeness and residue Tor interval in the item. The coefficient-resolution node states the triangle for arbitrary, possibly unbounded M and identifies its arrow with the quotient map. The long-exact-sequence node then gives the claimed epimorphism; this is an epimorphism of sheaves before evaluation, not an assumption that section functors are always exact.

Step 2 uses `lem-weil-pbc-proetale-weakly-contractible-evaluation-exact` under the exact stated weak-contractibility hypothesis, so the epimorphism from step 1 is surjective on sections. The shifted-free Hom bijection in `lem-sf-projective-cohomology-split-model` applies with C=B_T and arbitrary target M; its bounded-cohomology hypothesis is for its separate split-model clause, not for this universally quantified Hom clause. The lifts of the finitely many actual theta_b(e_i) give f. The reduction of a generator is its original quotient image, so the equality with theta_b follows on each generator. There is no unexplained compatibility assertion.

Step 3 uses TR1 for the cone triangle, the free-resolution node's actual quotient-completeness clause for P[-b], and the ring-sheaf identity from the integral-limit node to identify the completeness definition with `sk-def-pe-derived-completion`. The latter and the cone-closure clause of the Nakayama node therefore apply to this exact coefficient category and these exact quotient maps. This avoids adding a hypothesis that the sheaf B_T is discrete constant.

Step 4 uses the exact-functor clause of `lem-pur-derived-change-of-rings`, for a map of arbitrary ring sheaves, not just constant coefficients. The K-flatness of the single free term follows immediately by tensoring an acyclic complex, so its reduction has the stated generators. Taking the unit k_T as the Tor-amplitude test object gives the bounded-cohomology hypothesis needed to apply the split-model node with C=k_T. Its final statement is precisely the assertion that any map inducing theta_b is the top inclusion under the chosen zero-differential model. Thus “any” in the item's model clause is proved, not replaced by one preferred model.

Step 5 uses the explicit cone formula in the derived-category definition. I checked degrees and signs directly: C(i) has the source A^(j+1), hence the extra copy is in b-1 and the differential to the copy in b is +identity. The displayed h therefore satisfies dh+hd=identity. TR3 supplies a morphism between the two triangles, and `lem-sf-triangle-morphism-iso` applies because the first two components are isomorphisms. I marked this step non-elementary because that triangle comparison uses a theorem, while retaining the elementary contraction as an explicit step instead of manufacturing a lemma.

Step 6 is a direct K-flat/tensor calculation from `def-pc-kflat-complex` and `def-weil-derived-tensor`, applied to the finite split complex after restriction to an arbitrary site object. A tensor with an acyclic complex is a finite sum of reindexed copies with differentials plus or minus the original differential, hence acyclic. The degree-zero test tensor has terms N^(r_q) precisely in [a,b-1]. This proves the local Tor condition as well as the cohomology ranks. No claim about restriction commuting with derived limits is needed here.

Step 7 applies complex Nakayama only after L is known complete and L_1=0. The cone-zero/isomorphism theorem then applies to the distinguished triangle already constructed. I tested a=b, r_b=0, all ranks zero, nonconsecutive nonzero ranks, and empty T. For a=b the identity pair is still contractible and the lower direct sum is empty; for r_b=0 the lifted map has zero source and removes no existing lower cohomology. No interval [a,b-1] assertion is made with a=b. Empty T has the zero module category.

Against delivery-errors B-E: the statement is self-contained and unchanged; all notions already have statement dependencies. There are no new statement-only nodes, elementary-node inflations, duplicate nodes, Mathlib leaves with unverified file positions, or restated clauses disguised as lemmas. Every non-elementary input is a named existing node whose statement I read. All 21 citations are checked against literal statement substrings. The argument uses no proof-only feature of another node, no omitted smallness condition and no parent dependency. The four off-unit statement tools are declared in split_report.tool_uses with their exact purpose. Every step is below 1100 characters, so none meets the 2000-character long-step threshold; the only identification inside the cone step is the explicitly written direct-sum decomposition and contraction. The statement, imported metadata, blueprint route, and coefficient categories have not been weakened or silently altered.

## Validation

The server-only `srvcheck.py ... review_split` passed for the initial seven-step split with 0 new nodes. The final direct-delivery dry run and push are run after this report is written; their command results are the authoritative delivery status.

The first delivery dry run stopped at the local quotation-length gate: the cone formula quotation in step 5 and the tensor formula quotation in step 6 were shorter than 40 characters. I expanded both to their enclosing verbatim statement text. This changed neither the split nor its dependencies. Every quotation now has at least 40 characters and is checked as a literal substring by the construction helper; the dry run is repeated below.
