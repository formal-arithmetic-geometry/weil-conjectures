# Worker report: lem-sf-complete-residue-cohomology-bounds

## Files written

- `dag/nodes/sec-six-functors/lem-sf-complete-residue-cohomology-bounds.json`: statement; split into seven steps; Mathlib searches find no exact match or one-line specialization. No new nodes and no Mathlib leaves.
- `citations.json`: one verbatim statement excerpt for every citation of every proof step.
- `searches.jsonl`: actual searches recorded by the prescribed `msearch.py` command. `prepare.py` is a sandbox-only preparation script, not a delivery file.
- `report.md`: this report.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id, complete/residue/cohomological-bound combinations, and derived-complete/residue/Tor-amplitude notions found no project declaration stating the entire item. The completed-category code and constructible reductions found in SixFunctors impose different categorical or constructibility hypotheses and do not give this arbitrary-complete-complex theorem. No upstream-master sorry is treated as a finished proof.

## Wanted literature

None. The source and the auxiliary source passages are present locally.

## Problems found and corrections

The shared repository's `dag/nodes/` had no file for the assigned id, and `tools/blueprint_refs.py ancestor` consequently printed `None`. The launcher's synchronized read-only DAG mirror `/home/ubuntu/weil-nt-live-dag/nodes/sec-six-functors/lem-sf-complete-residue-cohomology-bounds.json` does contain the assigned unsplit node, created by Q48 on 2026-10-16 below `lem-fix-residue-lisse-projective-models`. I copied that exact file to the sandbox rather than inventing a statement or ancestry. The shared checkout contains its ancestors, chapter, unit and all cited nodes. The existing blueprint ancestry and unit have been retained. The required delivery tool fetches its own current base; no worker git operation or live write was made.

No statement dispute and no statement change. The item does not assume constructibility, local constancy, Noetherianity of X, an invertibility condition on X, or an a priori bound on K. None is used in its proof. Quasi-compactness is retained even though the given uniform interval makes it unnecessary for this specialized argument. This is a consequence of the proof of Stacks 09C2(1),(2), rather than an application of that lemma's full statement, which assumes constructibility. The proof uses the DVR quotient filtration directly over the completed sheaf B_X and therefore needs neither a blanket identification of completed and constant coefficient categories nor a new lemma for that identification. The source's general finite-Tor amplification is replaced only by its explicitly written principal-DVR induction, below the existing unit's route.

In particular I did not cite `lem-coef-integral-residue-tor`: its statement requires a constructible integral object, a finite-field datum and invertibility, so it cannot justify this item's more general setting. I also did not cite `lem-pod-dvr-complex-amplitude-mod-uniformizer`: that statement requires bounded finite-generated ordinary R-module cohomology. These are not duplicates of this item. Existing generic K-flat, triangle, cohomology and pro-etale limit nodes supply all non-elementary inputs.

## Blueprint and Mathlib searches

Read `dag/chapters/sec-six-functors.json`, `dag/units/sk-rem-sf-pf-done.json` and the main-20261015 proof of `lem-fix-weil-operations`. The item's ancestry identifies the evaluation sentence in the exceptional-adjoint paragraph through `lem-fix-constructible-tensor-completion` and `lem-fix-residue-lisse-projective-models`. The synchronized latter split explicitly uses this item to bound the complete object before its residue-basis induction. This is supporting homological algebra, not a replacement of a projection-formula or exceptional-adjunction unit step; the unit has no steps or theorem of resolutions/limits to realize here.

Searched the whole blueprint with `tools/blueprint_refs.py search 'cohomological bounds'` and `... search 'residue'`, and searched DAG statements and source tags (09C2, 099I, 0947, 0990, 093M and the ideal-filtration lemma). The other residue bounds impose the extra hypotheses described above. `same_as` remains empty. No new node was created, so there are no new-node duplicate pairs.

Ran the following actual Mathlib searches through `msearch.py`, read the returned hits, and appended the exact log records with verdicts to the item's inherited search list:

- LeanFinder: "A derived complete proetale sheaf complex whose residue reduction has Tor amplitude in a fixed interval has cohomology in the same interval". Hits express ordinary derived-category t-structure bounds, without derived completeness or the reduction comparison.
- Loogle: `"DerivedCategory", "complete"`. Zero hits.
- Grep: `derived.?complet|complete.*cohomology|cohomology.*complete`, CategoryTheory. Zero hits.
- LeanSearch: "Derived adic completeness and finite Tor amplitude modulo a uniformizer imply cohomological bounds". Hits concern ordinary adic completion and completeness of modules/rings.
- Second LeanFinder phrasing: "The Milnor exact sequence bounds a derived complete complex over a discrete valuation ring by the cohomology interval of its reduction modulo the uniformizer". Hits include period rings, finite-module adic exactness and cotangent exact sequences; none supplies the asserted pro-etale sheaf-complex bound.
- Second source grep: `derived.?complet|complete.*cohomology|cohomology.*complete|[Mm]ilnor`, Algebra/Homology. Zero hits.

All services returned successfully. No search is recorded as run unless it occurs in this sandbox's search log. Historical search records of the assigned node are preserved rather than attributed to Q38.

## Review by Q38

I read Stacks `proetale.tex`, Tag 09C2, label `lemma-describe-constructible-complexes`, including its whole proof, and `sites-cohomology.tex`, Tag 0942, label `lemma-bounded`, and Tag 0947, label `proposition-enough-weakly-contractibles`, including their proofs. The source obtains uniform finite-level bounds, then uses surjectivity of the top cohomology maps to remove the possible degree added by the derived limit. The item isolates precisely this boundedness argument without the constructibility conclusions. I also read proetale Tag 099Q and algebraization Tag 099I; they corroborate the origin but are not invoked as unqualified theorems about this completed-coefficient object. There are no new nodes whose source needs a separate audit.

Step 1 uses only the Tor-amplitude test against the coefficient sheaf itself and the derived tensor unit. I opened `def-weil-proetale-tor-amplitude` and `def-weil-derived-tensor`; their statements give that test and its K-flat tensor interpretation. Taking V=X is explicitly allowed by the item's quantified hypothesis. The equality P tensor k = P verifies the unit identity, hence the residue base case. This step does not assume that cohomology being locally constant over k makes a site complex perfect.

Step 2 uses the statement of `lem-pc-kflat-resolution`, which explicitly produces flat terms as well as K-flatness on any ringed site, and the computation clause of `lem-pur-derived-change-of-rings`, which is stated for any morphism of ring sheaves. I read sites-cohomology Tags 06YS (`lemma-K-flat-resolution`) and 06YY (`lemma-derived-base-change`). They apply with the actual nonconstant ring sheaf B_X and each projection B_X to C_n. Fixing one resolution makes all quotient maps strict and canonical. A result restricted to constant coefficients would not suffice here; I did not use one for this computation.

Step 3 is an explicit coefficient calculation, not a new lemma or a hidden invocation of flatness of B_X. I read the coefficient-extension definition: R is a DVR and the uniformizer is nonzero, so cancellation makes multiplication by varpi^n injective from R/varpi to R/varpi^(n+1). Its image is the quotient kernel, and the quotient is surjective. Constant-sheaf sections and equalities are locally represented by coefficient elements; this gives the same kernel and local lifting calculation after sheafification, using the constant-sheaf definition read in full. The B_X action on the kernel is checked by reducing its (n+1)-component modulo varpi, so the sequence is exact in B_X-modules, the category needed in the next step. This argument needs no exactness of global sections and no geometric stalk conservativity on the pro-etale topos.

Step 4 uses flatness in exactly the sense stated by `def-pc-flat-sheaf-modules`: tensor preserves the short exact coefficient sequence. I opened `lem-weil-pbc-complex-ses-triangle`, whose statement is about degreewise short exact sequences in any abelian category, and `lem-sf-derived-homology-long-exact`, whose statement supplies the displayed exact cohomology segment for any distinguished triangle. Derived Categories Tag 0152 (`lemma-derived-canonical-delta-functor`) and the cohomology discussion around Tag 05RS justify these interfaces. The triangle's second arrow is the original quotient transition, so the surjectivity proved next belongs to the correct tower. The argument never assumes tensoring by K is underived exact.

Step 5 writes the induction rather than citing its desired conclusion as another node. Its base is the bounded residue of Step 1, and the exact segment of Step 4 gives the induction step because both adjacent degree-j sheaves vanish outside the interval. The separate top-degree segment ends in H^(b+1)(K_1)=0, so its transition is epimorphic. There is no circular assumption that K is bounded or that reductions are already normalized in some stronger constructible category.

Step 6 uses the statement of `det-pe-milnor-sequence`, which is explicitly for arbitrary sheaves of rings on a pro-etale site and arbitrary towers of their complexes, not only constant finite coefficients. I opened its main-20261015 blueprint file as well as its JSON statement; the Milnor sequence agrees with Stacks 0947(7). Completeness refers to the same quotient tower as Step 2. I separately cite only clause 1 of `lem-weil-derived-limit-existence`, whose statement makes any two derived limits isomorphic, to pass from the cone model to the derived limit provided by the hypothesis. I do not infer a canonical isomorphism, and I do not use that node's clauses imposing enough injectives or exact products.

Step 7 checks every exceptional degree explicitly. For j<a and j>b+1 both relevant towers are zero. For j=b+1 only R^1 lim H^b(K_n) could remain. I opened `det-pe-milnor-epimorphic` and its main-20261015 source file; its statement kills this first derived limit under exactly the epimorphic-transition hypothesis proved in Step 5, for ring sheaf B_X. This is the same endpoint calculation as the proof of 09C2(1). No assumption that arbitrary inverse limits are exact was substituted.

The off-unit statement tools are declared individually in `split_report.tool_uses`, with their precise uses. They are generic resolution, triangle and limit facts, not replacements for the unit's reference route. The argument is carried by the item's own steps, with zero new nodes; thus neither a clause nor the whole item has been relabelled as a child. I checked the transitive dependencies of all seven cited statement tools against the combined shared/mirror DAG: none reaches the item, so these edges do not create a cycle.

For edge cases, X empty has all sheaves zero and the proof still applies; K=0 does too. When a=b, the induction leaves one degree and the same top-surjectivity argument eliminates degree b+1. The first nontrivial quotient step n=1 is 0 to R/varpi to R/varpi^2 to R/varpi to 0, so no n=0 term or injectivity of multiplication on the quotient ring itself is being assumed. An unbounded K is allowed until Step 7. As a check that completeness is essential, a nonzero varpi-inverted module has zero residue reduction but is not the limit of its (zero) reductions. For residue K_1=0, the same induction makes every K_n zero and completeness then kills K. No constructibility, finite generation of cohomology, finite-dimensional scheme or characteristic restriction enters these checks.

I checked delivery-errors B through E against the written files: no new-node form/search/duplicate obligations arise; all statement notions remain cited or defined inline; TeX uses single logical backslashes; source places use verified labels/tags; every non-elementary step cites an existing statement that gives its input. `citations.json` copies those statements verbatim, including the exact clauses just discussed. I corrected the potential category mismatch by keeping B_X throughout, and corrected the potentially missing b+1 endpoint by proving top-transition surjectivity before using Milnor. The statement itself needed no correction.

## Unfinished work

No mathematical part of this one-level split remains. This worker does not deliver; the fresh second reader must review the accepted sandbox and push it.

## Validation

Required command: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q38 lem-sf-complete-residue-cohomology-bounds --no-push`. Its output is saved as `dry-run.log` in the sandbox. The worker answers READY only after this command prints OK. No push, Lean write or compiler invocation is part of this delivery.

## Second reading by Q38

- Item statement: checked against `proetale.tex` Tag 09C2, `sites-cohomology.tex` Tags 0942 and 0947, and the cited definition nodes; the DVR, completed coefficient sheaf, derived-completeness, residue Tor-amplitude, and conclusion are present with no added constructibility or finiteness hypothesis. Verdict: pass.
- Step 1: checked `def-weil-proetale-tor-amplitude` and `def-weil-derived-tensor`; taking the final site object and the coefficient sheaf gives the asserted residue cohomology vanishing. Verdict: pass and elementary.
- Step 2: checked `lem-pc-kflat-resolution` and `lem-pur-derived-change-of-rings`; their statements give one flat-term K-flat representative and compute every quotient with the same strict transition maps over (B_X). Verdict: pass.
- Step 3: checked `def-weil-l-adic-coefficient-extension` and `def-weil-pbc-constant-sheaf`, and Tag 0942; cancellation in the DVR and local sheaf lifting give the exact (B_X)-linear sequence (0\to k_X\to C_{n+1}\to C_n\to0). Verdict: pass and elementary.
- Step 4: checked `def-pc-flat-sheaf-modules`, `lem-weil-pbc-complex-ses-triangle`, and `lem-sf-derived-homology-long-exact`; flat tensoring gives the degreewise short exact sequence and exactly the displayed cohomology segment. Verdict: pass.
- Step 5: checked the induction against Tag 0942 and the exact segment from Step 4; it proves all finite-level vanishings and epimorphic top-degree transitions, including (a=b). Verdict: pass and elementary.
- Step 6: checked `det-pe-milnor-sequence`, `def-weil-derived-limit`, and clause 1 of `lem-weil-derived-limit-existence`; the tower starts at (n=1), reindexing is harmless, and completeness identifies the cone limit with (K) up to an allowed noncanonical isomorphism. Verdict: pass.
- Step 7: checked `det-pe-milnor-epimorphic` and Tag 0947; degrees below (a), above (b+1), and the possible (b+1) derived-limit term are all handled, with the latter killed by the proved epimorphisms. Verdict: pass.
- New nodes: none; therefore B1--B7, duplicate searches, and new-node source audits have no applicable entries. Verdict: pass.

I independently checked the zero complex, the empty scheme, (a=b), the first quotient (n=1), and a zero residue reduction. The proof remains valid in each case; a nonzero varpi-inverted module confirms why derived completeness is needed. I also verified every citation quote is a verbatim substring of its cited node statement and that no cited dependency reaches the item, so the DAG is acyclic.

Changes made by this second reading: appended this review only. No node, statement, proof step, citation, search record, or dependency required correction.
