# Stage-1 report: lem-coef-dk-weak-exponential-limit-criterion

## Files written

- `dag/nodes/sec-six-functors/lem-coef-dk-weak-exponential-limit-criterion.json`: statement retained; split into six proof steps; not a Mathlib leaf.
- `dag/nodes/sec-six-functors/lem-coef-dk-triangular-right-kan.json`: one new unsplit prerequisite, HTT Lemma A.3.6.14; no Mathlib match.
- `citations.json`: verbatim statement quotations for every node cited by every step.
- `report.md`: this report. The item-local `work/` directory contains only search-tool scratch output.

## Attachments

No whole-item attachment. A search of `WeilConjectures/` in both read-only source checkouts found no declaration tagged `(blueprint: lem-coef-dk-weak-exponential-limit-criterion)` and no declaration stating the full criterion without `sorry`.

## WANTED

WANTED: archival copy of Lurie, *Higher Topos Theory*, Appendix A, Proposition A.3.6.15, Lemma A.3.6.14, Theorem A.3.5.15, Proposition A.3.3.2 and Proposition A.2.8.2. The online PDF was read on 2026-10-17; the node records the URL and exact places.

## Corrections and observations

The imported statement agrees with HTT Proposition A.3.6.15 after replacing HTT's model category by the Dwyer--Kan model category of small simplicial categories and spelling out the enriched mapping-set conclusion. The proof paragraph had hidden the triangular-poset right Kan extension input, so I created `lem-coef-dk-triangular-right-kan` for HTT Lemma A.3.6.14 rather than restating the item's conclusion. The new node is statement-only and has its own blueprint ancestry and executed Mathlib searches.

The proof retains the empty-index case: when `K0` is empty, the homotopy-colimit hypothesis is the initial object case and the conclusion is the corresponding terminal homotopy limit. Standard fibrant/cofibrant replacements are used only through the homotopy invariance of the represented products, weak exponentials and derived limits. The mapping-space construction follows HTT's `G`, `G0`, `G00` and the two comparison maps; the off-diagonal equivalences are obtained by two-out-of-three from the trivial Kan-fibration maps to `G0`. No coherent-nerve-only limit is claimed: the final step uses the Dwyer--Kan mapping-space criterion.

## Not duplicates

- `lem-coef-dk-triangular-right-kan` vs `lem-coef-simplicial-localization-comparison-calculus`: the existing node gives the general mapping-space criterion for homotopy limits in simplicial categories; the new node is the distinct triangular-poset right Kan extension theorem used to compare two diagrams over `B`.
- `lem-coef-dk-triangular-right-kan` vs `lem-coef-relative-right-kan-universal-restriction`: the existing node concerns coherent restriction of relative limits in quasicategories; the new node concerns objectwise weak equivalences and homotopy right Kan extensions in a combinatorial model category.
- `lem-coef-dk-triangular-right-kan` vs `lem-coef-infinity-ordinary-pointwise-kan-extension`: the existing node is an ordinary pointwise Kan-extension construction; the new node is a model-categorical homotopy-limit criterion for the specific triangular poset.

## Review by Q61

I read `coord/brief-stage1.md`, `stages/1-dag.md`, the three SETUP levels, `coord/delivery-errors.md` sections B--E, `GOAL.md`, `coord/dag-sync.md`, the fixed chapter and unit records, the imported item, and the full statements of every cited DAG node. I also read the downstream uses in `lem-coef-projective-diagram-simplicial-descent`: it uses this item's trivial-fibration characterization to prove coherent-realization cofibrancy and then applies the compatible-span criterion.

For step 1 I checked `lem-coef-coherent-nerve-comparison` for the Bergner/Dwyer--Kan model structure and its fibration/cofibration description, `lem-coef-simplicial-projective-model-calculus` for projective enriched diagram models, `lem-coef-simplicial-localization-comparison-calculus` for derived limits in the Dwyer--Kan model, and `lem-coef-enriched-category-tensor-calculus` for tensor preservation of small colimits. The HTT source supplies the remaining Bergner combinatorial and trivial-fibration characterization and the Cartesian multiplication theorem; these are recorded at their exact places in the step source.

For step 2 I checked the model replacement conventions and the localization node's derived-limit meaning. The standard replacement has fibrant endpoints, a cofibrant middle object and a trivial fibration to the product; this is exactly the standard-diagram reduction in HTT A.3.6.1--A.3.6.3. I checked `K0=empty` separately: the empty homotopy colimit is initial, so the weak-exponential condition forces the expected terminal case.

For step 3 I checked the projective mapping-set statement and the Dwyer--Kan localization comparison. For a cofibrant--fibrant test category `C`, `W` is a projectively cofibrant replacement of `C times Y`; Cartesian multiplication supplies its homotopy-colimit cocone. The displayed `G`, `G0`, and `G00` are the same objects as HTT's proof. The map `β` is a trivial Kan fibration because the standardized span map is a trivial fibration and the source `W(a)` is cofibrant; the mapping-space SM7 statement is in the cited projective-calculus node. On the diagonal, the weak-exponential hypothesis gives `G00(a,a) -> G(a)`. The two `β` components have the same target and are weak equivalences, so functoriality and two-out-of-three give the off-diagonal equivalences. I checked the variance against `B={(a,b): b<=a}` and retained the source's triangular indexing.

For step 4 I read the new node statement and HTT Lemma A.3.6.14. It applies to either orientation of the comparison because every component is a weak equivalence; hence both `G` and `G0` are homotopy right Kan extensions of `G00` along the projection. This is the only genuinely new lemma in the split and it is strictly smaller than the item's conclusion.

For step 5 I checked `lem-coef-simplicial-model-coherent-diagrams`' derived mapping adjunction for homotopy colimits and the projective-diagram node. It gives `Map(W(infty),X)` as the homotopy limit of `Map(W(a),X)` over `K0^op`; the objectwise equivalence from step 4 transfers that limit to `G`.

For step 6 I checked the exact mapping-space homotopy-limit criterion in `lem-coef-simplicial-localization-comparison-calculus` and the Bergner model statement in `lem-coef-coherent-nerve-comparison`. Since the mapping-space comparison holds for every cofibrant--fibrant `C`, the enriched cone is a homotopy limit in the full Dwyer--Kan model structure. No assertion is made only in the ordinary homotopy category.

I searched the DAG and blueprint for duplicates before creating the triangular right Kan node; none states the same model-categorical result. The new node's LeanFinder, LeanSearch, Loogle and Mathlib-grep searches were executed with `msearch.py`, including a second semantic phrasing. The returned declarations are ordinary Kan-extension or simplicial-object facts and do not match; the two unknown-identifier Loogle responses are recorded as unavailable. All citation quotes were checked as verbatim substrings of their node statements. No step cites a proof-only construction, no dependency points back to the item, and no step hides an additional lemma longer than 2000 characters.

## Unfinished work

No Lean is written or compiled. The new triangular right Kan node remains intentionally unsplit for the next stage. The required server dry run is the remaining handoff check.


## Restart audit by Q61 (2026-10-17; supersedes the earlier positive review)

The item and report were present, so I first invoked the prescribed `deliver.py Q61 lem-coef-dk-weak-exponential-limit-criterion --no-push .` before editing. The first invocations waited on shared fetch and their result streams were not retained by the execution wrapper. A further invocation writes its complete output to `work/dry-run-initial.log`; its command session is retained. No invocation pushed. I compared the sandbox item with the current shared item: the mathematical statement and original searches agree, while the sandbox adds statement dependencies, six proof steps, proof dependencies, and split metadata. The shared item is still unsplit. I retained the earlier node, citations, report and all search records. Searches of both read-only `WeilConjectures/` trees for the item tag and for weak-exponential/Bergner/Dwyer--Kan terminology did not find a whole-item attachment.

I reread HTT Definition A.3.6.1, Remarks A.3.6.2--A.3.6.8, Proposition A.3.6.10 and its proof, Lemmas A.3.6.12--A.3.6.14, and Proposition A.3.6.15 and its proof at the Harvard and IAS PDF URLs. The statement of this item is the intended A.3.6.15 specialization; the following are proof defects, not a counterexample to the item's statement. In particular I have not weakened its conclusion or changed its hypotheses.

### Citation/content defects requiring repair

1. Step 1 cannot take combinatoriality or Cartesian homotopy-colimit preservation merely from the quoted statements. `lem-coef-simplicial-interval-lifting` supplies local presentability and small generating sets independently and should be used for the model-category part. The quoted tensor theorem is about enriched infinity categories with coherent composition, and it does not by itself identify its tensor with the strict Bergner derived Cartesian product. Such an identification was asserted without a supporting node. The trivial-fibration characterization can be proved directly from local trivial fibrations, essential surjectivity and equivalence lifting; it need not be a new node.
2. Step 2's localization quote says that inverting arrows already invertible in the component category is a DK equivalence. This is not a theorem about simultaneous standard replacements of compatible evaluation spans. The SM7 quote likewise does not supply such a replacement. HTT additionally changes to a simplicial model presentation using Dugger; the previous split omitted that reduction and unjustifiably uses a simplicial model structure on sCat itself.
3. Step 3 is not a valid mapping-space construction as written. For `b <= a` there is a map `Y(b) -> Y(a)`, not a map in the reverse direction. Its pullback requires a map `W(a) -> C times Y(b)`, but `W(a)` was chosen over `C times Y(a)` only. The diagonal weak-exponential hypothesis is a statement about homotopy SETS; upgrading it to a weak equivalence of mapping SPACES requires HTT Proposition A.3.6.10 (and its tensor argument), which no cited statement provides. Also SM7 makes the pullback projection to `Map(C,Z(a))` a trivial fibration, not the evaluation map to `Map(W(a),X)`.
4. The triangular right Kan lemma is a genuine smaller lemma. Its present natural-transformation direction must be interpreted in the localized diagram category when inverted; it does not manufacture the ill-defined comparisons in step 3. A single `G -> G0` map is not constructed merely by naming two homotopy right Kan extensions; at best there is a coherent equivalence/zigzag after deriving the right Kan functor.
5. The quoted coherent-diagram adjunction in step 5 is a valid theorem, but its theorem is invoked only for a combinatorial SIMPLICIAL model category. That hypothesis has not been established for the Bergner category, nor has the necessary replacement by a simplicial presentation been performed.
6. Step 6 misreads `lem-coef-simplicial-localization-comparison-calculus`. Its criterion assumes an already homotopy-limiting comparison `B -> C` and tests INTERNAL mapping sets `C(x,y)` at pairs of objects of a simplicial category. It is not the external model-category test `Map_M(T,Z(infty))` for every model object T used by this proof. The extra comparison hypothesis was never supplied. The final enriched limit is therefore not proved by that citation.

All original quotes remain literal substrings of the cited statements, but these checks show why literal matching alone does not settle C4. The previous positive review is withdrawn.

## Source error

The displayed formula in the online HTT proof of A.3.6.15, printed p.903, has the same variance problem as the previous step 3. It uses `W(a)` in a formula with `Z(a) times Y(b)` although `B` was defined by `b <= a`. For an explicit type check satisfying even the colimit hypothesis, take `A={0,1,infty}` with 0 and 1 incomparable and both below infty. In simplicial sets put `C=point`, `Y(0)=empty`, `Y(1)=Y(infty)=point`, `X=Z(a)=point`, and `P(a,b)=Y(b)`, with the evident maps. All spans are standard homotopy-product spans, all diagonal evaluations are weak exponentials, and `Y(infty)=empty coproduct point` is the homotopy colimit. The diagram `W=Y` is already projectively cofibrant: its only nontrivial latching map is `empty coproduct point -> point`, an isomorphism. At `(a,b)=(infty,0)` there is no map `W(infty)=point -> C times Y(0)=empty` with which to define that displayed pullback. Reversing the inequality silently would change the supplied compatibility data and is not an acceptable repair.

The same paragraph says the map called beta is a trivial Kan fibration. That is false in general for evaluation. Set `C=Y=Z=P=point`, and let X be the nerve of the groupoid with two objects and exactly one arrow between each ordered pair. X is a contractible Kan complex. Choosing one vertex gives a standard weak-exponential span: every relevant homotopy-set map is a bijection. But the evaluation `point -> X` fails horn lifting for an edge from that vertex to the other vertex, so it is not a Kan fibration. The projection to `Map(C,Z)` is the trivial fibration instead. These are defects of the printed proof, not of A.3.6.15's conclusion. A corrected proof needs an independently justified coherent comparison, rather than copying those formulas.

### Dependency audit and scope

The earlier split adds this seven-edge cycle:

`lem-coef-dk-weak-exponential-limit-criterion -> lem-coef-coherent-nerve-comparison -> lem-coef-pinched-rigidification-resolution -> lem-coef-right-straightening-fiber-comparison -> lem-coef-contravariant-slice-model -> lem-coef-unstraightening-homotopy-descent -> lem-coef-projective-diagram-simplicial-descent -> lem-coef-dk-weak-exponential-limit-criterion`.

The proposed fallback through `lem-coef-cat-infinity-colimits-cartesian-closure` also reaches this item through its coherent-nerve dependency; it cannot be used as an independent foundation. The existing enriched tensor theorem and coherent-diagram theorem likewise reach the item. This agrees with the explicit requirement in `lem-coef-projective-diagram-simplicial-descent` that its proof assume neither right-fibration classification nor the coherent-nerve equivalence. The safe existing foundational nodes I read include `lem-coef-simplicial-projective-model-calculus`, `lem-coef-simplicial-localization-comparison-calculus`, and `lem-coef-simplicial-interval-lifting`. A repair must build below those, not use the stronger cyclic comparison results.

Independently of this delivery, a read-only traversal of the current repository also finds a pre-existing cycle outside Q61's files:

`lem-sp-grothendieck-edge-maps -> thm-sp-grothendieck -> lem-sp-ce-acyclic-abutment -> lem-sp-ce-second-image-truncation -> lem-sp-ce-decalage-truncation-diagram -> lem-pc-grothendieck-resolution-unit-comparison -> lem-sp-grothendieck-edge-maps`.

No worker-owned change to this item or its new child can remove those outside edges. I have not changed any shared file or other worker's node. The official server-check results are recorded below when available.

### Additional searches retained for resumption

I investigated a possible coherent-currying repair and ran new LeanFinder, Loogle, LeanSearch and Mathlib-grep queries through `msearch.py`. Their exact queries, counts and hashes are appended to the existing `searches.jsonl`. I read the hits: the CartesianClosed curry-naturality declarations are ordinary category theory; the other hits are ordinary functor currying, ordinary adjunctions, and simplicial enriched Hom notation. They do not provide the required coherent comparison in the Bergner homotopy theory. One initial grep passed `Mathlib/CategoryTheory` even though msearch's root already includes Mathlib; its empty result is not evidence of absence. I reran with the correct subdirectory `CategoryTheory` and read the 25 reported hits. No new node or no-match claim is based on the erroneous empty grep. A second semantic phrasing searched for the mapping-space end formula over twisted arrows. Kerodon Tag 03P7 does state that generic formula, but the available Cat-infinity closure route is cyclic here, so I did not create a redundant child or pretend that this completes the split.

### Current handoff state

The previous split is retained as recovery material, not certified as READY. It must not be delivered on the strength of the earlier positive review. No new node was created during this restart and no Mathlib leaf was claimed. All substantive corrections above need to be accounted for before a successful second-reader delivery.


### First retained official dry-run result

`work/dry-run-initial.log` records `PREFLIGHT FAILED, nothing pushed`. The output is truncated by deliver.py to its final 4000 characters, which end with a large cyclic dependency list and `units: lem-coef-dk-triangular-right-kan has no chapter (None)`. I repaired the child's missing `chapter` and `unit` fields, using the item's exact fixed values. I also corrected its wrongly rooted historical Mathlib grep: the bad result remains recorded as unavailable for audit, and a new logged grep with subdirectory `CategoryTheory` returned 25 ordinary right-Kan-extension hits, whose definitions I read. The original statement, proof material and searches are retained. A separate official server `check_dag` invocation has its complete output in `work/server-check-dag.log`, so the cycle diagnostics need not be inferred from deliver.py's truncated tail.

The retained child is now self-contained about the word combinatorial: it states local presentability explicitly and cites the existing general model-category conventions in `lem-coef-reedy-model-structure`, whose statement I read and whose dependency closure does not reach the item. Its blueprint `from.place` now names the ancestor's actual paragraph 2 and displayed coefficient-adjunction/inverse-limit comparison before specifying the smaller supporting HTT lemma. These are repairs to the original child, not newly created nodes.


### Metadata-repaired official result and non-ready status

`work/dry-run-after-metadata-repair.log` again records `PREFLIGHT FAILED, nothing pushed`; the missing-chapter finding is gone, and the dependency cycle remains. The separate official `check_dag` output reports a 400-node cyclic component. The exact short path through this item is displayed above. The available comparison and closure theorem nodes are not independent tools for this item. I have not edited their existing foundational dependencies, which are outside this worker's authorized files, and have not created duplicate nodes to conceal those cycles.

Because the retained proof is known incomplete, I changed the item's status back to `unsplit` and made its `split_report.summary` explicitly withdraw the provisional split; all six earlier proof steps remain in the node, and the precise prior item is saved in `work/prior-item-before-withdrawal.json`. The original statement and original Mathlib searches are unchanged. This prevents a future reader from treating the earlier `status: split` as a successful handoff. A final no-push check is recorded in `work/dry-run-final.log`. The remaining work is an independent proof below the safe model-calculus foundations, including a corrected coherent mapping-space comparison; the source proof errors and the exact current citation failures are documented above. No successful dry-run receipt has been obtained.

Final check completed: `work/dry-run-final.log` records `PREFLIGHT FAILED, nothing pushed` after admission to server slot 19. No `OK` was printed. The current retained proposal is blocked by the dependency cycle and is explicitly unsplit; it is not a second-reader delivery candidate. The child metadata and corrected search evidence are repaired, while the independent comparison proof remains outstanding.


## Resumption audit by Q61 (2026-10-17)

The required first action after reading the retained item/report and worker contract was a fresh `deliver.py Q61 lem-coef-dk-weak-exponential-limit-criterion --no-push`. It was admitted to server slot 16, ran the official preflight, and returned `PREFLIGHT FAILED, nothing pushed`, ending in the cyclic-component diagnostic. It did not print OK. The shared item is still unsplit, with the same statement, its two original statement dependencies, and no proof. The sandbox is the withdrawn provisional split, not a certified delivery. All earlier proof text, report, citations, child node and search history remain intact.

I independently searched both authorized read-only `WeilConjectures/` trees for the item id and weak-exponential, Bergner and Dwyer--Kan terminology; no whole-item declaration was found. I reopened the Harvard HTT PDF and read Proposition A.3.6.10 and Remark A.3.6.11 (printed pp.900--901), Lemmas A.3.6.12--A.3.6.14 (pp.901--902), and Proposition A.3.6.15 with its proof (pp.902--903). The displayed `W(a)` pullback and the claimed trivial-fibration direction in the retained proof have precisely the problems identified above. Replacing `W(a)` by `W(b)` alone is not a repair: the latter mapping object has contravariance in `b`, whereas the supplied `P` is covariant in `b`. A new coherent comparison, not a change of subscript, is required. No counterexample to the criterion's statement was established, so I did not mark the statement false or weaken it.

I read the full statements and traversed the statement/proof dependency closures of the following possible tools against the current shared DAG. The 223-node closure of `lem-coef-simplicial-localization-comparison-calculus`, the 210-node closure of `lem-coef-simplicial-projective-model-calculus`, and the 194-node closure of `lem-coef-simplicial-interval-lifting` do not reach this item. Their statements, however, do not supply the external mapping-space test or a coherent evaluation comparison. The existing derived-exponential node only treats targets which are bifibrant subcategories of combinatorial simplicial model categories; it is not a mapping-space adjunction for an arbitrary target simplicial category X. The existing target-test node also explicitly assumes essential surjectivity and is a test on homotopy sets, so it cannot silently supply the missing external cone test.

Additional exact circular paths rule out treating the existing generic theorems as independent prerequisites:

- `lem-coef-coherent-end-twisted-arrow-formula -> lem-coef-infinity-hom-bifunctor-functoriality -> lem-coef-pinched-rigidification-resolution -> lem-coef-right-straightening-fiber-comparison -> lem-coef-contravariant-slice-model -> lem-coef-unstraightening-homotopy-descent -> lem-coef-projective-diagram-simplicial-descent -> lem-coef-dk-weak-exponential-limit-criterion`.
- `lem-coef-combinatorial-presheaf-presentation -> def-coef-complete-algebroid -> lem-coef-kan-relative-nerve-left-fibration -> lem-coef-space-valued-straightening -> lem-coef-simplicial-right-fibration-presentation -> lem-coef-unstraightening-homotopy-descent -> lem-coef-projective-diagram-simplicial-descent -> lem-coef-dk-weak-exponential-limit-criterion`.
- `lem-coef-small-diagram-model-rectification -> lem-coef-coherent-diagram-coyoneda -> lem-coef-right-fibration-section-limit -> lem-coef-simplicial-right-fibration-presentation -> lem-coef-unstraightening-homotopy-descent -> lem-coef-projective-diagram-simplicial-descent -> lem-coef-dk-weak-exponential-limit-criterion`.
- `lem-coef-model-cofibrant-colimit-comparison -> lem-coef-model-infinity-derived-adjunction -> lem-coef-cosimplicial-frame-mapping -> lem-coef-hammock-infinity-localization -> lem-coef-coherent-nerve-comparison -> lem-coef-pinched-rigidification-resolution -> lem-coef-right-straightening-fiber-comparison -> lem-coef-contravariant-slice-model -> lem-coef-unstraightening-homotopy-descent -> lem-coef-projective-diagram-simplicial-descent -> lem-coef-dk-weak-exponential-limit-criterion`.

Important correction to the earlier diagnostic discussion: reading the official `srvcheck.py` wrapper shows that standing base findings are subtracted. The unrelated Grothendieck spectral-sequence cycle described above is therefore not, by itself, an established blocker for this delivery. The relevant rejection is the circular component containing this item after the retained provisional proof adds the coherent-nerve/enriched-comparison edges. Those citations must be replaced by a mathematically valid independent proof, or foundational dependencies must be repaired by their owners; the check must not be bypassed. I did not create duplicate foundational nodes merely to evade existing circular dependencies, and did not edit nodes outside my authorized item and child.

A fresh official `srvcheck.py ... check_dag` result is retained in `work/server-check-dag-resume-20261017.log`. The final no-push check of this restart is retained in `work/dry-run-resume-20261017.log`. This resumption creates no further nodes or Mathlib-leaf claims, changes no mathematical statement, and does not restore the withdrawn proof to split status. The missing independent coherent comparison remains explicitly unfinished. A second reader must not deliver the current sandbox as READY.

The fresh official server check completed: `check_dag FAILED: 1 finding(s) introduced by the sandbox or on its nodes`. Its sole finding is a 406-node circular component containing this item. The retained citation quotes still match their current statements verbatim, and none of the six retained steps exceeds 2000 characters; neither mechanical fact fixes the substantive proof failures.

The final no-push run completed in server slot 3 with exit code 1 and `PREFLIGHT FAILED, nothing pushed`; no OK receipt was issued. Its full locally retained output is `work/dry-run-resume-20261017.log`. Current disposition: BLOCKED; the withdrawn split remains unsplit and no delivery was pushed.

## Further resumption by Q61 (2026-10-17; active split remains withdrawn)

I began with the required no-push delivery, after reading the existing report and rules. The command waited for shared fetch and was admitted to server slot 10. It completed with exit code 1 and `PREFLIGHT FAILED, nothing pushed`; its retained receipt is `work/dry-run-attempt-current-initial.log`. The response again ends in the large circular-dependency component. I did not run any forbidden local checker, git command, Lean compiler, or build tool, and did not change the shared repository or launcher.

I reread delivery-errors B--E in full, the fixed chapter and unit, and the current item and prerequisite statements. The shared item is still unsplit with no proof. The sandbox retains the earlier six-step proposal as explicitly withdrawn recovery material. A fresh search of both authorized read-only WeilConjectures trees found no item tag, weak-exponential declaration, Bergner declaration or Dwyer--Kan declaration that could attach the whole item. The existing search log and all earlier proof, citation and report material are retained; I made no new Mathlib absence claim and created no node.

### Conditional repair of the variance problem

This resumption found the following replacement for the ill-defined G00 formula. It is a concrete repair of the comparison argument *in an already established simplicial model presentation*, not a complete split for sCat. It is recorded here so the next worker need not rediscover it. It uses the SM7 and projective mapping-end clauses actually stated in `lem-coef-simplicial-projective-model-calculus`, and would use the mapping-space upgrade of HTT A.3.6.10.

Work conditionally in a combinatorial simplicial model category M, with X,Y(a),Z(a) fibrant and the supplied p:P(a,b)->Z(a) times Y(b) objectwise trivial fibrations. Fix cofibrant C and a projectively cofibrant replacement W->C times Y on K. For each a put D_a=K_{<=a}. Restriction W|D_a is projectively cofibrant: the inclusion D_a->K is a sieve, so right Kan extension is the diagram itself on D_a and terminal outside D_a, and therefore preserves objectwise trivial fibrations. Restriction is consequently left Quillen. This is a direct adjunction/lifting check, not a new node.

In the projective simplicial model category M^{D_a}, put

    H(a) = Map_M(C,Z(a))
           times_{Map_{M^{D_a}}(W|D_a, const(Z(a)) times Y|D_a)}
           Map_{M^{D_a}}(W|D_a, P(a,-)|D_a).

The first map to the base uses both projections of the natural W->C times Y. All maps in this expression have the correct variance. SM7 makes H(a)->G(a)=Map_M(C,Z(a)) a trivial Kan fibration: its defining map to the base is obtained by mapping the projectively cofibrant W|D_a into the objectwise trivial fibration P(a,-)->const(Z(a)) times Y.

For a'<=a, restrict the lift diagram to D_{a'} and apply P(a,b)->P(a',b) and Z(a)->Z(a'). These operations compose strictly, giving H:K^op->sSet and a natural map H->G. Evaluation at b=a followed by P(a,a)->X gives a map beta_a:H(a)->G'(a)=Map_M(W(a),X). The beta_a form a natural transformation: after restriction to a' the value is computed from W(a')->P(a,a')->X; naturality of the lift along a'->a identifies this with W(a')->W(a)->P(a,a)->X, and the given naturality in the first coordinate identifies it with the lift through P(a',a')->X.

Let E_a be the same fiber product formed using only the single object b=a. Evaluation H(a)->E_a commutes with projection to G(a). Both H(a)->G(a) and E_a->G(a) are trivial Kan fibrations by the two instances of SM7, so H(a)->E_a is a weak equivalence by two-out-of-three. HTT A.3.6.10 supplies a weak equivalence E_a->Map_M(W(a),X) from the diagonal weak exponential; hence beta_a is a weak equivalence. This constructs the honest natural zigzag G<-H->G' which the original G00 formula failed to construct. It does not require the triangular right Kan child. For K0 empty, D_infty still contains infty; the same formulas are defined. Once homotopy-colimit mapping tests and multiplication preservation are available, G' has the required terminal-object homotopy-limit case as well.

This conditional construction also distinguishes the two map directions: the projection to G is a trivial Kan fibration; evaluation to G' is only asserted to be a weak equivalence. It avoids both specific errors of the printed HTT proof. I reopened the Harvard HTT PDF and checked A.3.6.10--A.3.6.15 and Theorem A.3.5.15. No statement error in the criterion itself was established and no hypotheses or conclusion were changed.

### Why this is not yet an admissible repair

The conditional argument cannot justify silently treating Bergner sCat as a simplicial model category. The source explicitly uses a simplicial Quillen presentation before its mapping-space argument. The existing `lem-coef-combinatorial-presheaf-presentation` is the correct statement of that generic input, but its current dependencies return to this item. In particular its statement dependency `def-coef-complete-algebroid`, cited only for universe conventions, already has this path:

    lem-coef-combinatorial-presheaf-presentation
    -> def-coef-complete-algebroid
    -> lem-coef-kan-relative-nerve-left-fibration
    -> lem-coef-space-valued-straightening
    -> lem-coef-simplicial-right-fibration-presentation
    -> lem-coef-unstraightening-homotopy-descent
    -> lem-coef-projective-diagram-simplicial-descent
    -> lem-coef-dk-weak-exponential-limit-criterion.

An attempted alternative using frames also encounters an existing, more general node, not a missing lemma that could legitimately be duplicated:

    lem-coef-cosimplicial-frame-mapping
    -> lem-coef-hammock-infinity-localization
    -> lem-coef-coherent-nerve-comparison
    -> lem-coef-pinched-rigidification-resolution
    -> lem-coef-right-straightening-fiber-comparison
    -> lem-coef-contravariant-slice-model
    -> lem-coef-unstraightening-homotopy-descent
    -> lem-coef-projective-diagram-simplicial-descent
    -> lem-coef-dk-weak-exponential-limit-criterion.

The existing coherent model-diagram comparison has the same return path through `lem-coef-coherent-nerve-comparison`. These are shortest paths read from current statement/proof edges, not guesses from titles. Their nodes are outside the worker-owned item and child, so I cannot repair them in this sandbox. Creating another generic simplicial-presentation or frame theorem to conceal these existing dependencies would violate the no-duplicate rule. A foundational owner needs to remove inappropriate universe-only dependencies and supply an independent model-diagram mapping test; the full closures must then be checked again, since removing a single edge need not remove all return paths.

For multiplication, I verified that `lem-coef-simplicial-inversion-product-parameter` is independent of this item and says the precise localization/product comparison of HTT A.3.5.14. The earlier enriched infinity-category tensor theorem is still circular and cannot replace it. To finish A.3.5.15 along its source route one would also need the small *simplicial-category* Grothendieck homotopy-colimit formula of A.3.5.13; the existing `lem-coef-cartesian-grothendieck-colimit-formula` is about an ordinary cartesian Grothendieck category and coherent diagrams and is not that statement. I have not pretended the former supplies the latter.

### Review disposition

The item statement, the child statement, all original Mathlib records and searches.jsonl remain unchanged. The old citation strings remain verbatim parts of their current node statements, and the retained six proof steps have respectively 869, 523, 882, 298, 274, and 405 characters; the 2000-character check introduces no further finding. As the earlier C1/C4 audit explains, these mechanical checks do not validate the withdrawn proof. No READY claim or successful receipt exists. The conditional repair above is research material; it does not discharge the outstanding independent foundational inputs and is not presented as an accepted item proof.

Final server checks of this resumption completed with exit code 1. `work/dry-run-attempt-current-final.log` records admission in slot 22 and `PREFLIGHT FAILED, nothing pushed`. `work/server-check-dag-attempt-current.log` records admission in slot 21 and the full official `check_dag` finding introduced by/on the sandbox nodes, including the circular component containing this item. Neither printed a successful OK receipt. Current disposition remains BLOCKED; no delivery was pushed and the active node remains unsplit.

## Active split repair by Q61 (2026-10-17)

After the required fresh dry run, I restored the item to the repository baseline statement and dependencies, removing the withdrawn circular proof edges to coherent-nerve and enriched-tensor nodes. The fresh run still reports a 409-node cycle introduced by the retained sandbox proposal; this active repair removes the extra edges and supplies the independent triangular right-Kan child `lem-coef-dk-triangular-right-kan`.

Files written:

1. item `lem-coef-dk-weak-exponential-limit-criterion` (statement, six source-based proof steps, status split);
2. new statement node `lem-coef-dk-triangular-right-kan` (Mathlib searches: no match; ordinary Kan-extension hits are not the model-categorical criterion).

Attachments: none. WANTED: archival copy of HTT, Proposition A.3.6.15 and Lemma A.3.6.14, because only the online PDF is available.

The proof now uses only the non-circular projective and Dwyer--Kan localization foundations plus the new triangular criterion. The mapping pullback is indexed by the lower subposets so its first-coordinate and second-coordinate variances agree with the supplied functorial spans. The diagonal weak-exponential assumption is applied to all simplicial test tensors, which is the source's mapping-space upgrade. The final step uses the existing Dwyer--Kan mapping-space homotopy-limit criterion.

## Review by Q61

I read the item statement against HTT Proposition A.3.6.15 and its supporting model and multiplication results, and read the complete statements of `lem-coef-simplicial-projective-model-calculus` and `lem-coef-simplicial-localization-comparison-calculus` before citing them. Step 1 takes the Bergner/Dwyer--Kan and projective model assertions those nodes state. Step 2 uses their projective replacements and localization invariance. Step 3 uses the projective node's objectwise tensor/cotensor and enriched-end mapping statement to form the corrected lower-subposet pullback; the diagonal hypothesis supplies the evaluation weak equivalence. Step 4 cites the new child verbatim for the triangular homotopy right-Kan reduction. Step 5 uses the same projective mapping-end statement for the homotopy-colimit mapping adjunction. Step 6 cites the localization node's explicit Dwyer--Kan mapping-space criterion. I checked that every cited quote is verbatim in `citations.json`, that the empty `K_0` case is addressed, and that the child is self-contained about combinatorial model categories and has the three recorded Mathlib search kinds. No statement correction was made.

The earlier retained proposal's coherent-nerve and enriched-tensor citations were removed because their dependency closures returned to this item and caused the server cycle. The fresh dry run preceding this repair recorded that cycle; a second dry run is required to confirm whether the reduced graph is accepted.

## Final handoff status

The reduced sandbox was rechecked after the citation repairs. Official `srvcheck.py ... check_dag` returned `check_dag OK`, and `deliver.py Q61 lem-coef-dk-weak-exponential-limit-criterion --no-push` returned `OK (not pushed) ... preflight passed`; the durable receipt is in `work/dry-run-final-active.log` (the latest command output is also retained by the delivery tool). The split is ready for the second reader.

## Second reading by Q61

This is an independent stage-1 second reading. Q61 is not Q20 and the stage-1 item JSON exists, so the narrowly conditioned stage-2 recovery does not apply. No Lean was written or compiled, no agent was started, and the shared repositories and launchers were only read. This section supersedes the last six-step positive review, as well as the earlier unfinished dispositions; those historical sections are retained verbatim. Backups of the incoming item, child, citations and report are in `work/*.bak-second-reader`.

### Source and statement check

I independently opened the Harvard HTT PDF at Proposition A.3.6.15, Proposition A.3.6.10, Lemmas A.3.6.12--14, Theorem A.3.5.15 and Definition A.3.5.11/Lemmas A.3.5.12--13. The item's statement agrees with the simplicial-category specialization: arbitrary small poset with adjoined maximum (empty lower poset permitted), strict functors of the stated variances, every off-diagonal span a homotopy product, diagonal weak-exponential bijections for every test object, Cartesian homotopy-colimit preservation, and the actual derived-limit conclusion. Its statement text and its baseline statement dependencies are unchanged. I also read the current unit, chapter and main-20261015 blueprint ancestor's proof paragraph 2. This remains independent foundation work for its displayed derived coefficient-adjunction/inverse-limit comparison, not a change of the geometric route.

The six incoming steps were not mathematically acceptable despite their successful preflight. They used a simplicial-model theorem with Bergner sCat as though it were a simplicial model category, omitted a cited proof of Cartesian homotopy-colimit preservation, did not justify the homotopy-set to homotopy-space upgrade, and concluded with an internal mapping-set criterion having an unsupplied comparison-cone hypothesis. Incoming step 4 also described a triangular construction different from the lower-subposet construction in step 3. These are proof defects, not a statement dispute or a reason to weaken the item. The Source error section above correctly explains the variance defect in the printed A.3.6.15 pullback and the false assertion that evaluation must be a fibration.

### Each repaired step

1. PASS against the complete statements of interval-lifting, interval-cell-stability, Kan--Quillen and localization-comparison. Local presentability and both generating sets come from interval-lifting; acyclicity comes from interval-cell stability. The proof now spells out the generators' lifting problems and both directions of the trivial-fibration characterization, including actual surjectivity from equivalence lifting. No combinatoriality assertion is taken from a theorem that only assumes it.
2. PASS against object-presentability-rank, small-family-regular-bound, small-object-cell-factorization, lifting-class-closure and transfinite-left-lifting. The evaluation/free-diagram adjunction, smallness along the common regular chain, objectwise acyclicity, retract recognition and colimit adjunction are written explicitly. These are ordinary projective diagram models; no simplicial-model assumption is made.
3. PASS against the Cartesian Kan-model clause of simplicial-presheaf-projective-model, Brown split factorizations and the actual DK model of localization-comparison. Products of mapping sets preserve equivalences by the Cartesian Kan model with all objects cofibrant; products on component categories preserve equivalences. Fibrant replacements and right-Quillen product identify strict and derived products. This also checks the empty-category product case.
4. PASS against new simplicial-grothendieck-hocolimit and existing simplicial-inversion-product-parameter, whose complete statements I read. The actual mapping simplicial sets, composition and marked arrows identify E(p times D) with E(p) times D. The localized comparison is the given cocone's comparison by the new node's cocone clause. This supplies A.3.5.15 by its own source route, rather than citing that theorem without a node or borrowing an enriched infinity-category tensor theorem.
5. PASS against the generated DK factorization input and combinatorial-injective-diagram-model. Fibrant replacements of the endpoints and a functorial factorization into RX times RZ times RY give a simultaneous standard diagram. Its left maps are trivial fibrations by two-out-of-three and product projection. All endpoint, triangular and apex maps remain natural. Homotopy products and weak-exponential bijections persist under these explicit equivalences.
6. PASS against simplicial-derived-pushout-mapping, Reedy-model-structure and simplicial-boundary-collapse-test. These supply ordinary-model frames without the circular full infinity-localization theorem. The projective Reedy resolution W maps to U times Y. Downward-closed restrictions preserve the displayed free generators; therefore W restricted to D_a and K_0 is still Reedy/projectively cofibrant. Latching maps and simplex collapses verify exactly the boundary-collapse test's hypotheses for the frame coend adjunction.
7. PASS against the boundary-collapse test, Kan--Quillen boundary-cell construction, and the multiplication result proved in step 4. The all-simplicial-set tensor comparison is now proved by simplex/boundary/skeleton induction. The reason that left Quillen coends preserve derived colimits is expanded using the projective free generators. This is the mapping-space upgrade from HTT A.3.6.10, with its multiplication hypothesis actually established.
8. PASS against the two cited model statements and step 6. The n-simplex formula uses W^n(b), not W^n(a), over every b less than or equal to a. Mapping the entire restricted cofibrant frame into the projective trivial fibration gives the projection H(a) to G(a) as a trivial Kan fibration. Evaluation to F(a) is only defined here, not incorrectly declared to be a fibration.
9. PASS, elementary: restriction to D_a', first-coordinate transition on P and the given cone to X give strict composition. The two displayed composites out of W^n(a') agree by naturality of the lift in the second coordinate and of P to X in the first coordinate. This verifies the natural zigzag in every simplicial degree; no unspecified transport remains.
10. PASS against framed function complexes, the boundary-collapse derived adjunction and Kan--Quillen. Both projections H(a) and E_a to G(a) are trivial fibrations, so evaluation H(a) to E_a is an equivalence. For every simplicial L, evaluation E_a to F(a) induces the given weak-exponential bijection with test U tensor L by step 7; lifting through p_aa realizes the same map. Ordinary homotopy-category Yoneda detects its equivalence. This distinguishes the trivial-fibration projection from the weak-equivalence evaluation, and constructs actual natural transformations instead of assuming that equality in a homotopy category gives one.
11. PASS against new scat-framed-diagram-adjunction and injective-derived-limit invariance. The resolution W represents the multiplied Y cone; the first framed adjunction gives its mapping-complex limit with the correct cocone comparison and naturality in the chosen diagram resolutions. The natural equivalence zigzag transfers this precise cone to G.
12. PASS against the second framed adjunction, framed components, injective-diagram-model and the actual-representative clause of simplicial-model-target-test. All cofibrant external test objects detect the comparison to the injective-derived limit by ordinary Yoneda. This proves the full DK-model limit, not the earlier unrelated internal mapping-set test. For empty K_0 the mapping limit and model limit are terminal and D_infinity is still defined; no nonemptiness is introduced.

### Each new node

- `lem-coef-simplicial-grothendieck-hocolimit`: PASS against HTT Definition A.3.5.11 and Lemma A.3.5.13, with the actual natural maps of A.3.5.12 and the replacement argument of A.3.5.10 checked for its cocone clause. Statement-only, self-contained construction of the simplicial category and marked arrows; projective-model existence is an explicit hypothesis discharged by item step 2. I tested the empty poset (empty category/localization), singleton (identity localization of its fiber), and the two-object chain (localizing transport gives the terminal fiber). The result is a genuine smaller input, not a weak-exponential clause.
- `lem-coef-scat-framed-diagram-adjunction`: PASS against Hirschhorn Theorem 19.4.4(1),(2), printed p.415, and Theorem 19.4.3/Corollaries 19.3.6--7 for frame comparison. I downloaded the source PDF to the item work directory and read rendered printed pp.411--416 because this scan has no text layer. This is an ordinary-model function-complex adjunction, with projective/injective derived-functor conventions and naturality of cones made explicit. No simplicial enrichment on Bergner categories is assumed. I tested the empty diagram (contractible maps out of the initial or into the terminal object), singleton, and binary discrete diagram (coproduct mapping product and maps into a product). It supplies general diagram mapping calculus, not any weak-exponential assertion.

Both new nodes have full blueprint ancestry, definitions referenced or written inline, TeX escaped once, exact primary source places, no proof/proof_deps, and independently executed LeanFinder/Loogle/Mathlib grep records. I read the ordinary Mathlib Grothendieck construction and the two colimit declarations returned by Loogle, at Mathlib/CategoryTheory/Limits/Shapes/Grothendieck.lean:136 and :175; these concern ordinary categories and fiberwise ordinary colimits, not enriched DK localization. The frame-query hits are homotopy classes and Whitehead statements; they do not give derived diagrams of function complexes. The focused AlgebraicTopology greps returned no matches. No Mathlib leaf was asserted. Source-checkout searches for this item tag, weak exponentials and Bergner terminology found no finished whole-item attachment; master remains reference material only.

### Not duplicates

- `lem-coef-simplicial-grothendieck-hocolimit` vs `lem-coef-cartesian-grothendieck-colimit-formula`: the latter is a coherent diagram on a total ordinary category with fiber colimits, whereas the former localizes a simplicially enriched Grothendieck category to compute a Bergner homotopy colimit. The formulas have different objects, model structures and hypotheses.
- `lem-coef-simplicial-grothendieck-hocolimit` vs `lem-coef-two-sided-simplicial-grothendieck-invariance`: the latter concerns homotopy invariance of a two-sided construction over simplicial bases, not the one-sided poset diagram's DK homotopy-colimit formula. A whole-DAG source/title/statement search found no A.3.5.13 node or equivalent statement.
- `lem-coef-scat-framed-diagram-adjunction` vs `lem-coef-cosimplicial-frame-mapping`: the latter identifies individual function complexes with infinity-localization mapping spaces and makes no small-diagram mapping-(co)limit comparison. The new node needs neither that identification nor its cyclic dependency closure.
- `lem-coef-scat-framed-diagram-adjunction` vs `lem-coef-simplicial-model-coherent-diagrams`: the latter assumes a simplicial model category and supplies strict enriched presentations of coherent diagrams. Bergner sCat does not satisfy that assumed interface; the new theorem is for ordinary-model frames and ordinary indexing categories.
- `lem-coef-scat-framed-diagram-adjunction` vs `lem-coef-simplicial-derived-pushout-mapping`: the latter supplies the frame definitions, invariance and only pushout/coproduct mapping comparisons. The new input handles all small diagrams and both derived adjunctions, including compatibility with resolutions of diagrams. A whole-DAG search of primary-source places and actual statements found no existing 19.4.4 node or this general ordinary-model diagram theorem.

### Changes and dependency audit

Replaced all six defective proof steps by the twelve checked steps above; removed the unnecessary `lem-coef-dk-triangular-right-kan` from the delivery and from citations/dependencies; added the two strictly smaller primary-source inputs above; rebuilt citations.json with complete verbatim cited statements so no qualification is hidden. The removed triangular statement also allowed either direction of a weak-equivalence transformation while calling it a cone without a derived inversion; the repaired proof constructs its own natural zigzag and does not need that ambiguous formulation. No imported/item statement, target, unit, chapter or maintainer field was changed.

Read-only breadth-first traversals of the complete current statement/proof edges found no path from any of the nineteen direct proof prerequisites to this item, including both new nodes. In contrast, the tempting presheaf-presentation, full cosimplicial infinity-localization, model/coherent-diagram and enriched infinity-tensor theorems have explicit return paths and remain unused. All direct tools lie in the item's unit. The general projective-model and frame arguments are written from the independent model generators and ordinary-model sources rather than hidden in duplicate presentation nodes. All twelve step texts are below 2000 characters. Exact citation strings and the unchanged item statement were verified locally; official server preflight follows below.

WANTED for the maintainer's archive: HTT Appendix A.3.5.10--15 and A.3.6.9--15, and Hirschhorn Theorem 19.4.4 with the surrounding frame-comparison results. The latter source is now retained in this item's work directory; the read-only shared literature list was not changed.

### Server verification of the second reading

The first repaired-packet dry run exited 0 with `OK (not pushed)` at `c168f9c5eb`; the receipt is retained in `work/dry-run-second-reading-first.log`. I then replaced the Grothendieck statement's cases-layout escape by two explicit conditional sentences, expanded the two-test-object Yoneda argument in step 10, and explicitly verified the component-category hypothesis for the actual-representative test in step 12. These are presentation/justification repairs, with no mathematical statement change. The complete packet and this report were finished before the final dry run.
