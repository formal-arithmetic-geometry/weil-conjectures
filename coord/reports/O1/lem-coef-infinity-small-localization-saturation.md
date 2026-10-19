# Stage-1 report: lem-coef-infinity-small-localization-saturation

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-small-localization-saturation.json`: statement, now split in five steps; statement unchanged. No Mathlib match.
- `citations.json`: verbatim statement excerpts for every step/dependency pair.
- No new nodes, no Mathlib leaves, no unit edits. The sandbox also holds the logged search records and the item-specific writing script.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag/id and for saturation, quasicategory localization, Bousfield and local-object terminology found no project declaration stating this result. The ordinary Grothendieck-topology saturation results in CategoryTheory/Pro/Generating.lean do not state it. The upstream master is not used as evidence of a finished proof.

## Sources wanted

WANTED: Jacob Lurie, Higher Topos Theory, Definition 5.5.4.5, Remark 5.5.4.6, Lemma 5.5.4.11, Proposition 5.5.4.15 and Lemmas 5.5.5.12-14, for lem-coef-infinity-small-localization-saturation. No HTT copy is archived under literature/. Read the author's PDF directly at https://www.math.ias.edu/~lurie/papers/HTT.pdf (printed pp. 476-478, 482, 490-491). No download or shared-tree write was made. Consequently proof_origin.by is agent, with the exact checked online places recorded. There is no Stacks tag for this presentable-quasicategory theorem, and no SGA source is used.

## Audit and corrections

The item had no proof or lean_audit entry. It does not need a statement correction. The three equivalent conditions and the unit assertion agree with HTT Proposition 5.5.4.15. The separate retract requirement in the item's generated class is stronger in its definition than the explicitly listed closure operations of the existing coslice node. The split deliberately introduces W using exactly the coslice node's definition, shows W is contained in the item's G, and proves units are in W up to equivalence. It never silently applies the coslice theorem to a different closure class and never assumes an uncited theorem equating the two definitions.

Read the chapter/unit records and both the master ancestor and the current main-20261015 `sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`. The current proof's second paragraph still contains the finite mapping-complex adjunction before derived inverse limit, exactly the inherited blueprint ancestry. This item is a supporting general localization tool in that route, not a replacement for any geometric or coefficient argument. The item is not a unit's key statement, so realized fields are untouched. Blueprint searches for strongly saturated, S-local and mapping-space detection found no blueprint node with this statement; the S-local hits concerned unrelated algebraic localizations. The DAG searches for strongly saturated, 5.5.4.11/14/15, orthogonality and coslice presentability identified the existing prerequisite nodes used here. All five cited dependency closures were traversed and none reaches the item.

Mathlib searches were run through msearch.py and recorded exactly from searches.jsonl, retaining the inherited searches as inherited data. Fresh searches include both natural-language phrasings, Loogle, and two grep queries. The returned Bousfield and OrthogonalReflection declarations concern ordinary categories with Hom-set bijections. Read OrthogonalReflection.lean lines 73-103 and 410-445 and Bousfield.lean lines 41-61: these do not give coherent mapping-space equivalences or a presentable-infinity-category saturation theorem. The second LeanSearch query returned ordinary retract/colimit/model-category facts, also not this statement. No candidate is being mislabeled as a Mathlib leaf.

## Not duplicates

No new nodes. In particular no child was created for the unit assertion, for saturation detection, or for the terminal-W-arrow construction. The latter construction is actually proved in the item's steps 2-3 using the existing coslice and mapping-space nodes. Ordinary small-object-factorization nodes were not mistaken for infinity-category versions.

## Review by N1

I read the item against HTT Definition 5.5.4.5 and Proposition 5.5.4.15 and read the full proof of Lemma 5.5.5.14. I also read the statements of all five dependencies in the shared DAG, not just their titles or their proof steps. There are no new statements needing a source audit. The item remains the general theorem for a presentable infinity category and a small set of arrows; it gains no monoidal, stable, algebroid or compact-generation hypothesis.

Step 1 uses lem-coef-infinity-yoneda-presheaf-limits for pointwise arrow colimits and for mapping out of colimits as limits, and lem-cbc-enhanced-functor-cone-calculus for componentwise equivalences of coherent functor diagrams. Both assertions occur explicitly in those nodes' statements. I expanded pushout preservation and gave the actual inverse of a retract of an invertible map; thus no closure lemma for retracts is hidden here. Equivalences of Kan mapping spaces, rather than bijections of Hom sets, are used.

Step 2 uses lem-coef-small-saturated-coslice-presentability exactly as stated for its replete closure W and small generating set S. It does not assert the indexing category of all W-arrows is small. That node's conclusion is presentability of the full coherent coslice D_X, so the small-limit clause of lem-coef-presentable-infinity-adjoints applies to D_X and supplies a terminal object. This is a use of the adjoints node's statement about limits, not of the stronger unit-membership claim that happens to occur inside its proof. The classes W and G are separated explicitly to check the different closure hypotheses.

Step 3 uses only the stated dual cone/coslice mapping-space formula and Kan assertion of lem-cbc-enhanced-functor-cone-calculus, the pushout-to-pullback mapping-space formula of lem-coef-infinity-yoneda-presheaf-limits, and both directions of lem-coef-space-contractible-fiber-equivalence. I checked the domains: P=Map(Z,Y), Q=Map(Y,Y), R=Map(X,Y); the fiber over the identity of Q times_R {s} is the fiber of P to Q over 1_Y, and the pushout identifies it with the fiber over g:A to Y. Terminality is used only for objects s,s' inside D_X, where fullness permits the ambient coslice mapping spaces. The proof does not confuse a homotopy fiber with a strict set fiber. W's pushout and composition stability ensure s' is indeed in D_X.

Step 4 takes the mapping-space adjunction, local reflector, and units from the statement of lem-coef-presentable-infinity-adjoints. Since both target objects are local, the two universal restriction equivalences give the comparison maps and the two inverse homotopies explicitly. This is an elementary comparison of universal arrows using steps 1-3; it is not an appeal to the desired localization detector. It proves the unit assertion before the final cancellation argument.

Step 5 again uses only the coherent mapping-space adjunction and natural unit of the same node. I checked that the two detecting test objects LA and LB are local, so they are allowed tests. The inverse of Lf is supplied by surjectivity on components at LA, and its other inverse identity by injectivity at LB. The naturality square then uses the units already proved in G and two-out-of-three. These are explicit elementary inverse and cancellation calculations, not an uncited general Yoneda lemma.

The cone-calculus node has another unit. Its use is declared in split_report.tool_uses: it supplies the generic coherent coslice formula and equivalence criterion, not a replacement for the unit's proof route. The other dependencies are in the item's unit. No cited dependency uses the item, so this does not create a cycle.

I checked the empty generating set S, where local objects are all objects, the reflector is equivalent to the identity and the result reduces to equivalences. For S consisting only of equivalences, the same test works. For S={empty space to point} in spaces, locality forces contractibility and the detector inverts every arrow, consistent with the construction. I checked the empty arrow-diagram colimit in step 1 (identity of the initial object), empty Map(A,Y) in step 3 (the fiber criterion is still valid), and X initial or terminal. In ordinary presentable categories regarded as infinity categories with discrete mapping spaces the fiber argument reduces to existence and uniqueness of extensions, which checks the directions of all restriction maps. No false imported statement or source error was found.

The corrections made during self-review were to distinguish W from G, avoid using a dependency's proof as if it were its statement, spell out the identity-fiber calculation, and replace a potentially uncited equivalence detector by the explicit two-test-object inverse argument. Sections B-E of delivery-errors were checked against these concrete statements and arguments. No unresolved mathematical step remains in the split; prerequisite nodes retain their own stage-1 work.

## Validation

The completion check is the required server dry run through deliver.py --no-push, including maintainer preflight, check_dag and review_split. The sandbox is handed to the second reader only after that command prints OK. No delivery push is authorized for this first reader.

Fresh self-review on 2026-10-17 re-read all five cited statements and the universe definition, the current blueprint ancestor proof and the assigned chapter/unit. I repeated the project-source searches by exact id and saturation/localization terminology, repeated LeanFinder with two phrasings, Loogle, LeanSearch and Mathlib grep through msearch.py, and read the ordinary-category candidates. The fresh results are preserved exactly in mathlib_searches. I removed an inherited section claiming an independent second reading: this sandbox is still first-reader work, and the next worker must perform that reading. The statement and mathematical proof required no change. The server check was invoked through srvcheck.py; its outcome and the dry-run result follow below.


## Second reading by N1

- Statement: checked against HTT Definition 5.5.4.5, Remark 5.5.4.6, Proposition 5.5.4.15(1),(3),(4), and Lemma 5.5.5.14; the hypotheses on a presentable infinity category, small arrow set, local objects, reflector, closure operations, and arrow colimits agree. Tested S empty, S consisting of equivalences, and the empty-to-point map in spaces.
- Step 1: checked the cited Yoneda/pointwise-colimit statement and vertexwise equivalence statement; pushout, two-out-of-three, retract, and arrow-colimit closure are written in the step, including the explicit retract inverse.
- Step 2: checked the cited saturated-coslice presentability and presentable-category limit statements; W is exactly the cited replete pushout/colimit/two-out-of-three closure, and terminality is taken in the coherent full coslice. Checked empty and singleton generating sets.
- Step 3: checked the cited cone mapping-space fiber formula, pushout mapping formula, and contractible-homotopy-fiber criterion with P=Map(Z,Y), Q=Map(Y,Y), and R=Map(X,Y); the argument is repeated for each g and keeps homotopy fibers and Kan hypotheses explicit. Checked empty mapping spaces and initial/terminal X.
- Step 4: checked the cited mapping-space adjunction statement; the comparison maps k and h and both inverse homotopies follow from the two restriction equivalences, and the unit conclusion uses only W\subseteq G and composition closure.
- Step 5: checked the cited coherent adjunction and unit naturality statement; the tests LA and LB are local, the two inverse identities are obtained by component surjectivity/injectivity, and the naturality square plus two-out-of-three gives membership in G.
- New nodes: none; therefore B1-B7 and duplicate-node checks have no new-node cases. All five dependency statements were opened, and every citation quote in citations.json is verbatim from the corresponding statement.
- Changes: none to the item or citations; appended this independent audit and retained the worker's five-step proof. The required server dry run passed (`e003e42134`).
