# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-presheaf-naive-fibration-whitehead.json`: existing statement split into fourteen explicit lifting and homotopy calculations; no Mathlib match.
- `citations.json`: empty list, because every proof step is elementary and cites no node.
- `report.md`: this worker's source review and handoff report.

New nodes: 0. New Mathlib leaves: 0. The item is a supporting lemma, not its unit's key statement, so no unit file is changed. All writes are in the assigned sandbox.

## Attachments

None. I searched the slopmaster2 `WeilConjectures/` source for the exact item id and blueprint tag, naive fibrancy/fibration, Whitehead and interval-homotopy terminology. I also checked the upstream master reference source. No project declaration states the item. Both imported Lean audits say `none`; no upstream sorry is treated as a finished proof.

## Literature wanted

WANTED: Denis-Charles Cisinski, *Higher Categories and Homotopical Algebra*, July 30, 2026, Section 2.4, especially Definition 2.4.18, Propositions 2.4.17 and 2.4.26, and Lemmas 2.4.24, 2.4.27, 2.4.28, for lem-coef-presheaf-naive-fibration-whitehead. Source: https://cisinski.app.uni-regensburg.de/CatLR.pdf, printed pp. 56–61 (PDF pp. 71–76). I reopened the online PDF and read its extracted text; its screenshot service failed for two pages, but the text of the statements, displayed maps and proof equations was available. Nothing was downloaded into literature or elsewhere. The source is not archived in literature, so `proof_origin.by` remains `agent` as the worker brief requires. This specific interval theorem has no identified Stacks tag; I cite the actual Cisinski lemma instead of inventing a tag. No SGA source is used.

## Problems found and changes made

The sandbox held a complete prior fourteen-step proof, but the previous worker ended without a usable answer. I checked the proof anew and retained its mathematics. The inherited report contained a purported second-reader section and a dry-run-success claim which this worker had not established. I replaced that report rather than presenting either claim as current validation. The second reader still needs to read this split and deliver it.

The statement is preserved verbatim. It matches Cisinski Lemma 2.4.28 under the product cylinder: Definition 2.4.18 is precisely the naive lifting and fibrant-object condition and the test by homotopy classes; the trivial-fibration condition recalled before Proposition 2.4.17 is lifting against every monomorphism. The endpoint hypothesis makes the union descriptions meaningful. The source's homotopy-Yoneda assertion and deformation-retract assertion are expanded into explicit calculations here. Thus no unproved invocation of those source propositions remains.

I retained `def-weil-size-convention` as the sole statement dependency after opening its statement: it fixes the universes used here. All other special notions are defined inline in the item. The proof constructs only finite products, unions and maps in the input universe and tests only X and Y already in that universe. Small generation and the second interval axiom are stronger than this proof needs, and are retained unchanged.

The node was originally created by Q13 for `lem-coef-presheaf-cylinder-model-recognition`. I restored that original `created` record after noticing it is protected provenance, not current-worker ownership; Q07's split is recorded only in `split_report` and this report. I refreshed the sandbox's read-only Lean audit copy from the shared node. No protected metadata, chapter, unit, ancestor or target statement is changed by the proposed delivery.

I read the chapter/unit records, the parent recognition split, and both the master and main-20261015 ancestor proof texts. The historical ancestry serves the finite-coefficient mapping-complex adjunction before the derived limit. Its `from.place` is already precise and is retained. There is no blueprint update on this item. Whole-blueprint searches for Whitehead, naive fibrations and anodyne returned no duplicate imported statement. No unit route is replaced and no off-unit theorem is used. In particular the parent recognition theorem, which depends on this lemma, is not cited.

All six fresh searches were actually run through msearch.py for Q07 and this item and copied with their exact tool/query/result records from searches.jsonl. They comprise LeanSearch, Loogle, two LeanFinder phrasings and two source greps. All services succeeded. I read the candidates at Mathlib/AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean:38–100, ModelCategory/JoyalTrick.lean:35–100, ModelCategory/Bifibrant.lean:105–128 and ModelCategory/Basic.lean:90–165. The simplicial-set result specifies Kan horn fibrations; the Joyal tricks require factorizations and extra lifting implications; the subcategory lemmas merely preserve an existing weak-equivalence predicate. None proves this arbitrary presheaf interval theorem by one-line specialization. The positive grep's declarations and file/line hits are recorded, and the empty grep and Loogle query are recorded as empty, not unavailable.

## Unfinished work

No mathematical part of the split remains open and no new subordinate node is needed. Archiving the source is the literature request above, outside this worker's write scope. This worker runs only the required no-push dry run; the fresh second reader must review and deliver.

## Not duplicates

No new nodes were created. I searched the whole DAG and blueprint and opened the nearby model-localization homotopy-classes, simplicial-interval localization/lifting, Kan Whitehead and CW Whitehead statements. Those require a model category, simplicial enrichment, Kan complexes, or topological CW hypotheses and do not state this arbitrary presheaf result. The parent cylinder-model-recognition node depends on this item and is not a reusable proof input.

## Review by Q07

I checked delivery-errors B–E against the item, the fourteen proof steps, the cited source and the size-convention statement. For B1–B10 there are no new nodes or claimed Mathlib leaves; the statement is self-contained, its inline definitions are explicit, TeX is retained correctly, all searches in the node are real logged searches, and the ancestry is preserved. The source is Cisinski rather than Stacks because that is the actual source of this generic theorem. The attachment searches found no project proof to reuse.

For C1–C8, each step's input is the item's stated interval/RLP hypotheses or an earlier numbered step. No proof step cites a node, so there is no C4 quote to invent and citations.json is correctly empty. The sole statement dependency is read and used only for the universe convention. There are no hidden uses of the parent model recognition theorem, a small-object argument, a Yoneda theorem, or a model-category Whitehead theorem. I checked that every intermediate source fact is explicitly proved below rather than referred to by name. For D1–D5 no conclusion has been moved into a new node and no induction or circular dependence occurs.

The step-by-step checks, including E1–E7, are as follows.

1. Componentwise injections identify the pushouts with the specified subset unions. Monicity of delta gives the disjoint endpoint faces. The formulas commute with restrictions, so the glued maps are maps of presheaves.
2. The two homotopies with common starting map and the constant third face agree at both intersections. Their union inclusion is e_0 square (delta times T), which is in An by the first interval axiom. Terminal lifting for Z gives the opposite edge with the required endpoints. This is the construction of Lemma 2.4.24, written out.
3. Constant homotopies, Step 2 with a constant second homotopy, and then Step 2 after reversing an edge prove reflexivity, symmetry and transitivity. Thus equality of classes into a naive fibrant target is a single direct homotopy. Whiskering explicitly gives the maps on the generated quotients; no reversal or connection map on I is assumed.
4. For an An-extension first extend the composite into Y using Y's fibrancy, and then lift against p. This verifies that X is a permitted fibrant test object rather than assuming it.
5. Apply the surjectivity test with target X to obtain t and [tp]=[1_X], then postcompose with p. This derives the needed part of Proposition 2.4.26 directly.
6. Apply the injectivity test with target Y to the two classes [pt] and [1_Y], whose restrictions are equal by Step 5. Step 3 supplies k with the specified orientation, from 1_Y to pt.
7. The endpoint inclusion is e_1 square (empty to Y), in An. The square commutes exactly at endpoint 1. Its lift k' has k'(1)=t and p k'(0)=1_Y, so s=k'(0) is a strict section.
8. Whisker k' with p and use [tp]=[1_X]. Step 3 applies to X by Step 4, yielding h from 1_X to sp. The proof does not yet assume that h is over Y.
9. I checked the three prescribed faces in the two distinct coordinates r,t. At r=1,t=0 the values are sp(x); at r=1,t=1 they agree because spsp=sp. Applying p to every face yields ph(r,x), using ps=1_Y. The base square is therefore commutative.
10. The domain inclusion is e_1 square (delta times X), so lifting against p is authorized. Restriction to r=0 gives K(0)=1_X, K(1)=sp and pK=p pr_X. These are the displayed equations in Lemma 2.4.28, and establish the relative homotopy needed in the next step.
11. For an arbitrary monomorphism i and an arbitrary square, the prescriptions on I times U and endpoint 1 times V agree because K(1,a(u))=spa(u)=sbi(u). Their images under p equal b pr_V. The inclusion is e_1 square i in An; no assumption that i is a generator is used.
12. Restrict its lift at endpoint 0 to obtain l. The two equations li=a and pl=b follow directly from the boundary and base equations. This is the expanded argument of Lemma 2.4.27 and proves every required monomorphism lift.
13. For the converse, lifting empty to Y supplies a section. Delta times X is monic, so another assumed monomorphism lift supplies a homotopy from 1_X to sp over Y. This is the needed part of Proposition 2.4.17; no fibrancy or model structure is smuggled into this direction.
14. Precomposition with s is an inverse on every testing quotient: fps=f, and gsp is directly homotopic to g. Step 3 establishes well-definedness. The claimed bijectivity follows, and all products, chosen maps and test objects stay in the fixed universe.

I tested the empty indexing category, identity/isomorphism p, empty domains, and the terminal indexing category with the two-point interval. In the last case take An to be the weak saturation of the nonempty singleton endpoint inclusion: it consists of injections with nonempty domain and the empty identity. Every set is naive fibrant. The map empty to a nonempty set is a naive fibration, but fails both the weak-equivalence test with Z empty and lifting against empty to a singleton. Surjective maps satisfy the expected lifting conclusion; the empty identity also works. This rules out a silent assumption that every naive fibration is weak. In all empty-domain uses a section is supplied by the actual lifting hypothesis, never by choosing an element of an empty set.

No statement dispute or source error was found. The substantive proof check was the passage from an arbitrary homotopy to the explicit homotopy over Y in Steps 9–10. The current report records this worker's checks only; it does not claim to be the independent second reading.

## Second reading by Q07

I independently read Cisinski, *Higher Categories and Homotopical Algebra*, Lemma 2.4.28 (printed pp. 58–61, PDF pp. 73–76), together with Lemmas 2.4.24 and 2.4.27 and Propositions 2.4.17 and 2.4.26. The item's hypotheses and conclusion agree clause by clause: a presheaf product interval with monic endpoint pair, the two interval/anodyne closure assumptions, naive fibrancy, the homotopy-class definition of (W_I), and the equivalence between (W_I) and lifting against all monomorphisms. The source uses “trivial fibration” for the latter condition; the item expands that terminology. I checked the terminal, empty, identity, and two-point-interval cases; no statement dispute or source error was found.

1. Step 1 was checked against the presheaf pushout-product definitions and the monicity of δ; the displayed unions and gluing agree objectwise, including empty intersections.
2. Step 2 was checked against Cisinski Lemma 2.4.24; the three faces agree on both overlaps and the inclusion is exactly (e_0\square(\delta\times T)∈\mathrm{An}).
3. Step 3 was checked against the generated homotopy relation: constant paths give reflexivity, the two-face filler gives symmetry and transitivity, and pre/postcomposition descends to quotients.
4. Step 4 was checked against the naive-fibration and fibrant-object hypotheses; extending (pa) into (Y) and lifting the resulting square proves (X\to1) is naive fibrant.
5. Step 5 was checked against the surjectivity half of Proposition 2.4.26; testing (W_I) at (X) gives (t) and [(tp)]=[(1_X)], and postcomposition by (p) gives the stated equality.
6. Step 6 was checked against the injectivity half at the fibrant target (Y); the restrictions are equal and Step 3 supplies a direct homotopy (1_Y\sim pt).
7. Step 7 was checked against the endpoint lift in Lemma 2.4.28; (e_1\square(\varnothing\hookrightarrow Y)) is in An and yields (ps=1_Y) with the required endpoint (t).
8. Step 8 was checked by whiskering the endpoint homotopy with (p); it correctly obtains (1_X\sim sp) and does not assume this homotopy lies over (Y).
9. Step 9 was checked against the source's two-coordinate boundary prescription. The three faces glue at ((1,0)) and ((1,1)), where (spsp=sp) follows from (ps=1_Y), and their (p)-images agree with (ph).
10. Step 10 was checked against the final lifting square of Lemma 2.4.28; (D\hookrightarrow I_r\times I_t\times X) is (e_1\square(\delta\times X)), and restriction at (r=0) gives all three equations for (K).
11. Step 11 was checked against Lemma 2.4.27 for an arbitrary monomorphism (i); the two prescribed maps agree on (I\times U\cap(\{1\}\times V)), and their (p)-images are the same bottom map.
12. Step 12 was checked by restricting the filler at endpoint (0); it gives (li=a) and (pl=b), hence the full monomorphism lifting property.
13. Step 13 was checked against Proposition 2.4.17; lifting ∅→(Y) gives a section and lifting δ×(X) gives (1_X\sim sp) over (Y), with no model-structure assumption.
14. Step 14 was checked on representatives and homotopy classes; precomposition by (s) is the inverse to (p^*), with (fps=f) and (gsp\sim g), and all constructions remain in the fixed universe.

There are no new nodes and therefore no new-node statements or citations to audit. The sole statement dependency, `def-weil-size-convention`, was opened and supplies exactly the universe convention used in the final sentence. I found no duplicate DAG node, no Lean or Mathlib declaration, no hidden proof dependency, and no circular citation. I changed only this second-reader report section; the item JSON and empty `citations.json` were already correct.
