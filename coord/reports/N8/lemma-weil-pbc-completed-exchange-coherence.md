# Worker report

## Files written

- `dag/nodes/sec-proper-base-change/lemma-weil-pbc-completed-exchange-coherence.json`: repaired seven-step split, unchanged item statement and current maintainer metadata.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-ordered-exchange-coefficient-comparison.json`: one new statement-only, unsplit theorem; no Mathlib match. It supplies the missing coefficient/reconstruction comparison for the raw ordered exchange on every complete input.
- `citations.json`: a verbatim current statement for every citation in every item step.
- `report.md`: this report; preserved earlier reports follow. Sandbox-only scripts and the prior-report archive are under `repair/` and are not delivery files.

## Attachments

None. Fresh read-only searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` for the item id, completed-exchange names, ordered/coefficient exchange and strict-tower normalization found no declaration stating the item or the new lemma. The source text in shared `lean/Sheaf/Paper/CompletedBaseChangeMap.lean:38` and `CompletedTowerCompatibility.lean:79` was read only to check the exact raw formula; the stage-2 sorry declarations are not finished proofs and are not attachments.

## WANTED

None. All cited blueprint and Stacks ingredient sources are available locally. The new comparison is explicitly an agent-supplied supplement, not attributed as a theorem already stated by Stacks.

## What was wrong and what changed

This repairs the specific latest return, not just the earlier returns reproduced below. The preserved seven-step packet passed the required initial dry run at e831ff4bf0 (not pushed). That packet still contained exactly the unsupported identifications described by the maintainer. I compared the sandbox with the current shared node, retained its searches and reports, and refreshed maintainer metadata from the shared version. The item statement is unchanged. The reviewed `lem-weil-pbc-strict-tower-exchange-mate-normalization` is retained unchanged and still used in Step 2. The 2026-10-14 strict-normalization/derived-limit/ordered-reconstruction route is retained; the new statement-only comparison isolates the missing content in the old long conjugation argument. The item itself still proves both pasting laws, identity and naturality.

## Repair of the latest return

1. **Step 3, E5/C4.** Added `lem-weil-pbc-ordered-exchange-coefficient-comparison`. Clause (2) expressly gives the actual strict-tower isomorphism Res(R^a K) ≅ R(Res K), the diagram projection-formula equation beta Res(H^a) = H^0 rho_M, the tower-mate equation, and its agreement with the existing normalization's b,d when witnesses are present. Clause (3) states both reconstruction equations separately, then the exact equations for Res(s) and Res(c) against the general comparison's s,t. The repaired Step 3 cites these statements and writes the resulting conjugation equation. It no longer says the normalization lemma defines b,d by projection-formula comparisons.
2. **Step 6, C3/E1.** The new lemma defines the raw ordered map by the same strict H' R(e) H inverse construction used by `towerV'` in the read-only stage-2 source. It asserts the comparison for every complete input without witnesses. Step 6 applies that precise theorem to F_g' K and R_e K. Their completeness was checked in Step 1. No witness for R_e K is asserted, no proof of the old normalization theorem is mined, and the completed-coefficient raw map is not silently replaced by a constant-coefficient extension. On witnessed inputs clause (2) identifies it with the definition's map.
3. **Step 1, C1.** Clause (1) of the new comparison explicitly states Res/Ru_* compatibility and identifies the completed adjunctions with their units, counits, composition and identity comparisons. Step 1 now cites it for exactly this previously uncited fact. Constant-completion-equivalence alone is no longer used to supply that compatibility.

The earlier successful Steps 2, 4 and 5 are retained. Steps 3, 6 and 7 use the new comparison rather than a claimed equality of endpoints or derived evaluations. All seven item steps remain under 2000 characters.

## Review by N8

The resumed repair was compared with the current shared node: only split-owned fields differ; the shared item remains unsplit and its statement, source and maintainer metadata are retained. The required initial dry run of the retained repaired packet exited OK at `39c89dfbb2` on 2026-10-17. I reread the equations against the current cited statements and verified all retained search-log entries. One additional scope correction was needed: the new lemma allows nonproper squares, whereas `def-weil-pbc-four-corners` introduces a proper square. Its raw H/H-prime construction now cites the general `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` instead. That statement gives the canonical tensor comparison for arbitrary ringed-topos morphisms, natural in both arguments, and hence also applies on the indicated small diagram sites. Properness remains required only for the clause identifying the original witnessed map. This changes no comparison equation or search question. All citation quotations were refreshed after this correction.


I read the current main-20261015 item statement and both proof paragraphs, the master-era item split and retained normalization statement, the proper-base-change chapter and unit, and the complete statements of every node cited by the repaired item. I read Stacks proetale.tex `lemma-naive-completion` (Tag 099M, lines 4304 onward) and `lemma-pushforward-Noetherian-case` (Tag 099N, lines 4335 onward), sites-cohomology.tex `lemma-Rf-commutes-with-Rlim` (Tag 0A07, lines 5149 onward) and `remark-compatible-with-diagram` (Tag 0E48, lines 13714 onward), and the full local blueprint `fix-lem-exchanges.md`. These sources give the completion formulas, direct-image/limit comparison, adjunction and projection rectangle ingredients; they do not state the new combined coefficient theorem. Its source explicitly labels that extra comparison as agent-supplied, and it remains statement-only for later splitting.

The new statement is fully quantified: one cartesian scheme square, the full adic datum including Noetherianity, finite perfect P_n and additive torsion A/I, small sites, unbounded module derived categories, and any quotient-derived-complete K. It distinguishes A_T from constant underline A and names each ringed and diagram operation. Properness and witnesses appear only in the clause identifying the existing witnessed construction. Its maps rho, beta, delta, chi, phi, lambda and both reconstructions have explicit domains, directions and displayed equations. I checked the order of composition against the definition c inverse Rlim(v') s, the general tool's t E^c = L(v) s, and the raw stage-2 definitions. In particular, multiplying the s and c equations by the tower-mate equation cancels L(beta), L(delta) in the stated order. The new result does not assert a coherence clause of the item: it is a comparison for one square, and the item must still use mate-pasting.

**Step 1.** The completed-map definition gives the exact ordered map. Constant-completion-equivalence gives the equivalence of full complete categories; the new clause (1), rather than that equivalence alone, gives chi, phi and adjunction normalization. Completed-pullback-adjunction gives the reflector, the normalized adjunction on constant coefficients and completeness preservation. Thus both types of intermediate input are in the complete category. All Noetherian and smallness hypotheses are supplied by the datum and the small pro-etale site convention.

**Step 2.** The existing strict-tower normalization is used only on the witnessed proper input where its hypotheses hold. It gives an actual equality d Res(v') = E^T b and natural isomorphisms, not merely their evaluations. Rlim-functoriality supplies an actual functor, so applying it preserves this equality and inverses. Neither etale bounded-below exchange nor faithfulness of derived evaluations is assumed.

**Step 3.** The new comparison's clauses (2)--(3) are exactly the missing statements: strict rho_K, H^a versus H^0, both reconstruction maps, and Res(c) versus t^0. I checked these are literal parts of the cited statement. Elementary functoriality and cancellation give the displayed formula. Completion-mate-comparison then gives E^c, because its A-Noetherian and P_n-perfect hypotheses hold. This step uses its statement, not its internal proof.

**Step 4.** The general comparison fixes completed composition maps as adjunction conjugates. Ringed-topoi-derived-pushforward-composition specifies the K-injective direct-image comparison. Right-adjoint-preserves-kinjective applies since constant inverse image is exact; successive images of a K-injective therefore already compute the derived composites. On those complexes, direct-image composition and unit comparisons agree with the same section maps, whose ordinary associativity can be checked directly. The conjugate bijection explicitly preserves identities and reverses composition, so it carries these equations to completed pullbacks. This fixes the canonical maps used in the claim.

**Step 5.** Mate-pasting clause (1) gives (E2 F_g')(F_h E1). Clauses (2) then (3) give (R_f' E3)(E1 R_e). Step 4 inserts the specified associativity maps. Cartesian-square-pasting is used also on the transposed diagram to obtain the two outer cartesian rectangles. No exchange isomorphism or geometric base-change theorem is needed for these equations.

**Step 6.** The new clause (3) expressly covers all complete inputs obtained by either operation, so it applies also to R_e K without witnesses. Its raw construction is exactly the diagram H' R(e) H inverse, not a newly chosen intermediate arrow. Clause (2) identifies witnessed occurrences with the definition's exchange. The generic constant-coefficient comparison then identifies every occurrence with E^c. Identity orientations use mate-pasting (4) and the explicit unit--square--counit formula with identity adjunctions. Those cited statements supply the two required identity calculations.

**Step 7.** Adjunction-mate is a natural transformation. The new comparison states natural-transformation equalities on the full complete category, with no requirement to lift an arbitrary k to the etale origins. Naturality of iota_S and iota_T therefore transfers the equation; the complete coefficient equivalence reflects it. The old endomorphism-only reduction clause is not used for arbitrary k.

For B--E I checked that every proof use is a statement actually cited, every new notion in the new statement has a named dependency or explicit definition, proof_deps is exactly the union of uses, and quotations are copied verbatim. The new theorem has no proof and no hollow definition. Its hypotheses are precisely the adic datum, not an unmentioned regularity or cohomological bound. It is not an elementary two-line fact: the strict comparison and compatibility with adjunctions and reconstructions are the return's missing substantive lemma. Whole-DAG and blueprint searches, described below, found only the separate weaker ingredients. No existing node is altered except the assigned item. The new node is not given an unearned reviewed status.

Small cases checked: K=0 makes every exchange and normalization equation the zero map between zero objects. Identity edges reduce the comparison to the same completion-unit and direct-image maps, without deriving the item's identity law from that check. If A is finite and I=0, constant and completed coefficients coincide and the quotient diagram is constant; rho, chi, phi and the conjugating equations reduce to their standard constant-coordinate versions. If I=A or A=0 the complete category is zero, and no nonzero assumption is needed. For A=Z and I=(ell), the quotient diagram is genuinely nonconstant; the statement specifies a diagram-site map, so it does not infer equality of tower arrows from levelwise equality. These tests check the directions and scope; the statement-only theorem's later proof remains a separate DAG task.

## Searches and duplicate audit

I retained and read the four searches already logged on 2026-10-17 and the historical item searches. For the new node I ran seven additional msearch.py commands in this sandbox: two LeanFinder phrasings, two Loogle queries, two grep patterns, and LeanSearch. The node records the exact tool/query text and serialized command log result. The first Loogle query reported unknown Rlim and is recorded unavailable; the second returned no hits. LeanFinder/LeanSearch returned ordinary scalar-restriction, adic-completion and generic diagram facts; they do not identify these derived strict-tower maps. Grep returned no hits for either pattern. No unexecuted search is recorded.

Whole-DAG key-word searches included ordered exchange, completion/mate, restriction/scalars, strict-tower normalization, and the four ingredient tags. Whole-blueprint searches via blueprint_refs.py for `completion mate`, `completed exchange` and `restriction completion` returned the item and unrelated or more specialized exchange results; its ancestor is itself. I also opened the specialized O_E linear-natural-exchange result, the finite-ring direct-image/restriction result and the Frobenius-specific finite restriction result. Their coefficient or square hypotheses and conclusions do not provide this comparison. No closed project Lean declaration was found. The new statement's shared-tag candidates are each distinguished below, including definitions and the item itself.

## Not duplicates

- lem-weil-pbc-ordered-exchange-coefficient-comparison vs def-pur-integral-derived-operations: defines integral operations for O_E coefficients; the new node proves specific coefficient/tower comparisons for the general adic datum.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs def-weil-pbc-adic-coefficient-datum: defines coefficients and quotient towers; it does not prove their compatibility with exchange or direct image.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs def-weil-pbc-completed-base-change-map: defines the ordered map on proper witnessed inputs; the new comparison is about the exact maps of that formula and its raw construction on all complete inputs.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs def-weil-pbc-completed-pullback: defines strict completed pullback and its completion map; it does not compare projection-formula exchange or direct-image/limit reconstruction across coefficients.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs def-weil-pbc-four-corners: defines the four finite objects and pullback/reduction maps; it does not state the scalar-normalization equation for ordered exchange.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs def-weil-pbc-intrinsic-completion: defines the Koszul completion complex and unit; it has no exchange comparison conclusion.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs def-weil-pbc-ringed-tensor-square-presentation: defines representative-normalized tensor-square data; it gives no completed exchange scalar-normalization theorem.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs det-prop-diagonal-tower-system: constructs the integral diagonal-class tower; it gives no exchange/reconstruction comparison.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs lem-pod-integral-pullback-composition: gives integral composition on constructible O_E complexes; it does not normalize completed exchange under restriction of scalars.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs lem-sbc-completed-operations-linear-natural-exchange: is restricted to A = O_E with a uniformizer and states linearity/naturality; the new statement allows the full Noetherian adic datum and pins down strict tower and reconstruction comparisons.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs lem-sp-completed-pullback-adjunction: gives the reflector and completed adjunction over constant coefficients; it does not identify scalar restriction of the completed-coefficient ordered exchange.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs lem-sp-completion-mate-comparison: works entirely over constant A coefficients and proves t E^c = L(E^T) s; the new node compares the actual completed-coefficient ordered maps, including both reconstructions, with its specified s,t.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs lem-weil-pbc-constant-completion-equivalence: gives the coefficient equivalence, levelwise reduction comparisons and completion units; it does not state the strict tower isomorphism together with projection, direct-image, adjunction and ordered-exchange compatibility.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs lem-weil-pbc-finite-level-rectangle: states the rectangle at one finite quotient; the new node states equality in the strict derived tower category and fixes the limit conjugations.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs lem-weil-pbc-finite-reduction-reconstruction: identifies finite reductions of reconstructed complete objects; it does not identify ordered exchange maps in the derived tower category.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs lem-weil-pbc-levelwise-isomorphism-cones: detects isomorphisms by evaluations or complete reductions; it gives no equality of the specified tower morphisms.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs lem-weil-pbc-reconstruction-uniform-tower: reconstructs uniformly bounded constructible towers over finite-type schemes; the new comparison treats arbitrary complete inputs and specified exchange maps.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs lem-weil-pbc-ringed-exchange-tensor-coherence: gives the projection-formula/base-change rectangle for a ringed square; it does not identify the constant/completed coefficient constructions or both reconstruction maps.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs lem-weil-pbc-tower-compatibility: asserts compatible strict corners and the rectangle for the given finite arrows; it does not identify scalar-restricted towers with the constant reduction functor or normalize s,c.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs lem-weil-ringed-tower-pushforward-limit-comparison: compares direct image with strict derived limit for one ringed morphism; it does not compare quotient diagrams or the ordered square exchange across coefficients.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs lemma-weil-pbc-completed-exchange-coherence: is the item: identity and pasting/naturality laws; the new node asserts no identity or pasting law, only coefficient/reconstruction normalization for one square.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs lemma-weil-pbc-completed-map-reduction: compares finite reductions of a witnessed completed exchange; the new node asserts a strict-tower and derived-limit equation for all complete inputs.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs lemma-weil-pbc-completed-pullback-reduction: gives finite reductions of completed pullback; it does not identify the corresponding strict-tower exchange or s,c maps.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs prop-weil-pbc-direct-image-limits: proves direct-image/limit and projection comparisons within completed coefficients; it does not identify these with the constant-coefficient exchange comparison or completed adjunction.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs prop-weil-pbc-koszul-reconstruction: identifies Koszul and quotient completion, respecting the unit; it gives no exchange or coefficient-adjunction comparison.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs prop-weil-pbc-levelwise-truncations: concerns truncations and Tor compatibility of DVR reduction towers, not scalar normalization of ordered exchange.
- lem-weil-pbc-ordered-exchange-coefficient-comparison vs thm-weil-pbc-complete-proetale: asserts invertibility of witnessed proper completed exchange; the new theorem asserts coefficient normalization without properness or witnesses and no invertibility of exchange.

## Validation and unfinished work

The retained packet's required initial dry run exited OK (not pushed), commit e831ff4bf0. An isolated srvcheck review_split invocation exited PASS; it reported 0 new nodes and therefore did not certify the newly added statement. The full deliver.py dry run, which assembles the whole packet and runs server preflight including check_dag/review_split, is the authoritative validation for this repair; its result will be appended. Only stage 1 was performed. No Lean was written or compiled, no Lake or library build was run, no local check_dag/review_split/preflight was run, and no live repository or launcher was edited. The single new node is intentionally unsplit; no item proof gap is left outside its cited statement.

Final full-packet dry run: deliver.py --no-push exited 0 and printed OK at 6804186d06; server preflight passed. The dry run finished before any push invocation. The delivered mathematical delta is one new statement-only node and zero Mathlib leaves.

## Preserved earlier report (superseded by this repair)

# Worker report

## Files written

- `dag/nodes/sec-proper-base-change/lemma-weil-pbc-completed-exchange-coherence.json`: seven-step repaired split; statement unchanged; no new nodes, no Mathlib leaves.
- `citations.json`: regenerated with a verbatim statement quotation for each node used by each step.
- `repair/update.py`: sandbox-only reproducible JSON edit; not a delivery file.

## Attachments

None. The item-id, blueprint-tag and completed-exchange declaration/concept searches in the read-only `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` returned no declaration. The shared node records stage-2 statements, but these are not closed slopmaster2 proofs. Nothing is attached on their strength.

## WANTED

None.

## What was wrong and what changed

The returned sandbox had four steps. I compared it with the current shared item, which retains the seven-step historical split, its reviewed strict-tower normalization dependency, stage-2 metadata, and the main-20261015 update. I preserved the current repository metadata and the sandbox's search records. The current blueprint statement and proof sketch are the same mathematical route as the earlier snapshot: finite exchange, strict tower, derived limit, then the specified completion comparisons. The previous report's claim that a changed blueprint justified discarding the normalization argument was incorrect.

The new split retains `lem-weil-pbc-strict-tower-exchange-mate-normalization` as an existing dependency. I did not edit it, remove it, merge it, or recreate it. The current repository already holds that reviewed node and `def-weil-pbc-strict-tower-operations`. Two existing generic tools in another unit fill the completion gap: `lem-sp-completed-pullback-adjunction` and `lem-sp-completion-mate-comparison`. They are declared in `split_report.tool_uses`, for the maintainer's judgment, without writing maintainer-owned `tool_uses`. Their dependency closures were inspected and neither depends on this item. The second tool identifies a particular ordered construction with an adjunction mate; it does not assert the identity or pasting clauses of this item. The steps still carry those arguments.

## Repair of every return point

1. C4, wrong finite coefficient category: the etale abelian exchange-identity-pasting citation is removed. Step 2 instead invokes the reviewed normalization equation in the actual derived category of constant-A strict module towers, with its b,d comparisons, then applies the derived-limit functor. This is exactly the ringed exchange identified by that lemma.
2. C4, arbitrary morphisms versus endomorphisms: naturality is now the natural-transformation equation of the completed adjunction mate in Step 7. Both the normalization lemma and the general completion-mate comparison explicitly assert naturality for morphisms of the input. No endomorphism clause of tower-compatibility or completed-map-reduction is promoted to arbitrary morphisms.
3. E3/E5, derived evaluation: no step assembles equalities in D(Tow) from levelwise equalities. Step 2 starts with the normalization lemma's equality in D(Tow). Rlim is applied to that equality. The possible lim^1 kernel of derived evaluation is irrelevant to this inference.
4. C2/E5, cancellation and composition: every step is marked non-elementary. Step 3 uses the existing comparison theorem for precisely the specified projection-formula and direct-image/limit maps, with their directions. It never identifies completed pullback of c inverse with the next square's reconstruction map. Step 4 fixes completed composition by conjugate adjunctions and checks the coherence on right adjoints, and Step 5 applies mate-pasting with these maps. Completed associators are not called finite associators.
5. Intermediate hypotheses: Step 1 establishes completeness of completed pullbacks and direct images from the completed-adjunction tool. Step 6 states exactly why the general mate-comparison tool applies to F_g' K and R_e K: it has no properness or etale-origin hypotheses and gives the same ordered exchange on every complete object. At a witnessed input the normalization lemma identifies this with the definition's map. No additional etale-origin witness is postulated for an intermediate object; the general construction provides the canonical extension used by the pasting equations.
6. D3/regression: the reviewed normalization node is explicitly restored in Steps 2, 3 and 7 and in proof_deps. All its downstream users and its statement are untouched. The source route is retained.

## Review by N8

I read the item's current `main-20261015` statement and both proof paragraphs, its old master proof and current shared split, the proper-base-change unit and chapter, and the statements of every node used in the repaired steps. I read proetale.tex Tag 099M (`lemma-naive-completion`), Tag 099N (`lemma-pushforward-Noetherian-case`) and Tag 09C9 (`theorem-proper-base-change`), and sites-cohomology.tex Tag 0D6E (`lemma-derived-pushforward-composition`), Tag 07A7 (`remark-base-change`), the horizontal and vertical compose-base-change remarks, Tag 0A07 (`lemma-Rf-commutes-with-Rlim`), and Tag 0E48 (`remark-compatible-with-diagram`). Stacks omits the completed base-change construction; I have not attributed the general mate-identification theorem to Stacks. Its existing DAG statement is the explicit agent-supplied tool filling that omission. I also read the source `fix-lem-exchanges.md` and the existing tool's detailed comparison argument to check the provenance, but the item uses only its statement.

Step 1 uses the completed-map definition for the ordered formula, the completed-pullback definition for its tower model and completion unit, the constant-completion equivalence for reduction, Rlim, and unit compatibility, and the completed-adjunction statement for its reflector and preservation of completeness. Its hypotheses are Noetherian A and an ideal on small sites, all present in the adic datum; the comparison lemma's additional perfectness hypothesis is also present. The complete categories are full, so arbitrary morphisms remain available. Ambient coefficient categories are kept distinct.

Step 2 uses the normalization lemma's exact displayed equality with b,d, for the given proper square, derived-complete K and its retained witnesses. It is an actual tower equality, explicitly natural in K. The Rlim statement is a functor on the derived strict-tower category; it therefore preserves that equality and the invertible comparisons. Levelwise equality is not used as a faithfulness argument.

Step 3 uses the generic comparison's exact equation t E^c = Rlim(v) s and its natural-transformation clause. Its H is the diagram projection map, and its t the normalized direct-image/limit map. These match the H,H-prime and b,d normalization in the retained lemma, and the K-injective direct-image/limit comparison specified by direct-image-limits. The definition supplies the ordered s, v', c inverse. Thus the statement citations give the actual maps being identified, not only isomorphic endpoints. The generic tool is valid for arbitrary small sites with constant coefficients and perfect quotients; these are the constant coordinates from Step 1.

Step 4 uses the comparison tool's stipulated conjugate completed composition maps, the general ringed-topos derived-direct-image composition statement (not its etale-only analogue), preservation of K-injectives by a right adjoint with exact left adjoint, and the conjugate bijection's composition and identity equations. The coefficient is constant A, so the inverse image is exact; iterated direct images of a K-injective need no additional replacement. At that model the comparisons are restriction along the same composite scheme map, giving the ordinary elementary associativity and unit equations on sections. This checks the canonical completed comparisons rather than assuming the finite-level ones suffice.

Step 5 substitutes the completed adjunctions into clauses (1), (2), (3) of mate-pasting and writes both resulting formulas. The square identifications paste by Step 4. Cartesian-square pasting provides the outer rectangles, also in the transposed configuration. This proves the item's two clauses using an existing general mate lemma, rather than declaring them part of a new lemma.

Step 6 checks the missing intermediate domain issue: completed pullbacks are complete by their reflector codomain, and direct images preserve completeness. The general comparison expressly says no etale-origin, constructibility, smoothness or properness is imposed. Therefore the canonical all-complete-input extension is used at the intermediate objects; where witnessed inputs are given it is the same map by Step 3. The two identity orientations use mate-pasting (4) and the explicit mate definition with identity adjunctions. This replaces the false assertion that s and completed pullback of c inverse automatically cancel.

Step 7 uses the mate definition as a natural transformation and the general comparison as a natural-transformation equality, plus the normalization lemma's morphism-naturality. Thus a map k need not come with etale lifts or be an endomorphism. Restriction reflects the result on complete objects by the coefficient equivalence.

I checked B--E against the files: no statement or hypotheses changed; no new nodes, definitions, duplicate candidates, or Mathlib leaves are introduced; every non-elementary fact above is covered by an actual cited statement. The two generic tools are strictly general comparison/adjunction facts and do not replace the unit's geometric route. All seven steps are below 2000 characters (largest 1272); there is no hidden long-step lemma. All quotations in citations.json are literal current statements, with their hypotheses included. JSON proof_deps is precisely the union of uses.

Small cases: K=0 and k=0 give the zero-map naturality equation; arbitrary k:K to H is handled in the full complete category. For either identity orientation the specified identity adjunction maps reduce the mate to identity. A horizontal double identity and a vertical double identity give the same identity after the unit comparisons. I=0 and A=0 cause no exception: the reflector argument allows the empty generating list and the zero ring, and no nonzero assumption was added. No uniform bound on finite origins, no witnesses for arbitrary intermediate objects, and no equality detection by evaluation is required. The only claims of exact finite witness transport are those of the retained reviewed normalization statement at its stated witnessed inputs.

## Searches and duplicate audit

I retained and read `searches.jsonl`: the 2026-10-17 LeanFinder query gives generic iterated limit isomorphisms; LeanSearch gives NatTrans.exchange, inverse-system and pullback results; grep for completed exchange/pasting/Rlim in CategoryTheory has no hits; Loogle reports its category identifier unknown, recorded as unavailable. These do not state this item's completed coefficient construction. The earlier recorded searches are retained too. No new node is created, so no new search is claimed. Whole-DAG and blueprint searches for completion mates, completed exchange, derived direct-image composition and the normalization notion led to the existing nodes cited here; `blueprint_refs.py ancestor` confirms this item is its own blueprint ancestor. The two generic comparison tools have no dependency path back to this item.

## Validation and unfinished work

The required initial dry run of the retained four-step packet exited OK (not pushed), commit b575aeea21. That mechanical pass did not establish its mathematics, and is superseded by this repair. A fresh dry run of the repaired packet is required before pushing. No Lean, Lake, compiler, local preflight or live repository mutation was run.

No mathematical work remains for this stage-1 split; server validation and delivery follow.

## Prior attempt report (retained, superseded)

The following is retained for continuity only. Its four-step proof and claims about evaluation and cancellation were returned and are superseded by the repair above.

# Worker report

## Files written

- `dag/nodes/sec-proper-base-change/lemma-weil-pbc-completed-exchange-coherence.json`: existing item updated and marked `split`; no new nodes were needed.
- `citations.json`: verbatim statement quotations for every cited node in every proof step.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` for the item id, blueprint tag, completed-exchange names, and the declaration recorded in the DAG; no declaration was present, so there is no finished Lean attachment.

## WANTED

None.

## What was checked and changed

The item statement was retained verbatim. The imported proof was tied to the older master snapshot and cited a long list of reconstruction and projection lemmas. The current `main-20261015` blueprint update gives the shorter finite-reduction and derived-limit route, and all facts needed by that route already have DAG nodes. I replaced the old proof by four complete steps and removed no statement hypotheses.

No source or blueprint error was found. The item remains in the proper-base-change chapter and unit. No new node was created, so there are no duplicate-node candidates or new Mathlib leaves to report. The item’s existing Mathlib search record was supplemented by fresh `msearch.py` runs for LeanFinder, Loogle, grep, and LeanSearch; the hits were generic limit/naturality declarations and no completed-exchange theorem (Loogle’s category query was reported invalid by the service).

## Review by N8

I read the current item statement and proof update at `literature/blueprint/main-20261015/blueprint/sec-proper-base-change/sk-thm-properbasechange/lemma-weil-pbc-completed-exchange-coherence.{md,proof.md}`, the imported statement and dependency records, and the source records of every cited node. I also checked the read-only slopmaster2 source for the recorded Lean declaration and found no declaration to attach.

Step 1 uses `lemma-weil-pbc-completed-map-reduction` for the exact finite reduction equation, transition compatibility, and compatible-endomorphism clause; `lem-weil-pbc-exchange-identity-pasting` for the finite identity, horizontal, vertical, and naturality equations as natural transformations; and `lem-weil-pbc-tower-compatibility` for the fact that the four corners and exchange maps are morphisms in the strict derived tower category. Those statements supply the finite hypotheses and ensure the equations assemble at the tower level.

Step 2 uses `prop-weil-pbc-rlim-functoriality`, whose statement makes `R lim` a triangulated functor, so it preserves identities and composites. It also uses `lemma-weil-pbc-r-lim-levelwise-isomorphism` exactly for invertibility of a specified Roos-triangle morphism whose components are levelwise isomorphisms. I checked that the proof does not infer equality merely from componentwise evaluation.

Step 3 uses the defining statement of `def-weil-pbc-completed-base-change-map`, including its ordered reconstruction, derived-limit exchange, and inverse direct-image/limit comparison. The cancellation is an elementary composition calculation with the same intermediate comparison and its inverse; the finite associativity maps are those in the cited exchange equations. This establishes identity and both pasting laws with the canonical associativity maps retained.

Step 4 checks naturality for an arbitrary morphism of inputs. The finite exchange node explicitly states naturality, `lem-weil-pbc-constant-completion-equivalence` states naturality of the reduction comparisons and quotient transitions, and tower compatibility supplies the compatible tower maps. The same `R lim` functor and fixed conjugation from Steps 2–3 therefore give the completed naturality square. All hypotheses used in these steps—properness and derived completeness, finite étale-origin witnesses, specified tower maps, and the chosen comparison maps—come from the completed-base-change definition and are unchanged.

The small edge cases checked were identity squares (the tower map is the identity, so cancellation gives the identity), a single finite quotient (the statement reduces to the finite exchange law), and a zero input morphism (naturality is the zero-map equation). The server-side `check_dag` preflight passed before this report was written.

## What could not be finished

Nothing remains for this stage-1 split.
