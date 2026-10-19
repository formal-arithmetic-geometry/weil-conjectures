# Stage 1 report: lem-per-etale-local-infinitesimal-lifts-smooth

Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-etale-local-infinitesimal-lifts-smooth.json`: item, statement, split; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-etale-local-lift-torsor-quasi-coherent.json`: one new statement-only node, unsplit; no Mathlib match.
- `citations.json`: verbatim statement quotations for each of the six steps' cited nodes.

Attachments: none. Read-only searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the exact item id, infinitesimal lifting, formal smoothness, and lift/torsor terminology found no project declaration of this criterion or the supporting scheme lift-sheaf lemma. The generic torsor module in `CategoryTheory/Sites/Torsor.lean` concerns arbitrary abelian sheaf torsors, not the identification of scheme morphism lifts. It is already represented by the cited general torsor node. No Lean was written or compiled.

WANTED: none.

The item statement is unchanged from the current shared DAG. It is the etale-local version of the formal smoothness criterion: the torsor argument in Stacks Tag 02H6 (`more-morphisms.tex`, `lemma-smooth-formally-smooth`) and its etale version Tag 04AM (`spaces-more-morphisms.tex`, same label) apply, with the hypothesis here supplying the local lifts. Tag 03P2 supplies affine etale acyclicity. The item does not assume Noetherian schemes, separatedness, smoothness of the test square, or finite presentation of its square-zero ideal; none is needed. I read the item's chapter and unit records. The generic infinitesimal criterion supports the existing descendant `lem-per-strict-log-jacobian-criterion`, Steps 3--5, without changing the chapter/unit route.

## Repairs to the retained attempt

The required initial dry run exited with SEARCH CHECK FAILED: its four supporting-node search entries were absent from `searches.jsonl`. I ran those exact queries through `msearch.py`, read their actual hits, and tried a second semantic phrasing, a second Loogle name query, and a broader grep. The new record contains seven actual logged queries with results and assessments. The failed Loogle identifier pattern is described as invalid, not treated as evidence of absence; the second query worked. Ring-level `derivationToSquareZeroEquivLift` (Mathlib `RingTheory/Derivation/ToSquareZero.lean:116`) and the presheaf universal property (`Algebra/Category/ModuleCat/Differentials/Presheaf.lean:96`) are related ingredients, not one-line specializations of the scheme sheaf statement. The prior log and the original item's inherited search records were preserved; no unrun query was added.

STATEMENT-DISPUTED (earlier supporting-node draft): the displayed `Hom` over `O_T` had an argument explicitly defined on `T_0`, with no direct-image identification. The type check is `a_0:T_0→V`, so `a_0^*Omega` is in `Mod(O_{T_0})`, whereas `Hom_{O_T}` expects modules on `T`. The repaired statement uses `H=i_*Hom_{O_{T_0}}(a_0^*Omega,I)` and explicitly defines its sections and quotient scalar action. This also records why the ideal is an `O_{T_0}`-module. The item statement itself was not disputed or altered.

The earlier draft bundled globalization into the supporting node, leaving the item almost entirely an application of that node (D2). I removed every existence conclusion from the new node and generalized its test schemes beyond the affine case. It now states only the sheaf property, the quasi-coherent coefficient module, and its natural simply transitive action on any nonempty lift-section set. Local nonemptiness and globalization are proved in the item using the already existing general torsor and cohomology lemmas.

The earlier blueprint place claimed to quote a local-model Step 3 of `lem-per-artin-gabber-affine-curve`. I opened the current main-20261015 blueprint text and the current ancestor node: that ancestor has since been split by a different dimension/duality argument, and its current Step 3 is an adjunction argument, not the historical preparation text. I retained the required ancestor and via chain but replaced the inaccurate quotation with an explicit reference to the actual immediate parent's Steps 3--5 and a note about this historical lineage. No ancestry or unit record was rewritten.

## Not duplicates

lem-per-etale-local-lift-torsor-quasi-coherent vs lem-per-etale-local-infinitesimal-lifts-smooth: the former identifies a lift sheaf and its coefficient module for one fixed square, over arbitrary schemes, and asserts no existence of lifts; the item quantifies over all affine test squares and concludes smoothness by local nonemptiness, vanishing, and torsor classification.

lem-per-etale-local-lift-torsor-quasi-coherent vs lem-sc-torsor-h1: the existing general theorem classifies arbitrary abelian etale sheaf torsors by H1; it does not identify scheme morphism lifts with a torsor or prove quasi-coherence of their derivation module. The classification is reused in Step 4, not copied.

lem-per-etale-local-lift-torsor-quasi-coherent vs lem-sc-etale-affine-qcoherent: the existing theorem gives higher-cohomology vanishing once a quasi-coherent module is supplied; it says nothing about the lift sheaf or its action. Step 3 reuses the vanishing theorem.

lem-per-etale-local-lift-torsor-quasi-coherent vs lem-per-log-smooth-infinitesimal-calculus: that node assumes log smoothness and locally Noetherian fs log schemes and concerns log morphisms and log derivations. The new node assumes only a locally finitely presented ordinary scheme morphism, permits arbitrary square-zero test schemes and possibly empty lift sheaves, and asserts no local lifts.

I searched the entire DAG for Tags 061A, 061C, 061D, 04AM, 04FH, 04FJ, 04FK and the lift/derivation/torsor concepts, and used `tools/blueprint_refs.py search` for torsor, derivation, 04FJ and 061C plus `ancestor` for the item. No existing node carries the new lemma's Stacks tags or its statement. The generic finite-constant torsor results are too restrictive in their coefficient sheaves; the general abelian classification above is the correct reusable one. `same_as` remains empty.

## Review by Q31

I reviewed this as a direct-delivery worker, with the JSON node statements and Stacks sources open. For the item I read Tag 02H6 in `more-morphisms.tex`, including its two separate tasks (local sections and vanishing), and Tag 04AM in `spaces-more-morphisms.tex`, which uses exactly this argument on the etale site. For the new node I read Tags 061A (`lemma-sheaf`), 061C (`lemma-action-sheaf`) and 061D (`remark-special-case`, target thickening equal to itself), and the final quasi-coherence paragraph of 04AM. The scheme counterparts 04FH/04FJ/04FK give the same derivation action on Zariski opens. The source's 04AM paragraph has an immaterial `Omega_{X/S}` in one sentence, while its displayed coefficient and required argument use `Omega_{X/Y}`; the new node consistently uses differentials relative to the actual base W. The finite-presentation hypothesis, not smoothness or local freeness of differentials, is what is needed for quasi-coherence of Hom.

Step 1 cites only the new lemma: its statement explicitly supplies H on T, its quasi-coherence, the sheaf L with the required two equations, and the simply transitive natural action. The test schemes here are affine, which is allowed by the new lemma's more general arbitrary-scheme hypothesis. Step 2 uses exactly the general abelian-sheaf clause of `def-sc-gm-torsor`: the given a_j satisfy the defining equations and the family is jointly surjective, so restrictions are trivialized by translation. This is a direct use of the definition; it asserts no automatic descent of the originally given maps.

Step 3 uses `lem-sc-etale-affine-qcoherent`, whose statement expressly covers every quasi-coherent module on every affine scheme and every q>0. With q=1 and the module H on T all its hypotheses hold, even for a non-Noetherian base and an ideal not finitely generated. I read Tag 03P2 (`etale-cohomology.tex`, `theorem-zariski-fpqc-quasi-coherent`) for this input. Step 4 uses `lem-sc-torsor-h1`, whose actual statement has arbitrary abelian G and sends zero to the trivial torsor. I read Tag 03AJ (`sites-cohomology.tex`, `lemma-torsors-h1`) and checked this is not merely a theorem about finite constant torsors. Since H1 is zero, bijectivity yields an isomorphism with H_et; taking the preimage of zero gives a global lift. These two off-unit statements are declared generic tool uses in `split_report.tool_uses`; neither replaces a step of the unit's own proof.

Step 5 uses `def-sbc-formally-smooth` and its full quantifiers over affine first-order thickenings and compatible maps: the arbitrary square fixed in Step 1 is exactly such a square. Step 6 uses the present `def-sbc-smooth-morphisms`, whose statement cites the dedicated locally-finite-presentation definition and makes formal smoothness plus that property its smoothness criterion. The previous draft's citation quote for this definition was stale; `citations.json` was regenerated from the current statements. The item retains its original finite-presentation hypothesis.

For B1--B7 the new node is statement-only with empty proof/dependencies and null proof origin; it introduces f,i,I,a0,b,E,H,L,U,U0 and their types, cites the definition of each specialized notion, and states the actual meaning instead of requiring interpretation by a tag. The relative differential and module pullback definitions have domains V→W and T0→V as used; the quasi-coherent definition is `pqf-def-coherent` and the associated etale coefficient is exactly `def-sc-etale-qcoherent-module`. No hollow definition, clause restatement, new elementary lemma, or new H1 classification was introduced. All non-elementary uses in the item are the statements of its cited nodes, not facts hidden in their proofs (C1/C3/C4). No proof step exceeds 2000 characters.

I tested the new statement at I=0, when the lift sheaf is a singleton and H=0; at a square-zero extension with no lifts, when the sheaf can be empty and the action assertion is correctly conditional on a chosen section; at V=the affine line over W, when lifts differ by sections of the square-zero ideal; and at non-affine T, where the statement correctly does not assert globalization. This last test explains why deleting the old global-existence clause matters. For the item, empty tests cause no exception, an empty source is smooth, and local lifts are never glued without first trivializing their torsor.

Unfinished work: no part of this one-level split remains; the new statement-only lemma is intentionally left for a subsequent stage-1 item. Required dry-run results and delivery are recorded below when obtained.

## Retained earlier report (superseded by the repairs and review above)

# Stage 1 report: lem-per-etale-local-infinitesimal-lifts-smooth

Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-etale-local-infinitesimal-lifts-smooth.json` — item, statement node, split.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-etale-local-lift-torsor-quasi-coherent.json` — new statement node, unsplit, no Mathlib match.
- `citations.json` — verbatim statement quotes for every cited node in every item step.

Attachments: none. I searched the slopmaster2 source by the item id and by the lifting/smoothness terminology; no sorry-free project declaration states this item exactly.

WANTED: none.

The imported item statement agrees with Stacks Tag 02H6: locally finite presentation plus the stated étale-local square-zero lifting condition implies smoothness. I retained all hypotheses, including affine test schemes, square-zero ideal, compatibility on the closed subscheme, and joint surjectivity of the étale family. The blueprint ancestor is inherited from the imported node; its final sentence gives the infinitesimal criterion used here. No source statement was corrected.

The new node isolates the non-elementary part of the argument for one fixed lifting square. It defines the étale sheaf of lifts explicitly and states that differences of lifts are derivations, identified with the quasi-coherent sheaf `Hom(a₀^* Ω¹_{V/W}, I)`, so the lift sheaf is a torsor. It also states the affine globalization when its first cohomology vanishes. This is the sheaf-of-lifts/derivation-torsor argument in Tag 02H6, with affine quasi-coherent étale cohomology vanishing from Tag 03P2. I searched the whole DAG and blueprint for this torsor statement and found no duplicate; the existing finite torsor and generic sheaf-torsor nodes concern different coefficient objects or different conclusions.

### Earlier review from the retained attempt

I read the item node, its source reference, the imported blueprint place, and the definitions cited by the statement: `def-sbc-first-order-thickening`, `def-sbc-formally-smooth`, `def-sbc-locally-finite-presentation`, and `def-sbc-smooth-morphisms`. I also read `lem-sc-etale-affine-qcoherent`, whose statement gives vanishing of positive étale cohomology for a quasi-coherent module on an affine scheme, and `def-sc-relative-differential-sheaf` for the relative differentials used by the new node.

Step 1 fixes an arbitrary first-order thickening and compatible maps. The cited new node states exactly the lift sheaf, its derivation torsor structure, quasi-coherence, and the implication from local sections plus affine H¹-vanishing to a global lift. The cited affine acyclicity node supplies the H¹ hypothesis for the sheaf in that node. The given family in the item is jointly surjective and therefore supplies the required local sections; the ideal is square-zero and the test scheme is affine, matching every hypothesis.

Step 2 cites the definition of formal smoothness. Since Step 1 handled an arbitrary affine first-order thickening and arbitrary compatible map, it supplies precisely the dotted lift required by that definition. Step 3 cites the definition of smooth morphism and the locally finite presentation definition; the original hypothesis supplies the latter, while Step 2 supplies formal smoothness, so their conjunction is exactly smoothness.

I checked edge cases while auditing the statement: an empty source makes the lifting condition vacuous in the same way as formal smoothness; a zero ideal makes the lift sheaf a singleton torsor; and a trivial morphism on an affine scheme reduces to the usual square-zero lifting criterion. I corrected the imported item only by filling its blueprint proof place and adding the explicit supporting torsor node; the mathematical statement and its dependency list remain unchanged. All Mathlib searches for the item and new node were run through `msearch.py` and recorded in `searches.jsonl`; none gives an exact scheme-level theorem.
