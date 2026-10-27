# Worker report: lem-sfb-exact-algebraic-group-property-permanence

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-exact-algebraic-group-property-permanence.json`: existing statement, split into nine proof steps; no exact Mathlib match.
- `citations.json`: verbatim statements supporting every use in every proof step.
- `searches.jsonl`: actual Mathlib search log, preserved with the sandbox.
- `report.md`: this report. Sandbox-only reading notes and the generation script are not delivery files.

New nodes: 0. New Mathlib leaves: 0. All non-elementary inputs already have nodes. The statement and statement dependencies are unchanged.

## Attachments

None. I searched `lean/WeilConjectures/` for the item tag and the affine/quotient/extension/smooth/connected notions, and inspected relevant group-scheme files. No project declaration states all six implications. General translation and identity-component lemmas, results about proper images, finite etale torsor quotients, and individual descent theorems do not attach this item. The existing affine-normal-quotient node is a proper input for the affine quotient clause, not an attachment of the item.

## WANTED

None. Milne's Algebraic Groups PDF and the relevant Stacks sources are present locally. No SGA source is used.

## Problems found and changes

The item was statement-only, with no proof or proof dependencies. Its statement agrees with Milne Proposition 8.1(a),(b), printed p.149, interpreted by Definition 1.61 on p.24. I found no statement dispute and changed no hypotheses. The source's one-line reference to four earlier results is expanded into an argument using existing nodes rather than four nodes restating the clauses.

The affine quotient theorem produces an affine quotient Q_0, whereas the item has a specified target Q. Step 4 explicitly descends maps both ways, with equality checked on E, to prove Q is that quotient. Merely saying 'apply the affine quotient theorem' would omit this comparison. The smooth quotient clause does not assume a smooth kernel. For connectedness I avoid assuming a fibre has a rational point over its original residue field: an arbitrary point supplies a possibly inseparable residue-field extension L, and the rational-point criterion applies to the kernel over every L/k.

The latest blueprint is `literature/blueprint/latest/` (main-20261024). I read the current unit section and its direct-images proof, especially (3). This item is a prerequisite far below the algebraic-group/product ancestry already recorded on the item. There is no level-one or level-two route alteration. The ancestor search returns None for this imported ancestry; I preserve the item's existing `blueprint.from.node = null` and its precise place, rather than invent a blueprint id. Whole-blueprint search for algebraic groups found only representation/monodromy and characteristic-zero affine geometry material; nothing states these six arbitrary-field implications.

## Unfinished work

None in this stage-1 item. This delivery writes no Lean and invokes no compiler, Lake or global build.

## Not duplicates

No new node is created. I reuse `lem-sfb-affine-normal-quotient-geometry` for the affine quotient and the existing fpqc, smoothness and connectedness tools. In particular I do not duplicate `lem-sfb-connected-group-extension` (affine groups over an algebraically closed field), or `lem-sfb-smooth-affine-normal-quotient-lifts` (smooth connected groups over an algebraically closed field); neither applies to the full statement here. The existing affine-normal-quotient node's dependency closure does not contain the item, so that reuse does not reverse the dependency direction.

## Mathlib searches

The item's inherited searches are retained. I additionally ran msearch.py with LeanSearch, Loogle, grep, and two LeanFinder phrasings; all completed and their exact queries, results and digests are recorded. I read the hits. The Loogle hit constructs the Hopf algebra of global sections of an affine group scheme. The grep hit is in Geometrically/Connected.lean, where connectedness follows from an already geometrically connected open morphism. LeanFinder returns module finiteness/exactness and cotangent sequences for the first phrasing; the second returns flat-surjective affine criteria, the quotient-map theorem and faithfully flat ring descent. LeanSearch likewise returns tensor exactness, smooth algebra flatness and individual morphism definitions. These are useful general ingredients but do not assert permanence in exact sequences of finite-type group schemes. The hits therefore neither attach the item nor make it a Mathlib leaf. No new node requires additional searches.

## Review by Q61

I read Milne Proposition 8.1 on p.149 and its cited proofs: Proposition 1.62 on p.24, Example 2.68 and Proposition 2.69 on p.60, Corollary 2.70 on p.61, Proposition 5.24 on pp.104--105, Theorem 5.13 on p.101, Proposition 5.29 on p.105, and Proposition 5.59 on p.114. Milne's smoothness argument uses geometric reducedness; my replacement uses the already available general smooth descent theorem, so `proof_origin.by` is honestly `agent`. Similarly, the connectedness clause is proved via fibres and quotient topology rather than importing the source's component-group argument. There is no source for a new node, since there are no new nodes.

For step 1 I opened the statements of `pqf-lem-locnoeth-lft`, `lem-weil-pbc-proper-fp-permanence`, `pqf-lem-lft-fp-locnoeth`, `lem-weil-pbc-closed-immersion-integral-separated-uc`, `lem-weil-pbc-affine-morphism-permanence`, `lem-weil-pbc-qcqs-morphism-permanence` and `def-weil-pbc-fpqc-covering`. They supply, respectively, the locally Noetherian target, finite-type cancellation (clause f), conversion to local finite presentation, affineness of the diagonal, its quasi-compactness, quasi-compactness of q, and the exact covering condition. I also read Stacks morphisms.tex at lemma-permanence-finite-type (01T8) and lemma-noetherian-finite-type-finite-presentation (01TX), and verified tags against tags/tags. A field is Noetherian by its two ideals. Finite type gives quasi-compactness; separatedness gives an affine, hence quasi-compact diagonal. The finite affine cover of the inverse image of each affine target open verifies the fpqc definition directly, without an uncited theorem converting flat surjections to covers.

For step 2 I read `def-sc-group-scheme` and `def-pc-fibre-product`. These really give morphisms for multiplication and inverse, the kernel square, and uniqueness of fibre-product maps. The displayed inverse maps are consequently scheme morphisms, not just a bijection of field points. The two identities are an elementary computation. There is no hidden representability lemma or appeal to a weaker Yoneda statement.

For step 3 `pqf-def-affine-morphism` identifies affineness over the affine point; `lem-weil-pbc-affine-morphism-permanence` provides base change and affine source over affine target, and `lem-weil-pbc-fpqc-descend-affine` gives the required base descent. I read Stacks descent.tex at lemma-descending-property-affine (02L5), including its proof. The descent cover is q itself, justified before use, and the torsor isomorphism respects the projection required by the base change.

For step 4 I read the entire statement of `lem-sfb-affine-normal-quotient-geometry`, not its proof. Its hypotheses demand that E and N are affine; N is shown affine using the closed-immersion and affine-permanence statements. Its conclusion supplies an affine finite-type Q_0, a flat surjective finitely presented q_0, and exactly the same kernel. I use none of its other permanence conclusions. `lem-weil-pbc-fpqc-representable-descent` states existence and uniqueness for compatible morphisms on an fpqc covering, which is precisely what constructs a and b and then makes their composites identities. I read its full statement and the Stacks 023Q interpretation. The overlap calculation is written for both covers, so there is no silently assumed universal property of the originally given Q. This comparison is a short direct application of the cited descent statement, not a separate unsplit lemma.

For step 5 I read `lem-pc-proper-base-change`, specifically its smooth clause (2), `lem-trf-smooth-fpqc-base-descent`, and `lem-trf-smooth-composition`. They supply the base-changed smooth projection, descent along a flat quasi-compact surjection, and composition. I read Stacks 01VB/01VA in morphisms.tex and 02VL in descent.tex. All flatness, quasi-compactness and surjectivity hypotheses on the actual map q are available from step 1. No affine hypothesis is introduced into the smooth clause.

For step 6 I read `lem-sbc-smooth-flat-surjective-source-descent` and the corresponding project Lean theorem's source and proof in `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`. Its statement asks for flat, surjective and locally finitely presented q, which step 1 establishes. Its conclusion concerns the structure map Q -> Spec k. This is source descent, distinct from the base descent used in step 5. No assumption of smoothness of N is made here.

For step 7 I read `lem-sbc-connected-rational-point-geometrically-connected`, `def-pc-scheme-fibre` and `lem-weil-pbc-surjective-base-change`. The first explicitly allows every field extension, not merely separable or algebraic ones; I read Stacks varieties.tex lemma-geometrically-connected-if-connected-and-point (04KV). The second includes the homeomorphism with the ordinary topological fibre and the canonical residue-field morphism. The third makes F_L -> F surjective. The chosen x is an arbitrary point of a nonempty fibre, so its residue field L is legitimate without a Nullstellensatz or closed-point existence assumption. The inverse translation is the same formula already proved in step 2. Connectedness descends along a continuous surjection by pulling back clopen separations, an argument written out here. Thus no separate fibre-translation or geometric-connectedness node is hidden in the step.

For step 8 I checked `lem-weil-pbc-flat-qc-surjective-quotient-map` against its flat/quasi-compact/surjective assumptions, and `lem-weil-pbc-connected-fibres-quotient-preimage-connected` against nonempty connected fibres and the quotient topology. I read Stacks topology.tex lemma-connected-fibres-quotient-topology-connected-components (0377), including its proof. The subset used is the whole of Q, hence closed. For step 9 the definition `def-weil-connected-scheme` requires nonemptiness, which the identity section provides, and the continuous-image proof is elementary and explicit.

I checked B1--B10: there are no new statement-only nodes or undocumented notions introduced into the statement; no new Mathlib leaf or unmatched line citation; searches are genuine; blueprint metadata is preserved and same_as is searched. For C1--C8, every non-elementary tool is a cited existing statement with a full verbatim citation in citations.json, all uses occur in proof_deps, and off-unit non-leaf tools are declared only in split_report.tool_uses. For D1--D5, the steps give the argument instead of relabelling clauses, there is no circular inference, and no source's 'obvious' hides a new lemma. Every step is below 2000 characters. For E1--E7 I checked actual maps, projections and hypotheses, and found no false statement or required correction.

Small cases checked: N=1, Q=1, and the wholly trivial group satisfy the argument; the identity ensures nonemptiness. In characteristic p the Frobenius G_m -> G_m has kernel mu_p, so the smooth quotient argument must allow a nonsmooth kernel, as it does. A connected kernel over an imperfect field is covered through its identity and the all-field-extensions criterion, without assuming perfectness. Affineness of the quotient uses normality, so the nonnormal GL_2/B = P^1 example is not misclassified. Noncommutative multiplication order is (g,n) -> (g,gn) with inverse (g,h) -> (g,g^{-1}h), and normality is used where the affine quotient theorem requires it.
