# Stage-1 report: sbc-def-admissible-lattices

## Worker report

This handoff completes the existing stage-1 definition split. It introduces no new nodes and makes no Lean changes. An earlier attempt treated a historical stage-2 review as a blocker; the present assignment explicitly requests stage 1, so no stage-2 artifacts or compiler results are claimed.

## Files written

- `dag/nodes/sec-smooth-base-change/sbc-def-admissible-lattices.json`: definition, status split, thirteen existing statement dependencies; no full Mathlib match.
- `citations.json`: empty list, because a definition has no proof steps.
- `report.md`: the source audit and handoff.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: this definition is not the statement of `sk-rem-rest`. The earlier authorized searches and `searches.jsonl` are retained.

## Attachments

None. I searched all of `WeilConjectures/` in `/home/ubuntu/weil-src-slopmaster2` and the read-only upstream master for the exact blueprint tag, admissible/integral lattice wording and the corresponding camel-case names. No declaration states this three-part derived-square datum. The existing audits are none; no upstream sorry declaration is used as a finished proof.

## WANTED

None. The repository-relative blueprint path is absent on this machine, but both source branches are available read-only under `/home/ubuntu/work-bp/sheaf/literature/blueprint/`. I read the complete master file `master/blueprint/sec-smooth-base-change/sk-rem-rest/sbc-def-admissible-lattices.md`, its unit `_section.md`, and slopmaster2 `src/version/sketch/32_smooth_base_change.tex`, lines 1170–1288. This is a blueprint-specific definition, not a theorem of a Stacks tag. Its source field retains the repository-relative identity, and no fictitious Stacks source is substituted.

## Statement corrected

STATEMENT-DISPUTED: the import uses the integral and rational constructible categories without their domain hypotheses. The actual statements of `def-weil-pbc-bounded-constructible-complete` and `def-weil-pbc-rational-category` require a noetherian finite-dimensional scheme with ell invertible. The identity square on Spec F_ell satisfies the imported smooth/qcqs hypotheses, but these category definitions do not apply. This is a natural-language domain check, not a compiler experiment or a counterexample to smooth base change. The corrected statement makes exactly that domain explicit on T. No finite-dimensionality assumption is added on another corner.

The definition also specifies A_n=A/(varpi^(n+1)) for n>=0, the completed coefficient sheaf, the reduction tensor over that sheaf, the essential-image functor, and the four output corners. The common interval is independent of n and of the four families; a common stratification is not imposed. No preservation-of-constructibility or reduction/direct-image comparison theorem is asserted.

The master's parenthesis points forward to a comparison with Karoubi pairs. That assertion is kept separate from the definition, whose chosen data are precisely (L,alpha) in the master's raw rationalization. The older slopmaster2 source instead uses (L,e,alpha) in the Karoubi envelope, without assuming the idempotent splits. These presentations are not silently identified. The existing `thm-weil-pbc-finite-stage-karoubian` is a separate comparison interface, not a constituent of the lattice definition.

The exact imported statement and dependencies, the source and reason for the correction, and the complete direct-citer audit are recorded in `split_report.statement_change`. This is the stage-1-owned record; no stage-2 `lean` or top-level `statement_change` record is supplied.

Direct citer audit (all DAG `stmt_deps` and `proof_deps` were checked): `sbc-thm-e-coefficient-smooth-base-change` is the sole direct citer and is marked **holds: false**. It assumes all schemes noetherian and ell invertible, but not finite dimension of T; noetherianity alone does not supply this. Its current exchange also prints S although its functors land on X. Both issues are reported for that node's worker; this delivery does not edit it. The Qbar-coefficient theorem is a consumer but does not directly cite this definition in its dependency lists.

## Search and duplicate audit

The retained ten Mathlib search records were compared by exact tool and query with `searches.jsonl`. They include two semantic phrasings, Loogle searches for the essential image and derived category, and source greps. LeanSearch was unavailable and is recorded as unavailable. The invalid first query `CategoryTheory.EssImage` is explicitly marked invalid and was followed by the valid `CategoryTheory.Functor.essImage` search. No search was invented or silently converted from unavailable into no match.

The semantic hits concern perfectoid rings, geometric integrality, condensed modules and generic sheaf constructions. The lattice grep hit is a root-system lattice. I read `Mathlib/CategoryTheory/EssentialImage.lean:35–78`: `Functor.essImage` at line 45 supplies the generic existential object and isomorphism, not the adic constructible categories or four-square predicate. These partial ingredients do not make the full definition a Mathlib leaf.

Whole-DAG searches for lattice/admissibility/rationalization and whole-blueprint searches were used in the earlier split; I repeated `tools/blueprint_refs.py search 'admissible lattice'` and the whole-DAG lattice search. The blueprint matches are this definition and its E/Qbar consumers, not another definition. Lattice sheaf and lisse-lattice lemmas concern sheaves, and the lattice-stabilizer lemma concerns vector spaces; none duplicates this derived-square datum. Thus `blueprint.same_as=[]`. Since the item is itself imported, `blueprint.from=null` is correct. No new node or new same-tag pair is proposed.

## Review by NL

I read the chapter and unit records, the full master definition, and the surrounding slopmaster2 adic/rational text. The unit's continuation into pro-etale, adic and rational coefficients has no proof steps; a constituent-definition split keeps this route. Renaming the slopmaster2 labels (X,Y,X',Y'; f,g,v,f') to (T,S,Y,X; g,f,e,h) gives exactly the four families here. The master rather than the older Karoubi-envelope presentation determines the lattice data.

I opened the actual statements of all thirteen dependencies and checked their uses clause by clause:

- `sbc-def-base-change-square` gives h:Y->X, e:Y->T, f:X->S, g:T->S and the Cartesian identification. `def-sbc-smooth-morphisms` defines smoothness; `def-weil-pbc-scheme-conventions` collects qcqs. No theorem of smooth base change is taken from these definitions.
- `def-weil-l-adic-coefficient-extension` supplies the finite extension, DVR, uniformizer and finite quotient rings at positive index. The shifted index n+1 ensures n=0 is the residue-field quotient, not A/(1).
- `def-weil-pbc-adic-coefficient-datum` supplies the completed coefficient ring sheaf, its derived module category, and reduction by derived scalar extension. Its hypotheses hold here: a DVR is noetherian; finite quotients are supplied by the coefficient-extension node; A/(varpi) is additively torsion because finite; and [A --varpi^k--> A] resolves A/(varpi^k), since the nonzero uniformizer is not a zero divisor in the domain A. Thus each quotient is perfect. This two-term calculation introduces no lemma node.
- `lem-weil-pbc-profinite-coefficient-inverse-image` explicitly supplies both the finite constant-coefficient identification and the inverse-image coefficient isomorphisms for any scheme map and countable finite-ring tower. The quotient tower meets these hypotheses. Only its finite-level identifications are needed here; inverse image is not assumed to preserve arbitrary limits.
- `def-weil-pbc-bounded-constructible-complete` supplies the integral full subcategory with derived completeness, uniform reduction-tower constructibility and compatible etale witnesses. Its stronger tower condition is retained by reference, and its domain on T is explicit. `def-weil-pbc-rational-category` supplies raw localization with the same objects and Hom groups tensored with E, so L[1/varpi] and alpha have exactly the stated meaning. Neither definition is used as an idempotent-splitting theorem.
- `def-weil-pbc-constructible-complexes` supplies the bounded constructible etale category for the finite commutative ring A_n. `def-weil-pbc-proetale-modules` supplies the derived comparison inverse image nu_T^*. The displayed existential M_n and isomorphism are exactly essential-image membership, without a full-faithfulness assertion or extra chosen witnesses.
- `def-weil-pbc-proetale-operations` supplies ordinary uncompleted unbounded pullback/direct image with identified ring sheaves. The finite coefficient identifications above meet its input. The outputs are respectively on S, X, Y, X. No constructible-preservation theorem is needed: that property is the condition being defined.
- `def-weil-proetale-constructible-sheaf` supplies finite-coefficient constructibility by finite stratifications and locally constant finite stalks on each corner. `def-weil-derived-cohomology-sheaves` supplies H^i for any ring sheaf. The same integers a<=b work for every n and all four families, while their stratifications may vary.

For B I checked self-contained objects, genuine notion dependencies, source identity, TeX and the exact attachment criterion. No new statement or unsupported Stacks attribution is present. For C there are no proof steps or proof citations, so `citations.json=[]` is complete; the substantive coefficient identification is nevertheless an explicit statement dependency. For D this is the prescribed split of a definition into existing constituent notions; no clause is moved into a new child. For E I checked the category domain, quotient index and corners above against the actual inputs of the cited statements.

Small cases: the zero object with its identity rationalization meets both predicates with an interval containing degree zero. The empty scheme introduces no nonempty-corner requirement. An identity square leaves all four functors correctly typed. The n=0 stage is A/(varpi). A nonzero torsion integral object may rationalize to zero, so neither torsion-free cohomology nor an integral isomorphism alpha may be demanded; neither was added. Separate bounds depending on n would be weaker than the source and are not used.

The fresh local audit checked the imported old statement and dependencies verbatim, the complete one-citer correction audit, all thirteen bracketed statement dependencies, all ten searches against their actual log, and the 417-node dependency closure for cycles and missing references. It passed. No independent second-reader signature is asserted by this author; the next reader reviews the final sandbox and delivers it.

## Historical review scope

The previous attempt read a stage-2 return at head `41486c0bdd16`, requiring a Lean module, a lean record, compiler evidence, an independent second reading, and a hollow-definition audit. Those stage-2 requirements are outside this explicitly stage-1-only dispatch. The natural-language domain correction and citer audit are retained here, but no stage-2 repair is claimed. This historical mismatch is not a blocker to the stage-1 handoff requested now.

## Unfinished work

No stage-1 split work remains. The direct citer's missing category-domain assumption and corner typo are reported above for its own worker. Independent second reading and delivery belong to the next worker, as specified by the brief.

## Dry run

Validation command: `python3 /home/ubuntu/weil-launcher-nt/deliver.py NL sbc-def-admissible-lattices --no-push`. Its output is retained in `dry-run.log`. The installed tool takes two positional arguments; the brief's trailing `.` prints usage, so it is omitted. No push is made; READY is returned only after this command prints OK for the final files.

## Second reading by NL

I independently opened delivery-errors B–E, dag-sync, GOAL, the master definition `sec-smooth-base-change/sk-rem-rest/sbc-def-admissible-lattices.md` (order 1444), its chapter and unit records, and the older slopmaster2 text at `/home/ubuntu/work-bp/sheaf/literature/blueprint/slopmaster2/src/version/sketch/32_smooth_base_change.tex:1230–1261`. The master definition is the primary source; it has no Stacks tag, and substituting one would misattribute this square-dependent predicate. I compared its hypotheses and every clause with the sandbox statement and opened each of the thirteen dependency statements in the read-only shared DAG.

- Item hypotheses: compared the Cartesian square, smooth f, qcqs g and finite E with the master and the integral/rational category domains with their definition nodes; PASS with the already recorded STATEMENT-DISPUTED correction. The identity square on Spec F_ell verifies the original domain omission. The correction is explicit and the source's lattice and admissibility predicates are retained.
- Integral-lattice clause: compared with the master's chosen isomorphism L[1/varpi] to K_E; PASS. The older source instead uses an idempotent-pair datum. The sandbox follows the master and asserts no equivalence with that older presentation.
- Finite-level clause: compared with the master's essential-image condition and the older source's explicit A_n=A/(varpi^(n+1)); PASS. The existential M_n and isomorphism express the condition without adding chosen witnesses to the lattice data.
- Square-constructible clause: compared all four functor expressions with both sources, using (old X,Y,X',Y'; old f,g,v,f')=(T,S,Y,X; g,f,e,h); PASS. The outputs are on S,X,Y,X respectively, and a single interval bounds all four families at every n. A common stratification is not required by either source.
- Proof steps: none, checked against `proof=[]` and `proof_deps=[]`; PASS. This is a definition resolved into existing notions, not a theorem whose proof has been moved to a child. `citations.json=[]` exactly matches the absence of proof citations.
- New nodes: none, checked all sandbox node paths against the shared DAG; PASS. No elementary fact, duplicate, clause restatement or potential Mathlib leaf is being introduced as a new node.
- `sbc-def-base-change-square`: checked its four arrows and Cartesian identification against the displayed square; PASS.
- `def-sbc-smooth-morphisms`: checked the smoothness hypothesis, without taking a base-change theorem from a definition; PASS.
- `def-weil-pbc-scheme-conventions`: checked that it explicitly supplies the definitions of quasi-compact and quasi-separated morphisms used for g; PASS.
- `def-weil-l-adic-coefficient-extension`: checked the finite extension, DVR, uniformizer and finite positive-index quotients; PASS. Replacing its index by n+1 keeps n=0 nontrivial.
- `def-weil-pbc-adic-coefficient-datum`: checked the completed coefficient sheaf and its quotient scalar-extension functor; PASS. The coefficient assumptions hold: A is a DVR, its finite quotient is additively torsion, and [A --varpi^(n+1)--> A] is a finite free resolution because the uniformizer is a nonzero element of a domain. No preservation or pushforward/reduction comparison is used.
- `lem-weil-pbc-profinite-coefficient-inverse-image`: checked that its statement explicitly identifies the finite coefficient sheaves with constant sheaves and gives their inverse-image isomorphisms for every arrow; PASS. Only these finite-level assertions are needed here.
- `def-weil-pbc-bounded-constructible-complete`: checked its noetherian finite-dimensional, ell-invertible domain and its derived-complete, uniform-tower and compatible-witness membership conditions; PASS. They are retained by reference, without replacing that category by a weaker one.
- `def-weil-pbc-rational-category`: checked raw scalar localization, the same objects and localized Hom groups; PASS. No Karoubi completion or idempotent-splitting assertion is imported into the datum.
- `def-weil-pbc-constructible-complexes`: checked finite commutative A_n and the bounded constructible etale source category; PASS.
- `def-weil-pbc-proetale-modules`: checked the exact comparison inverse image and the source and target of its derived functor; PASS.
- `def-weil-pbc-proetale-operations`: checked that identified finite coefficient sheaves give ordinary uncompleted unbounded pullback and direct image for arbitrary scheme arrows; PASS. No noetherian or finite-dimensional assumption on another corner is needed to define these operations.
- `def-weil-proetale-constructible-sheaf`: checked finite-coefficient constructibility on arbitrary corner schemes, finite locally closed constructible stratifications and finite stalks; PASS.
- `def-weil-derived-cohomology-sheaves`: checked that H^i is defined for any sheaf of commutative rings and in every integer degree; PASS.

Small cases checked independently: L=K_E=0 admits the identity rationalization and zero witnesses, with every output zero and interval [0,0]; the empty scheme imposes no nonempty-stratum or nonzero-object requirement; over Spec k with characteristic different from ell, the identity square has all four outputs on the expected corner; n=0 gives A/(varpi), and n=1 gives A/(varpi^2). A torsion integral object can rationalize to zero, so the statement correctly imposes neither torsion-free cohomology nor an integral isomorphism to K_E. Bounds varying with n would be weaker and have not been substituted.

I repeated the whole-blueprint searches for “admissible lattice” and “integral lattice”, and the DAG lattice/admissibility search. The hits include this definition, coefficient-theorem consumers, lisse-sheaf lattice existence and a vector-space stabilizer lemma; none states this derived-square datum. I repeated the source-tree grep by the blueprint id, lattice phrases and camel-case names in both read-only Lean checkouts; it found no exact declaration to attach. No upstream sorry declaration was accepted as a finished proof.

Changes in this second reading:

1. Added four independently executed Mathlib search records, preserving their actual top results and service notes in the node and searches.jsonl. The different semantic phrasing found standard etale algebra statements, not this definition. The unqualified Loogle query was invalid and is explicitly recorded as such; the subsequent fully qualified witness query succeeded and found generic essential-image witness/getIso declarations. The categorical grep found subobject lattices and admissible t-structure morphisms. I read EssentialImage.lean lines 35–78, including essImage at line 45 and its witness/getIso definitions: these implement the generic existential predicate only. No full Mathlib match or leaf is justified.
2. Added this independent second-reading record. No mathematical statement, dependency, source identity, proof or citation change was needed. The first worker's Review by NL and all other sections remain in place.

The independent structural audit verified the old statement and dependencies verbatim against the shared imported node, all thirteen bracketed references against stmt_deps, and the complete direct-citer list. The sole shared-DAG citer remains `sbc-thm-e-coefficient-smooth-base-change`; its missing finite-dimensionality hypothesis and output-corner typo are accurately marked holds:false in the correction record. The repaired version in that item's separate sandbox is outside this delivery. Traversing the 417-node dependency closure found no cycle or missing node. B1–B7, C1–C4, D and E pass for this definition; there are zero new nodes and zero new Mathlib leaves. No Lean file was written or compiler/build tool run, and neither shared repository nor live launcher was changed.
