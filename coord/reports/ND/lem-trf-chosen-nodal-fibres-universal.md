# lem-trf-chosen-nodal-fibres-universal — ND stage-1 delivery

## Files written

- dag/nodes/sec-trace-formula/lem-trf-chosen-nodal-fibres-universal.json: statement, split into four assembly steps; existing statement and statement dependencies unchanged. Mathlib verdict: no match for the whole assertion.
- citations.json: verbatim statements for every step/node citation.
- searches.jsonl: five actual fresh searches (two LeanFinder phrasings, LeanSearch, Loogle, source grep); earlier searches in the existing item retained.
- report.md: this report. No new nodes and no new Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures/ for the exact blueprint tag and for nodal/ordinary-double-point notions. The only nodal mentions were explanatory docstrings in relative Kunneth/projection-formula files, not declarations proving this item. No compiler or Lake command was run. The upstream library's sorry declarations were not treated as completed proofs.

## WANTED

None. All sources used are available in literature/stacks-project/.

## Corrections and scope

The sandbox initially had no item, report, or searches, so this is a new split from the live unsplit item. No released repair note was present. There is no statement dispute: the statement and stmt_deps are unchanged. The initially cited source 0C59 describes nodal families via their first Fitting singular subscheme; this proof needs no new Fitting criterion because the existing node lem-trf-node-algebraically-closed-extension already supplies exactly the algebraically closed field extension comparison. Smooth loci are handled directly by the existing pointwise scheme theorem 02V4, not by claiming that the definition of smoothness itself proves their base-change equality.

Read the chapter and unit records, the three levels in SETUP, and the newest blueprint under literature/blueprint/latest/. The ancestor's current proof treats local terms; the item's recorded ancestry identifies this auxiliary claim as the semistable-alteration input in its nearby-cycle branch. The delivery supplies that auxiliary geometric claim without modifying chapter or unit statements or route. Whole-blueprint searches for nodal, geometric fibres, and smooth locus returned no node stating this item. DAG searches by 0C56/0C59 and the relevant notions located all the existing tools used here; no new-node search or duplicate distinction is needed.

## Not duplicates

No new nodes. In particular, reused lem-trf-node-algebraically-closed-extension instead of inventing another 0C56 node, and reused lem-trf-relative-dimension-base-change instead of inventing a dimension-preservation node. The former is strictly the field-extension part; the parent also extends residue-field closures, associates fibres, preserves their dimensions, and identifies relative smooth loci under arbitrary base change.

## Review by ND

I read Stacks curves.tex Tag 0C56 (lemma-node-field-extension), including its compatible algebraic-closure choice, the warning that closed points may map to nonclosed points, and its completed-local-ring argument. I also read Tag 0C59 (lemma-nodal-family), whose proof uses first Fitting ideals; none of that proof is silently taken from the definition of a nodal fibre. For the generic tools I read fields.tex Tag 09GU (lemma-map-into-algebraic-closure), and morphisms.tex Tags 02NK (lemma-base-change-relative-dimension-d), 01V9 (lemma-smooth-at-point), and 02V4 (lemma-set-points-where-fibres-smooth). I checked the smooth source-cover statement against Tag 01V6 (lemma-smooth-characterize). There are no new nodes whose sources need separate review.

Step 1 cites the actual statement of lem-weil-pbc-algebraic-extension-embeds-algebraically-closed, not merely uniqueness of algebraic closures. That statement accepts an arbitrary map from the residue field to an algebraically closed target, precisely what this geometric point supplies, and extends it across the algebraic closure. A field homomorphism is injective. The second citation, def-pc-fibre-product, states the universal property and uniqueness of the scheme fibre product, not only a notation. Compatible maps into either iterated product give the same pair of maps into Y and Spec Omega; the map to Spec k_s is forced. This proves the association rather than asserting an unexplained comparison.

Step 2 cites def-sbc-locally-finite-presentation and def-weil-finite-type-morphism for the affine meaning of the two local finiteness properties. A finite polynomial presentation has finitely many algebra generators, so there is no theorem hidden in the implication needed here. The statement of lem-weil-pbc-lft-base-change requires only local finite type and allows every base change; hence C is locally finite type over k_s. The statement of lem-trf-relative-dimension-base-change assumes exactly that local finite type property and purity of all nonempty original fibres, and gives purity for every base-changed fibre. With target Spec k_s or Spec Omega, that fibre is the entire scheme. No properness, finite-type global source, or Noetherian-base hypothesis is being inserted.

Step 3 uses the complete statement of lem-trf-node-algebraically-closed-extension. It allows a locally finite type scheme, empty schemes, abstract ring isomorphisms of completed local rings, and no global dimension or quasi-compactness hypothesis. Both k_s and Omega are algebraically closed, and Step 1 supplies the extension structure. Its nonsmooth-point hypothesis is exactly the assumption of the parent at s. Its conclusion applies to every nonsmooth point after extension. This avoids the invalid inference that every closed point upstairs has closed image; that issue is internal to the separately stated existing node, whose statement already gives the full needed conclusion. Scheme isomorphisms over Omega identify neighbourhoods and local rings, so the result concerns exactly Y_Omega.

Step 4 uses lem-weil-pbc-smooth-local-on-source to assemble the smooth restrictions on the union U; the node's statement includes arbitrary open covers and the empty cover. Thus U is actually the largest smooth open, not merely an unexplained subset of smooth points. The node lem-sfb-scheme-flat-smooth-point-base-change is specifically about schemes and states smoothness at a point upstairs if and only if smoothness at its image for flat locally finitely presented f and arbitrary h. Both hypotheses are given in the parent, and h need not be flat. Its pointwise equivalence yields equality of the underlying opens, hence equality of their open subschemes. The nonsmooth-image assertion is its contrapositive. This node belongs to another unit, so split_report.tool_uses explicitly declares it as a generic scheme tool; it does not replace the semistable proof route. All other cited off-unit statements are Mathlib leaves.

Every node cited by every step was opened and its statement read. citations.json quotes those statements verbatim, including all hypotheses; no proof-internal construction is used as if it were part of a statement. proof_deps is exactly the union of the uses lists. The assembly is 2335 characters and each step is under 700 characters, so there is no long step concealing another lemma.

I checked the empty scheme (all nodality clauses vacuous and the empty smooth locus remains empty), a smooth line (no nonsmooth points), and the standard node k[u,v]/(uv) (the node stays nodal after transcendental as well as algebraic extensions). The statement allows nonclosed image s in S and nonalgebraic Omega/k_s; the embedding node and field-extension node explicitly cover these cases. Characteristic 2 is not excluded, and no factorization or division by 2 is used. Non-quasi-compact sources and non-Noetherian bases are permitted because every invoked statement is pointwise, local finite type, or valid for arbitrary schemes. Nilpotent changes of base are permitted by the arbitrary h clause of 02V4. No forbidden SGA source, new definition, duplicate lemma, circular dependence, or assertion proved only from an uncited Stacks tag is introduced.

The five current Mathlib search results were read: LeanFinder found smooth-base-change instances on the first phrasing and power-series/Weierstrass preparation on the second; LeanSearch found smooth-base-change and the definition of smoothLocus; Loogle found smooth implies flat, descent of smoothness, and whole-fibre smoothness implies smoothness; grep found no nodal or matching smooth-locus base-change text. I read the local Smooth.lean and SmoothFiber.lean declarations (smooth_isStableUnderBaseChange at line 117, of_smooth_fiberToSpecResidueField at line 34). None gives the item's nodal completed-ring clauses. IsAlgClosed.lift at Basic.lean:350 is already represented by the existing embedding Mathlib leaf, which is reused.

## Unfinished work

None in this stage-1 split. Existing cited unsplit theorem nodes remain their own stage-1 items. No Lean proof is claimed or written. Delivery awaits the required server dry run and push below.

## Validation

The required deliver.py --no-push completed with exit 0: `OK (not pushed) deliver/ND/lem-trf-chosen-nodal-fibres-universal at bed705d5f0b: preflight passed`. The preflight ran on the server and included the DAG and split checks. Local source-only comparison confirmed unchanged statement, nine citation records, and zero new nodes. This is the direct-delivery worker's self-review; the maintainer performs the independent review.
