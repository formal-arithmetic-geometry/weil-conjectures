# Stage-1 report: lem-cbc-open-extension-zero-etale-adjunction-agreement

## Files written

- dag/nodes/sec-smooth-purity/lem-cbc-open-extension-zero-etale-adjunction-agreement.json: statement node, now split into six steps; no exact Mathlib match.
- citations.json: exact statement quotations for all 13 step/node citations.
- searches.jsonl: six actual msearch.py queries, with both semantic phrasings read.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None for this item. The exact blueprint tag has no project declaration. I searched the slopmaster2 WeilConjectures tree by tag and extension-by-zero terminology and read SixFunctors/Etale/LowerShriek/EtaleMap.lean, OpenImmersion/Defs.lean and the relevant comparison interfaces. Their lower-shriek definitions/adjunctions do not state the specified single-summand presheaf map kappa, its sheafification, and its compatibility as one exact project declaration. Generic uniqueness of left adjoints is insufficient evidence for ATTACH.

## WANTED

None. All sources used are available in literature/.

## Corrections and scope

The statement, coefficients, sites and canonical comparison are unchanged. The imported item had no proof. Its main mathematical obligation is the equality of the actual transposes, not just the existence of an isomorphism between two left adjoints. I retained its blueprint ancestry and read the current main-20261015 cor-cbc-derived-extension-zero-base-change.proof.md in sec-six-functors-basics/sk-prop-sf-cbc. Its degreewise-isomorphism argument is the place this bridge serves through the underived-compatibility child. The chapter and unit records were read and are untouched.

The adjunction of lem-weil-pbc-etale-restriction-injectives is the canonical sum/sheafification adjunction of its cited construction (Stacks 03DI and the blueprint proof), rather than an independently twisted choice of Hom bijection. Step 4 explicitly reconstructs that bijection. The cited node is used only for its adjunction assertion; the formula needed here is proved in Steps 3–4 instead of being attributed to a statement that does not contain it.

## Unfinished work

None in this split. No Lean was written or compiled. Downstream nodes keep their existing states.

## Not duplicates

No new nodes were created. Whole-DAG source/tag and concept searches, and whole-blueprint searches for extension by zero and adjunction, found existing definitions and adjunction tools sufficient for the argument. The existing slice-presheaf adjunction node concerns abelian sheaves; I did not silently apply it to arbitrary Lambda-module sheaves. The finite/pro-etale and condensed-coefficient nodes likewise do not replace this small-etale, arbitrary-commutative-ring comparison.

## Review by NW

I read Stacks sites-modules.tex, Lemma 03DI (sites-modules-lemma-extension-by-zero), both the direct-sum formula and its proof constructing alpha prime. I read etale-cohomology.tex, Definition 03S3 (etale-cohomology-definition-extension-zero), the following restriction formula and equation-j-p-shriek. I also read categories.tex, Definition 0037 (categories-definition-adjoint) and the following paragraph defining unit/counit and their transpose formulas. These supply the item; there are no new nodes requiring further sources. The blueprint's etale-restriction-injectives proof was read to determine the canonical adjunction meant, while every black-box node use was checked against its statement, not that proof.

Step 1 uses the objects-over-U and presheaf clauses of def-weil-pbc-extension-by-zero and the sum/restriction formula of def-weil-pbc-etale-sum-extension. The first explicitly states uniqueness of lifts and that a lift is an etale U-object, so no unrecorded geometric factorization theorem is needed. I checked both naturality cases: restriction from a nonfactoring V has zero source even when V-prime factors. The inverse is evaluation on the unique summand, and the two identities are checked on the summand or zero.

Step 2 uses those same definitions only to identify the named extensions with the two sheafifications. def-weil-pbc-sheafification states the unique factorization into a sheaf, exactly what constructs kappa and its inverse and proves their compositions and naturality. No unsupported claim about sections of a sheafification is made. The proof never identifies a presheaf with its sheafification objectwise.

Step 3 uses the sum definition and the restriction equality explicitly stated in lem-weil-pbc-extension-by-zero-adjunction. It writes both maps of the presheaf Hom bijection and checks the restriction equation, linearity and mutual inverse identities on summands. This is a direct calculation for the open immersion in the item, not a new non-elementary lemma hidden behind a claim that a standard comparison exists.

Step 4 uses sheafification's Hom bijection, the generic natural-bijection-to-adjunction theorem lem-weil-pbc-adjunction-of-natural-bijection, and only the adjunction clause of lem-weil-pbc-etale-restriction-injectives. I checked that each statement actually gives this input. The last is Lean-closed in the recorded slopmaster2 audit; the generic theorem is already a Mathlib leaf and closed. The entire additional transpose formula is obtained from the explicit preceding calculation, including the inverse verification omitted at the end of Stacks 03DI. Thus no additional lemma about preservation of injectives or stalks is used.

Step 5 uses the precise open-extension transpose clause of lem-weil-pbc-extension-by-zero-adjunction and the uniqueness clause of sheafification. It compares the actual presheaf maps after iota and proves equality after sheafification by the universal property; it does not replace this with abstract uniqueness of left adjoints. Step 6 uses exactly the unit, counit and forward-Hom formulas in lem-weil-pbc-adjunction-of-natural-bijection. Substituting the identity on the sum extension gives the stated unit direction; substituting the identity on the restriction gives the stated counit direction. I checked the domains and orders of both composites.

I checked B1–B10: complete objects/hypotheses already in the retained statement, single-escaped TeX, exact source tags/labels, blueprint provenance, and actual logged searches; no new statement-only nodes or Mathlib leaves need metadata. I checked C1–C8: every ingredient used as a theorem is cited, every cited statement was opened, and every use has its exact quote in citations.json. Definitions, existing Mathlib leaves and closed adjunction nodes are the only proof dependencies, so no off-route tool declaration is required. I checked D1–D5: the item itself contains its argument; nothing was moved into a fresh restatement, and the explicit inverse/naturality checks fill the omitted verification. I checked E1–E7 with an arbitrary constant commutative Lambda, no noetherian, finiteness, properness or constructibility assumptions. All maps are Lambda-linear because their components are the supplied module maps. There is no change to condensed or pro-etale coefficients and no SGA source.

For small cases I checked j the identity, U empty, X empty, the zero coefficient ring, F zero, V without a lift, and restriction from a nonfactoring V to one with a lift. In particular Hom_X(empty,U) is a singleton, even for U empty; the proof branches on lifts, not on nonemptiness of V. Empty direct sums and singleton direct sums give the required inverse identities in all cases. Each step is shorter than 2000 characters and is one stated calculation; none hides a separate standard comparison theorem. Statement/proof dependency lists were checked against their uses, with no ancestor cited and no cycle introduced by construction.

The six new Mathlib searches were run only through msearch.py. The first semantic phrasing returned scheme structure-sheaf restriction and lift formulas; the second returned generic sheafification Hom adjunctions. The Loogle and CategoryTheory grep hits for leftAdjointUniq were read in Mathlib/CategoryTheory/Adjunction/Unique.lean, lines 36–60: they do not identify this kappa. The targeted AlgebraicGeometry/Sites grep returned no hits. No match or unavailable status was fabricated.

## Validation

Pending required server dry run and delivery; their actual results will be recorded after completion.
