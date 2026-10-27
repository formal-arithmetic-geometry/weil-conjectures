## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-rational-based-retract-universal-homotopy.json`: item, statement; split into seven explicit proof steps using the existing complement Mathlib leaf. The whole item is not a Mathlib leaf.
- `citations.json`: one verbatim statement quotation for each of the two cited step/node pairs.
- `report.md`: this report. Search output is retained in `searches.jsonl`.

No new nodes and no new Mathlib leaves.

## Attachments

None. Searches by the exact blueprint tag and by rational/based retraction and homotopy concepts in `lean/WeilConjectures/` found no declaration covering the item. The split-functionals and Roos homotopy retract declarations concern different objects and hypotheses; neither is an attachment. No Lean was written or compiled.

## Wanted

None. This is an explicitly agent-written linear-algebra argument, with its only non-elementary existence theorem already an existing Mathlib leaf.

## What was wrong or changed

The item had a complete, correct statement but no proof. The statement and its sole statement dependency are retained. In particular, the rational maps i and p remain the specified retraction; no replacement by an arbitrary cohomology splitting is made. The new proof supplies the previously absent kernel-boundary argument, the inverse-differential homotopy calculations, the direct-sum support argument, and the finite-column scalar-extension calculation, including the zero algebra and constant-complex cases.

The original source path names an older blueprint snapshot. I read only the current `literature/blueprint/latest/` direct-images proof (3), its unit `_section.md`, and the chapter/unit DAG records. The latest paragraph records the open-direct-image obligation but does not itself prove this rational retract lemma. Accordingly proof_origin is agent, with the latest source path, and no claim that the blueprint contains these computations. The ancestor lookup reports that blueprint.from.node is None; this inherited null anchor and the already precise from.place are retained, with the lookup explained in split_report. No chapter or unit route was changed.

## Existing-node and Mathlib searches

I searched the whole DAG for complements, column-finite matrices, rational scalar extension and acyclic kernels, and searched the whole imported blueprint with blueprint_refs.py for complements, scalar extension, contracting homotopy and vector subspaces. `lem-trf-vector-subspace-complement` already states exactly the required arbitrary-dimensional complement theorem and is reused. `lem-trf-field-complex-cohomology-splitting` states existence of some homotopy splitting, but does not prescribe this i,p, complement formula, side conditions or universal matrix extension. The ringed-site free-matrix extension node is finite-rank and concerns internal sheaf tensor products; it is unnecessary here. No new node is needed for finite sums, uniqueness of basis coefficients, or the elementwise calculations written in the steps.

Six additional actual searches were run through msearch.py and are copied verbatim, with actual results, into the item's search record. Both semantic phrasings were read. Loogle returned no retract homotopy match; grep found a column-finite matrix comment and the homotopy constructor/K-projective declarations. I read the signatures of Homotopy.mkCoinductive (which requires successive witness data) and IsKProjective.homotopyZero (which assumes K-projectivity and does not provide the specified side conditions), as well as Submodule.exists_isCompl at lines 280–282. The Dold–Kan, cylinder and CM5b hits have particular simplicial/mapping-cone hypotheses, not the arbitrary prescribed rational retract. None states the whole item in one-line specialization. Old search records were retained, not represented as newly run searches.

## Not duplicates

No new nodes were created. In particular no duplicate complement, kernel-contraction, or scalar-extension node was introduced.

## Review by Q129

I checked delivery-errors B–E with the current item, both cited node statements, and source files open. The sources read were the latest blueprint direct-images proof (3) and unit/chapter text for the obligation, Stacks `homology.tex` section-complexes (Tag 010V, verified against tags/tags) including the cochain kernel/image formula at lines 3141–3153, and Mathlib `LinearAlgebra/Basis/VectorSpace.lean` lines 270–287 for the arbitrary-dimensional complement. No SGA source is used. There are no new statements to audit under B1–B9: the item's statement remains unchanged and all notions it needs beyond elementary linear algebra have the existing homology statement dependency or an explicit inline meaning.

Step 1 uses only the hypotheses pi=1, di=0 and pd=0. The formula q=1-ip proves image in ker p, uniqueness of decomposition and compatibility with d directly. It does not assert exactness from a definition or use a derived-category splitting theorem.

Step 2 cites `def-weil-pbc-module-chain-complex-homology` for precisely its kernel-modulo-image description and induced homology map. Its statement actually supplies those, including zero extension; reindexing n to -n gives the cochain convention. The injectivity hypothesis on H(p), not an unproved exactness lemma, gives z=dy. The correction y-i(p(y)) is an explicit preimage in C since pi=1 and di=0. This also checks n=0: the incoming module is zero, hence Z^0=0. The acyclicity argument is written in the step, not delegated to a definition citation.

Step 3 cites `lem-trf-vector-subspace-complement` for its precise assertion that every vector subspace of a vector space over a field has a complementary subspace with unique expressions and no finite-dimensionality hypothesis. Here the field is Q, V=C_m^n and the subspace is Z_m^n; all hypotheses hold. Choices are indexed by the set M times the natural numbers. Injectivity of d on L and surjectivity onto Z in the next degree follow in the displayed few lines from step 2, so no extra node for those elementary deductions is introduced. Inverse linearity follows by uniqueness of preimages; the bottom inverse has zero domain. This is the only step marked non-elementary, because choosing complements is the only imported existence result.

Step 4 computes dh and hd separately on the unique i(k)+z+l decomposition, in the correct cochain degrees. It checks n=0 separately and explicitly proves hi, ph and h squared from which summands h kills and where its image lies. These are elementwise linear-map equalities; there is no hidden comparison or claim that the bases respect the complements.

Step 5 checks direct sums on finite m-support, so arbitrary M is allowed and there is no product-totalization or infinite sum. Finite basis expansion applies even when each term has an infinite basis. Empty M, zero spaces and bases with empty index sets give zero modules and the formulas remain valid.

Step 6 spells out the map on arbitrary finitely supported B-coefficients. For each composed column it identifies the finite union of supports and proves the coefficient formula by the ring-map laws. Therefore it really proves preservation of addition, negatives, composition, identities and all the stated relations. It assumes neither faithful scalar extension nor flatness nor injectivity of Q to B. The zero algebra is admitted: its free modules are zero and identity equals zero there. Arbitrarily large finite column supports are allowed, with no common bound. No standalone hidden lemma is needed for this two-level finite-sum calculation.

Step 7 checks cohomology and all homotopy equations in degree zero, positive even degrees and odd degrees for the constant complex. Specifically h^2=h^4=...=1, but h^1=h^3=...=0; the composite of adjacent components is zero. Thus there is no sign or parity reversal. At n=1 the hd term is the identity, and at n=2 the dh term is the identity. The scalar-extension proof includes this case and the zero algebra without exception.

I checked C1 and C4 by opening both cited statements and placing their exact text in citations.json. All other steps use only hypotheses, definitions and the calculations actually written. All seven step texts are shorter than 2000 characters (the longest is the finite-column calculation at 1080), and none hides a new non-elementary subclaim. There are no new nodes restating a clause of the item, no unproved cited lemma, and no added dimension, boundedness, nonzero-ring or finiteness hypothesis. No mathematical correction or statement dispute was necessary. There was no second worker, as required by this direct-delivery brief.

## Unfinished work

None at stage 1. This delivery is a natural-language split only; it makes no claim of a new formal Lean proof.
