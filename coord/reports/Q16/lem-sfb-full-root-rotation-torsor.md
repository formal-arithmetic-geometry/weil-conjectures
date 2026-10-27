# Q16: lem-sfb-full-root-rotation-torsor

## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-full-root-rotation-torsor.json`: existing statement, now split into seven steps; no statement or statement-dependency change. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `searches.jsonl`: actual msearch command output records, retained unchanged.

Attachments: none. The project search for the exact blueprint tag and for full-root/rotation/torsor terminology found no finished declaration stating all clauses under the item's hypotheses. `AlgebraicGeometry.Scheme.strict_local_root_torsor_properties`, `lean/WeilConjectures/AlgebraicGeometry/Morphisms/StrictLocalRootTorsorProperties.lean:59`, treats a single parameter over a regular strictly henselian local ring, with regular/nonunit conditions, and gives geometric-point uniqueness rather than this scheme isomorphism and full inverse-limit/boundary package. Its proof cannot be attached here. I read its statement and the root-invariants definitions; I also read the existing full-parameter algebra and character definitions in `lean/Sheaf/Paper/FullParameterRootTower.lean` without writing or compiling Lean.

WANTED: none for this split. The item explicitly attributes its algebra and inverse-limit calculation to an agent expansion of the blueprint. I follow that attribution, and reuse an existing statement node for the non-elementary Kummer comparisons rather than claim to have read its cited external PDF.

What was wrong or incomplete: the dispatched node was statement-only. The main-20261015 direct-images proof paragraph (3) supplies the direct-image route, not a printed proof of this expanded root-algebra lemma. The existing `lem-sfb-compatible-kummer-tower-cech` states the finite comparisons, their power-transition compatibility, their infinite comparison and base-change compatibility for the same root data. Creating new nodes for those clauses would duplicate it. The remaining root-to-zero map is elementary and must stay in this item's steps. The CRT node's source metadata says 00U3, but the actual Chinese-remainder lemma in the local Stacks source is Tag 00DT, label `algebra-lemma-chinese-remainder`; I cite the correct source in step 2 and do not edit the other node.

What remains unfinished: no part of this stage-1 split. The comparison node remains an honest pre-existing unsplit dependency, as permitted for a one-level split; this delivery does not claim its Lean proof is complete.

## Sources and searches

Read `AGENTS.md`, `GOAL.md`, the stage-1 brief and stage document, worker role, the three blueprint levels in `SETUP.md`, `coord/STATE.md`'s open-stage entry, and delivery-errors B–E. Read the item's chapter and unit records and main-20261015 `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3). The older stored unit record has the six-functor chapter heading; I retain the item's current six-functors-basics chapter and use the current blueprint proof as the item specifies. No unit or chapter statement or route is changed.

Read Stacks `algebra.tex`, label `lemma-chinese-remainder`, Tag 00DT, including its proof, and `limits.tex`, label `lemma-directed-inverse-system-affine-schemes-has-limit`, Tag 01YW. Read the complete statement of every node cited in the split. The residue universal-property node is a Mathlib leaf with lift, specification, uniqueness, residue separation and norm criterion; I use its stated clauses, not a private lemma from its proof.

Before writing, searched all DAG statements/titles for Chinese remainders, profinite completion, adic integers, affine inverse limits, root towers and Kummer comparisons. `blueprint_refs.py search` was run for `Chinese`, `torsor`, `affine limit`, `root rotation`, and `Kummer`, and `ancestor` for the item. No imported blueprint node states the whole item. The ancestor command returns null, which is the existing item's inherited provenance; I preserve its exact paragraph/step place and via chain, with `same_as: []`.

The six new Mathlib search records were run through msearch and read: Loogle for primitive roots with torsors, grep for Kummer/root torsors, LeanSearch for the full comparison with fixed boundary, two LeanFinder phrasings, and grep for the Kummer automorphism equivalences. All services answered. The first grep and Loogle returned zero hits. Semantic hits concern spectrum fibres, field Kummer automorphisms, unrelated root systems, or general profinite limit cones. I read `Mathlib/FieldTheory/KummerExtension.lean`, including the irreducible-field hypotheses and the equivalence at line 248: it is not the scheme torsor comparison for arbitrary rings with multiple parameters. No search is recorded as a match or as unavailable. Existing search records on the imported node are retained.

## New nodes

None. New Mathlib leaves: zero.

## Not duplicates

No new/existing-node pairs arise. `lem-sfb-compatible-kummer-tower-cech` already covers the punctured comparison clauses, and is reused. `lem-exc-tame-roots-product` was inspected but is not cited: its field and algebraic-closure setup would import unnecessary hypotheses for a group-theoretic residue calculation. Instead step 2 uses the already available generic CRT and Mathlib adic residue statements.

## Review by Q16

I reread the seven steps against the actual node statements and the local source places, with the following conclusions.

1. The full-parameter-root definition names the actual compatible-root algebra and quotient generators. The formula on generators preserves each relation because zeta has nth power one, the negative label gives its inverse, and multiplying labels adds exponents. I wrote the transition calculation `(zeta_m^a x_m)^(m/n) = zeta_n^a x_m^(m/n)` rather than assert compatibility without a calculation. This is elementary quotient/colimit reasoning from the definition; I did not take a scheme-isomorphism theorem from a definition node.

2. The CRT node states an isomorphism for arbitrary finite pairwise coprime ideals, so it applies to the ideals generated by the distinct prime powers dividing a positive n. The residue node explicitly supplies reduction compatibility, unique lifts of compatible ring maps, residue separation and the norm criterion. For the inverse construction its source ring is the compatible-residue subring L, with the coordinate ring maps as the compatible family; it is not a forbidden application of a ring universal property to an arbitrary set. The two inverses are checked by CRT and residue separation. I checked continuity in both directions using the norm criterion and finite coordinates; no appeal to uncited compactness or Tychonoff is hidden. The exponent-zero and n=1 targets are singletons. Both cited nodes are Mathlib leaves, so they are generic arithmetic tools, not a change to any purity proof route.

3. The localization definition gives exactly maps to rings where f is invertible. That universal property identifies the localized colimit by maps into every ring; no unproved assertion that tensor products preserve an injective system is needed. The cited Spec-colimit node states that the affine spectra form a limit in schemes, not merely in affine schemes, and it allows any directed ring system. The index N_p has 1 and multiplication as an upper bound; it is small. Thus its hypotheses hold and it identifies the particular ring defining T-circ with the scheme limit required in step 4.

4. I read all of `lem-sfb-compatible-kummer-tower-cech`'s statement. Its hypotheses are characteristic p, finitely many parameters, positive prime-to-p exponents, compatible primitive roots and unit differences, exactly as here (it even allows zero base rings). Its statement gives the actual finite and infinite scheme maps, both projections, the power transitions with residue reductions, and ring-base-change naturality. It is not merely a theorem about geometric fibres or torsors of sheaves. The item's arbitrary finite index set is enumerated and then the formulas are checked coordinate by coordinate; the comparison has no additional conclusion taken from that node's proof. `def-sfb-profinite-test-objects` explicitly identifies X[P] with the inverse limit over finite quotients. This is citation of a pre-existing more general package, not creation of a node restating the item. I checked that its dependency closure does not reach this item (no circular reference).

5. For the boundary map, the exponent n and every transition exponent m/n are strictly positive. Therefore zero really respects all root relations and all power relations, including n=1. The full-root presentation permits the colimit homomorphism and the affine-spectrum definition supplies the contravariant map of schemes. The fixedness equation is checked on constants and every generator: a scalar multiple of zero remains zero, even in H/J=0. No regularity, strict henselianity, reducedness, residual chart, or sheaf-extension hypothesis is inserted.

6. The root-coordinate image under a ring map preserves the defining relations and the compatibility of roots of unity. The quotient exists because every t_i maps to t_i-prime, hence J maps into J-prime. The two boundary composites are explicitly compared on constants and all root generators. For the punctured comparisons the cited Kummer statement explicitly gives base-change compatibility, so I am not using its proof or adding an unstated naturality assertion. The adic group depends only on p and the finite index set.

7. With no parameters all stages are H, f=1, J=0 and the quotient/root-to-zero map is the identity. The punctured zero-ring case is permitted by the comparison statement; the full tower and boundary construction do not use invertibility of f. I also checked parameters all zero (nonempty I gives empty puncture but a valid fixed boundary), a unit parameter (J=H and the empty boundary), nilpotent parameters/nonreduced H, mixed unit/nonunit parameters, n=1 and the zero quotient ring. No step divides by a parameter on the full unpunctured tower.

Against delivery-errors B–E: no statement-only child carries a hidden proof because no child is created; every symbol is introduced in the unchanged item; TeX is encoded once in JSON. Every non-elementary fact has a cited node that states it, and every such citation has a verbatim quotation in citations.json. The boundary construction and the finite actions remain explicit elementary arguments rather than artificial nodes. No clause is moved into a newly created node. There is no circularity, SGA citation, new hypothesis or silent statement correction. Every step is under 2000 characters; the arithmetic step is one explicit reconstruction with its inverse and topology, not a hidden comparison lemma. The off-unit adic input is declared in split_report.tool_uses as a generic Mathlib arithmetic tool. The independent maintainer review remains the next mathematical review.

Corrections during self-review: avoided using the algebraically-closed-field tame-root product theorem for arbitrary H; replaced that tempting specialization by the explicit residue calculation. Reused the existing Cech comparison instead of creating duplicate finite or inverse-limit torsor nodes. Made localization/colimit and root-to-zero compatibility explicit and recorded the CRT source tag discrepancy without changing another node.

## Validation

The required server dry run exited 0 and printed `OK (not pushed)` at commit `96be9f9daec`: preflight passed, including the server DAG and split checks. The only subsequent report edit records this outcome and corrects the inspected theorem keyword line from 63 to 59; the mathematical files are unchanged. The final delivery command reruns the required checks before pushing. No Lean writing or compilation occurred.
