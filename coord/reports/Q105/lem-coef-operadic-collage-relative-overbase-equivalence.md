# Q105: lem-coef-operadic-collage-relative-overbase-equivalence

## Files written

- dag/nodes/sec-six-functors/lem-coef-operadic-collage-relative-overbase-equivalence.json: existing statement, now split in seven steps; no Mathlib match.
- citations.json: a verbatim statement quotation for every proof-step citation.
- report.md: this report.

No new nodes; no Mathlib leaves. All work is confined to the assigned sandbox. No Lean was written and no compiler or build command was run.

## Attachments

None. Searches of WeilConjectures/ in the slopmaster2 source by the exact blueprint tag, relative-overbase name, isofibration, strict fibers, and over-base functor equivalences found no project declaration proving the item. Ordinary geometric fibers and over-category equivalences are not the coherent relative functor category here. The upstream master source is not treated as proof evidence.

## WANTED

WANTED: an archived copy of Gepner–Haugseng, Enriched infinity-Categories via Nonsymmetric infinity-Operads, arXiv:1312.3178v4, Remark A.4.2, for the assigned item.

WANTED: an archived copy of HTT, Theorem 2.2.5.1, Corollary 2.2.5.4 and Proposition 2.2.5.8, and Kerodon tags 01F1, 01P8, 01L5, 0329 and 032B, for the existing tool interfaces used by the assigned item. These sources were opened online; the cited tags are Kerodon tags, not Stacks tags. No Stacks tag states these quasicategorical results, and none has been invented.

## Findings and corrections

The sandbox had only the unchanged item copy and searches.jsonl, without a proof or report; there was no interrupted delivery process for this item. I retained the existing statement, provenance, ancestry and inherited searches and read the logged hits before using them. Searches show ordinary HasFibers results, generic fibrations, StrictSegal and the strict bicategory of quasicategories. Reading Mathlib/AlgebraicTopology/Quasicategory/StrictBicategory.lean:14-31 and :44-73 shows only bicategory infrastructure, and CategoryTheory/FiberedCategory/HasFibers.lean:13-40 concerns ordinary category fibers. The previously returned HasFibers.instIsEquivalenceFibFiberInducedFunctor name is absent in the pinned CategoryTheory source; it is not an available match. Further grep results are appended exactly as logged. I did not repeat the unchanged earlier semantic search questions.

Remark A.4.2 states the collage replacement by a categorical equivalence; it does not state this general strict-fiber theorem verbatim. Accordingly proof_origin is agent, with the model-factorization and mapping-space arguments supplied explicitly and each substantive input cited. No statement dispute was found. In fact the proof works for any quasicategorical base; the given ordinary-base and no-nonidentity-isomorphisms hypotheses are retained, rather than silently changing the assigned statement. We never identify unrelated coefficient categories or use an SGA route.

The current blueprint source is literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.md and its .proof.md. I read both, the chapter and unit records, and the assigned node's ancestry. The supporting comparison serves paragraph 2's derived coefficient adjunction and its specified units/counits. The historical unit metadata places the node in sk-prop-sf-biduality-general; I have not changed that maintainer-owned binding. The unit is not this item's key statement, so no realized fields are edited.

## Not duplicates

No new nodes were created. Whole-blueprint searches for strict fiber, isofibration and relative functor returned no matching blueprint node; the existing tool statements already cover every needed ingredient. The proof does not move an item clause into a new node.

## Review by Q105

I read delivery-errors.md B–E in full and reviewed the actual statements used by each step, not merely their names. The item source read was Gepner–Haugseng Remark A.4.2 (including its surrounding free-algebra discussion). For the expansion I read HTT's Joyal model statement and product corollary, and Kerodon 01F1, 01P8, 01L5, 0329 and 032B. There are no new-node sources to audit.

Step 1 uses def-cbc-enhanced-diagrams-cones for the degreewise pullback and internal Hom, and lem-coef-infinity-isofibration-exponentiation for its actual empty-domain specialization. Its statement allows arbitrary small T, so neither P nor the indexing simplicial sets are assumed quasicategories. The relative horn lift is explicitly over the constant simplex; a fiber need not be nonempty.

Step 2 uses lem-coef-joyal-functor-equivalence-test to pass from the stated categorical equivalence to Joyal weak equivalence; lem-coef-joyal-model-structure states both factorization systems, two-out-of-three, lifting against cofibrations, and the fibrancy criterion. This yields both j and q trivial in the indicated senses, with Q a quasicategory because M is fibrant. Lem-coef-joyal-quasicategory-characterizations(1) says exactly that an inner fibration lifting equivalence edges is a Joyal fibration, so it applies to p between the specified quasicategories. No smallness of V in the original universe is smuggled in: the whole construction is moved to a universe containing V.

Step 3 uses the actual unmarked pushout-product conclusion of lem-coef-joyal-cartesian-pushout-product. Its two inputs are degreewise injective, j is also a categorical equivalence, and the maps to S on the union agree. The exponential adjunction is the displayed internal-Hom formula in the definition node. The resulting lifting property against every monomorphism is the trivial-fibration class stated by the Joyal model node, and characterization(2) supplies the coherent equivalence between the quasicategories from step 1. This is a direct lifting argument, not an appeal to right properness of the Joyal model structure.

Step 4 uses the same model node's lifting class to construct a section of q and a homotopy on Q times the full walking-isomorphism nerve, whose exact nerve is introduced in lem-coef-quasicategory-invertible-interval. The two endpoints agree after q, so the prescribed square commutes; the endpoint inclusion is a monomorphism even though the walking-isomorphism nerve is infinite. Its reverse arrow and two inverse triangles give the inverse-equivalence witnesses after precomposition, directly from the definition node. The equation qH = q pr_Q is recorded: it forces the whole equivalence to remain in the strict relative fiber. This is why a merely absolute quasi-inverse would not suffice. The argument is applied to q from this particular factorization, not delegated to a new general lemma.

Step 5 uses the unpinched U-space assertion actually present in lem-coef-infinity-isofibration-exponentiation. It is applicable to the inner fibration C_T -> D_T from step 1. The strict-fiber equality follows by interchanging the explicitly given degreewise pullbacks; its distinguished arrow really is the identity of s_T. Lem-coef-kan-pullback-path-comparison states precisely that inserting a constant path compares a strict pullback to the path model when either leg is a Kan fibration. All three mapping objects are Kan complexes, as required. I did not use that lemma to assert preservation of strict fibers of an arbitrary equivalence square.

Step 6 uses the natural right-pinch equivalence, with the correct direction, from lem-coef-infinity-pinch-comparison. Lem-coef-kan-homotopy-pullback-invariance applies to the resulting strictly commutative diagrams of Kan complexes, with the point factor unchanged and both other vertical maps weak equivalences. The identity vertex is preserved. The zigzag is written explicitly, proving the right-pinched clause without any uncited theorem on right-pinched mapping-space fibrations.

Step 7 is elementary from the same simplicial formulas and the naturality clause actually in the pinch node. I checked commutation before passing to weak-equivalence classes: restriction, postcomposition, pinching and constant paths are literally the same precompositions in either order. Therefore the comparison retains every higher simplex. The natural assertion concerns the specified restriction map and the displayed canonical comparison zigzag; it does not claim a natural choice of the section t or inverse equivalence. Postcomposition is considered between targets satisfying the item's hypotheses.

I checked B1–B10: there are no new unsplit objects, unexplained definitions, unrun added search records, fabricated Stacks tags, Mathlib matches, or ignored project attachments. C1–C8 were checked against all cited statements; citations.json quotes them verbatim. The only off-unit tool is the shared foundational definition, declared in split_report.tool_uses with its reason. Dependency reach inspection found no path from any of the ten used tools back to this item. D1–D5: the actual extension and mapping-space arguments are in the item; no relabelled child lemma, circular induction, or omitted-standard assertion remains. E1–E7: all fibrancy, monomorphism, equivalence, Kan and universe hypotheses are verified where used.

Small cases checked: P=M=empty gives terminal functor fibers and a one-point mapping space; a nonempty domain with empty V can give empty fibers, for which the equivalence proof still applies and the mapping-space clause has no objects; i=identity gives the same comparison on both sides. If a categorical equivalence collapses equivalent vertices, i need not be injective, which is exactly why the factorization through j and q is required. For an ordinary noninvertible arrow in the base, the fixed base transformation is still the identity, not an arbitrary endomorphism. No step exceeds 2000 characters (lengths 606, 699, 795, 996, 757, 825, 983), and none hides a separate standard identification.

## Remaining work

No mathematical part remains open in this one-level split. The existing cited nodes retain their own stage-1 status; this delivery claims only the proof of the assigned item, subject to the independent maintainer review. Required server dry-run and delivery results will be recorded below.

## Delivery checks

The required server dry run passed: `OK (not pushed) deliver/Q105/lem-coef-operadic-collage-relative-overbase-equivalence at a40c57ef43: preflight passed`.
