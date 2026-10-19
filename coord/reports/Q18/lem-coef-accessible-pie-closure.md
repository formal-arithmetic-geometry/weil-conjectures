# Stage-1 repair: lem-coef-accessible-pie-closure

Q18, 2026-10-17. Direct delivery of the dedicated human-requested re-split.

## Files written

- `dag/nodes/sec-six-functors/lem-coef-accessible-pie-closure.json`: item, split; retained statement and Lean record exactly, retained steps 1–11 verbatim, replaced the returned step 12 by steps 12–15.
- No new nodes and no new Mathlib leaves. The substantial hidden cocone-descent argument is supplied by the existing Mathlib leaf `lem-weil-pbc-colimit-initial-full-subcategory`, clause (1), under the explicitly written opposite-category substitution.
- `citations.json`: 24 entries, one for every step/node citation; each quotes the current node's statement verbatim.
- `prior-NE-report.md`: preserved earlier delivered report copied from the read-only repository because this sandbox had no report or node files on resumption. The original proof was preserved in the current repository node, which was copied before repair. The original search log in this sandbox was retained and read.

## Attachments

None. Searches in the supplied `WeilConjectures/` source for the item's tag, inserter and equifier found no declaration proving the item. The recorded stage-2 declaration in `lean/Sheaf/CategoryTheory/AccessiblePieClosure.lean` has a `sorry` body and is not a finished attachment. Its statement and the item's Lean record remain unchanged. The upstream-master reference search gives no exact item attachment either.

## WANTED

The earlier report's WANTED requests for the full Adamek–Rosicky uniformization proof, Positselski's *Notes on limits of accessible categories*, and Ching–Riehl Appendix A remain; see `prior-NE-report.md`. This repair's replacement tool is locally available: `literature/stacks-project/categories.tex`, Tag 0BUC (`lemma-cofinal-in-filtered`) and Tag 04E7 (`lemma-cofinal`). No new source is required or downloaded, and no SGA source is used.

## Findings and repair of the return

The human return identifies the 2039-character final step as hiding lemmas. Its general cocone-extension, independence-of-choice and uniqueness argument is exactly the full cofinal-subcategory colimit theorem, already in the DAG. Step 14 now cites that node instead of reproving it inline. I applied its actual cofiltered statement, not an unmentioned dual theorem: I = D_X^op and J = (Delta_E/X)^op, so a factorization P → Q over X is exactly j → i in I. The node takes a diagram on I^op, hence gives the required colimit in A, without passing A to its opposite. The statement explicitly identifies the canonical comparison on the coprojections, so it also identifies the specific cocone with vertex X.

The other parts of the former step are elementary after steps 3 and 11 and are now separately displayed. Step 12 writes the naturality calculation transporting membership in the equifier to a chosen representative and the two factorization maps; step 13 obtains a kappa-small cocone by postcomposing the ambient cocone with one arrow from its apex. These are two/three-line calculations, not new lemmas to duplicate as nodes (brief step 3, Elementary). Ordinary filteredness alone would not establish kappa-filteredness; step 13 explicitly handles every diagram with fewer than kappa arrows. Step 15 writes the restriction of the universal property to a full subcategory and the accessibility conclusion. This retains the original approximation/density route, including the empty equifier case; it does not replace equifier closure with a new clause-sized child.

The item statement, source, proof_origin, existing searches, statement dependencies, Lean record and maintainer metadata are unchanged. Steps 1–11 are byte-for-byte equal as JSON values to the current returned node; their longest text is 1489 characters. All new steps have fewer than 2000 characters. No Lean was written or compiled, no build tools were run, and all writes were confined to this sandbox. No git command was run by the worker.

## Not duplicates

No new nodes are proposed. The existing `lem-weil-pbc-colimit-initial-full-subcategory` was found by searching the whole DAG for full subcategories, filteredness, finality and expected declaration names. I opened its full statement, source and Mathlib match. A new cofinal full-subcategory colimit lemma would duplicate its first clause after the opposite-index substitution, so I did not create one. Whole-blueprint searches for cofinality, full subcategories and cardinal filteredness supplied no additional blueprint statement needed for the repair; the recorded blueprint ancestor remains `prop-coef-integral-exceptional-adjoint`.

## Review by Q18

I read the returned node, its repair-note entry, the prior NE report, the chapter and unit records, and the actual current blueprint ancestor paragraph. That paragraph is about the derived coefficient adjunction; the PIE infrastructure is an agent-formulated auxiliary, as the inherited source and proof_origin already say. I read the local Stacks statements 0BUC and 04E7 and their labels in categories.tex and verified their tag mapping. Their proofs are omitted there, so the existing Mathlib leaf is essential: I read Mathlib `Filtered/Final.lean:144–201` (full-faithful weak cofinality gives filteredness and finality, and the dual initial version) and `Limits/Final.lean:295–392` (restriction of a specified colimit cocone, canonical comparison with its coprojection formula, and existence transfer). The existing node's first clause is precisely the tool needed, not merely a definition of cofinality.

I opened the statement of every cited node and checked each citation against what its step uses. For the preserved steps, my checks were:

- Step 1: `lem-coef-accessible-system-ranks` supplies lambda < kappa, both preservation ranks, upper-rank accessibility and presentability of images. Its small cardinal bound gives |S| < kappa. The regular lambda ordinal is lambda-filtered; this justifies exactly the chain colimits subsequently used, without claiming colimits of all shorter chains.
- Step 2: `lem-coef-ordinary-small-colimit-presentable` supplies the fewer-than-kappa small colimit claim. `lem-coef-accessible-set-functor-limits` supplies products and equalizers of Hom functors at that cardinal. The elementary filtered-set quotient explanation gives stage factorization and eventual equality; cocones on fewer than kappa witnesses impose them simultaneously.
- Step 3: `lem-coef-accessible-presentable-density` states both canonical filteredness and the colimit with the actual legs, assuming accessibility rather than cocompleteness. The written retract/idempotent argument gives a small representative family; it is used in every later index category.
- Step 4: the colimit definition supplies coordinatewise universality; the set-functor-limit statement gives presentability only because |S| < kappa; canonical density gives the coordinate presentations. Nonempty filtered indices allow the coordinate cocone identification. Empty products and empty factors are covered explicitly.
- Step 5: the colimit definition gives the structure arrow from the preserved F-colimit. The set-functor-limit statement gives the Hom equalizer; its target Hom_B(FP,G(-)) preserves the required colimits because FP is presentable and G preserves them. The chain case uses the lower rank already supplied.
- Step 6: canonical density supplies every proper-limit cone. At successors, the domains FT_j and FP_a are presentable by step 1, so step 2 applies to the displayed fewer-than-kappa equalities in GX. No intermediate colimit is assumed.
- Step 7: the colimit definition supplies w from the compatible FT_i legs and the unique map q to X. The small-colimit fact established in step 2 gives Q presentable, since lambda < kappa. The displayed equations in step 6 yield both the inserter equation and retention of prescribed legs.
- Step 8: density supplies a cone on the underlying diagram; steps 6–7 make its legs structure maps, and the written conjugation formulas transfer to the small representatives. Empty diagrams yield nonemptiness.
- Step 9: density gives the universal property of D_X; the colimit definition is the final universality assertion. The written joining argument uses filteredness to equalize P-arrows before the structured extension, so the construction does not silently assume an arbitrary forgetful functor is final.
- Step 10: the rank node supplies all required filtered and chain colimits and preservation by F. Naturality then gives the equifier equation on each colimit leg; the colimit definition and fullness give creation. The Hom restriction gives presentability.
- Step 11: density supplies the ambient stages and proper-limit cones; the set-functor-limit consequence in step 2 gives presentability of Q, while the colimit definition and preservation by F give alpha_Q = beta_Q. The eventual equality uses presentability of FT_i and preservation by G, both already supplied. Thus step 11 really produces a presentable E-object above every ambient presentable arrow into X.

For the replacement steps:

- Step 12: I checked the types in the conjugation formula: F(e^-1):FR → FQ, alpha_Q:FQ → GQ, G(e):GQ → GR. If qh = p, then (qe^-1)(eh) = p, so this arrow really lies over X. The retained representative set is independent of X and is small. No external lemma is hidden here.
- Step 13: the cited density statement says D_X is kappa-filtered; step 3 replaces it by the small representative model. Any kappa-small diagram in the full subcategory has a cocone there after composing with the one arrow obtained in step 12. This checks all diagram relations at once, including the empty index. There is no mistaken inference from ordinary filteredness to kappa-filteredness.
- Step 14: I checked each hypothesis of clause (1) of the existing cofinal-subcategory node with the explicit I,J substitution described above. Fullness is essential and holds because Delta_E/X is defined as a full subcategory of D_X. Canonical density supplies both ambient filteredness and its specified colimit cocone. The canonical coprojection characterization in the cited clause gives the same X-cocone, so there is no uncited identification or transport. This is the non-elementary hidden lemma extracted from the old step; it is already a Mathlib leaf and therefore usable across units without tool_uses.
- Step 15: for any Z in E, fullness identifies each Hom and cocone equation with that in A, so restriction of the universal property is a direct calculation using the cited colimit definition. Step 10 supplies presentability and creation of filtered colimits; step 13 supplies the correct indexing rank. Thus the small family really witnesses accessibility of E and accessibility of its inclusion.

I tested the replacement on a terminal category (the representative slice is terminal), alpha = beta (the entire presentable family is retained), and an empty equifier (there is no X and no generation obligation). More generally, the full-subcategory condition in step 14 cannot be dropped: a discrete two-object subcategory of a connected filtered category need not have compatible cocones; here fullness is built into the definition. The opposite-category direction was checked on the ordered category of natural numbers with the even-number full subcategory: every ambient object has an arrow toward an even number, giving exactly the initial arrows in the opposite and preserving direct, not inverse, colimits. The kappa-small postcomposition proof works for arbitrary regular kappa and does not use an unprovided cocompleteness hypothesis.

I checked delivery-errors B–E point by point. B: no new node or unverified Mathlib match is introduced, all citations are to self-contained existing statements. C: every new non-elementary fact is cited by its actual statement, with verbatim quotes; existing uses in steps 1–11 are retained. D: the actual approximation and generation argument remains in the parent; no child restates an item clause. E: the universe, smallness, opposite-index direction, fullness, representative transport and empty cases are explicitly checked above. The sole return point is repaired substantively by replacing the generic cocone-descent argument with an existing Mathlib leaf, not by merely shortening or relabelling it. There is no statement dispute.

## What remains unfinished

No outstanding work in the requested stage-1 repair. Existing unsplit dependencies remain for their own owners; this delivery neither changes their statements nor claims to prove Lean declarations.
