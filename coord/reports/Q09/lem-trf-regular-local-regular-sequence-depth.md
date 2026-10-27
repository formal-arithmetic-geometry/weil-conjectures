# Q09 stage-1 report: lem-trf-regular-local-regular-sequence-depth

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-regular-local-regular-sequence-depth.json`: statement unchanged; four-step split, no Mathlib match for the full statement.
- `citations.json`: twelve step/node entries, each quoting the cited node's actual statement verbatim.
- `searches.jsonl`: the required search command's authentic log; the five new queries are also recorded in the item, retaining its earlier searches.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. All ingredients were already in the DAG.

## Attachments

None for the item. Searching the blueprint tag throughout `lean/WeilConjectures/` found none. Concept searches in that library and in `lean/Sheaf/` found parameter regularity, depth upper bounds and one-element quotient results, but no declaration covering every arbitrary regular-sequence prefix quotient under exactly the item's hypotheses. In particular, `IsRegularLocalRing.isRegular_and_quotients_of_generators` assumes a system of maximal-ideal generators, whereas the item's sequence need not be a system of parameters or extend to a minimal generating set. Its arbitrary regular quotients need not remain regular local. `IsLocalRing.depth_quotient_nonzerodivisor` provides only the general single-element induction step. Neither is an attachment for the whole item.

## WANTED

None. All sources used are available in `literature/stacks-project/algebra.tex`.

## Findings and changes

The original node was unsplit, with a true statement and adequate definition dependencies; these were retained. Its sources 00NQ, 02JN and 00LK are correct. I supplied the induction rather than creating another node for the whole result or for one of its clauses. I also avoided the incorrect inference that an arbitrary regular-sequence quotient of a regular local ring is regular local: for example, the regular sequence consisting of $t^2$ in $k[[t]]$ yields the nonregular zero-dimensional ring $k[[t]]/(t^2)$, although it has depth and dimension zero as required here.

The blueprint source read was the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md` and its `.proof.md`, snapshot `main-20261023-1620`, together with the recorded chapter and unit. This item is an existing algebraic descendant, extracted from step 6 of `lem-trf-completion-local-complete-intersection`; it is not the unit's key statement, and I changed no chapter or unit realization. The existing exact `blueprint.from.place` and via chain were retained. Whole-blueprint searches for `regular local`, `regular sequence`, `depth`, `Cohen` and `00NQ`, and the DAG's tag/concept searches, disclosed no blueprint node stating the whole item in another form. Thus `same_as` remains empty.

Mathlib searches were run through msearch.py using LeanFinder (two different phrasings), Loogle, LeanSearch and grep. All five services/commands succeeded. The semantic hits give regular-sequence definitions and dimension drops, not depth equality. I read `Mathlib/RingTheory/KrullDimension/Regular.lean:210` and its surrounding declaration; the dimension theorem is already represented by `lem-trf-regular-sequence-dimension-formula`, so it is neither a new node nor a full match for this item. The grep hit is a TODO concerning depth, `Regular/RegularSequence.lean:21`. Earlier recorded searches were retained as history, including their genuine unavailable LeanSearch result; none was invented or silently reclassified.

## Not duplicates

No new nodes, hence no new/existing tag pairs requiring distinction. Reused the existing regular-generator, local-quotient, Noetherian-surjection, CM one-element quotient and depth-upper-bound nodes after opening their statements. In particular I did not create a second 00NQ or 02JN node.

## Review by Q09

I read Algebra 00NQ (`lemma-regular-ring-CM`, algebra.tex at line 25732), 02JN (`lemma-reformulate-CM`, line 25319), and 00LK (`lemma-bound-depth`, line 17814), verifying the tags against `tags/tags`. 00NQ makes a minimal generating set of the maximal ideal regular; its last sentence gives the initial Cohen--Macaulay input. 02JN allows an arbitrary regular sequence in the maximal ideal, not just minimal generators, and explicitly asserts that every prefix quotient is Cohen--Macaulay. 00LK requires a nonzero finite module over a Noetherian local ring. I also read 00FN (`lemma-Noetherian-permanence`, proof on quotients), 00E9 (`lemma-characterize-local-ring`) and 07BJ (`lemma-characterize-local-ring-map`), and the existing depth and regular-sequence definitions (00LI, 00LF). No SGA source is used.

For step 1 I opened `def-weil-regular-scheme`, `lem-weil-pbc-quotient-local-structure` and `lem-weil-pbc-surjective-image-noetherian`. The first includes Noetherianity of a regular local ring; the second explicitly gives nonzeroness, locality and the maximal ideal image when the ideal is contained in the maximal ideal; the third applies to the quotient's surjective ring map. Every prefix ideal lies in the maximal ideal because all the original elements do. This establishes all structure hypotheses needed later, rather than assuming them in the induction.

For step 2 I opened `lem-weil-pbc-regular-local-generators-regular-sequence` and `def-weil-pbc-depth`. The former says precisely that a list of dim R maximal-ideal generators is regular, which the definition of regular local ring lets us choose. The latter takes the supremum of lengths of such regular sequences when mR is proper. Here mR=m is proper. These statements give the initial lower bound directly, including dimension zero, with no claim about arbitrary quotients being regular.

For step 3 I opened `def-weil-pbc-regular-sequence` and `lem-weil-pbc-cm-local-quotient-nonzerodivisor-cm`. The definition supplies injective multiplication by the next element on the actual prefix quotient. Its image lies in that quotient's maximal ideal by step 1. The quotient theorem assumes only a Noetherian local ring of finite dimension e, depth at least e, and a nonzerodivisor in its maximal ideal; all are exactly available at the induction step. Its conclusion gives quotient dimension e-1 and a regular sequence of that length in the quotient maximal ideal. I used only those stated clauses. I wrote out the double-quotient identification on representatives, checked both inverse maps, and explained preservation of prime chains and regular sequences under it. These are direct uses of the cited dimension, regular-sequence and depth definitions, not an uncited theorem about invariance of Cohen--Macaulayness. The step is 1276 characters and contains no hidden source lemma. It does not need a module-depth change-of-rings theorem: the cited one-element node already states depth over the quotient ring itself.

For step 4 I opened `lem-weil-pbc-depth-le-support-dimension`, whose statement gives exactly depth(M) bounded by support dimension for a nonzero finite module over a Noetherian local ring. The module here is the quotient ring over itself, nonzero by step 1 and generated by 1. The proof writes out why its localization at every prime is nonzero, so its support is the entire spectrum. Thus the cited bound gives the upper inequality in the same dimension convention as `def-weil-pbc-krull-dimension-ring`; antisymmetry with the inductive lower bound proves equality. The final quotient and empty sequence require no further theorem.

The three off-unit statement tools are declared in `split_report.tool_uses`: regular-generator regularity, the CM one-element quotient theorem, and the module depth upper bound. They are generic commutative algebra facts with no replacement of the trace-formula unit's argument. The local quotient and Noetherian image statements are existing Mathlib leaves. All cited nodes' statements were read and copied verbatim into citations.json, not reconstructed from their proofs. There are no new statement-only nodes needing source, definition, elementary-fact, Mathlib-match or duplicate audits. All four steps have explicit elementary=false judgments; none exceeds 2000 characters, and the full proof text is under 3000 characters.

Small-case checks: c=0 gives R itself; a field permits only the empty regular sequence in its zero maximal ideal, giving depth=dimension=0; a nonzero sequence containing a zero next image cannot be regular on a nonzero prefix quotient; a unit is excluded by maximal-ideal membership, so a zero quotient is impossible; the hypersurface t^2 example above checks that no regularity assumption was illicitly retained after the first cut. No statement dispute or correction was necessary. The repairs made during this review were to spell out quotient/depth transport and to use the existing Noetherian-surjection node explicitly, avoiding uncited permanence.

## Unfinished work

None in the split. Independent maintainer review is supplied by the delivery process.
