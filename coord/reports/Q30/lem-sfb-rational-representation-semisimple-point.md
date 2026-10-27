# Stage-1 report: lem-sfb-rational-representation-semisimple-point

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-rational-representation-semisimple-point.json`: existing statement, split into four steps; no Mathlib match.
- `citations.json`: five verbatim statement quotations, one for every step/node citation.
- `searches.jsonl`: five actual searches made with the required msearch command. The item's inherited searches were retained; the new results were appended to mathlib_searches.
- `report.md`: this report. `milne-extract.txt` is a local reading extract of the supplied PDF.

New nodes: 0. New Mathlib leaves: 0. Only the item node is delivered.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint id and for semisimple representations, Jordan decomposition and semisimple points found no declaration stating the item. The existing semisimple-module declarations concern decompositions of representations, not diagonalizability of one group point. No sorry declaration was treated as a finished proof.

## WANTED

None. All sources needed are present.

## Findings and changes

The imported item has an empty proof. Its statement is correct and is unchanged, including faithfulness on all commutative algebras, arbitrary characteristic, and possibly nonreduced or disconnected J. Milne 9.19 is the faithful-detection assertion; its proof through 9.18 uses the linear compatibility and Tannaka reconstruction already present as reviewed nodes. Creating a new group Jordan-decomposition node would be unnecessary here. The four steps construct the compatible family of semisimple parts, reconstruct a point h, use i(k) to identify h with g, and conclude that r(g) equals its semisimple part.

The two existing inputs are `lem-sfb-multiplicative-jordan-linear-compatibility` and `lem-sfb-tannaka-rational-point-reconstruction`. I read both statements in full. They are in this item's unit and neither depends on this item. The reviewed unipotent analogue is a useful comparison but is not cited as implying the semisimple assertion.

The current latest blueprint's direct-images proof (3) was read. This is the inherited supporting branch of its constructibility input, through alteration, PGL, torus centralizers and the cyclic closure. I retained blueprint.from and its via chain. The ancestor command prints None for this existing chain, so I did not invent an ancestor. Whole-blueprint searches for Jordan, Tannaka, semisimple point and faithful representation found no equivalent imported statement; same_as stays empty. No chapter or unit record was changed.

## Mathlib searches

Ran the required leanfinder, loogle, grep and leansearch commands, then a second leanfinder phrasing. All returned successfully; none was marked unavailable or matched. The log contains the exact queries and actual hit lists, and every entry newly appended to mathlib_searches comes from that log.

I read `Mathlib/RepresentationTheory/Semisimple.lean:34` and the surrounding declarations: IsSemisimpleRepresentation means every subrepresentation has a complement. It does not address semisimple points. I also read `Mathlib/LinearAlgebra/Semisimple.lean:259,277`: the adjoin-singleton/pair results concern endomorphisms in a generated subalgebra. The present i(g) and r(g) lie on different vector spaces and those results supply no relation between them. The second phrasing instead returned affine-scheme faithfulness and scheme diagonals; the leansearch hits concern abstract-group diagonal representations or finite-group injectivity. None specializes in one line to this item.

## Not duplicates

No new nodes were created. The whole DAG searches found the existing linear Jordan and Tannaka inputs and I reused them. The unipotent-point node concludes nilpotence of r(g)-I under nilpotence of i(g)-I; it does not state the diagonalizability conclusion of this item.

## Review by Q30

I read Milne, Algebraic Groups (the supplied iAG2017 PDF), Theorem 9.2 and conditions (a)--(c), printed pp.164--165; Theorem 9.11, printed pp.168--169; Propositions 9.13 and 9.15, printed p.169; the proof of Theorem 9.18, printed p.170; and 9.19 and 9.23, printed p.171. These are also the sources of the two reused inputs. There is no new node with a separate source to check. Milne 9.23 explicitly confirms that Jordan decomposition is not restricted to smooth algebraic groups. The route uses no SGA source.

Step 1 uses the linear Jordan node for existence of invertible semisimple parts, intertwiner compatibility, tensor compatibility and uniqueness. Its statement explicitly gives all four; it is not merely a decomposition without functoriality. The Tannaka statement supplies the precise rational representations, equivariant maps, tensor action and unit. An equivariant map can be evaluated at the actual algebra k and point g, giving the intertwining equation needed by the linear node. The unit condition is checked, not assumed: I=I times I is a valid Jordan decomposition, so uniqueness supplies its semisimple part I. Both statements permit the zero representation. The step is non-elementary because it invokes those two results.

Step 2 invokes exactly the conclusion of the Tannaka statement. I checked its field hypothesis against the given algebraic closure, its affineness and finite-type hypotheses against J, and every family condition against step 1. The given i and r on k^m and k^d are particular rational representations in that statement, so its conclusion gives both displayed evaluations at h. There is no substitution of abstract group representations for rational group-scheme representations, and no density argument about J(k).

Step 3 uses only the uniqueness clause of the linear Jordan statement. The decomposition i(g)=i(g)I has an invertible diagonalizable first factor by the actual hypothesis and a commuting unipotent second factor with exponent 1. Thus i(g)_s=i(g), and step 2 gives i(h)=i(g). The stated faithfulness applies at A=k and yields h=g. This short uniqueness-and-injectivity argument is marked elementary while naming its input; it does not require i to identify J with a closed subgroup or invoke an unrecorded immersion theorem.

Step 4 substitutes h=g and uses the explicit diagonalizability of the semisimple factor from the linear Jordan statement. On the standard space k^d, an eigenbasis gives the conjugating invertible matrix in the item's definition of diagonalizable; this is the elementary change-of-basis calculation. This step is also marked elementary and cites the needed statement rather than its proof. citations.json was checked by direct substring comparison with the current statements for all five citations.

For small cases I checked g=1, where every semisimple part and the reconstructed point are the identity; m=d=1, where an invertible scalar is already diagonal; arbitrary characteristic, where the argument uses no logarithms, division by an integer or characteristic-zero assertion; a nonreduced group such as mu_p in characteristic p, whose only k-point is the identity; and disconnected finite groups. Repeated eigenvalues cause no change to the uniqueness argument. The zero-dimensional representation is allowed in the family even though the two displayed matrix representations have positive dimensions. All of these satisfy the stated conclusion without adding hypotheses.

Against delivery-errors B--E: the item retains its self-contained statement and definition dependencies, no statement-only node contains a hidden proof, no new duplicate or clause-restatement node exists, every non-elementary fact in the proof is in the statement of one of its two citations, and no cited dependency creates a cycle. I corrected the missing proof by writing the family construction and the faithful-identification calculation explicitly. No source error or statement dispute was found. The longest step is 783 characters and the total assembly proof is 1864 characters; no long step hides another lemma.

## Unfinished work

None in this split. The two supporting nodes already exist and retain their own independent proof obligations. Delivery validation and push are run with the required unmodified delivery tool.
