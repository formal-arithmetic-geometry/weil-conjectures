# Stage 1 report: lem-sfb-cartesian-groupoid-pushforward-adjunction

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-cartesian-groupoid-pushforward-adjunction.json`: statement node, split, no new nodes.
- `citations.json`: 35 citations, each checked verbatim against the cited node statement.

## Attachments

No new attachments. The project source search found no declaration tagged `(blueprint: lem-sfb-cartesian-groupoid-pushforward-adjunction)` and no declaration stating this equivariant groupoid pushforward adjunction.

## WANTED

None. The proof follows `literature/stacks-project/groupoids.tex`, whose Tags 03LJ and 09VH are present locally; the omitted details are expanded using existing DAG statements and the Mathlib mates API.

## What was checked and corrected

The imported node had an empty proof, a null blueprint ancestor inherited through its creation chain. The original `created.item` parent is retained. I retained its statement and source, filled the nearest current blueprint ancestor as `det-thm-sf-ctf-stability-direct-images`, and supplied an eight-step proof. I created no node because every non-elementary input is already represented in the DAG: pullback/pushforward adjunction (`lem-pc-module-pullback-adjunction`), quasi-coherent pullback (`lem-weil-pbc-module-pullback-quasi-coherent`), qcqs pushforward (`pqf-lem-pushforward-qcoh`), degree-zero flat base change (`lem-pc-flat-base-change-cohom`), qcqs permanence under base change (`lem-weil-pbc-qcqs-morphism-permanence`), flatness under base change (`lem-weil-pbc-flat-morphism-base-change`), and mate identities (`lem-amb-mate-unit-counit`, `new-integral-residue-mate-pasting`, `lem-sfb-adjunction-transpose-square`).

## Review by Q41

I read the complete source statement and proof of Tags 03LJ and 09VH in `literature/stacks-project/groupoids.tex`, including the exact hypotheses that the object map is quasi-compact and quasi-separated, the target source and target maps are flat, and only the target square is assumed Cartesian. Step 1 checks that inversion transfers Cartesianity to the source square and verifies the pullback equivariance equations using the groupoid-functor laws. Step 2 defines the canonical ordinary base-change comparison as an adjunction mate and proves its pasting and identity properties from the existing inverse-mate node; this is the omitted coherence argument in the source. Step 3 reads the transpose of the comparison explicitly and uses the existing ordinary module adjunction and mate-counit identity. Step 4 applies the existing qcqs pushforward and flat base-change nodes to construct the equivariant structure on `f_*N`; all hypotheses are matched to the source squares and to the stated flat maps. Step 5 checks that the two pair-groupoid projection squares are Cartesian by the fibre-product universal property, that `f_1` is qcqs by base-change permanence, and that the pair projections are flat by flatness stability under base change. Step 6 proves the identity condition by pasting the identity square and cancelling the invertible comparison; no flatness of the identity map is assumed. Step 7 expands the cocycle calculation, naming the three comparison maps and using naturality, pasting, and the original cocycle for `gamma`. Step 8 transposes an arbitrary ordinary map in both directions; the transpose calculation identifies equivariance on the source and target, so the ordinary Hom bijection restricts to the claimed natural bijection. I checked every `uses` entry against its node statement and recorded the exact sentence or formula in `citations.json`. I also ran all four required Mathlib search kinds for the item; the hits were only ordinary sheaf-module adjunctions, pseudofunctor comparisons, or generic mates, so the item is not a Mathlib leaf.


I also read the supporting sources directly: `schemes.tex` Tag 01LC (`lemma-push-forward-quasi-coherent`), `coherent.tex` Tag 02KH (`lemma-flat-base-change-cohomology`), `modules.tex` Tag 01BG (`lemma-pullback-quasi-coherent`), and `sheaves.tex` Tags 0096 and 0097 (ordinary tensor-pullback adjunction and composition). For the formal calculation I read Mathlib `CategoryTheory/Adjunction/Mates.lean` at the mate-counit and unit identities and the pasting declarations, and read the existing `lean/Sheaf/Paper/IntegralResidueMatePasting.lean` statement. I checked that the inverse-mate pasting result can be used in reverse here: insert the composite forward mate, whose inverse mate is the pasted pullback comparison; the pullback composition equality determines the outer comparison, and bijectivity forces equality of the forward mates. This use is declared in `split_report.tool_uses` because the node belongs to another unit.

Small cases checked: identity groupoid morphisms give identity base-change maps and the usual identity adjunction; unit groupoids give the ordinary qcqs quasi-coherent adjunction; empty object and arrow schemes cause no existence or faithfulness requirement. The arguments do not assume `f_0` is flat, proper, affine, or surjective, nor that the schemes are Noetherian, nor that an identity section is flat. The two pair-projection comparisons are obtained from flat base change with `f_1`, after verifying its qcqs hypothesis, rather than assuming a general nonflat base-change theorem. The three maps in step 7 are maps from the same module to the same module on `P'`; their intermediate factor at the middle vertex is `C_w`, which is precisely the common source/target pullback because `s pr_0 = t pr_1`.

B--E audit: no new node is elementary, duplicate, or a clause relabelled as a lemma because no new nodes are introduced. Every substantive input has a node citation, none is borrowed from a dependency's proof, and the definition nodes are used only for their stated data or formulae. The only elementary steps (3, 6, 7, 8) are explicit substitutions and cancellations from the canonical comparison identities proved in step 2 and the cited adjunction equations. Every step has fewer than 2000 characters. No axiom or unstated theorem is hidden in a long step. The current `literature/blueprint/latest/` chapter, unit, direct-images statement and proof were read: this is a supporting groupoid lemma below inherited proof (3), without changing the chapter or unit route. Whole-DAG and blueprint searches for groupoid, flat base change, pushforward quasi-coherence, mates and transpose showed the existing inputs; no alternative blueprint node states the complete item. The earlier six historical Mathlib searches are preserved verbatim; the Q41 logged queries are appended, with the actual hits read.

## Not duplicates

No new nodes. All input statements above reuse existing DAG ids.

## Unfinished work

None in the requested one-level split. Deeper splitting of existing dependencies is outside this item. No statement dispute, no source correction, no Lean writing or compiler invocation.
