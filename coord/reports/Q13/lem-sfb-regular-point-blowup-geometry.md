# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-regular-point-blowup-geometry.json`: statement, split; eight proof steps, all using existing DAG interfaces. No new nodes and no new Mathlib leaves.
- `citations.json`: verbatim statement excerpts for all 26 step/node citation pairs.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log. `write_split.py` is sandbox scratch work, not part of the delivery.

The item statement, its statement dependencies, source, creation record and inherited blueprint ancestry are unchanged. Only split-owned fields were updated. No Lean was written and no compiler or build tool was run.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, regular blowup geometry, and blowup Noetherianity. The existing declarations in `Blowup/Proper.lean` and `Blowup/Density.lean` cover properness or Noetherianity, not regular local rings at exceptional points; the affine `isRegular_awayAlgebraMap` results concern nonzerodivisors. No declaration found gives the entire item. The already existing DAG interfaces for these partial results are used.

## WANTED

None. All sources used are present in `literature/stacks-project/`.

## Problems and corrections

The imported statement is correct. Its assumptions are deliberately weaker than the excellent globally two-dimensional setting of `lem-per-surface-point-blowup-geometry`: only the local dimension at the center is two. I did not introduce excellence, separatedness, an ample sheaf, a field base, or a global dimension bound. I replaced the empty proof by a localization argument, explicitly proving the local-ring comparison and the closedness of the lift of a closed exceptional point. These are needed before applying the local surface lemma.

During self-review I removed an imprecise attribution of an ideal-sheaf stalk computation to the structure-sheaf stalk lemma. Nonzeroness is now checked directly on an affine neighborhood: a zero center ideal would make its maximal ideal zero and the local ring a field. I also added the actual definition of finite type for a sheaf to the first step's citations.

No unit or chapter route changed. The generic off-unit tools that are not already Mathlib leaves or Lean-closed are declared in `split_report.tool_uses`: integral blowup geometry and the canonical map from the spectrum of a local ring. Properness, the complement theorem, and the flat blowup comparison are existing closed tools. This is the local geometry prerequisite named in the inherited blueprint place, not an alteration argument. `blueprint_refs.py ancestor` reports no blueprint ancestor for this already unlinked chain; its inherited null ancestor and via list were retained. Searches of the full blueprint for `blowup regular`, `quadratic`, `0AGR`, `0AGQ`, and `blowup` found no imported node with this exact global statement. The first four searches had zero hits; the last returned general Nagata blowup nodes, which were inspected and reused as applicable.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs to justify. I reused `lem-sfb-local-surface-maximal-blowup-geometry` rather than creating another local 0AGQ/0AGR lemma. `lem-per-local-surface-maximal-blowup-geometry` already states that same local result; it was not copied or edited. The global excellent surface lemma has additional excellence, global-dimension and ampleness assumptions and cannot prove the present item under its stated hypotheses. The local lemma applies to Spec of the local ring; the proof here supplies the passage to an arbitrary integral regular Noetherian scheme.

## Searches and Mathlib verdict

The item's inherited Mathlib search results were retained. I ran the required logged searches again for this split's global statement: LeanFinder in two phrasings, LeanSearch, Loogle on `"AlgebraicGeometry", "IsRegular"`, unrestricted grep, and a further grep restricted to `AlgebraicGeometry`. Every query is recorded with exactly the tool/query text of the command log. The unrestricted grep was capped, so it is not used as evidence of absence by itself. The restricted grep has only seven regular-epimorphism hits. The semantic searches return smoothness and standard-smoothness, scheme integrality/properness predicates, normalization, and residue-field maps; none is a point-blowup regularity theorem. In particular categorical regular epimorphisms and nonzerodivisors do not mean regular local rings. The item is not a Mathlib leaf.

## Review by Q13

I read Stacks `resolve.tex`, Tags 0AGQ (`lemma-blowup`) and 0AGR (`lemma-blowup-regular`), including their full proofs. The latter checks regularity at a closed exceptional point by a Cartier equation whose quotient is the regular local ring of a point of the projective line. I checked the local lemma's two-dimensional closed-point assertion against that calculation, rather than treating the word "regular" alone as a dimension statement. I also read the actual statements and proofs of flat base change of blowups (0805), integrality (02ND), the complement/Cartier-divisor lemma (02OS), projectivity for finite-type ideals (02NS), and finite-type preservation of Noetherianity (01T6). For the localization comparison I read the affine fibre-product statements and proofs (01I4 and 01JQ), the open fibre-product statement (01JR), the affine stalk formula (01HV), the canonical local-spectrum construction (01J6/02NA), and the tensor-localization and spectrum-localization statements/proofs (00DK and 00E3). No SGA source is used.

For every step I opened the files of all cited nodes and checked the statement, not its proof, against the claimed use. The complete matching excerpts are in `citations.json`:

1. The closed-immersion ideal definition gives quasi-coherence and its affine ideal. The locally Noetherian definition supplies a cover with Noetherian coordinate rings, the Noetherian-ring definition makes the ideals finitely generated, and the quasi-coherence/finite-type definition converts those generators to the local finite-free surjections. The affine stalk theorem identifies the local ring with the prime localization; the Krull-dimension definition rules out the field case. No separate ideal-stalk theorem is invoked.
2. Integral blowup geometry is applied only after nonzeroness, finite type, quasi-coherence and integrality have been verified. The proper blowup lemma needs only the verified finite-type ideal. The properness definition includes finite type, and the finite-type-over-Noetherian theorem says exactly that the source is Noetherian. Its quasi-compactness clause is thus accounted for.
3. The complement theorem explicitly gives an isomorphism off the zero set of the center. This zero set is the singleton p. The regular-scheme definition supplies the local-ring characterization; ordinary restriction along the open isomorphism identifies the stalks.
4. The canonical-local-spectrum node explicitly gives flatness and the affine localization model. The regular-scheme definition and the item's dimension hypothesis give precisely a regular local ring A of dimension two. The flat comparison definition specifies the extended ideal and the correct fibre product, and its theorem states that this comparison is an isomorphism. The inverse image of the reduced point is the maximal ideal of A, not an arbitrary thickening.
5. The open fibre-product node identifies the actual inverse-image chart as an open subscheme. The affine fibre-product theorem identifies its coordinate ring as the tensor product. The tensor-localization node identifies this with the localization of B. The localization-spectrum node gives the unique prime over Q because Q contracts to p, hence avoids the inverted elements. This proves uniqueness in the entire inverse image, not just inside one chart.
6. The affine stalk node gives the two localized rings. The localization-spectrum node says which primes survive, so the displayed fraction formulas have valid denominators. Multiplication of fractions verifies both inverse composites and their fraction relations. This is an elementary argument from those interfaces, not an unsupported general assertion that all flat base changes preserve local rings. It applies to nonclosed points as well.
7. The reused local surface node explicitly states regularity of Y. The regular-scheme definition converts this to regularity of its local rings. Step 6 transports those local rings, while step 3 covers the complement. Local Noetherianity has already been proved, so the equivalence in the definition applies to X'.
8. The singleton preimage is closed by continuity and the uniqueness in step 5. Its point is over the maximal ideal and is consequently a closed point in the exceptional fibre. The reused local surface node explicitly gives dimension two for precisely such points. The ring isomorphism from step 6 preserves the prime chains in the cited Krull-dimension definition.

I tested the hypotheses on a local regular surface, on a smooth affine surface over a field with possibly nonrational closed points, and on an integral regular scheme with points of local dimension different from two away from the center. The proof needs no residue-field algebraic closure and does not infer that all local rings of X' have dimension two. The generic exceptional point is handled for regularity but is deliberately excluded from the dimension-two conclusion: its local dimension is one. No zero center ideal or zero-dimensional center local ring can satisfy the dimension-two input. I also traversed the existing dependency edges and found no path returning to this item (unrelated missing descendant IDs were not edited), and that every step is below 2000 characters; the short fraction calculation hides no deferred lemma.

## Unfinished work

None in the stage-1 split. Existing unsplit dependencies remain existing queue items; no new subsidiary statements were introduced. Delivery validation is performed by the required remote dry run, followed by the direct push.
