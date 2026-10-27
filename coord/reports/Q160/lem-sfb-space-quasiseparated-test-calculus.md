# Q160: lem-sfb-space-quasiseparated-test-calculus

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-quasiseparated-test-calculus.json`: statement, split; no Mathlib match. Five proof steps, all inputs already in the live DAG.
- `citations.json`: 15 verbatim statement excerpts, one for every step/node citation.
- `searches.jsonl`: the actual search-command log, retained unchanged.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the whole `lean/WeilConjectures/` for the item tag and algebraic-space terminology, and inspected the quasi-separated scheme material. No declaration of the project proves this algebraic-space statement. The Mathlib scheme declarations are not attachments.

## WANTED

None. All mathematical sources needed are present in `literature/stacks-project/`.

## Corrections and route

The original statement had doubled TeX backslashes. I corrected those and added the explicit definition-node citation for quasi-compact schemes. The mathematical statement, all four conclusions and all hypotheses are unchanged. No STATEMENT-DISPUTED issue was found.

Read the chapter and the unit record and the latest blueprint's `sk-thm-sf-ctf-stability/_section.md`, direct-images statement and direct-images proof (3). The item belongs to the pre-existing chain of algebraic-space tools for the stack quasi-separatedness composition argument, via adequate moduli and stable-curve parameters. The latest blueprint no longer expands that old alteration/moduli chain: it now assembles direct images through compactification. I preserve the item's inherited provenance, including its null `from.node` and its complete `via` list, rather than inventing an ancestor or changing the unit or chapter. This helper supplies separation calculus at precisely the place already recorded in `from.place`.

The sole off-unit statement input is `lem-trf-space-fibre-products-etale-covers`, recorded in `split_report.tool_uses`: it supplies the generic fibre-product construction and atlas pullbacks, not an alternative cohomological route. The other off-unit statement inputs are existing Mathlib leaves about schemes.

## Searches and reuse

Ran the required search command for leanfinder, loogle, grep and leansearch, then tried a second leanfinder phrasing. All services answered. LeanFinder/Loogle/LeanSearch returned `AlgebraicGeometry.QuasiSeparated` and its scheme composition/base-change/diagonal results. Read `Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean`, lines 46-52 and 116-130: its variables are Scheme, so these do not state the algebraic-space result and do not specialize to it in one line. The grep hits are the same scheme declarations. The node retains Q149's historical searches and appends exactly the five searches run by Q160, with the command's actual result summaries.

Searched the whole DAG for 03KM, 03KL, 03KQ, 03KK and the quasi-compactness/diagonal inputs, and ran blueprint_refs searches for quasi-separated, quasiseparated and 03KM. Read the existing quasi-compact affine-test lemma, diagonal scheme-test lemma, separated/finite-presentation composition lemma, and quasi-compact fppf-locality lemma before choosing inputs. The affine-test lemma uses quasi-compact SCHEME tests, so I did not silently identify its predicate with this item's all-algebraic-space-test definition. Instead the proof uses the exact all-test fppf-locality statement, with elementary all-test base-change/composition calculations. No new node is needed for either calculation or for the diagonal identities.

## Not duplicates

No new nodes are created, so there are no new/existing same-tag pairs. The nearby `lem-sfb-space-separated-fp-composition` has separated, locally finitely presented and finitely presented composition conclusions, and separated base change; its statement does not give this item's quasi-separated scheme-test equivalence or quasi-separated base change/composition. I use none of its internal proof as an unstated lemma. The affine-test and fppf-locality statements concern quasi-compactness itself, not quasi-separatedness.

## Review by Q160

I read the source proofs in `spaces-morphisms.tex`: 03KM (`lemma-separated-local`), 03KL (`lemma-base-change-separated`), 03KN (`lemma-fibre-product-after-map`), 03KQ (`lemma-composition-separated`) and 03KK (`lemma-trivial-implications`). I also read the exact all-test definition 03HE, the transitivity hints in 03HF/03HG, the representable comparison proof 03HD, and the quasi-compact target-locality proof 03KG. No new node needs an additional source review.

Step 1 cites the algebraic-space clause of `def-sfb-stack-qcqs-morphism`, not its different stack quasi-separatedness predicate. That statement defines quasi-compactness by ALL quasi-compact algebraic-space tests. The fibre-product node states the universal property needed to reassociate the products. For base change the same test Z works; for composition the intermediate Y_W is quasi-compact by the first hypothesis and therefore is an admissible test of the other map. These are the complete transitivity arguments omitted in 03HF and 03HG, not unrecorded permanence theorems.

Step 2 uses only the fibre-product statement's universal property. I checked the targets of both relative diagonals: A over B gives A times_B A; the composite over C gives A times_C A. The right-hand comparison map is a pullback of B's diagonal over C. The description on sections gives a natural isomorphism of sheaves, rather than just equality of their point sets. The same calculation identifies the diagonal after arbitrary B-prime base change. This is elementary categorical bookkeeping, not a new lemma hidden in a long step.

Step 3 applies the definition of quasi-separatedness from the exact algebraic-space clause of the definition node to the two identities and the previously established quasi-compactness calculus. Both diagonals in the composition argument are quasi-compact by hypothesis. The arbitrary base change has no scheme or quasi-compactness restriction, so it includes every scheme test and proves the forward implication as well.

Step 4 uses the statement of `def-trf-algebraic-space` for the existence of an arbitrary scheme atlas of D, and the fibre-product construction node for all products. The map T to B is well-defined because the two coordinates of its map to A times_B A have the SAME B-value. The pair of sections defines the map s; a pullback of the diagonal along s is the equalizer of those two sections, which is exactly A times_D T. This proves the comparison explicitly and does not assume that A_T is a scheme. The hypothesis applies to this T, since it is a scheme over B; it makes the tested diagonal quasi-compact. The fppf-locality node's statement genuinely uses the SAME all-space-test predicate and gives descent along a small jointly surjective family flat and locally of finite presentation on etale charts. Our family is a singleton atlas and therefore small, with the required surjectivity. The scheme etale definition supplies flatness and local finite presentation for its represented chart tests. No quasi-compactness of the atlas, the base scheme S or the diagonal target is needed. This avoids using the affine-test node with a mismatched convention.

Step 5 follows 03KK's closed-immersion input and expands the representable comparison argument of 03HD. The closed-immersion definition's statement explicitly includes the affine characterization, so it really supplies affineness of inverse images; it is not a bare definition being cited for an unstated permanence theorem. The affine-scheme Mathlib leaf supplies their quasi-compactness. The finite-type definition identifies this with scheme quasi-compactness. The quasi-compact inverse-image Mathlib leaf then applies with W equal to ALL of U, a quasi-compact open, so E is a quasi-compact scheme. The fibre-product node states preservation of etale covering families under arbitrary pullback, which applies to the atlas U to Z and gives E to A times_D Z. This is the required actual etale atlas; I did not replace atlas quasi-compactness by point-space compactness without justification. Z is every quasi-compact algebraic-space test, so this proves the desired diagonal predicate in full.

For C4, every cited statement was opened and read; `citations.json` copies its actual sentence or formula without alteration. For C1, the only non-elementary facts are the cited fppf quasi-compactness descent, existence/pullback of atlases, affineness in the closed-immersion characterization and the two scheme compactness leaves. All are named at their uses. All remaining facts are explicit fibre-product calculations or immediate applications of established steps. No proof has been moved to a new node that restates a conclusion; there are no new unsplit proof sketches, new notions without definitions, or new literature tags to audit. I checked that no cited dependency reaches this item, so the proposed edges introduce no cycle. All steps are shorter than 2000 characters.

Small cases: the empty target diagonal admits an empty atlas, and the argument still works; the singleton atlas family remains small and surjective, including the empty-space case. Identity maps have an isomorphism diagonal and satisfy all four conclusions. On schemes the two diagonal identities reduce to the ordinary relative ones. Neither the composition step nor the reverse scheme-test step assumes absolute separation of a source or target. The closed-immersion step uses a quasi-compact atlas only for Z, which is quasi-compact BY THE TEST; it never assumes the original morphism or its diagonal target is quasi-compact. Thus the proof does not add the missing hypotheses responsible for the E1 return cases.

## Unfinished work

No mathematical split work remains. New-node count is zero; the final remote dry run and direct delivery are performed by the required delivery command.
