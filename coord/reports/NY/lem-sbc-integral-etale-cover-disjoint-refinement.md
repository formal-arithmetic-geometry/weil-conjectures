# Stage 1 report: lem-sbc-integral-etale-cover-disjoint-refinement

## New nodes

None. The split reuses `lem-sbc-standard-etale-finite-subalgebra` and `lem-sbc-finite-pointed-piece-refinement`.

## Attachments

`AlgebraicGeometry.Scheme.Hom.Nbhd.exists_hom_disjoint_cover` in `WeilConjectures/AlgebraicGeometry/Morphisms/Integral/DisjointCover.lean:254` is relevant Lean source, but is not an exact attachment: it is formulated for an algebraically closed geometric point and a covering sieve, whereas this item quantifies an ordinary point of an etale object and an indexed covering family.

## WANTED:

None.

## What was checked

The item source is Stacks Project `literature/stacks-project/etale-cohomology.tex`, Tag 04DR (`lemma-integral-B`), with the explicit refinement condition from Tag 04DP and the finite reduction through Tag 04DQ. I read the existing DAG statements for `lem-sbc-standard-etale-finite-subalgebra` and `lem-sbc-finite-pointed-piece-refinement`; each says exactly the input used in its cited step. Step 1 performs the affine and finite standard-etale reduction described in 04DR. Step 2 uses the finite-subalgebra statement to descend the finite family. Step 3 uses the finite pointed-piece refinement to obtain a disjoint clopen decomposition after an etale neighbourhood. Step 4 checks that scalar extension preserves the decomposition and maps, then reindexes the pieces and handles the empty pullback. I also inspected the Lean declaration `Scheme.Hom.Nbhd.exists_hom_disjoint_cover` and verified its hypotheses and conclusion differ from this item's ordinary-family formulation, so I did not claim attachment.

## Not duplicates

`lem-sbc-integral-etale-cover-disjoint-refinement` vs `lem-sbc-standard-etale-finite-subalgebra`: the latter is ring-level finite descent for standard etale algebras; the item is the resulting scheme-level disjoint refinement.
`lem-sbc-integral-etale-cover-disjoint-refinement` vs `lem-sbc-finite-pointed-piece-refinement`: the latter assumes a finite morphism and gives geometric-fibre pieces; the item handles arbitrary integral morphisms and an arbitrary covering family.

## Review by NY

I checked every proof step against the cited Stacks passage and opened both cited node files. The affine reduction is explicitly the first paragraph of 04DR; the finite descent is the displayed algebra reduction there and matches the finite-subalgebra node; the finite decomposition is the 04DQ input; and the final pullback/reindexing is the concluding paragraph of 04DR. The hypotheses that the covering is etale and jointly surjective, that the morphism is integral, and that the empty decomposition is permitted were checked against the item statement and the source. I corrected the initial attachment temptation after comparing the Lean theorem's geometric-point/sieve hypotheses with the item's ordinary-point/family hypotheses. No new node was introduced because the two substantive reductions already exist in the DAG.

## Second reading by NY

- Item statement: checked hypothesis by hypothesis against etale-cohomology.tex 04DR (lemma-integral-B) and 04DP (lemma-simplify-B): integral, arbitrary etale base object, ordinary point and arbitrary jointly surjective family agree; repeated covering indices are represented by α. True also for the empty scheme and over a field; no statement change needed.
- Step 1: checked 04DR affine reduction, 01IT affine-opens basis, 01WL integral base change, covering base change, and the actual integral definition. Corrected the reduction to the integral morphism over an affine open of V; no unjustified assertion that the original X is affine.
- Step 2: checked 00UE (proposition-etale-locally-standard), 03WT (lemma-etale-open), 00E8 (lemma-quasi-compact) and the cited affine-opens statement. Finite selection uses openness plus quasi-compactness; all refinement maps into the original family are retained. Non-elementary inputs now cited.
- Step 3: opened the full finite-subalgebra node and StandardEtale.lean:170–197, and checked 04DR with 00GQ (lemma-integral-overring-surjective). Corrected the input ring to B=Γ(X times_Y V_0), and supplied the missing surjectivity argument for the descended cover. B_0 is genuinely a subalgebra, so lying over has its injectivity hypothesis even if A→B is not injective. Correct for the zero ring and an empty covering of an empty scheme.
- Step 4: opened the full finite-pointed-piece node and PieceSection.lean:53–173, and checked the finite-fibre input 01WN/02NU/02NH and geometric-cover lifting 03PR (lemma-geometric-lift-to-cover). The cited piece lemma supplies one selected piece, not maps for all pieces; applied it separately to the finite set of geometric fibre points. Finite-module base change and the finite-dimensional-domain argument justify that set's finiteness and its identification with Ω-points. Checked a field with several separable embeddings and a nonreduced finite fibre; neither is collapsed to a single selected lift.
- Step 5: checked the finite-limits clause of def-weil-pbc-etale-site and the actual fibre-product/open-subscheme definitions. The tuple of marked points gives a common pointed neighbourhood; ordered clopen differences give disjoint pieces retaining each marked point. This elementary set argument works for zero or one piece without relying on an unspecified simultaneous-refinement theorem.
- Step 6: opened finite-geometric-point-lift and finite-closed-map-finite-fibres in full, and checked 04DQ's last paragraph, 01WN and the finite-geometric-lift source explanation (09ZE, 01TG). Every ordinary point over the marked base point lifts with the same Ω, hence is covered. Removed the finite closed image of the complement, including the zero-piece case. A geometric fibre cover alone was not assumed to cover the whole scheme.
- Step 7: checked the two actual descent isomorphisms and the fibre-product universal property against 04DR's concluding reduction. W_t maps to the original member via its two compatible maps, then the retained refinement map; structural projection compatibility follows from those components. Pullback of disjoint opens is elementary by inverse-image union/intersection identities.
- New nodes: none; B1–B7 and new-node Mathlib searches are vacuous. Existing nodes were searched by source tags, standard-etale vocabulary, lying over, finite closed maps, geometric lifts and affine bases. Their full statements were opened, and citations.json now quotes those statements verbatim. The extra inputs are existing generic tools; their uses are declared in split_report.tool_uses.

Changes: replaced the unsupported elementary affine/standard-etale reduction with cited reductions; based descent on the already pulled-back integral algebra; proved the descended family covers by lying over; expanded the one-piece lemma into finitely many pointed refinements, explicit disjointization and closed-complement shrinking; expanded the final fibre-product maps; refreshed all citation quotes. The original statement, first-worker report and Review by NY remain in place. No new nodes, Mathlib leaves, Lean edits or builds.

The affine tensor-product/fibre-product comparison in step 3 is also spelled out on affine test schemes using def-weil-affine-spectrum and the tensor universal property, followed by gluing; later finite-module base changes and step 7 use this established comparison.
