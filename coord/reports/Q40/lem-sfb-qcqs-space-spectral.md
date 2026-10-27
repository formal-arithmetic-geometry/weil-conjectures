# Stage-1 delivery: lem-sfb-qcqs-space-spectral

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-qcqs-space-spectral.json`: statement, split. No change to the statement. Mathlib verdict: no match for algebraic spaces; the scheme and prime-spectrum instances do not apply to the atlas point topology.
- `citations.json`: thirteen step/node citations, with literal statement excerpts.
- `report.md`: this report. No new nodes, no new Mathlib leaves, no Lean files.

## Attachments

None. Searched the project source for the exact blueprint tag and for algebraic-space/spectral notions. No project declaration supplies the assertion. Existing source declarations with sorry would not count as attachments.

## WANTED

None. All sources needed for this split are present.

## Corrections and route

The imported statement is correct; no STATEMENT-DISPUTED correction is needed. The item previously had no proof. Its existing statement dependencies and provenance are retained. The absolute diagonal in the item must not be silently identified with the relative diagonal in the existing sobriety node: step 1 now gives the base-change square and cites the affine-test/base-change theorem before applying sobriety.

Read the chapter and stored unit records, SETUP's three levels, and the current blueprint at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`, including the current unit statement and direct-images proof (3). This is the auxiliary spectral-topology input in the already recorded constructibility/Chevalley branch; it replaces no unit step. `blueprint_refs.py ancestor` reports the existing null ancestor, which is preserved together with the exact inherited place and via chain. The whole-blueprint spectral search found schemes/spectral-topology tools but no algebraic-space assertion matching this item. In particular `lem-weil-pbc-qcqs-scheme-spectral` and `lem-a1-qc-open-intersection-spectral-presentation` are about schemes, so neither states this item.

The proof follows Stacks Tag 0A4G, label lemma-quasi-compact-quasi-separated-spectral. Instead of introducing open subspaces for two quasi-compact opens, it covers both by finitely many images of affine opens of the chosen atlas. This is the same affine-pair fibre-product argument of 0A4G/0AHR. The finite-cover reductions and finite-union argument are written out, rather than made into new nodes.

## Not duplicates

No new nodes. All substantive inputs are existing nodes. Searched the whole DAG for Tag 0A4G and the topology, sobriety, atlas and intersection notions, and read the candidate statements. The other nodes citing 0A4G use the theorem rather than supplying a more general proof of it.

## Review by Q40

I read Stacks `spaces-properties.tex` Tag 0A4G in full, including its proof, and the displayed statements/proofs of 03H6 (affine atlas), 06NJ (sobriety) and 0AHR (affine-pair criterion). For the scheme and topological tools I read `schemes.tex` Tag 01IT (affine-open basis) and `topology.tex` Tag 04Z9(1) (continuous image of a quasi-compact space). No new node needs a separate source review.

For step 1 I opened `lem-sfb-space-quasicompact-affine-tests`: it states both the affine-test equivalence and preservation under arbitrary algebraic-space base change, including the representable scheme-test formulation. The pullback of the absolute diagonal to the relative product is the relative diagonal, with the same equality condition on test maps. This verifies the relative hypothesis of `lem-sfb-quasiseparated-space-sober`, whose actual conclusion supplies existence AND uniqueness of the generic point. No condition on separation of the base scheme is introduced.

For step 2 I opened all seven cited statements. `lem-sfb-qc-space-affine-etale-atlas` uses only quasi-compactness of the point space and supplies an affine representable surjective etale atlas. `lem-a1-space-affine-etale-cover` identifies its quotient topology independently of the choice of atlas, so this is the topology in the item. `lem-weil-pbc-etale-composition-cancellation` gives open immersions etale and composition of etale scheme maps; apply those on scheme tests to each atlas restriction. `lem-a1-space-point-open-calculus` explicitly states continuity for every space morphism and openness for representable etale maps. `lem-weil-pbc-affine-scheme-qcqs` supplies quasi-compactness of each affine open; `lem-weil-pbc-continuous-image-quasi-compact` applies to its map to the point space. Finally `lem-weil-pbc-affine-opens-basis` supplies an affine neighbourhood inside the open inverse image. The lifted point proves containment and coverage of the image basis. This checks every hypothesis rather than assuming that an arbitrary quasi-compact open in the atlas is affine.

For step 3 I opened `lem-sfb-space-affine-source-qc-separated`: it assumes the ABSOLUTE quasi-separatedness in this item and says that each affine etale chart has quasi-compact pullback along every affine test. Thus it gives quasi-compactness of the scheme fibre products used here, without asserting they are affine. The surjectivity onto the fibre product of point SETS in `lem-a1-space-point-open-calculus` gives the required image equality; actual topological fibre-product equality is not assumed. Its continuity clause and `lem-weil-pbc-continuous-image-quasi-compact` justify the image's quasi-compactness. The final finite-union claim is proved directly by joining finite subcovers.

For step 4 I opened `def-weil-spectral-space`: its four conditions are precisely the hypothesis and the three properties proved. This is the sole elementary assembly step. Every non-elementary fact is a cited node, and every citation quote is checked as a literal substring of the cited statement. The off-unit chart/topology results are generic tools, declared in split_report.tool_uses; they do not alter the unit route.

I checked the empty space (an empty atlas and empty finite covers are allowed), empty A or B, the one-point field spectrum, and affine schemes over a base with no separation assumption. The argument never assumes an intersection of affine opens is affine, never assumes Noetherianity or finite type, and uses uniqueness from sobriety rather than existence alone. All proof steps are below 2000 characters and contain the finite-cover and point-lifting arguments explicitly. The B--E return checklist was checked against the node files and sources: no statement-only-node violation, duplicate, invented search, hidden source lemma, changed coefficient category, or clause restated as a new node.

The search log contains the actual four prescribed search kinds and a second LeanFinder phrasing. I read their hits and Mathlib `AlgebraicGeometry/Properties.lean:39-60` and `Topology/Spectral/Basic.lean:32-49`: the scheme/prime-spectrum assertions and general SpectralSpace constructor leave the algebraic-space work to be proved, so this is not a Mathlib leaf. Prior recorded searches are retained.

## Source wording

The last sentence of the local 03H6 proof calls the finite union's map “finite surjective”; the construction only establishes an etale surjective atlas, as the lemma statement correctly says. No finiteness of that morphism is used here or in the cited affine-atlas node.

## Unfinished work

None for this one-level split. Existing cited nodes retain their own stage status. No compilation or local DAG/preflight checker was run; verification uses the required server delivery dry run.
