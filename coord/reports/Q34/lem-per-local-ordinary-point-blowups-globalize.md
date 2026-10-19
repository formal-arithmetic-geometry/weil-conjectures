# Worker report: lem-per-local-ordinary-point-blowups-globalize

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-local-ordinary-point-blowups-globalize.json`: statement node, now split in ten steps; no Mathlib match for the whole tower assertion.
- No new nodes and no new Mathlib leaves. `citations.json` contains a verbatim statement excerpt for each of the thirty step citations. `searches.jsonl` records the five searches run by Q34. The item's earlier Q40 searches are retained.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree for the exact blueprint tag, the item id, ordinary/point blowups and blowup sequences. There is no declaration covering the prescribed finite local towers, all intermediate identifications, normality and the singular-center clause. Existing ordinary-blowup constructions and localization infrastructure alone do not attach this item. The upstream master checkout is reference material only.

## WANTED

None. All sources used for the split are present in `literature/stacks-project/`.

## What changed and what was wrong

The item had a statement and searches, but no proof. The statement is unchanged. Stacks 0BFY ends the converse with “in exactly the same manner”; the delivery supplies that manner as an induction with an explicit schedule and compatible intermediate identifications. It also proves the extra local-ring, normality, singular-center and zero-length assertions in the item. It does not infer that ordinary blowups preserve normality without the local-stage hypotheses.

The scheme-theoretic center needs care: a closed point in the local tower first gives a closed point in the closed global fibre, hence in the global scheme. Its reduced ideal then localizes to the reduced prescribed point, rather than to an unspecified subscheme with that support. Distinct closed base points give empty centers in the inactive local factors. I wrote both calculations out.

The nonzero-ideal hypothesis in the integral-blowup result is essential. If a center ideal were zero, the Rees algebra would have no positive degrees, so its blowup would be empty; its active local base change is an assumed integral, hence nonempty, prescribed next stage. This excludes that case before applying the integral-blowup node. In particular this also handles the potential dimension-zero exception.

## Existing-node and blueprint searches

I searched the full DAG for 0BFY, 0BFX, blowup localization and flat base change, integral blowups, local-ring comparisons, reduced closed subschemes and Noetherian preservation. I also ran `tools/blueprint_refs.py ancestor` and whole-blueprint searches for blowup, localization, local rings localization and blowups local. The ancestor is `lem-per-artin-gabber-affine-curve`; no other blueprint node states this ordinary point-tower globalization. The normalized-tower sibling `lem-per-local-normalized-blowups-globalize` has a different statement: it includes normalization after each blowup and cannot supply this ordinary tower. I reused `lem-per-integral-blowup-projective-geometry` for its integrality clause. All other ingredients already had DAG nodes; I created no specializations or duplicate leaves.

The chapter and unit records were read. This technical geometric input remains under the arbitrary-field duality/potential-dualizing surface construction of the ancestor's first proof step. The chapter and unit route are unchanged, as is the recorded blueprint ancestry. The current blueprint ancestor was checked in `main-20261015`. The unit's key nodes are not this item, so no realization record was edited.

## Mathlib searches

I ran LeanFinder on the finite-tower statement and again on extension of stalk-local point blowups with exceptional-fibre local-ring identifications. I ran LeanSearch on extension of point-blowup sequences, Loogle with `"blowup", "localization"`, and the recorded grep on the Mathlib source. I read the returned signatures: the semantic hits concern morphisms from stalk spectra, partial rational maps, finiteness, normalization and scheme definitions. None supplies the compatible finite ordinary tower theorem, nor a one-line specialization of it. Loogle and grep had zero hits. No unavailable search was recorded as absence. The queries and actual results are in the node and the command log.

## Tool uses

The canonical local-scheme morphism node and the reduced induced closed-subscheme node are generic scheme tools outside this unit, declared in `split_report.tool_uses`. The former provides affine localization and its image, the latter the center's quasi-coherent radical ideal and uniqueness. They do not replace the unit route. Flat-base-change, properness and the complement theorem already have closed Lean audits; ring-localization and Noetherian preservation nodes are Mathlib leaves. Integrality is supplied by the existing same-unit integral-blowup node.

## Review by Q34

I read `resolve.tex`, section-modifications, equation-equivalence and the complete proof of resolve-lemma-equivalence-sequence-blowups (0BFY), together with resolve-lemma-equivalence-fibre (0BFX). I checked the scheme localization proof in schemes-lemma-fibre-topological (01K1), the canonical morphism after schemes-lemma-morphism-from-spec-local-ring (01J6, equation 02NA), and schemes-lemma-reduced-closed-subscheme (01J3) with its construction and uniqueness proof. For blowups I read divisors-lemma-blowing-up-affine (0804), divisors-lemma-flat-base-change-blowing-up (0805), divisors-lemma-blowing-up-gives-effective-Cartier-divisor (02OS), divisors-lemma-blow-up-integral-scheme (02ND), and divisors-lemma-blowing-up-projective (02NS). I read morphisms-lemma-finite-type-noetherian (01T6). I opened the statements of every cited DAG node, including the definition nodes used for the empty blowup calculation. There are no new nodes requiring further source checks.

Step 1 uses the fibre-product universal property to initialize the finite scheduled induction, with no geometric theorem hidden in the bookkeeping. Step 2 takes the affine localization description and generalization image from the canonical local-scheme node, the tensor localization from `lem-weil-pbc-localization-base-change`, and the prime-space embedding from `lem-weil-pbc-localization-spectrum-embedding`. These statements give exactly those facts for arbitrary base rings; no finite-type, separateness or algebraic-closedness assumption is inserted. Step 3 writes inverse maps on fractions and checks their composites, giving the structural local-ring map and its flatness from the flat-morphism definition. It does not confuse the local-scheme base change with the quotient local ring of a fibre.

Step 4 transfers a closed point through the fibre subspace correspondence, uses that the base singleton is closed, and applies the reduced-subscheme node for its quasi-coherent ideal. The finite-type condition follows on a Noetherian affine cover from every ideal being finitely generated. Step 5 uses the localization-base-change and reduced-structure statements to check the ideal, not merely its support: the active quotient is the same residue field, and an inactive quotient is zero. The canonical image statement applies because the base points are distinct and closed; no two of them can generalize each other.

Step 6 applies the flat-blowup comparison only after step 3 proves flatness of the actual projections. Its statement and its statement dependency give the comparison with the blowup of the extended ideal. The complement theorem handles an empty center. Universal uniqueness of fibre products supplies the associators, and the comparisons are over the preceding stage, which proves commutativity with the tower arrows rather than just stagewise isomorphism.

Step 7 first excludes a zero ideal using the nonemptiness of the prescribed next stage; the Rees, affine-Proj, affine-blowup and global gluing definitions justify the empty blowup calculation. Only then does it invoke the nonzero-ideal integral-blowup statement. Step 8 checks the finite-type quasi-coherent hypothesis of properness, then uses the definition of proper and finite-type Noetherian preservation. Its complement citation says precisely that the restriction away from the center is an isomorphism. Step 9 obtains normality point by point using the prescribed normal stages over the exceptional fibres and the unchanged normal base off them. Step 10 reads singularity through the actual local-ring isomorphism; the regular-local definition is invariant under ring isomorphism.

I tested the empty index set, all lengths zero, one point with one blowup, unequal lengths at two distinct points, a regular Cartier point whose blowup is an identity morphism, and the attempted blowup of a zero-dimensional integral point. An identity blowup is still counted in the prescribed length and increments one index; the dimension-zero zero-ideal attempt contradicts the nonempty prescribed next-stage hypothesis. No excellence, dimension-two, Nagata, regularity of the base, or algebraic-closedness hypothesis is needed. The only corrections during self-review were to make the reduced-center and nonzero-ideal arguments explicit and to correct the fibre-topology tag to 01K1. Every proof step is shorter than 2000 characters; the localization calculations are elementary consequences of the cited ring statements and written inverse maps. No source or imported-statement dispute was found.

## Unfinished work

None within this stage-1 item. Existing unsplit dependencies remain their owners' items. No Lean was written and no compiler, Lake or build tool was run.

## Validation

The required `deliver.py Q34 lem-per-local-ordinary-point-blowups-globalize --no-push` exited successfully: `OK (not pushed)` at `75cfd6af1c`, with server preflight passed (including the DAG and split checks). No Lean compiler was run. The delivery command repeats preflight before pushing.
