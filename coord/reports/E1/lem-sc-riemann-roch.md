# Stage-1 delivery: lem-sc-riemann-roch

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-riemann-roch.json`: split item; four new facts and the existing Euler, divisor, and cohomology nodes support seven proof steps.
- `dag/nodes/sec-picard-framework/lem-sc-torsion-subsheaf-quotient.json`: statement, unsplit; no Mathlib match (LeanSearch HTTP 500, LeanFinder/Loogle/source grep no match).
- `dag/nodes/sec-picard-framework/lem-sc-regular-curve-torsionfree-free.json`: statement, unsplit; no Mathlib match (same three search kinds, with LeanSearch unavailable).
- `dag/nodes/sec-picard-framework/lem-sc-vector-bundle-line-subbundle.json`: statement, unsplit; no Mathlib match (same three search kinds, with LeanSearch unavailable).
- `dag/nodes/sec-picard-framework/lem-sc-determinant-short-exact.json`: statement, unsplit; no Mathlib match (same three search kinds, with LeanSearch unavailable).

## Attachments

- `AlgebraicGeometry.Scheme.Modules.exists_addEquiv_sections_higherDirectImage_H` belongs to existing `lem-pc-cohomology-sections-affine-base` (the declaration has `sorry` at DirectImage.lean:324).
- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_topologicalKrullDim_lt` belongs to existing `lem-sc-noetherian-cohomology-above-dimension` (the declaration has `sorry` at EulerChar.lean:73).

The sorry-free Lean declarations `AlgebraicGeometry.Scheme.eulerChar_unit_eq`, `eulerChar_free_eq`, and `Modules.eulerChar_eq_degree_add` cover the structure sheaf, free sheaves, and the line-bundle identity with a *cohomologically defined* degree. The source file says explicitly that its theorem narrows the coherent-sheaf assertion and has no coherent torsion/determinant degree. No declaration states this item exactly.

## WANTED

- WANTED: `literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-rr/lem-sc-riemann-roch.md`, full node proof, for `lem-sc-riemann-roch`, `lem-sc-vector-bundle-line-subbundle`, and `lem-sc-determinant-short-exact`. This machine has the imported `blueprint_proof_text` in the item JSON and the unit JSON, but not the blueprint tree. The latter two node statements follow that agent-written proof and their source files should be regenerated from `literature/LIST.md` before independent review.
- WANTED: the local Stacks project `.tex` tree for this item and the two Stacks-backed nodes. I read the pinned `divisors.tex` at commit `a04446e57ec1fbc252a871afcec7752fb2807b14` through the web, including the exact labels for Tags 0AXR, 0AXT, and 0CC4; I also read the Stacks pages for 0BS6 and 02O5. The local source can be regenerated as `literature/LIST.md` describes.

## Source and blueprint correction

The imported proof treats Tag 0BS6 as a direct statement about the node's divisor degree on line bundles. Stacks 0BS6 actually states its locally-free formula using its own degree, which is defined by Euler-characteristic difference in the Stacks degree section. The unit's divisor induction is needed to identify that degree with `def-sc-pic0`; Step 3 writes it out. The proof is accordingly marked `by: agent`, and the item statement has not changed. The Lean `eulerChar_eq_degree_add` uses the cohomological degree by definition, so it does not close this gap.

No other work was left unfinished in this one-level split. LeanSearch returned HTTP 500 for all four new-node searches; LeanFinder, Loogle, and the checked Mathlib source supplied the absence verdicts.

The item declares five cross-unit tool uses in `split_report.tool_uses`, following the current `coord/brief-stage1.md` rule: smooth connected curve local geometry, proper coherent higher-image finiteness, Noetherian cohomology vanishing, global functions on a proper connected curve, and coherence of submodules on a locally Noetherian scheme. Each is used as a general fact in the unit's `(RR)` route; none replaces the divisor induction or the torsion/line-filtration argument. The maintainer's reviewer can accept or reject these declarations at merge.

## Review by E1

I read the unit `sk-thm-picard-rr` and the imported full proof text in the item, then checked the cited Stacks pages and the pinned `divisors.tex`. The item assumes an algebraically closed field and a nonempty smooth connected proper curve. `lem-sc-smooth-connected-curve-local-rings` supplies Noetherian integrality, its generic point, and DVRs at closed points. `lem-sc-global-functions` uses exactly the proper, connected, algebraically closed hypotheses to give `H^0(O_C)=k`. The four new statements have their own complete hypotheses: 0AXT requires an integral scheme and a quasi-coherent module; 0CC4 requires integral, regular, dimension at most one, and coherent; the line-subbundle fact requires an integral regular Noetherian curve, a positive-rank bundle, and a nonzero generic vector; the determinant fact requires a short exact sequence of constant-rank finite locally free modules. None silently assumes projectivity or excellence.

Step 1 cites the precise nodes for finite coherent cohomology (`lem-pc-euler-characteristic-well-defined` and its higher-direct-image inputs), vanishing above dimension (`lem-sc-noetherian-cohomology-above-dimension`), and Euler additivity (`lem-pc-euler-additive`). I checked the two Lean-sorry declarations against the statements of their existing nodes and did not create duplicates. Step 2 uses `lem-sc-global-functions`, `def-sc-genus`, and the degree-zero identity from `def-sc-pic0`; the final subtraction is elementary. Step 3 uses `lem-sc-line-bundle-rational-section` for `L=O(D)`, `lem-sc-point-cartier` and the DVR description for the point modification, `lem-pc-chi-zero-dim-support` for the quotient's Euler characteristic, and `def-sc-pic0` for divisor degree. I checked the local inclusion both for positive and negative coefficients: the quotient is a one-dimensional residue-field module in the positive direction and the same equality is rearranged in the negative direction.

Step 4 uses new Tag 0AXT for the torsion subsheaf and torsion-free quotient, the existing coherent sub/quotient node for Noetherian coherence, `lem-sc-dim0-finite` for its finite support, and `lem-pc-chi-zero-dim-support` for `chi(T)=h^0(T)`. Step 5 applies new Tag 0CC4 to the coherent torsion-free quotient, then Euler additivity. Step 6 takes the strict smaller rank from the saturated-line node, takes determinant multiplicativity from the determinant node, and uses the line case and induction; the only algebra left is expanding `(r-1)(1-g)+(1-g)`. Step 7 substitutes the definitions of rank and degree. Each cited node's statement, rather than a construction hidden in its proof, supplies the claim used.

I searched all DAG nodes and the blueprint index for the four new statements by their phrases, concepts, and Stacks tags (0AXT and 0CC4); no existing node states them. The new nodes contain statements only, with no proof sketches or dependencies disguised as conclusions. For B1-B7 I checked that every object, rank and hypothesis is introduced, TeX is singly escaped, the Stacks labels are exactly `lemma-torsion-sections`, `lemma-torsion`, and `lemma-torsion-free-over-regular-dim-1` in pinned `divisors.tex`, and no Mathlib leaf is claimed. For B9-B10 I checked the blueprint ancestor/place and the absence of a sorry-free Lean theorem with the same statement; the item has `same_as: []` after a full blueprint search for Riemann-Roch.

Small cases: for `F=O_C` the torsion subsheaf is zero and the quotient is `O_C`; for a skyscraper `F=k(P)` it is all torsion, the quotient is zero, and `chi=1=deg`; for `F=O_C plus k(P)` the exact sequence adds `1` to both chi and degree. Tag 0CC4 gives rank zero as the zero bundle and rank one as an invertible sheaf. For the line-subbundle node, at rank one its saturated kernel is the whole bundle and quotient zero; in `O_C^2` the vector `(f,0)` over the function field saturates to the first summand even when `f` has a pole or zero. The determinant node gives `det(0)=O_C` and for a split sequence `O_C to O_C^2 to O_C` the standard wedge identifies both sides. These checks also rule out accidentally using an unsaturated cyclic subsheaf at Step 6.

The two new Stacks nodes match 0AXT and 0CC4 hypothesis by hypothesis. The saturated-line and determinant statements are precisely the two independent facts spelled out in the blueprint's rank-induction paragraph; they are not restatements of the Riemann-Roch conclusion. I corrected the Stacks label names after opening the pinned `.tex`. No return entry was supplied for this item.
