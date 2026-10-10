Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-kummer-base-change-compatibility.json`: corrected statement and two proof steps.
- `dag/nodes/sec-curve-estimates/lem-sc-h1-gm-pic-pullback.json`: statement-only compatibility of etale $H^1(G_m)$ with line-bundle pullback.
- `dag/nodes/sec-curve-estimates/lem-sc-pic-affine-base-change-compatibility.json`: statement-only compatibility of the affine Jacobian quotient with compactification base change.
- `citations.json`: verbatim citations for every dependency used by each step.

Attachments: none.

WANTED: none.

The returned item had an imprecise inverse-image claim and omitted the Picard functoriality and quotient-presentation compatibility needed by its downstream five-lemma use. I added the two missing statement-only nodes, introduced the comparison map $c$ and its restriction to $\\mu_n$, and cited the existing exact-sequence ladder and degree-zero pullback nodes. The Lean source was searched for the item tag and for Kummer/base-change declarations; no project declaration states this item.

## Review by E1

I checked the corrected comparison-map statement and both proof steps against every cited node and the returned review points. In particular, I verified that the comparison map on units, its restriction to roots of unity, the exactness and connecting-map naturality clauses, the degree-zero units clause, and the Picard pullback clause are all stated and cited. I also checked the compactification boundary and Jacobian quotient compatibility hypotheses and the small cases.

## Not duplicates

lem-sc-h1-gm-pic-pullback vs lem-sc-torsor-h1-boundary-representative: the new node concerns scheme pullback and the Picard interpretation of etale $H^1(G_m)$, while the existing node only represents a single Zariski torsor by a boundary extension.
lem-sc-h1-gm-pic-pullback vs lem-sc-zariski-contracted-power-torsor: the new node is functoriality under a morphism of schemes and includes degree zero, while the existing node computes a contracted power torsor on one Zariski site.
lem-sc-h1-gm-pic-pullback vs lem-sc-torsor-h1-ext-pushforward: the new node identifies etale $H^1(G_m)$ with line-bundle pullback, while the existing node describes pushforward of a torsor extension under a closed immersion.
lem-sc-h1-gm-pic-pullback vs lem-sc-zariski-ext-torsor: the new node is Picard pullback for arbitrary scheme morphisms, while the existing node constructs a Zariski extension attached to a torsor.
lem-sc-h1-gm-pic-pullback vs lem-sc-torsor-h1-functoriality: the new node specializes functoriality to $G_m$, etale sites, and invertible modules, while the existing node gives Zariski pushout functoriality for arbitrary sheaf morphisms.
lem-sc-h1-gm-pic-pullback vs lem-sc-torsor-h1-zariski-boundary-class: the new node compares Picard classes across scheme pullback, while the existing node identifies one Zariski torsor class with a connecting homomorphism.
lem-sc-h1-gm-pic-pullback vs lem-sc-torsor-h1-ext-pushout: the new node asserts the Picard interpretation of the induced etale map, while the existing node only constructs the pushout extension.
lem-sc-h1-gm-pic-pullback vs lem-sc-zariski-contracted-power-extension: the new node is naturality of $H^1(G_m)$ and line bundles under scheme morphisms, while the existing node concerns a contracted-power extension on one Zariski site.

I read the item source in `literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-ext-invariance/_section.md`, the unit record, and every cited node. Step 1 now uses clauses 1 and 3 of `lem-weil-pbc-pullback-cohomology-long-exact-ladder` for exactness and naturality, `lem-weil-pbc-cohomology-pullback-degree-zero` for global units, and `lem-sc-h1-gm-pic-pullback` for the line-bundle interpretation; the Kummer, Brauer, base-change-curve, field-extension, and Kummer-LES statements supply the remaining hypotheses. I verified that the new comparison map $c$ is the units pullback map and that its restriction preserves $n$th roots of unity.

Step 2 uses the new compactification/Jacobian quotient compatibility node, `thm-av-final` for divisibility and n-torsion, and `lem-sc-divisible-quotient-torsion` for the quotient exact sequences. I checked that the new node explicitly says $\\overline C_{k'}$ compactifies $C_{k'}$, identifies the boundary points and pulled-back divisor line bundles, and identifies the quotient map with Picard pullback. The small cases $n=1$ and $C=\\mathbf A^1$ remain valid: torsion is zero for $n=1$, and the one-point boundary gives $\\Lambda=0$ for $\\mathbf A^1$.

The statement was strengthened precisely by the returned requirements; no extra hypothesis was added. Both new nodes are unsplit and have their required Mathlib searches recorded. The item metadata retains its blueprint ancestor and records the two realized proof places.

What could not be finished: nothing.

## Second reading by E1

- Item statement: checked against the Kummer naturality sentence and affine Picard-torsion paragraph of the blueprint ancestor `thm-sc-constant-invariance`; verdict: hypotheses on algebraically closed fields, smooth separated connected curve, and `n` prime to the characteristic are present, and the affine conclusion is `Pic(C)[n]` invariance.
- Step 1: checked against `def-sc-kummer-sequence`, `lem-sc-kummer-exact`, `lem-sc-kummer-les`, `lem-sc-brauer-zero`, and `def-sc-field-extension`; verdict: inverse-image functoriality gives the sheaf-square and the induced cohomology maps, while the smooth connected base-change cases supply the Brauer-vanishing hypothesis.
- Step 2: checked against `lem-sc-pic-affine`, `thm-sc-jacobian-representability`, `thm-av-final`, and `lem-sc-divisible-quotient-torsion`; verdict: the expanded argument explicitly identifies all boundary points after base change, the induced subgroup and torsion maps, and the natural diagram of quotient-torsion exact sequences.
- New nodes: none; duplicate and Mathlib searches were checked for the quotient-torsion and Kummer facts, and the existing nodes were retained.
- Small cases: `n=1` gives the zero torsion groups; for `C=\\mathbf A^1`, the compactification has one boundary point and the subgroup `\\Lambda` is zero; the empty-curve case is excluded by the connected-curve definition.

Changed Step 2 to replace the unsupported phrase about coordinate values with the canonical Jacobian point map and an explicit finite-boundary-point argument, and to spell out naturality of the exact-sequence diagram. The second reading additionally repaired the Brauer hypothesis, tightened the helper hypotheses, and added the missing Jacobian base-change dependency.

Second-reading repairs: Step 1 was checked against the all-curves Brauer-vanishing statement; this removes the unsupported connectedness inference for $C_{k'}$. Step 2 was checked against the existing genus/Jacobian base-change compatibility node and now cites it through the affine quotient helper. The `lem-sc-h1-gm-pic-pullback` statement was restricted to curves and its invertible-module notion was cited explicitly. The affine helper's source records the Stacks Kummer/Picard and Yoneda tags. Its boundary-point and divisor-line-bundle claims were tested on $C=\\mathbf A^1$ and on a proper compactification with one boundary point; $n=1$ gives zero torsion. All three node statements remain statement-only and are not duplicates of existing nodes.
