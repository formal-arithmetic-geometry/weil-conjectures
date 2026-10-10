Files written:

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-gm-strict-henselization-stalk-formula.json` (item, split)
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-unrestricted-strict-henselization-stalk.json` (statement-only, Mathlib no match)
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-gm-pullback-strict-henselization.json` (statement-only, Mathlib no match)
- `citations.json`

Attachments:

- None. The existing `prop-weil-pbc-strict-henselization-stalk-formula` is torsion-only and does not state the unrestricted hypothesis needed for `G_m`; no sorry-free source declaration states this item.

WANTED:

- None; Tag 03Q9 and the Tag 09YQ limit argument are available in the cited Stacks source.

## Not duplicates

- lem-weil-pbc-gm-pullback-strict-henselization vs lem-weil-pbc-gm-strict-henselization-stalk-formula: the new node states only the units-sheaf pullback isomorphism, while the existing item states higher direct-image stalk cohomology and uses that isomorphism as one clause.
- lem-weil-pbc-gm-pullback-strict-henselization vs lem-weil-pbc-sets-pushforward-stalk-strict-henselization: the new node concerns the multiplicative sheaf under base change; the existing node concerns a set-valued pushforward stalk formula.
- lem-weil-pbc-gm-pullback-strict-henselization vs prop-weil-pbc-strict-henselization-stalk-formula: the new node identifies pullback of units, whereas the existing proposition compares higher cohomology only for torsion sheaves.
- lem-weil-pbc-gm-pullback-strict-henselization vs lem-weil-pbc-pullback-iso-prime-torsion-devissage: the new node is an units-sheaf base-change statement; the existing node is prime-torsion dévissage.
- lem-weil-pbc-gm-pullback-strict-henselization vs lem-weil-pbc-constructible-module-limit-descent: the new node is about units on a strict henselization; the existing node descends constructible modules.
- lem-weil-pbc-gm-pullback-strict-henselization vs lem-weil-pbc-sets-etale-section-continuity: the new node is an isomorphism of units sheaves; the existing node is continuity of sections of set-valued sheaves.
- lem-weil-pbc-gm-pullback-strict-henselization vs lem-weil-pbc-sets-affine-etale-inverse-image-comparison: the new node concerns units; the existing node compares affine-site inverse images for sets.
- lem-weil-pbc-gm-pullback-strict-henselization vs lem-weil-pbc-etale-cohomology-local-ring-colimit: the new node is a sheaf identification; the existing node is cohomology continuity over local-ring colimits.
- lem-weil-pbc-gm-pullback-strict-henselization vs lem-weil-pbc-limit-pullback-sections-colimit: the new node identifies units after pullback; the existing node identifies module sections in a limit.
- lem-weil-pbc-gm-pullback-strict-henselization vs lem-weil-pbc-etale-mayer-vietoris-pullback: the new node is units base change; the existing node is Mayer-Vietoris pullback.
- lem-weil-pbc-gm-pullback-strict-henselization vs lem-weil-pbc-etale-cohomology-limit-of-schemes: the new node is the units-sheaf clause, not the general cohomology colimit theorem.
- lem-weil-pbc-gm-pullback-strict-henselization vs lem-weil-pbc-complex-spectral-sequence-comparison: the new node is a units sheaf isomorphism; the existing node compares spectral sequences.
- lem-weil-pbc-unrestricted-strict-henselization-stalk vs lem-weil-pbc-gm-strict-henselization-stalk-formula: the new node allows any abelian etale sheaf and states only the first comparison, while the item specializes to G_m and adds the units identification.
- lem-weil-pbc-unrestricted-strict-henselization-stalk vs lem-weil-pbc-sets-pushforward-stalk-strict-henselization: the new node is a higher cohomology formula for abelian sheaves; the existing node is a set-valued pushforward statement.
- lem-weil-pbc-unrestricted-strict-henselization-stalk vs prop-weil-pbc-strict-henselization-stalk-formula: the new node removes the existing proposition's torsion hypothesis but omits its derived-category clause.

What was wrong in the imported material:

- The item was unsplit even though its proof uses two independent non-elementary facts. The nearby proposition with the same title assumes a torsion abelian sheaf, so it cannot be cited for `G_m`, which is not torsion. I retained the item statement and split the proof into the unrestricted Tag 03Q9 comparison and the units-pullback identification.

## Review by J1

I read the item source description and the Stacks Project etale-cohomology theorem Tag 03Q9, including its stalk-colimit proof, and checked the existing DAG proposition. That proposition has a torsion hypothesis, while the item uses the multiplicative sheaf, so it does not provide the first step. I also read the Tag 09YQ continuity statement cited by the source for the units identification. The first item step cites the new unrestricted stalk node, whose statement says exactly the canonical restriction isomorphism for every degree and arbitrary abelian etale sheaf. The second cites the new units-pullback node, whose statement says exactly that the canonical map from the inverse image of `G_m` to the units sheaf on the fibre product is an isomorphism; replacing the inverse-image sheaf gives the final clause. Every hypothesis (qcqs morphism, geometric point, strict henselization, fibre-product projection) is stated in each new node and matches the item. I searched the whole DAG for Tag 03Q9, Tag 09YQ, strict-henselization stalks, and units on limits; the only related stalk proposition was the torsion-only node, so no duplicate was created. I ran LeanFinder, Loogle, grep, and LeanSearch searches for the item and both new statements; LeanSearch was unavailable and is recorded as such, while the other searches found only generic stalk infrastructure and no matching Mathlib theorem. Small checks include `q=0` (the comparison is the ordinary stalk/sections comparison) and `X=empty` (both cohomology sides are zero); the units statement specializes to the identity base-change case, where its map is visibly the identity.

## Second reading by J1

- Item statement: checked against Stacks Tag 03Q9 (Theorem 59.53.1), including its qcqs, geometric-point, strict-henselization, and all-degree hypotheses; verdict: agrees. The `\mathbf G_m` specialization is an abelian étale sheaf, and the final replacement uses the separately checked units isomorphism.
- Item Step 1: checked against the statement of `lem-weil-pbc-unrestricted-strict-henselization-stalk` and Tag 03Q9; verdict: the cited node supplies exactly the arbitrary-abelian-sheaf comparison, with no elementary gap.
- Item Step 2: checked against the statement of `lem-weil-pbc-gm-pullback-strict-henselization` and the Tag 09YQ continuity argument; verdict: the cited node supplies exactly the sheaf isomorphism, and transport of cohomology across a sheaf isomorphism is elementary.
- New node `lem-weil-pbc-unrestricted-strict-henselization-stalk`: checked against Tag 03Q9, hypothesis by hypothesis; verdict: self-contained statement, all notions cite definitions, correct TeX/source label, and no Mathlib declaration. Tested at `q=0`, empty `X`, and identity `f`.
- New node `lem-weil-pbc-gm-pullback-strict-henselization`: checked against the Tag 03Q9 limit setup and Tag 09YQ (Theorem 59.51.3, directed-colimit cohomology); verdict: the qcqs limit and affine transition conditions are supplied by the strict-henselization construction, and the units pullback statement is the required specialization. Tested for identity base change and `X=empty`; no Mathlib declaration.

Changes made in this second reading: added this explicit step/node audit; corrected no statements because the source comparison and edge-case checks found no mathematical discrepancy. The dry-run preflight passes.
