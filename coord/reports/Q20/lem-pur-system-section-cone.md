## Worker report

Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-system-section-cone.json` — statement split, no new nodes, no Mathlib leaves.
- `citations.json` — verbatim statement quotes for every proof dependency.

Attachments: none. No declaration tagged `(blueprint: lem-pur-system-section-cone)` or matching the complete statement was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; the node's Lean audit is `none`.

WANTED: none. The direct cone formulas are supported by Stacks, Derived Categories, Tag 014E (`derived.tex`, definition-cone). The model-category portion uses the explicitly stated hypotheses of the existing DAG nodes `lem-coef-quillen-section-rectification` and `lem-coef-projective-cochain-monoidal-model`; no external source is required for the agent-written lifting calculation.

The imported node had no proof. I kept its statement and dependencies unchanged. The source blueprint paragraph defines the adic-stage functors using compatible finite-level systems but does not state the cone lemma or its cofibration argument, so I supplied that calculation as an agent-written proof. I did not create a node for a clause of the item: the map of sections, cokernel, and contraction are direct degreewise computations. The projective cofibration argument is one proof step using the already existing generic section-model and projective-cochain nodes. The blueprint search found no duplicate cone node, and the DAG search found no node with this complete statement.

## Review by Q20

I read the complete item statement and its source paragraph in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md`. I also read the full statements of every dependency named by the item, especially `lem-coef-quillen-section-rectification` and `lem-coef-projective-cochain-monoidal-model`, and the cone definition in `literature/stacks-project/derived.tex` at Tag 014E.

Step 1 checks that scalar-transition maps commute with the cone differential, composition identities, and the inclusion (Q\to CQ), so the cone and shift really are strict sections. It uses only the definitions, and I checked the signs directly. Step 2 takes exactly the Hom-complex compatibility axiom and the cofibrancy map (0\to Q) from `lem-coef-quillen-section-rectification`; it identifies the induced map as postcomposition with a trivial fibration. Step 3 uses the generator (S^0\hookrightarrow D^{-1}) from `lem-coef-projective-cochain-monoidal-model`. I checked the degree (-1) family (t(q)=b(q,0)), the equation (d_Yt+td_Q=pa), and that the lift gives a section-compatible (h) with (ph=t) and (d_Xh+hd_Q=a). Step 4 expands the filler (l(x,y)=h(x)+a(y)), verifies the cone differential sign, and checks both (li=a) and (pl=b); the cited section-model statement supplies the weak-factorization characterization. Step 5 verifies the projection to the shifted complex and proves its universal cokernel property directly, including transition compatibility. Step 6 uses the explicit contraction (H(x,y)=(y,0)); I checked (dH+Hd=1), its compatibility with every scalar transition, and the resulting componentwise acyclicity and weak equivalence.

I checked edge cases (Q=0), a one-level system, identity transitions, and zero differentials; all formulas reduce correctly. Every non-elementary citation in the six steps has a verbatim quote in `citations.json`. No proof step exceeds 2000 characters, and the item has no new nodes or duplicate claims.

## Not duplicates

`lem-pur-system-section-cone` vs `lem-pur-system-section-suspension`: the suspension node computes a pushout of two cones and its comparison with (Q[1]); this item proves the single cone inclusion is a cofibration, its cokernel, and its contraction.

`lem-pur-system-section-cone` vs `lem-cbc-projective-cochain-dg-compatibility`: the latter states enrichment/tensor/cotensor for ordinary projective (R)-complexes; this item concerns the cone inclusion and projective model structure on semilinear strict sections.
