# Stage-1 report: lem-sfb-ample-line-polarization-isogeny

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-ample-line-polarization-isogeny.json` — item, split; no new nodes and no Mathlib leaves.
- `citations.json` — 30 step/node quotations.
- `report.md` — this report.

Attachments: none. No project declaration in `lean/WeilConjectures/` has the exact arbitrary-field statement or the blueprint tag. The existing source declarations about multiplication-by-
`n` do not state the ample-line polarization result.

WANTED: none. The Milne AV PDF is present and was read at I Proposition 8.1, Proposition 8.14, and the normalized-difference discussion on pp. 35 and 39–40. The imported dual/Poincare and algebraically closed polarization nodes were also read in the DAG.

What I changed: the item now has an eight-step proof and `proof_deps`. The argument first base-changes to an algebraic closure, identifies the pulled-back normalized Poincare datum with the dual datum used by the existing algebraically closed polarization calculus, and chooses a positive power of the ample line bundle with an immersion into projective space. A nonzero section gives an effective Cartier divisor, so the existing effective-divisor criterion makes the induced map for that power an isogeny. The normalized difference of a tensor power is the tensor power of the normalized difference, hence the original map composed with multiplication by the exponent is an isogeny. This gives surjectivity of the original map and a closed immersion of its scheme-theoretic kernel into the finite kernel of the power map. Finally, surjectivity and finiteness descend along the faithfully flat algebraic-closure extension. The last step unfolds `def-sc-isogeny`.

I did not create a new node: every non-elementary ingredient was already stated by a DAG node. The item’s blueprint provenance was retained (the imported auxiliary has no blueprint id; `blueprint_refs.py ancestor` returns `None`). The latest blueprint unit read was `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`, with its direct-images proof; this auxiliary is used below that route and does not replace a six-functor step. No SGA source is cited.

## Not duplicates

The item is distinct from `lem-sfb-abelian-polarization-calculus`: that node states the construction and the effective-Cartier-divisor criterion over an algebraically closed field, while this item proves that an arbitrary ample line bundle over an arbitrary field itself induces an isogeny. It is distinct from `lem-sfb-abelian-euler-degree-square` and `lem-sfb-abelian-line-bundle-degree-square`, which compute the degree after an isogeny criterion but do not prove ampleness implies the criterion. It is distinct from `lem-sfb-finite-kernel-group-fibres`, which only computes fibres from an already finite kernel and does not prove finiteness or surjectivity of a polarization.

## Review by Q98

I read the current item, the latest blueprint unit and chapter records, the source declarations under `lean/WeilConjectures/AlgebraicGeometry/AbelianVariety/`, and the existing nodes used by all eight steps. I checked in particular that `def-sfb-abelian-dual-poincare-datum` supplies the normalized difference and tensor group law, that `lem-sfb-abelian-polarization-calculus` supplies the effective-Cartier-divisor-to-isogeny implication over an algebraically closed field, and that `def-sc-isogeny` means surjectivity plus a finite scheme-theoretic kernel.

For step 1 I verified the algebraic-closure, geometric-integrality, proper/smooth base-change, and relative-ampleness hypotheses. Step 2 uses only the universal property and tensor law actually stated by the dual/Poincare datum, together with the two pullback/tensor comparison nodes; it identifies the pulled-back datum with the algebraically closed dual rather than silently identifying distinct coefficient categories. Step 3 uses the stated ample-to-immersion result and the relative complete-linear-system result, then checks properness and the projective-space separatedness hypothesis before applying proper-monomorphism-closed. Step 4 checks that a generating section is nonzero at the identity, that integrality makes its zero scheme Cartier, and that the resulting line is exactly `O(F)` before applying the effective-divisor criterion. Step 5 spells out the tensor-power calculation and records the identity-axis normalization, so the classification gives both `[d] ∘ f` and `f ∘ [d]`. Step 6 verifies the direction of the kernel closed immersion and keeps nilpotents, using only the quotient of a finite-dimensional coordinate algebra. Step 7 checks that the algebraic closure is an fpqc cover, that the pulled-back map and kernel are the required fibre products, and that fpqc descent applies to the kernel’s structure morphism. Step 8 is the definition check.

I tested the edge cases in the prose: dimension zero gives a finite group scheme immediately; the section argument uses the identity point, and the kernel argument does not assume reducedness, separability, perfection, or characteristic restrictions. I also ran the required current Mathlib searches (LeanSearch, LeanFinder, Loogle, and Mathlib grep); their hits concern linear/character duals, affine-space points, ring Picard groups, and class groups, with no abelian-variety polarization theorem. No compiler, Lake build, or Lean-writing tool was run.
