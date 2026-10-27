1. Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-classical-finite-scalar-restriction-hull.json`: statement-only node; Mathlib searches found no match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-indetale-supported-hull-continuity.json`: split item; Mathlib searches found no match.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.

2. Attachments

None. I searched the project Lean source for the item id, its key notions, and the blueprint tag; no sorry-free declaration states the item.

3. WANTED

- WANTED: a single published theorem for the new node `lem-sfb-classical-finite-scalar-restriction-hull`, combining Stacks Tag 03SA filtered constructible approximation with finite open/closed devissage, bounded truncations, and exact scalar restriction from `O/pi^n` to `O`. The node is therefore statement-only and its proof is assembled in the item from the cited structural statements.
- WANTED: a published theorem identifying ordinary derived direct image with coefficient localization for all bounded-below internal condensed-module complexes. The existing DAG node `lem-sfb-localized-direct-image-comparison` supplies exactly the needed statement and is cited.

4. Statement, blueprint, and dependency audit

The item statement is unchanged. Its stated affine locally finite ind-etale factorization and etale supported-coinduction assumption are stronger than the proof needs: the coefficientwise argument proves the conclusion for every qcqs `b`, so I retained both hypotheses exactly as imported. No common finite etale stage, inverse-source descent, or completed/solidified category was introduced. I did not use any SGA 4 source. The blueprint ancestor is `det-sf-comp-coherence-cocycle`; the item and new node retain that `blueprint.from` chain and the current blueprint place.

I searched the entire DAG and blueprint before creating the one new node. Existing `lem-sfb-etale-supported-model-coinduction` contains a related finite-hull argument, but it proves membership for direct images of a finite discrete model and does not state the new node's all bounded-below classical complexes or its exact `O/pi^n`-to-`O` restriction. Existing 03SA nodes state only filtered-colimit approximation of individual sheaves. Existing quotient, tower, and rational-hull nodes state the other ingredients but not this combined structural assertion.

## Not duplicates

`lem-sfb-classical-finite-scalar-restriction-hull` vs `lem-sfb-etale-supported-model-coinduction`: the existing node treats a finite supported model and its etale direct image; the new node treats every bounded-below classical finite-coefficient complex and additionally exact scalar restriction to integral coefficients.

`lem-sfb-classical-finite-scalar-restriction-hull` vs `lem-weil-pbc-module-sheaf-colimit-constructible`: the existing node gives a filtered colimit of constructible degree-zero etale sheaves; the new node concludes membership in the supported derived hull for arbitrary bounded-below complexes and quotient scalar restriction.

`lem-sfb-classical-finite-scalar-restriction-hull` vs `lem-weil-pbc-module-sheaf-colimit-constructible-cocone`: the existing node records a colimit cocone and compactness data; it does not state the supported generators, truncation argument, or restriction-of-scalars conclusion of the new node.

lem-sfb-classical-finite-scalar-restriction-hull vs lem-sc-field-finite-stalk-subobject-element: the existing node covers one stalk element by a finite-stalk subobject over a field; the new node is a derived hull assertion on arbitrary qcqs schemes, including integral scalar restriction.

lem-sfb-classical-finite-scalar-restriction-hull vs lem-sc-field-torsion-finite-stalk-subobjects-cover: the existing node asserts a supremum of finite-stalk subobjects over a field, without a colimit cocone or derived hull conclusion.

lem-sfb-classical-finite-scalar-restriction-hull vs sk-thm-curve-package: the existing theorem gives cohomological bounds, finiteness and base change for curves; the new lemma is generation on arbitrary qcqs schemes with no dimension bound.

lem-sfb-classical-finite-scalar-restriction-hull vs def-weil-pbc-torsion-etale-sheaf: the existing node defines locally torsion via the colimit of annihilator kernels; it gives no constructible or supported derived hull generation.

lem-sfb-classical-finite-scalar-restriction-hull vs lem-pbc-q1-prime-constructible-pullback: the existing node extends a cohomological pullback bijectivity premise from constructibles to prime torsion; the new node is membership of arbitrary bounded-below classical complexes in a hull.

lem-sfb-classical-finite-scalar-restriction-hull vs lem-pbc-u2-constructible-subobject-presentation: the existing node requires Noetherian X and constructs a filtered subobject diagram for a sheaf; the new node has arbitrary qcqs X and a derived scalar-restriction hull conclusion.

lem-sfb-classical-finite-scalar-restriction-hull vs lem-pe-comparison-reflects-local-torsion: the existing node only reflects local torsion through site comparison; the new node constructs hull membership for bounded-below complexes.

lem-sfb-classical-finite-scalar-restriction-hull vs lem-weil-pbc-constructible-generation: the existing node gives a sheaf epimorphism from a coproduct of constructibles; the new node gives supported derived hull membership and integral scalar restriction.

lem-sfb-classical-finite-scalar-restriction-hull vs lem-weil-pbc-constructible-restriction-class-core: the existing node lifts an individual nonnegative cohomology class through a supplied filtered colimit; the new lemma gives a whole derived object in a supported hull.

lem-sfb-classical-finite-scalar-restriction-hull vs lem-weil-pbc-constructible-restriction-class: the existing node factors a cohomology class through a constructible sheaf; it does not give derived hull membership or integral scalar restriction.

lem-sfb-classical-finite-scalar-restriction-hull vs lem-weil-pbc-module-sheaf-colimit-constructible-data: the existing node supplies diagram and factorization/refinement data for degree-zero etale sheaves, not a derived hull conclusion or integral scalar restriction.

## Review by NH

I read the imported item and the current blueprint proof text, the chapter and unit records, and every statement cited by the eight item steps. Step 1 checks finite support-chain completion by the pro-etale open/closed exact sequence, internal/section-module transport, and the two retrocompact constructibility-image statements; I checked the restriction identities and the qcqs hypotheses on each edge. Step 2 uses the finite discrete encoding, fixed-module etale origin, bounded-below pro-etale/etale comparison, coefficient direct-image conjugation, and the new hull node; the comparison's qcqs hypothesis is exactly the item's hypothesis on `b`. Steps 3–5 use, respectively, finite scalar-model completeness and supported-extension completeness, the finite-model quotient theorem (including its uniform `[-1,0]` degree statement), the two fixed-module origin theorems, integral ambient tower comparison, and the strict-tower Roos triangle. I verified that the integral tower node itself asserts completeness, compatible quotient direct-image isomorphisms, and etale origins, so no unstated cohomological-dimension assumption is used. Steps 6–7 use the qcqs integral-leaf lattice tree, its actual canonical coefficient inclusion, the rational hull, and localized direct-image comparison; I checked that the latter explicitly assumes only bounded-below input and qcqs `b`. Step 8 invokes only the triangulated right-derived-functor statement and closure of the hull.

The new node was checked on the zero scheme, zero complex, finite free and torsion scalar modules, identity coefficient pair, and arbitrary bounded-below (including unbounded above) complexes. Its statement has no hidden Noetherian, constructibility, or Tor-amplitude hypothesis. I removed a nonexistent dependency name before writing the final JSON. Every `uses` id exists in the live DAG, and each citation quote is the verbatim full statement of that node. All non-elementary steps are under 2000 characters; the two short elementary steps spell out their restriction and closure arguments. The Mathlib search log records every leanfinder, Loogle, grep, and leansearch query run for the item and new node; none states this geometric hull theorem.

6. Unfinished work

No Lean file was written and no compiler, Lake, local DAG checker, or local preflight was run, as required for stage 1. The new structural node remains unsplit by design; the maintainer's later stage can prove it from its cited approximation and devissage ingredients.
