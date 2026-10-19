# Stage-1 report: lem-trf-graded-immersion-ample-criterion

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-graded-immersion-ample-criterion.json` — statement, split proof, status `split`; Mathlib searches found no matching theorem.
- `dag/nodes/sec-trace-formula/lem-trf-qc-immersion-proj-open-factor.json` — statement-only prerequisite; Mathlib search found only the more general quasi-compact immersion factorization declarations.
- `dag/nodes/sec-trace-formula/lem-trf-ample-restrict-closed-immersion.json` — statement-only prerequisite; no Mathlib ampleness API matched.
- `citations.json` — verbatim statement excerpts for every cited node at every proof step.

## Attachments

None. I searched the project source for the item id, its blueprint tag, and the relevant Proj/ampleness names; no sorry-free declaration states this item.

## WANTED

None.

## What was wrong or incomplete before the split

The imported item had the correct source statement but no proof and no statement-level dependency for the geometric step hidden in Stacks 01VJ: a quasi-compact immersion into Proj must be placed inside a quasi-compact open of Proj with a closed-subscheme factorization. It also lacked the general closed-subscheme restriction of ampleness (Stacks 01PU). I added those as statement-only nodes rather than moving the item’s conclusion into a new node. The source hypothesis is genuinely quasi-compact, as in Tag 01VJ; the imported bracket cites the project’s finite-type-morphism convention, but the prose and proof use only quasi-compactness, so I retained the seeded statement text and recorded no silent strengthening.

## Review by Q19

I read the item, the dedicated `sk-lem-trf-graded-immersion-ample-criterion` unit, the `sec-trace-formula` chapter, the current blueprint ancestry, and the Stacks source at Morphisms Tag 01VJ and Constructions Tag 01O9. I also read the source passages for Properties Tags 01PU, 01PT, and 01Q2. The item’s hypotheses allow arbitrary nonnegatively graded algebras, including non-degree-one generation and arbitrary degree-zero part, and the proof does not add either condition. The prior `sk-i-curve-zero` binding was wrong; the item and both auxiliary nodes now use the dedicated unit, and the unit realization records the item for the statement and all five steps, with the factorization and restriction nodes additionally recorded for steps 2 and 3.

Step 1 fixes an affine base open and uses the existing `lem-trf-space-line-module-proj-map` statement exactly for affine relative-Proj restriction and the canonical morphism. The condition `U(ψ)=Z` is used to obtain the positive-degree generation/nonvanishing cover on the inverse image. Step 2 uses the new factorization node, whose statement explicitly supplies a quasi-compact open ambient `Y`, a closed immersion of the source into `Y`, and the factorization of the given immersion. Step 3 uses the existing quasi-compact-open Proj twist-ampleness node and the new closed-immersion restriction node; their statements say precisely that a positive twist on `Y` is ample and that its pullback to `T` remains ample. Step 4 uses the existing canonical-map twist-comparison node, which gives `r^*O(dk) ≅ L^{⊗dk}` for every `k≥1`, together with the existing positive-tensor-power ampleness node. The tensor-power identifications are the ones defined by the cited sheaf tensor-product node. Step 5 checks the definition of absolute ampleness directly: an affine nonvanishing cover for `L^{⊗ed}` is already a positive tensor-power cover for `L`, with unchanged nonvanishing loci, and this is done for every affine base open.

I checked edge cases including empty source, empty Proj, degree-zero-only algebras (where `U(ψ)=Z` forces the source empty), and non-degree-one graded algebras. I verified every proof dependency against the exact statement of its node and recorded each quotation in `citations.json`. The current `split_report.tool_uses` records the four generic construction/ampleness helpers listed in the maintenance repair below; all remain black-box uses of their stated hypotheses. All new nodes have complete statements only, no proof sketches, no cycles, and no SGA citations.

## Not duplicates

lem-trf-ample-restrict-closed-immersion vs lem-weil-pbc-projective-ample-invertible: the new node restricts an arbitrary ample invertible module along every closed immersion of schemes; the existing node treats only the pullback of the standard twisting sheaf along a closed immersion into a projective space and supplies its affine-section cover.
lem-trf-qc-immersion-proj-open-factor vs lem-trf-graded-immersion-ample-criterion: the new node is the auxiliary factorization of a quasi-compact immersion into Proj through a quasi-compact open and closed immersion; the existing item is the overall ampleness criterion whose hypotheses and conclusion concern a graded sheaf algebra and an invertible module.
lem-trf-qc-immersion-proj-open-factor vs lem-pc-chow-relative-ample: the new node factors an arbitrary quasi-compact immersion into Proj; the existing node concerns a proper morphism and an immersion into finite projective space, proving projectivity and ampleness of a particular pulled-back O(1).
lem-trf-qc-immersion-proj-open-factor vs lem-trf-scheme-ample-canonical-proj-criterion: the new node is the geometric factorization of one quasi-compact immersion through an open and closed immersion; the existing node is an equivalence between relative ampleness and an open-immersion canonical Proj criterion, with no such factorization statement as its conclusion.
lem-trf-qc-immersion-proj-open-factor vs lem-trf-scheme-relative-ample-affine-cover: the new node factors a single quasi-compact immersion into Proj; the existing node transfers ampleness from an affine open covering of the base to all affine base opens and does not assert an immersion factorization.

## C7 metadata repair by maintenance (2026-10-18)

The authoritative live DAG repair is commit `809d1c24cc86aa2596062480334e96dc9f116196` in `/home/ubuntu/weil-conjectures-sheaf`; the side-project repair is `545fff978728feead3c5d9d9eaa61e165a183913` in `/home/ubuntu/weil-newtargets`. Both were committed by Bin Wu under their respective `coord/.merge.lock`. The item now belongs to `sk-lem-trf-graded-immersion-ample-criterion`, a dedicated source unit for Stacks 01VJ (6) implies (1). Its statement and five proof steps reproduce the retained item/source argument. The historical `blueprint.from` ancestry and the correct local-term realization of `sk-i-curve-zero` were preserved. The already-reviewed caller `lem-trf-relative-ample-very-ample` records this general ampleness criterion as a generic tool, so the binding correction creates no new caller route violation.

The retained item and both new prerequisite nodes now inherit the corrected unit. The unit's `realized.statement` names the item; its five `realized.steps` name the item, with the quasi-compact-open factorization prerequisite also carrying step 2 and the closed-immersion restriction prerequisite also carrying step 3. The authoritative unsplit base has an empty realization; this ordinary stage-1 delivery supplies the split and its complete realization together, avoiding references to prerequisites absent from the base.

The existing `lem-trf-space-line-module-proj-map`, `lem-trf-proj-qc-open-twist-ample`, `lem-trf-proj-canonical-map-twist-comparison`, and `lem-sc-ample-positive-tensor-power` are generic black boxes for the canonical map, ample twists on quasi-compact Proj opens, twist pullback comparison, and preservation of ampleness by positive tensor powers. They are explicitly declared in `split_report.tool_uses`; none asserts a Frobenius local-term result or replaces a step of that unit. Their existing bindings are preserved.

Maintenance changed no node statement, proof, citation quotation, or search claim, and wrote no Lean. The earlier repeated BLOCKED audits are retained in the adjacent `.bak` copy of this report. The C7 binding/realization obstruction is repaired; the resubmission still receives the normal independent stage-1 review.
