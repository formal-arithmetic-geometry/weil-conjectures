## What changed

Proved `AlgebraicGeometry.Scheme.etale_local_ring_triples` without changing its statement.
Added three proved private helpers in its module:
`affine_refinement`, `residue_image_separable`, and `compatible_colimits`.
The proof constructs affine refinements, including refinements over the chosen chart;
uses Mathlib's fully faithful inclusion lemmas for cofilteredness and initiality;
and proves residue-image containment using the separability instance for étale
scheme residue maps and `IsSeparable.map`.

The equivalence construction (original steps 5–7) is isolated in the new module
`Sheaf.AlgebraicGeometry.EtaleChartResidueTriplesEquivalence`. Its hypothesis is
residue-image containment, which the original module proves. Its conclusion has
only the equivalence, natural ring identification, and their two compatibility
formulas. It does not assert cofilteredness, initiality, affine refinements,
residue-image containment, colimit existence, or either colimit comparison.
The original theorem therefore combines a strict part of its argument with real
geometric and categorical proofs, rather than applying a renamed version of itself.

Colimit existence uses the initially-small category of elements of the Mathlib
étale point. The final affine inclusion gives the colimit of the affine diagram;
chart initiality and equivalence transfer give the other two. The helper constructs
the two isomorphisms and proves both coprojection equations explicitly.

Added proof-only imports of `Mathlib.CategoryTheory.Filtered.Final` and the new
module. Updated the original DAG node's proof and proof dependencies to this route.
All files are in the prescribed sandbox; no delivery is pushed by this worker.

## Proved and sorry left

The original module's sole sorry is closed:
`AlgebraicGeometry.Scheme.etale_local_ring_triples`
(node `lem-weil-pbc-etale-local-ring-triples`). The three private helpers are proved.

One sorry is split off:
`AlgebraicGeometry.Scheme.etale_chart_residue_triples_equivalence`
(node `lem-weil-pbc-etale-chart-residue-triples-equivalence`), in its own new module.
Its proof is exactly `:= by sorry`. Its docstring and DAG node explain the
object assignment, full faithfulness, essential surjectivity, and specified effect
on points and rings. The original theorem still depends on this sorry transitively.

## No longer needed

No existing imports removed and no original dependency nodes pruned: the remaining
equivalence still uses the affine spectrum and étale composition route of the plan.
`Sheaf.AlgebraicGeometry.AffinePointedNeighbourhoodCofinal` was considered but is
not imported: its relevant initiality argument is proved directly from affine
shrinking and the Mathlib full-inclusion lemmas.
No separate colimit-existence node or residue-containment node is needed.

## Where the brief, the DAG or earlier work was wrong

No false statement or mathematical error found. The planned affine-refinement and
residue-separability leaves are sufficient; the latter is implemented with the
scheme-level residue-field separability instance, avoiding an unnecessary detour
through residue fields of ring ideals. Colimit existence for these large indexing
categories uses the étale point's initially-small property, rather than just the
small filtered-colimit instance for commutative rings.

Edge cases checked for the new equivalence: if the chosen chart has no geometric
point then the input `xU` cannot exist; its assumed presence excludes the empty
spectrum case. The chart map is unique since an open immersion is monic. No
separatedness assumption is used. Residue field maps and the inclusion K → Ω are
injective, so prime kernels and commutation of point maps are recovered exactly.
The theorem does not assume a small skeleton or existence of any colimit.
The original unit's realized statement and steps are unchanged.

## New nodes

`lem-weil-pbc-etale-chart-residue-triples-equivalence` states the equivalence part
of the original argument under the separately proved image-containment condition.
Its module is `lean/Sheaf/AlgebraicGeometry/EtaleChartResidueTriplesEquivalence.lean`;
its source is the first paragraph of the proof of Stacks Tag 04HX and Remark 04HT.
The node and docstring contain the full mathematical construction and proof.
No definition or existing statement changed, and no change record is required.

## Second reading by P1

1. **Visibility and statements.** I diffed `EtaleLocalRingTriples.lean` against the repository version. The theorem signature and all existing declaration signatures are byte-for-byte unchanged. The added module contains only the new split theorem, whose statement is a strict equivalence component rather than a restatement of the original theorem.

2. **Proof and axioms.** Both delivered modules compile locally with `lcompile.py --all`; there are no `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations, and the only remaining `sorry` is the named split theorem. A scratch axiom check gives only `propext`, `Classical.choice`, and `Quot.sound` for the three helpers; the original theorem additionally has `sorryAx` solely through the intentionally open equivalence theorem.

3. **Split statement.** I checked the split theorem against its docstring and node. Its hypothesis is exactly the residue-image containment needed by the equivalence construction, and its conclusion contains only the equivalence, natural ring isomorphism, and the two compatibility formulas. Searches recorded in `searches.jsonl` found no existing declaration of this result; Mathlib's `SpecToEquivOfField` is a lower-level result and is not a duplicate.

4. **Pruning and route.** The proof follows the unit route: affine refinement, cofilteredness and initiality, residue separability, the chart/triples equivalence, and colimit transport. The updated proof dependencies match the uses in the proof. The direct dependency `def-weil-etale-morphism` is removed because it is used only through the split equivalence node; all other old dependencies remain.

5. **DAG and unit agreement.** The original node's `proof` and `proof_deps` match the Lean proof, and the new node has the required source, blueprint, proof steps, searches, Lean record, and `status: split`. The unit's realized statement and steps are unchanged.

I changed only this report section; no Lean statement or proof was changed during second reading.
