## What changed

Replaced the sole `sorry` in `AlgebraicGeometry.Etale.exists_cartesianHigherImage_germ_rep` by a complete Lean proof, preserving its signature and existing public imports. The proof lifts a germ through the derived-Hom comparison, refines its etale representative to an affine object, descends the raw class, and uses homology-shift and fiber naturality to identify its canonical leg image.

Seven new modules isolate the steps actually used. Six have complete proofs: the local homology comparison, cofiltered affine etale model descent, chart-system geometry, canonical restricted-over cohomology presentation, affine complex presentation, and affine raw-class factorization. The seventh states the remaining chart comparison, which contains the only new `sorry`. Both chart definitions are actual pullback functor/cone constructions. All existential data from the remaining theorem are used inside proofs, never to define an object.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Etale.exists_cartesianHigherImage_germ_rep`.

The delivery also supplies complete proofs of:

- `AlgebraicGeometry.Etale.exists_abelianDerivedHomology_sections_comparison`.
- `AlgebraicGeometry.Scheme.exists_affineEtale_model_of_cofiltered`.
- `AlgebraicGeometry.Etale.cartesianChartSystem_properties`.
- `AlgebraicGeometry.Etale.exists_restrictedOverAbelian_cohomology_presentation`.
- `AlgebraicGeometry.Etale.exists_cartesianHigherImage_affine_complex_presentation`.
- `AlgebraicGeometry.Etale.exists_cartesianHigherImage_raw_affine_factorization`.

Added one hole: `AlgebraicGeometry.Etale.exists_cartesianChart_cohomology_comparison`, node `lem-sc-cartesian-higher-image-chart-comparison`. Its proof must construct the chart-to-derived-Hom isomorphism using pullback pasting, the raw restricted-cohomology comparison and derived adjunction; construct stage lifts by inverse image of stage derived classes; and prove their compatibility with the prescribed cartesian exchange using the mate/counit equation and raw-comparison naturality. The statement has no cofilteredness, limit, affine-transition, qcqs or representative-surjectivity assertion. Its complete proof in words and edge cases are in its docstring and node.

This is a decomposition: one original hole closed, one strictly smaller hole added, net zero holes. The original theorem and the two presentation/factorization theorems still depend transitively on the new hole; they are not claimed to be axiom-free proofs of the target.

Validation: all eight sandbox modules compiled in import order without warnings. Individual files stayed within the 60-second limit. The final dry run checks compilation, axioms and delivery metadata again.

## No longer needed

The original proof dependency `lem-sc-cartesian-derived-image-map-exchange` is removed from this node's proof route. Its module remains a public import because it defines the original statement's cartesian objects and leg. Other parents still use its exchange theorem, so this delivery does not claim that its module can be withdrawn globally.

Removed the unused proof import `Sheaf.AlgebraicGeometry.RestrictedOverSingleCoherence` from the new restricted-over presentation: its proof uses the unit and composition declarations directly, together with the generic derived-cohomology pullback laws.

Exploratory free-representable, raw-adjunction and geometric-pasting helpers were discarded before delivery. No additional existing module or node becomes globally unreachable from this change. No original public import is removed. The new affine-model adapter exposes only `Mathlib.AlgebraicGeometry.Sites.AffineEtale`, replacing an unnecessary public import of `FullAffineEtaleSite`.

## Where the brief, the DAG or earlier work was wrong

The original node named only `cartesianDerivedImageMap_exchange` as a dependency for its whole affine descent argument. That equation does not itself supply affine etale model descent or continuity representatives. The final proof supplies the cofiltered affine-model adapter, actual chart geometry, a canonical cohomology diagram, and its application to the existing complex-continuity theorem. The unit's second-proof route through affine etale descent and cohomology continuity is retained.

An early full assembly was close to the compile limit. Profiling located the cost in kernel comparison of the existential presentation data. Explicitly typed local geometric instances and direct composition of the final equations make the file compile within the existing limit. No existing definition or signature was changed.

## New nodes

`lem-sc-abelian-derived-homology-sections` records the locally surjective derived-Hom-to-homology comparison, with its generator formula. Its proof uses the existing local comparison and the homology shift isomorphism.

`lem-sc-cofiltered-affine-etale-model` extends the already proved directed affine etale model theorem to arbitrary small cofiltered categories, by initial reindexing and the singleton-family specialization.

`def-sc-cartesian-higher-image-chart-system` records the actual `cartesianChartDiagram` and `cartesianChartCone` constructions. They use `Over.post`, `Over.pullback` and the underlying cone; no existence theorem supplies their data.

`lem-sc-cartesian-higher-image-chart-system` proves the chart system's limit, affine transitions and qcqs stage/apex structure maps by preservation of connected limits and base change.

`lem-sc-restricted-over-abelian-cohomology-presentation` constructs the canonical cohomology functor and cocone using proved identity, composition and leg equations, then applies the existing complex-data constructor.

`lem-sc-cartesian-higher-image-chart-comparison` is the sole unfinished node. It isolates the map identification and its stage lifts, independently of continuity. The remaining construction and compatibility calculation are described above and in its full docstring.

`lem-sc-cartesian-higher-image-affine-complex-presentation` combines affine model descent, chart geometry, the restricted-over presentation and chart comparison, using the actual cofiltered category `Over i`.

`lem-sc-cartesian-higher-image-raw-affine-descent` applies the existing complex-continuity colimit theorem and concrete filtered-colimit representatives to the preceding presentation, then transports through its apex isomorphism.

No change record is needed: existing definitions, statements and visibility are preserved, and no other existing module is adapted.

## Second reading by E1

1. **Signatures and accidental changes.** I diffed every delivered module against the repository copy. The existing declarations keep their signatures and visibility; the new declarations are represented by the supplied split nodes. I corrected the germ descent node's copied conclusion from the stray `y'` to the theorem's actual conclusion `y`, so the node and Lean agree.

2. **Proof validity.** I compiled all eight sandbox modules with `lcompile.py --all`, then compiled the item module separately. There are no forbidden declarations and the only remaining `sorry` is the named theorem `AlgebraicGeometry.Etale.exists_cartesianChart_cohomology_comparison`, which has a complete docstring and matching node. The main germ theorem and the other six new results are closed.

3. **Split statements.** I checked the seven new declarations against the imported library and their node statements. The six proved results are strict intermediate constructions used by the item. The chart comparison hole is a genuine map-identification subproblem, with no extra hypotheses and no duplicate of the item theorem. The constructions do not define data from arbitrary existential witnesses.

4. **Route and pruning.** The proof follows the unit route through local homology representatives, affine model descent, the chart system, restricted-over cohomology presentation, and filtered colimit representatives. The germ theorem directly uses only the homology comparison and raw affine factorization; the latter records its presentation dependencies. No old proof dependency is removed from the item, and the restricted-over presentation drops only its unused public proof import as documented.

5. **DAG agreement.** I checked each node's `lean`, `proof`, `proof_deps`, and `proof_origin` against the corresponding source. The corrected germ node now has the exact theorem conclusion. The unit's realized route remains intact, and the remaining split node is explicitly recorded in the report.

Changed: added this second-reading record and corrected the germ node's copied conclusion typo; no Lean proof or public interface was changed during review.
