## What changed

Replaced the sole `sorry` in `Sheaf.Paper.ModuleCupNaiveMap`, declaration
`AlgebraicGeometry.Scheme.Modules.moduleCup_naiveMap_comm`, with the node's planned
summandwise proof. Statements, definitions, visibility and imports are unchanged.
Added three proved private helpers: `sectionTensorMap_natural_left`,
`sectionTensorMap_natural_right`, and `naiveMapComponent_summand`. The first two use
`TensorProduct.ext'` and the existing section formulas for whiskering; the third
is the coproduct descent equation.

For adjacent degrees the proof uses `HomologicalComplex.mapBifunctor.hom_ext`,
expands `CochainComplex.ιTensorObj_d` on both sides, applies the descent equation,
and uses additivity of global sections to preserve the sum and integer-unit sign.
The two resulting terms are the reassociated naturality helpers. For nonadjacent
degrees both differentials vanish by the complex shape. All integer degrees are
covered, with no boundedness assumptions. The proof follows the existing DAG
route and does not bypass any realized unit step; no node update is required.

The complete module compiled without errors or warnings through `lcompile.py`
against the published project build (29.8 seconds). A larger heartbeat limit is
scoped to the chain identity because rewriting unfolds the induced monoidal
structures; the compilation remains within the single-file time limit.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Modules.moduleCup_naiveMap_comm`
(node `lem-sc-module-cup-naive-map-chain`).

Added zero holes. No `sorry` remains in the delivered module. All private helpers
are proved. Existing proof dependencies, including the tensor-closed structure,
are unchanged; this delivery does not claim to prove their remaining holes.

## No longer needed

None. All four existing public imports supply the constructions and instances
used by the unchanged definitions or by the proof. The proof still uses the
three dependencies of the existing node: `def-pc-tensor-complex-sheaves`,
`def-pur-sheaf-tensor-product`, and `def-sc-ringed-space-module-cohomology`.
No planned node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The shortest-route searches found generic
tensor-complex machinery rather than a chain identity for this explicit section
map. The source's `whiskerRight_app_tmulSection` and
`whiskerLeft_app_tmulSection`, together with `ιTensorObj_d`, implement the planned
argument without new intermediate statements. The naive map in Stacks Tag 0FKU
(the paragraph before Tag 0FP3) was checked against the unchanged construction.

## Second reading by F1

1. Compared the delivered module with the repository version. The only existing declaration changed is the proof of `AlgebraicGeometry.Scheme.Modules.moduleCup_naiveMap_comm`; its statement, all definitions, visibility, and imports are unchanged byte for byte. Verdict: pass.

2. Compiled the delivered module with `lcompile.py`. It compiles without errors or warnings and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. An axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound` for every declaration. Verdict: pass.

3. Checked the three private helper lemmas against existing declarations and searched the repository for duplicates. They are proved intermediate reductions, not split-off statements; no new public statement or node was added. Verdict: pass.

4. Read the proof from the target downward. It uses the existing coproduct descent, tensor differential formula, and tensor-section naturality, with a separate zero-shape case. The realized unit route is preserved and no import or proof dependency is unused. Verdict: pass.

5. Compared the node's statement, proof route, proof dependencies, and proof origin with the Lean proof. They agree; the target statement is unchanged. Verdict: pass.

Changed only this report by recording the independent compilation, axiom probe, signature comparison, and route review. No Lean or DAG repair was needed.
