## What changed

`affineEtale_finite_diagram_descent` now has a complete Lean proof from two strictly
smaller intermediate statements, each in its own new module. Common object descent
returns actual cartesian squares, independent of the supplied functors. The main proof
constructs the comparisons with the `v`-images using pullback uniqueness, lifts those
isomorphisms to the full affine étale categories, conjugates the arrows, applies eventual
arrow descent between fixed models, and composes the resulting comparisons.

All three files compile cleanly through `lcompile.py --all`. No existing signature,
definition, universe, or public import was changed. The unit route is unchanged: this
item is below the unit's realized nodes. Sources 0EYL, 01ZM, 01Z6 and 07RP were read
online because the local literature checkout is absent on this machine.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Scheme.affineEtale_finite_diagram_descent`
(node `lem-weil-pbc-affine-etale-finite-diagram-descent`) by decomposition, not by a
sorry-free proof of the geometric descent theory.

Added exactly two holes, with proofs exactly `:= by sorry`:
- `AlgebraicGeometry.Scheme.affineEtale_common_models`, node
  `lem-pbc-affine-etale-common-models`, module `AffineEtaleFiniteDiagramObjects`.
- `AlgebraicGeometry.Scheme.affineEtale_model_arrows`, node
  `lem-pbc-affine-etale-model-arrows`, module `AffineEtaleFiniteDiagramArrows`.

The main module has zero sorries; the delivery adds two and closes one (net -1).
The new object statement concerns objects only and gives no arrow descent. The arrow
statement fixes all models at one stage, constructs only their canonical later base
changes, and gives no descent of arbitrary limit objects. Neither restates the target.
Their docstrings and nodes give complete natural-language arguments and sources.
Empty object families are permitted; for zero sources the target still occurs as the
zero entry of `Fin (n+1)`. No covering, surjectivity, or faithful-base-change hypothesis
is asserted or used. Isomorphisms chosen in the proof are local existential witnesses;
no definition chooses arbitrary data from an unproved existence theorem.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`,
`Sheaf.AlgebraicGeometry.LimitAffineTransition`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` from the main module.
They belong to the geometric object descent component and remain its planned imports.
The arrow component needs the existing affine étale base-change construction for its
signature and the finite-presentation descent module for its plan. Removed étaleness
and limit-existence imports from the arrow component, whose fixed models are already
étale and whose limit is supplied. No original dependency node is globally pruned:
the object descent component retains the original geometric route. Global pruned
modules: none.

## Where the brief, the DAG or earlier work was wrong

The plan's `lem-weil-pbc-limit-affine-stage` and
`lem-weil-pbc-qcqs-morphism-permanence` have null Lean records, despite the brief's
expectation that every proof dependency has one. Mathlib supplies affineness descent
as `Scheme.exists_isAffine_of_isLimit`; finite-presentation permanence is handled by
instances. The closest existing finite-data theorem in `Sheaf.Paper.EtaleFiniteDataDescent`
does not retain affine models, so it cannot directly replace this statement.
LeanSearch returned an Internal Server Error; this is recorded as unavailable and
not as evidence of absence. LeanFinder and the Mathlib grep found no exact replacement.

## New nodes

`lem-pbc-affine-etale-common-models` records simultaneous object descent with actual
cartesian squares, in `Sheaf.AlgebraicGeometry.AffineEtaleFiniteDiagramObjects`.
Its source is 0EYL's qcqs proof and 01ZM/01YZ/01Z6/07RP. It retains the original
geometric proof dependencies.

`lem-pbc-affine-etale-model-arrows` records eventual arrow lifting between already
fixed models, in `Sheaf.AlgebraicGeometry.AffineEtaleFiniteDiagramArrows`.
Its source is 01ZM(2) and 0EYL; the final comparison uses canonical affine base change
and the supplied q-pullback squares. No change record is needed: all existing
statements and definitions are unchanged.

## Second reading by B2

1. **Statements and accidental changes.** Compared the delivered target module with the repository version. The existing target declaration is byte-for-byte unchanged; the proof only replaces its `sorry`. The two added declarations are new, named split statements and their DAG node statements match their Lean signatures. Verdict: pass.

2. **Proof and axioms.** Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds with no errors. The target module has no `sorry`, and the only remaining `sorry`s are the two named split theorems, each exactly `:= by sorry`. No forbidden declaration or hollow definition was found. Verdict: pass subject to the two declared split holes.

3. **Truth and strength of split statements.** The common-model theorem only asserts simultaneous affine étale object models and cartesian squares, including the empty-family case. The model-arrows theorem fixes the initial stage and models and asserts eventual lifted arrows with the supplied pullback comparisons; it does not assert arbitrary object descent or covering. Both are strictly smaller than the target and have source-backed docstrings and DAG nodes. Verdict: pass.

4. **Pruning and route.** The target proof uses the two split modules and the full affine étale site. The removed direct proof imports are not needed by the target proof; geometric dependencies remain in the object-model route. No existing target or definition was changed, and the unit route and `realized` records are unchanged. Verdict: pass; no additional pruning found.

5. **DAG and delivery metadata.** Checked both new node records, the target node proof and `proof_deps`, and the report's list of closed and added holes. The declarations, modules, dependencies, source descriptions, and split status agree. Verdict: pass.

Changed during second reading: added this section only; no Lean code, node, import, or statement required repair.
