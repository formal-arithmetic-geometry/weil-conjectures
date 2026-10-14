## What changed

Proved `AlgebraicGeometry.Scheme.Modules.boundaryCoefficientDegreeIso_tensor_product`
in `Sheaf.AlgebraicGeometry.BoundaryCoefficientTensorProduct`, preserving its signature
and the definition `boundaryIdealTensorProduct`. Added three proof-only imports, each
with a proved public comparison theorem in its own new module:

- `InvertibleTensorPowerBlockInterchange`: compute canonical concatenation on local
  free generators, express arbitrary sections locally as scalar multiples, and glue.
- `BoundaryPullbackTensorBraiding`: prove the symmetry square by the pullback adjunction
  and the existing proved `pullback_δ_app_unit_tmulSection`, then transport it through
  `boundaryPullbackComparison`.
- `BoundaryCoefficientDegreeSplit`: prove pullback power addition and block grouping
  recursively, normalize degree zero with the proved monoidal unit comparison, and
  derive the coefficient-first splitting identity by naturality and cancellation.

The main proof combines these morphism equalities and evaluates on `tmulSection q s`.
Updated the item's DAG proof and added nodes for the three proved comparison theorems.
No target, existing statement, public definition, or other holder's module changed.
The unit `sk-thm-curveestimate` retains its realized statement and route.

Sources read: Stacks Tags 01CA, 01CD and 09MS via their tag pages; existing Lean
`SquareZeroTensorBoundaryComparisons`, `PullbackTensorUnitSection`,
`PullbackMonoidalUnitComparison`, `TensorSection`, `FreeGenerator`, and
`SquareZeroTensorSectionProductComparison`. The two private power-addition helpers
adapt the existing proved private helpers in the last module; its stronger section
product theorem is neither imported nor used.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.Modules.boundaryCoefficientDegreeIso_tensor_product`
(node `lem-sc-boundary-coefficient-tensor-product`).

Added 0 holes. The three new public theorems are proved:

- `AlgebraicGeometry.Scheme.Modules.tensorPowAddIso_inv_block_interchange`
  (`lem-sc-invertible-tensor-power-block-interchange`).
- `AlgebraicGeometry.Scheme.Modules.boundaryPullbackTensorIso_braiding`
  (`lem-sc-boundary-pullback-tensor-braiding`).
- `AlgebraicGeometry.Scheme.Modules.boundaryCoefficientDegreeIso_split`
  (`lem-sc-boundary-coefficient-degree-split`).

Every private helper is proved. No `sorry` remains in any delivered Lean file.
Existing dependencies are reused with their existing proofs and axioms; this does not
claim that all remaining holes elsewhere in the targets' import closure are closed.
The four-file sandbox compiles cleanly through lcompile.py, each under the 60-second
limit (approximately 33, 4, 4 and 10 seconds). Zero exponents are included by the
recursive unit cases, with no nonempty-open or pure-tensor-generation assumption.

## No longer needed

None of the original imports or planned dependency nodes can be removed: the sole
original public import supplies the comparison definitions used in the statement.
No modules are claimed pruned. The final proof does not import the holed
`BoundaryPullbackTensorUnit`: its proved Mathlib-pullback normalization is sufficient.
No closed-immersion, square-zero, cohomology, kernel-lift, or graded-presentation
lemma is added as a proof dependency.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature correction was needed. The original DAG named only
`SquareZeroTensorBoundaryComparisons`, which defines the maps but does not state the
needed coherence identities. Those identities are now proved in the three new nodes.
Only block interchange needs invertibility; pullback symmetry and coefficient splitting
hold for arbitrary modules. The proof uses local generation only for the invertible
source of block interchange, rather than assuming arbitrary tensor-sheaf sections are
pure tensors. LeanSearch returned Internal Server Error; its searches are recorded
as unavailable. LeanFinder, Loogle, local rg, and the existing source proofs supplied
the usable API.

## New nodes

`lem-sc-invertible-tensor-power-block-interchange`, module
`Sheaf.AlgebraicGeometry.InvertibleTensorPowerBlockInterchange`, is the local-generator
proof that reversing two blocks does not change concatenation for an invertible L.
It is proved and independent of pullback and the coefficient comparisons.

`lem-sc-boundary-pullback-tensor-braiding`, module
`Sheaf.AlgebraicGeometry.BoundaryPullbackTensorBraiding`, is the symmetry square for
arbitrary modules and any scheme morphism. It is proved from the existing proved
single-pullback section normalization and the adjunction.

`lem-sc-boundary-coefficient-degree-split`, module
`Sheaf.AlgebraicGeometry.BoundaryCoefficientDegreeSplit`, splits off the first
coefficient block, without interchanging the L factors. It is proved without
invertibility, by tensorator coherence and recursive power comparisons.

There are no change records or forced adaptations.

## Second reading by A4

1. Compared the delivered item module with the repository version. The existing target declaration and `boundaryIdealTensorProduct` signature are byte-for-byte unchanged; only the proof and proof-only imports changed. Verdict: unchanged interface.
2. Compiled all four delivered modules with `lcompile.py --all`; they compile without errors or warnings, contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`, and all helpers are theorem proofs. Verdict: proof is valid under the local build.
3. Reviewed the three added theorem statements and their DAG nodes. Each is strictly an intermediate coherence identity used by the target, has source and proof documentation, and is stronger only where required (invertibility appears only in block interchange). No duplicate declaration was found in the library. Verdict: statements are true and appropriately scoped.
4. Checked the target proof route against the unit record. It retains the coefficient comparison route through block interchange, pullback braiding, and coefficient splitting, then evaluates on sections; zero exponents are covered by the same unit identities. Verdict: unit route preserved.
5. Checked DAG `proof`, `proof_deps`, and `proof_origin` against the imports and theorem applications in the Lean proof. The three new nodes and the existing tensor-symmetry dependency are recorded; no stale dependency was removed. Verdict: DAG agrees with Lean.

Changed in this second reading: added this review record only; no Lean statements or proofs required repair.
