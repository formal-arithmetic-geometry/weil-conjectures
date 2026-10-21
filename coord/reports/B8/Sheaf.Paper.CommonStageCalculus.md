## What changed

Completed the eight remaining proof bodies of `Sheaf.Paper.CommonStageCalculus`.
The integral closure argument uses the exact completion unit and the uniform
reduction cohomology criterion. Integral shifts inherit linearity through the full
inclusion. The existing `exactUnitLocus` and `uniformProfileLocus` theorems are reused from
`Sheaf.Paper.PbcUniformCompleteTriangulated`. Generic private tensor-Hom calculations construct the uniquely normalized
rational shift and identity comparison with rationalization. The existing `pbcScalarLocalization_isLocalization` and `pbcKanCommShift_ext`
are reused from `Sheaf.Paper.PbcScalarExtension`. Localization descent
constructs the uniquely compatible scalar shift. The scalar associator commutes with
shifts because its ambient mate does, and this property reflects through the integral
inclusion and the object-surjective rationalization. Finite products transfer from the
integral triangulated category to raw rational stages, and from one common stage to the
pair category; preadditivity makes them biproducts.

Existing statements, definitions, instance attributes and public imports are unchanged.
All new helpers are private and proved. The returned four duplicate theorem copies
and the now-unused private `cscRationalComparison` construction have been removed.
Private `import all` commands access the existing declarations without changing their
visibility or their owning modules. No other Lean module is edited. The node proof, proof dependencies and proof
origin follow the actual argument. The unit route is unchanged. Proof-context commands
are recorded in `coord/changes/B8-common-stage-calculus-proof-context.md`; no downstream
module needs adaptation.

Validation: a standalone `import all` probe compiled against the published library,
confirming access to all four existing private declarations. The repaired module
compiled cleanly through `lcompile.py` in 17.0 seconds, with no warnings and zero
`sorry` tokens. The delivery tool runs the final compile, axiom probe and preflight.

## Proved and sorry left

Closed all eight original holes, with their unchanged statements:

- `AlgebraicGeometry.Scheme.pbcIntegralStableShift`
- `AlgebraicGeometry.Scheme.pbcIntegralShiftLinear`
- `AlgebraicGeometry.Scheme.pbcRationalShift_exists`
- `AlgebraicGeometry.Scheme.pbcRationalizationShift_exists`
- `AlgebraicGeometry.Scheme.pbcScalarShift_exists`
- `AlgebraicGeometry.Scheme.pbcScalarAssociatorCommShift`
- `AlgebraicGeometry.Scheme.pbcStageFiniteBiproducts`
- `CategoryTheory.StageSystem.pbcPairFiniteBiproducts`

All realize `prop-weil-pbc-common-stage-calculus`. There are zero holes left in the
item, zero holes added elsewhere, and zero split-off statements. Existing imported
proof dependencies retain their own declarations and proofs.

## No longer needed

No module or node is withdrawn. The earlier claim that
`prop-weil-pbc-scalar-extension` was no longer needed has been corrected: this item
reuses two of its generic proved helpers. The proof also reuses the two generic
closure theorems in `lem-weil-pbc-uniform-complete-triangulated`; both nodes are now
recorded in the proof dependencies. Their main concrete theorems retain their
original geometric hypotheses.

Removed the duplicate private proofs `cscExactUnitLocus`, `cscUniformProfileLocus`,
`cscCommShift_ext`, and `cscIsLocalization`, along with `cscRationalComparison`,
which was used only by the last duplicate. Removed the private import
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom` because
this item no longer constructs that comparison.

Also removed these redundant or unused private imports:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.AdicCoefficientDatum`
- `Sheaf.Paper.IntrinsicCompletionCompleted`
- `Mathlib.CategoryTheory.Triangulated.Functor`
- `Sheaf.Paper.BoundedConstructibleComplete`
- `Sheaf.Paper.PbcRationalCategory`
- `Sheaf.CategoryTheory.ScalarLocalization`
- `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`
- `Mathlib.LinearAlgebra.TensorProduct.Basic`
- `Mathlib.RingTheory.Localization.Away.Basic`

Required statement declarations remain available through the unchanged public imports.
The finite-diagram, quotient-shift and equality-detection arguments already present in
the item remain intact. No additional node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The previous first DAG step appealed to exactness of the separate scalar-extension
package for the stage additive and shift structures. It did not itself construct the
strictly normalized raw tensor-Hom shift structures required by the Lean statements.
The updated proof constructs those structures explicitly and proves the associator's
compatibility from the normalized ambient and integral comparisons.

The existing integral triangulation theorem includes finite-dimensionality and
prime-invertibility binders, whereas the original shift-stability and stage-biproduct
statements here have neither binder. Its closure proof does not use those hypotheses.
The private generalization combines the existing generic closure theorems with the
named completion, uniform-reduction, and constructible-homology dependencies,
preserving all public signatures. No false statement was encountered.

Repair of return at `3bc2f1e57`: each of the four helper statements was indeed already
proved word for word in the library. Their private visibility is handled with
`import all`, already used elsewhere in the project. All four copies were removed,
and their call sites now use those original declarations. This also corrects the
previous report's mistaken pruning claim for `PbcScalarExtension`. No visibility,
public import, or statement changes in any companion module are necessary.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
