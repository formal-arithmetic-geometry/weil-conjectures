## What changed

Proved `AlgebraicGeometry.Scheme.Modules.externalGlobalSectionsTensor_bijective_of_isAffine`
without changing its signature. Added proved private helpers for the external tensor
identity over an algebra pushout and the projection-pullback section comparison.
The coordinate-ring calculation uses `isPushout_appTop_of_isPullback`, followed by
`CommRingCat.isPushout_iff_isPushout`; the module calculation uses Mathlib's two
`cancelBaseChange` equivalences. The affine pullback and sheaf tensor-section
comparisons are the existing declarations planned by the node. Tensor induction
identifies the composite bijection with the specified canonical external map.

Added proof-only imports of `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`,
`Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`, and
`Mathlib.RingTheory.IsTensorProduct`. The private helpers use declaration-scoped
transparency options to compare the explicit section-module scalar actions.
Updated the item's proof steps, dependencies, and origin to record this implementation.
No public definition, statement, visibility, or public import changes.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Scheme.Modules.externalGlobalSectionsTensor_bijective_of_isAffine`
(node `lem-sc-external-global-sections-tensor-affine`).
No `sorry` remains in the delivered module, and none is added elsewhere.
The private `externalTensorAlgebraEquiv`, `externalTensorAlgebraEquiv_tmul`, and
`exists_affine_projection_sections_tensor` are fully proved. This is a proof from
existing library dependencies, with no decomposition into new holes.

The algebra argument checks the canonical formula even for empty affine schemes
(the zero coordinate ring), zero coefficients, and arbitrary section modules;
no finite-dimensionality, finite generation, or nonempty scheme assumption is used.
The original unit route stays: the same affine computation supports the existing
finite-cover argument above this item.

## No longer needed

None of the original imports, nodes, or modules is pruned. The affine spectrum
fibre-product computation is retained, expressed by its global-section pushout
form. A redundant trial import of `Mathlib.LinearAlgebra.TensorProduct.Tower` was
removed; its declarations are available through the other imports. All three
original substantive proof dependencies are used. The newly explicit
`lem-weil-pbc-module-pullback-quasi-coherent` is a proved upstream tool.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or interface change was needed. The item initially omitted
proof imports for the dependencies named by its DAG; these are now imported.
The planned elementary module calculation is implemented with Mathlib pushout
base-change cancellation instead of constructing inverse balanced maps anew.
Lean distinguishes the top-open `appLE` action from `appTop`, and module-presheaf
restriction from underlying additive-presheaf restriction; the proof explicitly
uses their compatibility instead of relying on definitional equality.
LeanSearch returned an unavailable-service response; Loogle, Lean Finder, and
local searches supplied the cancellation lemmas. Source checked against Stacks
Tag 0BED's affine-case paragraph.

The final module compiled cleanly before the dry run, with no warnings or direct
sorry. The first dry run conservatively flagged newly added section commands;
these were replaced by explicit private-helper binders and declaration-scoped
options so that the existing importer interface remains identical.

## Second reading by M2

1. **Interface and accidental changes.** Compared the delivered module with the repository
version. The public theorem signature and existing declarations are unchanged; only proof-only
imports, private helpers, and the theorem proof differ. The DAG statement is byte-for-byte the
same as the Lean declaration.

2. **Proof checks.** The module has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by`; no definition contains a hole. The proof uses the stated affine pullback,
pushout, and quasi-coherent tensor-section dependencies and compiles through `lcompile.py`.

3. **Statements and dependencies.** The private helper statements are true algebraic
identities/equivalences, strictly subordinate to the target, and have complete proof
explanations. No new public statement or split-off hole was added, and the node's proof steps
and dependencies match the implementation.

4. **Shortest route and pruning.** The route uses Mathlib's pushout cancellation equivalences
and the existing affine section comparisons; no longer proof dependency import was found. The
unit's affine computation route is retained.

5. **Axioms and delivery readiness.** The target proof is constructive from the imported
results and standard equivalences; the delivery checks are being run with `deliver3.py`.

**Changes made by second reading:** added this review record only. No Lean proof or DAG change was
needed.
