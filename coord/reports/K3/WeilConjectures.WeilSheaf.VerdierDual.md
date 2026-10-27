## What changed

Replaced the native Verdier-biduality hole by the explicit evaluation-realization,
conservativity and natural-isomorphism assembly. The original signatures, attributes,
public imports and all non-theorem bodies in the adopted source module are preserved.
A fully proved private helper keeps the finite-field datum abstract while constructing
the comparison, avoiding competing scheme structure-map instances when specializing
to the source field. Within the coefficient-system proof it explicitly selects
the Spec algebra structure already stored in StructuralSystem; the native point
retains its identity structure. Added the proof import `Sheaf.WeilSheaf.StructuralBidualInvertible` and its one named
coefficient-level obligation. Updated the biduality node to follow this Lean argument.

The native datum uses the actual selected exceptional right adjoint and its actual
adjunction. The existing nativeModel comparison identifies its closed Hom restriction
with the source Verdier dual. The existing evaluation-realization theorem supplies the
natural native transpose and its precise realization equation. Inverting the coefficient
transpose, cancelling the two comparison isomorphisms and reflecting invertibility
produce the native natural isomorphism. The proof explicitly transports both dual
functors along nativeModel, including the opposite comparison.

Validation: the auxiliary coefficient module compiled through lcompile.py. The
complete source module compiled in 35.2 seconds; its reported style warning was an
empty line inside the new proof, which was removed before delivery preflight.

## Proved and sorry left

Closed upper hole: `AlgebraicGeometry.WeilComplex.nonempty_iso_verdierDual_rightOp_comp_verdierDual`
(node `lem-sf-weil-verdier-biduality`), by decomposition into an existing evaluation
realization and one new coefficient-only obligation. This is a decomposition, not a net
hole closure or a claim that the full Verdier theorem is now proved without sorry.

Added hole: `WeilConjectures.NativeBidualRealization.isIso_commonBidual`
(node `lem-sf-structural-evaluation-bidual-invertible`). It concerns the specified
ordinary common-stage evaluation transpose, not native Weil arrows or naturality.
It isolates the coefficient-invertibility part of the original node's step 4.

Untouched original hole: `AlgebraicGeometry.WeilComplex.nonempty_dualizingComplex_iso`
(node `lem-pur-weil-smooth-dualizing-complex`).

Actual counts: 2 original holes; 1 upper hole replaced by a complete assembly; 1 hole
added in a new module; 1 original hole remains. Net textual hole change across
delivered files is zero; the ledger separately counts pre-existing holes newly reached
through the required proof-dependency imports.

## No longer needed

No existing Lean import or module is removed. No source declaration is withdrawn.
For the biduality node, `lem-sf-weil-dual-realization-comparison`
(`Sheaf.WeilSheaf.DualRealizationComparison`) is not separately used: the existing
preservation theorem already supplies closure, while the evaluation-realization
interface defines its comparisons from the native section-closed data. Its additional
boundedness and presentation conclusions are not needed in this assembly.

The direct `thm-coef-qbar-verdier` edge and its old direct tool_uses entry are removed
from the parent. Coefficient Verdier duality remains needed below the existing
realization theorem and the new coefficient-invertibility obligation. This removes no
coefficient mathematics from the project's route and claims no globally pruned module.

## Where the brief, the DAG or earlier work was wrong

The original step 4 invokes coefficient biduality for the literal structural-system
omega and the literal evaluation transpose, whereas its recorded coefficient theorem
packages duality with another specified exceptional datum. The intervening normalized
right-adjoint and evaluation transport is not an exact existing Lean conclusion. It is
now a named coefficient-level obligation with a complete proof in words. No native
biduality or equivalence with fixed pairs in an ordinary derived category is assumed.

The smooth-dualizing node's older proof is formulated using fixed pairs in the ordinary
derived category, while the adopted source uses the derived category of Weil sheaves.
This delivery does not change that statement or conceal the remaining native transport
work. The current rework table also lists the module's historical quarantine; the item
is present in the live tree, and the delivery preserves every source declaration and
all inherited dependencies.

Searches were performed with msearch.py (LeanFinder, Loogle, grep and LeanSearch) and
with rg in the project and Mathlib. Mathlib supplies categorical assembly and linear
biduality but no literal structural common-stage evaluation-invertibility statement.
The existing commonBidual construction and its realization theorem were reused.
The import-direction check confirmed no cycle back to the source module. No revised
proof dependency reaches the parent biduality node; the dependency lists agree with
the uses recorded in the proof steps.

A broad DAG audit also encountered the pre-existing metadata cycle
`lem-pc-ring-hom-extension-differential` (proof dependency) to
`lem-pc-ring-hom-extension-differential-adjacent`, whose statement dependencies
point back. Both are reachable from the unmodified baseline parent. No unrelated
node is changed here, and none of the revised proof dependencies reaches this
delivery's parent biduality node.

## New nodes

`lem-sf-structural-evaluation-bidual-invertible`, in
`lean/Sheaf/WeilSheaf/StructuralBidualInvertible.lean`, isolates invertibility of the
ordinary coefficient evaluation transpose for the specified structural exceptional
system. It is strictly below the native natural-isomorphism claim. The source proof is
common-stage duality, normalized right-adjoint comparison, and transport of evaluation
and signed symmetry. Zero objects, empty schemes, arbitrary shifts and dependence on
the specified system are included; no global site-perfectness hypothesis is added.
No existing definition or public interface changes, so no change record or forced
consumer adaptation is required.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
