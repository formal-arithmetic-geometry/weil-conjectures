## What changed

The source module `WeilConjectures.WeilSheaf.VerdierDual` retains every existing
signature, attribute, public import, and definition body. Two theorem bodies change.

`AlgebraicGeometry.WeilComplex.exists_commShift_isTriangulated_verdierDual` composes
the existing exact chosen K-injective replacement with the existing exact signed
bifunctor Hom on the homotopy category, then restricts to the full triangulated
subcategory. A proved private helper carries out the generic categorical calculation.
It uses exactly the inverse of KInjectives.Qh and the representative already present
in bifunctorRHom. The new proof imports are private:
`Sheaf.CategoryTheory.KInjectiveReplacementTriangulated` and
`Sheaf.CategoryTheory.DerivedCategory.BifunctorHomHomotopyExact`.

`AlgebraicGeometry.WeilComplex.objectProperty_derivedHom_dualizingComplex` now applies
the geometric Hom constructibility theorem to K and the actual dualizingComplex,
transports its bounded-constructible conclusion across a geometric Hom comparison,
and applies the existing native membership criterion backwards. The private proof
import `Sheaf.Paper.ConstantModelTorAmplitude` supplies the proved invariance of
the bounded-constructible predicate under isomorphism. The comparison is
split into `Sheaf.Paper.NativeGeometricHomComparison`, privately imported by the
source module. Its public import of WeilGeometricHomConstructibility is necessary
for the specified nativeGeometricForget in its statement.

The two corresponding DAG proofs and their proof dependency lists follow these
arguments. No statement or definition repair, consumer adaptation, or change record
is required. The unit's own statement and realized route are preserved.

## Proved and sorry left

Original holes: 9. Original theorem bodies closed: 2. New holes: 1. Remaining
holes in the item: 7; remaining holes in this packet: 8. This is one proof and one
decomposition, with a net reduction of one hole, not two independent proofs.

Proved without adding a new intermediate hole:

- `AlgebraicGeometry.WeilComplex.exists_commShift_isTriangulated_verdierDual`
  (`lem-sf-weil-verdier-dual-triangulated`).

Decomposed with a complete Lean assembly proof:

- `AlgebraicGeometry.WeilComplex.objectProperty_derivedHom_dualizingComplex`
  (`lem-sf-weil-verdier-dual-preserves-weil-complexes`). Its remaining comparison
  asserts no constructibility, membership, duality or biduality conclusion.

Untouched holes in the item:

- `AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek`
  (`thm-sf-weil-compact-direct-image-right-adjoint`).
- `AlgebraicGeometry.WeilComplex.nonempty_iso_verdierDual_rightOp_comp_verdierDual`
  (`lem-sf-weil-verdier-biduality`).
- `AlgebraicGeometry.WeilComplex.nonempty_upperShriek_obj_iso`
  (`lem-sf-weil-upper-shriek-verdier-conjugate`).
- `AlgebraicGeometry.WeilComplex.nonempty_verdierDual_derivedLowerShriek_iso`
  (`lem-sf-weil-verdier-exchange`).
- `AlgebraicGeometry.WeilComplex.nonempty_dualizingComplex_iso`
  (`lem-pur-weil-smooth-dualizing-complex`).
- `AlgebraicGeometry.WeilComplex.nonempty_tensorLisse_dual_iso_derivedHom`
  (`lem-sf-weil-lisse-internal-hom-tensor-dual`).
- `AlgebraicGeometry.WeilSheaf.nonempty_iso_dual_dual`
  (`lem-sf-weil-lisse-biduality`).

Added hole:

- `AlgebraicGeometry.ProEtaleWeilSheaf.nativeGeometricForget_derivedHomComparison`
  (`lem-sf-native-geometric-hom-comparison`). The source, full proof in words and
  zero/empty/unbounded edge cases are in its docstring and node.

Validation: the new comparison module compiled successfully in the sandbox set.
The final source module then compiled without errors or warnings in 6.6 seconds
against that compiled comparison. Profiling settings were removed. The delivery
tool recompiles the packet and records its preflight result.

## No longer needed

No original imports or source declarations are removed; no module is withdrawn.
No whole module is claimed pruned.

The old exactness plan's steps 5 and 6, converting between the standard and signed
Hom differentials and conjugating the resulting triangulated structure twice, are
unnecessary for the actual upstream definition: bifunctorRHom already uses precisely
the signed bifunctorHomHomotopyFunctor to which the existing exactness theorem
applies. The direct proof therefore does not need `def-weil-triangulated-category`
as a separate proof dependency for this conversion; it remains ordinary ambient
infrastructure. No sign-comparison theorem or new module is introduced.

The preservation assembly no longer directly proves the coefficient realization
or native closed-forgetful comparison. The former direct dependencies
`lem-sf-locally-finite-coefficient-ring-realization`,
`lem-sf-weil-verdier-module-constructibility-comparison`, and
`lem-sf-weil-native-closed-forgetful` are needed by the new comparison node instead.
They are not globally pruned. Existing maintainer tool-use approvals are retained.

## Where the brief, the DAG or earlier work was wrong

The exactness plan described an additional standard-differential model comparison,
but the live derivedHom is already the signed model of the existing homotopy
exactness theorem. Its direct categorical composition suffices.

The preservation plan's step 3 suppresses coefficient transport: native_closed_forgetful
compares with the ordinary native coefficient presentation, whereas the geometric
constructibility theorem uses CondensedRing.derivedHom after nativeGeometricForget.
These are different Lean functors. The new statement isolates precisely the missing
comparison, rather than adding constructibility as an assumption or restating the
original preservation theorem. It applies to arbitrary two ambient derived objects,
including zero objects, empty geometric fibers, shifts and unbounded complexes.

Searches found no existing declaration of this coefficient-transported Hom comparison.
NativeDerivedHomComparison concerns pullback/direct-image adjunction transposition;
NativeGeometricTensorComparison is the tensor analogue, not the needed Hom statement.
The generic scalar-forgetting, tensor universal-property, and derived closed-structure
nodes used as tools in the new node supply coefficient algebra infrastructure; they
do not replace the unit's geometric duality argument.

## New nodes

`lem-sf-native-geometric-hom-comparison`, in
`dag/nodes/sec-six-functors/lem-sf-native-geometric-hom-comparison.json`, is realized
by the single public theorem in `Sheaf.Paper.NativeGeometricHomComparison`.
It is the coefficient-transport portion of the original preservation argument.
Its proof first forgets Frobenius using the native closed comparison, then transports
relative tensor and evaluation across the specified coefficient module equivalence,
and obtains the relative derived Hom comparison from the tensor-Hom adjunction.
It asserts neither the original bounded-constructible conclusion nor any special
property of a dualizing object. No change records are added.

The parent was seeded by the maintainer without a created.item ancestor;
`blueprint_refs.py ancestor` returns None. The new node therefore has a null
from.node, retains the parent in via, and names the conceptual blueprint passage
in from.place and source.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
