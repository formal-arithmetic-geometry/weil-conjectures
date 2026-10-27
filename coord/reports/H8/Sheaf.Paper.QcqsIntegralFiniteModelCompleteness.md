## What changed

Prove `qcqs_integral_finite_model_completeness` from the existing finite-stratum
completion detector, finite scalar-model completeness and finite-model sheaf quotient
calculation. The completion triangle comparison makes the actual completion-unit
isomorphism predicate triangulated. The already-proved generic
`DerivedCategory.prop_of_bounded` then assembles bounded complexes from their
cohomology sheaves.

For finite reductions, apply the normalized finite-discrete encoding. Identify its
ordinary finite local models with the source library's fixed-module constructibility,
using the existing private `ordinary_constructible_iff` theorem from
`Sheaf.Paper.LocalizingClosureCtfEqualsBc`, accessed through a proof-only
`import all`. Its existing `ordinary_localModel_iff` helper handles universe lifting
and smallness of the pro-etale precoverage. Both duplicate private theorems from
the returned delivery are removed. The source
fixed-module bounded-constructible etale-origin subcategory is triangulated; apply
bounded truncation a second time and retain its etale antecedent and comparison
isomorphism as the required witness. The target signature and all public definitions
are unchanged. The DAG proof now records this route.

Validation: the repaired module compiled through `lcompile.py` in 19.1 seconds
with no errors or warnings. Delivery also runs its complete preflight. The definition body, theorem signature and
public import list were compared verbatim against the shared source. There are no
`sorry` tokens in the delivered Lean file.

## Proved and sorry left

Original holes: one, `AlgebraicGeometry.ProEtale.qcqs_integral_finite_model_completeness`.
Closed: that theorem. Added: zero. Remaining in the delivered Lean module: zero.
No new statement modules or unproved private helpers are introduced. The proof uses
existing stated dependencies; their proofs remain the responsibility of their items.

## No longer needed

No module is withdrawn. Removed the duplicate private declarations
`ordinary_localModel_iff` and `ordinary_constructible_iff`; their proofs are reused
from `Sheaf.Paper.LocalizingClosureCtfEqualsBc`. This adds a proof-only import and
the corresponding dependency `det-def-localizing-closure-ctf-equals-bc`.

The direct proof dependencies
`lem-sfb-strict-completion-restriction-comparison`,
`lem-weil-pbc-truncation-triangle`, `lem-sf-derived-homology-long-exact`,
`lem-weil-proetale-dbc-triangulated`, `sk-thm-pe-constructible-comparison`,
`lem-pur-derived-change-of-rings`, and `lem-sfb-degreewise-bounded-devissage`
are replaced by the completion detector's interface, generic bounded truncation,
the triangle-morphism isomorphism criterion, and the already-proved fixed-module
finite-coefficient origin API. This does not claim their removal from other nodes
or from the library. In particular, completion comparison and its own dependencies
remain needed through the finite scalar-model module. The derived quotient is
triangulated directly by the existing internal-module adjunction and Mathlib's
triangulated-adjunction theorem; the ordinary-module change-of-rings construction
is not used. The generic `DerivedCategory.prop_of_bounded` in the source
TStructure module is already proved and suffices in place of the newer degreewise
devissage theorem in that module.

Removed direct proof imports (their declarations may remain transitively used by
the named interfaces above):

- `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison`
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`
- `Sheaf.CategoryTheory.ModuleObjects.LiftExact`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`
- `Sheaf.Paper.PrincipalReductionConeCalculus`
- `Sheaf.Algebra.Homology.RoosConeCalculus`
- `Sheaf.Paper.CompletionTriangleComparison`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.DerivedNakayamaResolution`
- `Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic`
- `Sheaf.Paper.FiniteConstantModelResolution`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative`
- `Sheaf.SixFunctors.ConstructibleOpenClosedRefinement`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection`
- `WeilConjectures.CategoryTheory.TruncationTriangle`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`
- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`

Public imports are preserved. The private import of
`Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit` is retained because it
realizes part of the unit route, as required by preflight. The change record is
`coord/changes/H8-qcqs-integral-completeness-proof-context.md`.

## Where the brief, the DAG or earlier work was wrong

The original eleven-step plan can be assembled with the existing generic bounded
truncation theorem; it does not require reimplementing a truncation induction or
proving a new triangulated constructibility API. The finite-Tor hypothesis is not
needed separately once bounded constructible cohomology and the existing sheaf-level
quotient theorem are available. This strengthens the proof route without changing
any statement. No statement is disputed. Preflight conservatively classifies the added scoped
opens and local irreducibility attribute as a command-context change. The required
change record documents the unchanged public API and the absence of downstream
Lean consumers; no forced adaptation is needed.

The return at head `d10261891` correctly identified two duplicate private
comparison lemmas. This repair removes both declarations and uses the existing
comparison theorem at both call sites; it changes no declaration in its owner
module. The theorem and definition signatures, the unit route, and all six public
imports are preserved. No new nodes or holes are introduced.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
