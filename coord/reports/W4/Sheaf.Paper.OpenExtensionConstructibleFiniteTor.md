## What changed

Filled `AlgebraicGeometry.ProEtale.CondensedRing.openExtension_constructible_finiteTor`
without changing its signature. The proof extracts the finite constant-model stratification,
applies the existing proved module-level open-extension theorem, and transports its models
through the exact-functor homology isomorphism. The unbounded open projection formula,
its degree-zero pullback comparison, and exactness preserve the specified Tor interval.
The forward local-model implication and the coefficient-isomorphism transport lemmas give
the additional general ring-object bounded-constructibility conclusion.

Updated the existing node proof and dependencies to match this route.
Two proved private helpers express Tor amplitude through the named derived tensor and
convert a stratification while preserving an arbitrary stratum property. The latter avoids
expensive kernel conversion of module-valued fields. No public statements, definitions,
modules or nodes are introduced. The local proof transparency commands are documented in
`coord/changes/W4-open-extension-local-proof-transparency.md`; downstream.py reports
zero current downstream modules and no external textual declaration users. The compactification-composition unit
and its input-extension step are preserved.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.openExtension_constructible_finiteTor`
(node `lem-sfb-open-extension-zero-constructible-finite-tor`).
No holes added or split off; no sorry remains in the delivered Lean module.
The full file compiles cleanly in 6.0 seconds through lcompile.py.
The existing library inputs are used as stated, independently of whether their own
transitive dependencies still contain holes.

## No longer needed

Removed redundant private imports (their required public interfaces remain available through
the retained imports):

- `Mathlib.RingTheory.Noetherian.Defs`
- `Mathlib.AlgebraicGeometry.Scheme`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Sheaf.AlgebraicGeometry.OpenModuleRestrictionIdentities`
- `Sheaf.Paper.ScalarModelRestrictionCriterion`
- `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`

The local proof does not directly use the following planned dependencies:
`lem-weil-pbc-reduced-induced-closed-subscheme`,
`lem-sfb-noetherian-complementary-stratifications`,
`lem-sfb-open-module-restriction-identities`, and
`lem-sfb-scalar-model-restriction-criterion`.
The already proved `lem-sf-open-extension-zero-constant-model-constructible`
provides exactly their module-level consequence while retaining the original scalar
models and allowing empty strata and complements. Their direct tool approvals were
removed from this node; they are not withdrawn from the library, and dependencies of
other or upstream declarations are not pruned.

The reused module theorem and scalar-isomorphism transport helpers are generic tools
from `lem-sf-open-extension-zero-constant-model-constructible` and
`lem-weil-pbc-module-constructible-pullback`; they do not replace a unit step. The former
node is already Lean-closed; the latter provides proved finite-presentation transport
rather than invoking its constructible-pullback conclusion. No new tool approvals were
written by the worker.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was necessary. The original node plan redundantly
reconstructed the module-level result already proved in
`Sheaf.Paper.OpenExtensionConstantModelConstructible` (the earlier node review also
identified this possible shortcut). The proof uses only the forward finite-constant-model
implication; it does not use its false converse. The intervals remain independent,
test modules for Tor amplitude remain arbitrary, and no admissibility is assumed.

Checked the current blueprint open-extension proof, composition-interchange proof (3),
open-immersion derived projection proof, and finite constant local-model definition.
The zero ring, empty schemes/strata/complement, identity immersion, and empty or different
integer intervals are covered by the existing module theorem, exactness and isomorphism
transport; the proof makes no nonemptiness or ordering assumption.

The initial concrete stratification conversion triggered a kernel timeout. A generic
property-preserving conversion removes that cost without changing the constructed strata.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
