## What changed

Proved `AlgebraicGeometry.ProEtale.constantModelConstructible_openImmersionLowerShriek`
with its original signature. The private helpers explicitly construct the extended
stratification, identify the open restriction using the linear adjunction and coefficient
isomorphism, prove closed-complement vanishing by empty fibre products, transport the
original covers and constant models, supply the zero model, and handle empty schemes.
The theorem docstring, node proof and dependencies now describe this route. No existing public signature,
target, definition used by a target, or public import changes. The elaboration-only
commands are recorded in `coord/changes/T2-open-extension-proof-scopes.md`.

Validation: `lcompile.py` compiles the full module without errors or warnings in 4.0 seconds against the current compiled library.
The retained proof originally hit a kernel timeout when specializing a concrete model
predicate through two stratification conversions. The conversion now uses a generic
property and passes `extendedStratification j S` explicitly, so Lean checks the structural
conversion before substituting the sheaf and coefficient constructions. This changes
only private proof helpers, with no increased timeout or heartbeat limit.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.constantModelConstructible_openImmersionLowerShriek`
(node `lem-sf-open-extension-zero-constant-model-constructible`).
No holes added; no `sorry` remains in the delivered module. This is a proof, not a
decomposition. Existing imported library obligations are not claimed closed here.

## No longer needed

Removed proof imports:

- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.Paper.ModuleObjects`
- `WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`
- `WeilConjectures.CategoryTheory.RingObjects.RingPresheaf`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`

The proof does not use the separate scalar-model equivalence
`det-def-sfb-constructible-local-model`: it directly transports the existing
`HasFiniteConstantLocalModel` witnesses. It does not need the sectionwise comparison
nodes `def-weil-proetale-inverse-image`, `def-weil-sheaf-of-modules-category`,
`lem-weil-pbc-conjugate-iso-unit-equation`, or
`lem-weil-pbc-proetale-ringed-open-closed`: the actual module extension is fully
faithful via its linear adjunction, and its underlying-sheaf vanishing is proved
with the abelian adjunctions. It does not use the theorem
`lem-weil-pbc-reduced-induced-closed-subscheme`: the existing canonical
`j.closedComplement` and its image lemma give the explicit scheme required.
Both obsolete top-level tool approvals have been withdrawn. The aggregate
`sk-def-sfb-ring-object` and `sk-def-sfb-module-lower-shriek` proof dependencies
are unnecessary beyond the specific module-object and open-extension interfaces
listed in the new proof. No unit statement or step is bypassed (the unit realized
lists are empty). These dependencies can remain required by other parents.

## Where the brief, the DAG or earlier work was wrong

The planned comparison between sectionwise ringed modules and tensor module objects
is unnecessary: the library already constructs the linear module extension and
its adjunction. Existing proofs in ProEtaleModuleConstructibleExtensionByZero and
CondensedOpenClosedRecollement provide the abelian support and module-unit arguments;
these are reproduced as private proved helpers to avoid importing their unrelated
constructibility and derived recollement obligations. No mathematical statement
repair is needed. Edge cases include zero coefficients, empty strata, empty U,
empty X, and invertible j.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
