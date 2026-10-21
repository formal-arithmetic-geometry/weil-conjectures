## What changed

Filled all four proof holes in `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`.
The constant-ring unit is locally bijective by transporting Mathlib's locally-bijective
sheafification result along the essentially small site and retaining its section functions
when forgetting commutativity. Constant module presheaves preserve sums componentwise.
Module sheafification is additive by `Adjunction.left_adjoint_additive`. Ordinary scalar
extension preserves sums sectionwise, using the module extension/restriction adjunction,
and its sheafification preserves that equality. The composite is therefore additive.

Added the private proof import `Mathlib.CategoryTheory.Adjunction.Additive`. Moved the
existing two component-additivity theorems before the composite-additivity theorem so its
proof can use those instances. All declaration signatures, attributes, definitions, public
imports and docstrings are unchanged. Two declaration-local unused-section-variable linter
settings preserve the existing theorem binders rather than removing hypotheses from the API.

Searches: LeanFinder's query about local bijectivity of the commutative-ring sheafification
unit found Mathlib's `GrothendieckTopology.instIsLocallyInjectiveToSheafify` and the
corresponding sheafification interfaces. Loogle returned zero hits because its server did
not resolve `Presheaf.IsLocallyInjective`. Repository and Mathlib searches found the direct
proof patterns in `ConstantFiniteFreeSectionBasis`, `RingComplexSemilinearExtension`, and
`RingedTopoiDerivedPullback`, and the precise Mathlib declarations in `Sites.Equivalence`,
`Sites.LocallyBijective`, and `Adjunction.Additive`. No additional Sheaf dependency is needed.

## Proved and sorry left

Closed four holes, all attached to `def-weil-pbc-strict-perfect-coefficient-package`:

- `SheafOfModules.scalarPerfectRingUnit_locallyBijective`.
- `SheafOfModules.scalarPerfectConstantFunctor_additive`.
- `SheafOfModules.scalarPerfectExtensionFunctor_additive`.
- `SheafOfModules.scalarPerfectFunctor_additive`.

Zero holes remain in the item; zero holes added; zero statements split off.
The file compiled cleanly in 13.5 seconds. Explicit `#print axioms` checks for all four
theorems report only `propext`, `Classical.choice`, and `Quot.sound`. Declaration headers
and docstrings were also compared against the original; all are preserved.

## No longer needed

None. No existing imports, nodes, modules, or unit steps are withdrawn. The definition
node has empty `proof` and `proof_deps`; the Lean proofs implement the existing theorem
docstrings directly from Mathlib, so no DAG route change or new node is required.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or definition required repair. The source order placed the
composite additivity theorem before its component additivity theorems; moving the latter
before it permits direct composition of the now-proved instances. The direct proofs do
not require the automatically included abelian-group hypotheses of local bijectivity or
the commutative-ring sheafification hypothesis of scalar-extension additivity, but those
existing binders are retained verbatim.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
