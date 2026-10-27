## What changed

Proved `AlgebraicGeometry.Etale.moduleDerivedRestrictionResolution` in
`Sheaf.TraceFormula.ModuleDerivedRestrictionResolution`, preserving its complete statement,
all three public abbreviations, all existing public imports and the coefficient universes.
The four new private helpers are fully proved: `module_compUnit_app` expands the
composite derived unit, `module_leray_fac` identifies the canonical composition
normalization, and `module_restriction_fac` combines the derived adjunction-unit equation
with that normalization at the ordinary unit; `module_chain` uses naturality at the
arbitrary map `a` and cancels resolution comparisons in abstract abelian categories. The final proof passes
from homotopy classes to cochain representatives and cancels the two invertible resolution
comparisons. Its component calculation uses `hw` and naturality of
`Sheaf.ΓNatIsoSheafSections`.

The generic calculation adapts the existing proved private helpers in
`Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula`; the terminal-section calculation
also appears for abelian coefficients in `Sheaf.Paper.EtaleKInjectiveUnitLeray`. Neither
module is imported, and neither specialized theorem is used. Searches used LeanFinder,
Loogle, the supported grep search, and direct searches of Mathlib and both library roots.
The DAG proof, proof dependencies, proof origin and obsolete tool approvals now describe
the actual proof. The unit route is preserved; its `realized` lists are empty for this node.
No source-library file, definition, public signature or consumer requires adaptation.
Preflight requires a record for the proof namespace and local transparency-option
commands: `coord/changes/W8-module-restriction-proof-options.md`. It records all three
transitive consumers and why none needs adaptation.

Validation: `lcompile.py` checked the refactored full proof successfully (22.6 seconds).
Its sole line-width warning was removed. The generic `module_chain` helper keeps the
resolution-comparison calculation abstract, avoiding repeated unfolding of concrete
scheme-site instances; earlier concrete calculations varied from 23.2 seconds to the
60-second limit. No file was split, no limit changed, and no definition or public
signature changed. The delivery probe also compiled the refactored proof in 26.5 seconds and reported
`SHEAF-PROBED 12` with no forbidden axioms. It stopped on the now-fixed width
warning; final delivery compilation and preflight are pending.
Every line of Lean is at most 100 characters.


Resume metadata: the original dispatch recorded start `1792672022.3941445`.
The launcher reset `.budget.start` to `1792736175.640566` on the resumed dispatch
(attempt markers `.brief2`–`.brief5`, refreshed 2026-10-23 14:16 +08).
No budget or launcher file was edited by the worker; work continues under the
original brief and session deadline. Repeated service exit 124 responses initially
provided no Lean diagnostics; the successful compiles above supplied validation.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.Etale.moduleDerivedRestrictionResolution`
(node `lem-trf-module-derived-restriction-resolution`).

Added 0 holes. Remaining holes in the delivered module: none. All four private helpers
are fully proved. No new theorem modules or nodes are introduced. The argument does not
assume that `a` is a quasi-isomorphism; it never inverts `a` or `w`. It also applies to the
zero ring, zero complexes and arbitrary lower bounds, with no finiteness hypothesis on
the scheme morphism or coefficient ring.

## No longer needed

Removed these unused private imports from this item:

- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.CategoryTheory.Adjunction.Basic`

The proof no longer needs these former proof dependencies:

- `lem-weil-pbc-module-sheaves-enough-injectives`
- `lem-sp-right-adjoint-preserves-injectives`
- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-right-derived-plus-injective`
- `lem-sf-kinjective-derived-map-computation`
- `prop-weil-pbc-kinjective-resolutions-exist`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-adjunction-of-natural-bijection`

In particular no extra module K-injective resolution, bounded-below injective
representative, homotopy-Hom lift, or choice of an adjunction from a Hom bijection is
needed. The given complexes already satisfy the Mathlib bounded-below K-injective
instance. Naturality of the canonical derived units computes all morphisms here.
The enough-injectives and explicit-resolution modules named above are unused by this
proof; the preserved source imports and other consumers may still use them. No module
is withdrawn, and no claim of a whole-library closure reduction is made.

The proof uses the existing Mathlib leaf
`lem-weil-pbc-bounded-below-injectives-kinjective` and the already Lean-closed generic tool
`lem-weil-pbc-right-adjoint-preserves-kinjective` (the source instance required for Leray).
The latter is a categorical tool for the constant-coefficient module adjunction, already
part of the canonical Leray construction; no trace-unit lemma supplies that infrastructure.
Removed the obsolete top-level tool approvals for
`lem-weil-pbc-module-sheaves-enough-injectives`,
`prop-weil-pbc-kinjective-resolutions-exist`, and
`lem-sf-kinjective-derived-map-computation`. No approval was added or reordered.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. Its five-step plan contained avoidable intermediate choices:
one need not choose further injective models or reconstruct the derived adjunction through
Hom bijections. Mathlib's derived-unit factorization and the source composition-of-derived-
functors universal property give the normalization directly. This is the same mathematical
unit/adjunction/Leray route, with the unnecessary choices and their dependencies pruned.
The original declaration docstring retains the stage-2 proof plan; the updated DAG and
proved helpers record its shorter implementation.

## Second reading by W8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
