## What changed

Filled the restriction exactness, residue-field unit, strict Roos, finite-Tor interval, integral
interval, finite full-subcategory equivalence, empty-family, and scalar-extension clauses,
without changing any public declaration signature, public import, or definition. All new helpers
are private and proved. The module-sheaf gluing and other categorical-equivalence clauses retain
their original named statements and proof plans.

Restriction exactness uses cocontinuity and the site inclusion adjunction. The strict Roos proof
applies the existing additive comparison and identifies its strict maps by their coordinates.
Finite-Tor bounds use finite ranges of integer endpoints, including the empty family. Integral
interval detection transports each reduction across the existing reduction comparison. Scalar
compatibility conjugates the normalized ordinary comparison by natural completion isomorphisms.
The rational comparison follows its published object and pure-tensor formulas.

The DAG keeps the original routes for the remaining clauses and records these shorter routes for
the clauses proved here. The finite full-subcategory equivalences transport the ambient
equivalence through the component coefficient equivalences and use isomorphism closure for
essential surjectivity. No source-library file is changed. No new modules, new nodes, or new
proof holes are introduced.

The local elaboration attributes and linter setting are documented in
`coord/changes/D9-finite-clopen-proof-transparency.md`. The prescribed downstream-use scan and
an exact-import search found no current downstream modules; no consumer adaptation is needed.
The local attributes export no reducibility change.

## Proved and sorry left

Eight of the original sixteen holes are closed:

- `WeilConjectures.PurityFiniteSetting.clopenRestriction_exact`
- `WeilConjectures.PurityFiniteSetting.clopenResidue_isUnit`
- `WeilConjectures.PurityFiniteSetting.finiteClopen_strict_roos`
- `WeilConjectures.PurityFiniteSetting.finiteClopen_finiteTor_iff`
- `WeilConjectures.PurityFiniteSetting.finiteClopen_finite_equivalences`
- `WeilConjectures.PurityFiniteSetting.finiteClopen_integral_bounds`
- `WeilConjectures.PurityFiniteSetting.finiteClopen_scalar_extension`
- `WeilConjectures.PurityFiniteSetting.finiteClopen_empty`

Zero holes added and zero statements split off. The eight remaining original holes are:

- `WeilConjectures.PurityFiniteSetting.finiteClopen_module_equivalence`
- `WeilConjectures.PurityFiniteSetting.finiteClopen_unbounded_decomposition`
- `WeilConjectures.PurityFiniteSetting.finiteClopen_finite_bounds`
- `WeilConjectures.PurityFiniteSetting.finiteClopen_constructible_equivalences`
- `WeilConjectures.PurityFiniteSetting.finiteClopen_tensor_and_reduction`
- `WeilConjectures.PurityFiniteSetting.finiteClopen_coefficient_units`
- `WeilConjectures.PurityFiniteSetting.finiteClopen_finite_restriction_identification`
- `WeilConjectures.PurityFiniteSetting.finiteClopen_integral_restriction_identification`

The two interval clauses use the existing, still holed `finiteClopen_finite_bounds`; the
integral clause also uses the original reduction comparison clause of
`finiteClopen_tensor_and_reduction`. Scalar compatibility uses the existing normalized scalar
comparison declarations, some still holed. These dependencies are retained, not asserted sorry-
free. The finite full-subcategory equivalences use the original ambient unbounded equivalence,
finite coefficient identifications, and predicate detection. The other four filled clauses use
proved declarations.

Validation: the complete module compiled with the prescribed server command in 44.1 seconds.
All 41 existing public declaration signatures, all public imports, and all non-theorem
bodies are unchanged. The file has eight named remaining holes and no new holes.

## No longer needed

Removed direct private imports:

- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.CategoryTheory.SetSheafCoverDescent`
- `Sheaf.CategoryTheory.SiteModuleSheafGluing`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`
- `Mathlib.CategoryTheory.Limits.HasLimits`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The standalone exactness proof does not need the finite-clopen gluing equivalence. The strict
Roos statement only asks about complexes: exactness of countable products and the derived-
product identification are unnecessary for that clause. Its proof uses the already proved `lem-
pur-roos-additive-comparison` instead.

No node or module is withdrawn globally. The remaining clauses still need the module gluing,
tensor, K-flat, and coefficient-transport steps of the existing node, so their DAG dependencies
are retained. Removal of direct imports is not a claim that these modules leave the targets'
transitive import closure.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. Several clauses admit shorter proofs from the
declarations now available than their original proof plans suggest. The integral-bound theorem
already assumes membership in the constructible complete category; it therefore need not re-
prove completeness detection. It only needs the finite interval detection and reduction
comparison, retaining the same interval at every reduction level.

Compiler diagnostics required avoiding repeated expansion of scalar functors in a large
comparison expression. The proof factors the categorical square through proved private helpers
and explicit associators. No time limit was raised, no definition was weakened, and no source-
library declaration was removed.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
