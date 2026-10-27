## What changed

Only `Sheaf.Paper.CompositeProjectionCoefficients` and its own DAG node change.
Public declarations, their signatures, definitions, and public imports are unchanged.

- `geometry`: supply Noetherian instances from finite type over the field, apply the
  existing compactifiability theorem to f, g and their composite, and infer additive
  smooth relative dimension from Mathlib.
- `finite_domains`: transport the ordinary coefficient unit through its published
  unit isomorphism and site comparison. The existing ordinary-origin and smooth
  exceptional preservation proofs give the two exceptional objects. Apply the
  existing smooth tensor-domain helper with input omega_g for the final tensor.
- `tower_domains`: the supplied right adjoints already take values in the full
  uniform constructible finite-Tor category. Its property fields, transported by
  the realization unit, give the exceptional memberships. The existing tower
  pullback result and uniform tensor closure give the composite tensor membership;
  the realization counit identifies its actual first tensor factor.

Use `import all` for the two existing modules whose proved private helpers are
reused. These are proof imports; no new public API is introduced. Add private
imports of CompactifiableOverField and UniformTowerTensorClosure. The DAG records
these routes while preserving the plans for the remaining theorem clauses.

Validation: `lcompile.py` compiled the final file with exit code 0, no warnings,
in 33.5 seconds. All existing definition bodies were compared with the source
and are verbatim. Local unusedSectionVars lint suppression preserves the original
included hypotheses. The required delivery preflight follows in deliver3.py.

## Proved and sorry left

Closed 3 of the original 13 holes, without adding any holes or split statements:
`AlgebraicGeometry.ProEtale.CompositeProjectionCoefficients.geometry`,
`AlgebraicGeometry.ProEtale.CompositeProjectionCoefficients.finite_domains`, and
`AlgebraicGeometry.ProEtale.CompositeProjectionCoefficients.tower_domains`.

The ten remaining holes are the following declarations, all in namespace
`AlgebraicGeometry.ProEtale.CompositeProjectionCoefficients` and all attached to
`lem-sp-composite-projection-coefficients`:

- `finite_composition`
- `finite_projection_laws`
- `finite_orientation_and_tor`
- `finite_site_projection`
- `tower_projection_laws`
- `tower_composition`
- `tower_orientation_and_intervals`
- `arithmetic_restriction_ctf`
- `arithmetic_projection`
- `arithmetic_composition`

Their theorem bodies remain exactly `by sorry`, with their existing source and
natural-language proofs. `UniformTowerTensorClosure.tensor_mem` is an existing
stated dependency and remains unproved in its own module; this delivery does not
add or alter that hole. This is a partial proof delivery, not a decomposition.

## No longer needed

Remove these 22 unused private proof imports from the item:

- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`
- `Sheaf.Paper.SmoothPurityTowerShriekLevels`
- `Sheaf.AlgebraicGeometry.CompactificationProjectionComposition`
- `Sheaf.AlgebraicGeometry.ShriekTensorComposition`
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`
- `WeilConjectures.Compactification.CategoryBaseChange`
- `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Sheaf.SixFunctors.CompositionProjectionMate`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `Sheaf.SixFunctors.RefinementProjectionCounit`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.Paper.RingedProjectionTensorComposition`
- `Sheaf.Paper.CofinalCoefficientProjectionCocone`
- `Sheaf.Paper.FiniteCompactSiteCoherence`
- `Sheaf.Paper.SmoothPurityStrictCompactificationComparisonRealization`
- `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting`
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
- `Sheaf.Paper.FiniteLocalizingExceptionalPreservation`

These removals concern the imports required by the delivered proofs. No module
is withdrawn, and no mathematical node is declared obsolete: the ten outstanding
clauses still retain their original plans and DAG dependencies. Public imports
are preserved. No adopted source-library declaration is changed or removed.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The geometry and domain clauses have shorter routes
than repeating the orientation arguments: use the already proved preservation
helpers and the full-subcategory output of the supplied right adjoints. No
nonvanishing, normalization, or nonempty-scheme assumption is added; this also
covers empty schemes, zero objects, and the zero finite coefficient ring.

Search before proof: leanfinder found the Mathlib smooth-composition instance;
loogle did not recognize the repository's older SmoothOfRelativeDimension name;
the remote grep query returned no hits. Local rg found the actual current
Mathlib instance, CompactifiableOverField, the finite/tower pullback-domain
helpers, the finite smooth ordinary/comparison helpers, and uniform tensor
closure. The remaining projection and arithmetic statements require the
specific canonical-map transport; no equality is inferred from finite tower
evaluations, and their holes are left untouched.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
