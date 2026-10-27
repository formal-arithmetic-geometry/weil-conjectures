## What changed

Proved `AlgebraicGeometry.ProEtale.SemilinearProperOpen.systemProperOpenInvertibility`
in `Sheaf.Paper.SystemProperOpenInvertibility`, preserving its complete statement and both
finite comparison definitions. The proof obtains an identity-scalar origin separately at
each positive level, applies the existing `gamma_finite` equation, detects invertibility by
exact derived evaluations, proves inverse naturality by cancellation, and proves the stated
isomorphism normalization by extensionality and cancellation. All helper declarations are
private proved theorems. No data definition or existing public interface changes.

The origin proof reuses finite lisse models and the proved `fixedDerivedOrigin` helper
of `Sheaf.Paper.ProEtaleConstructibleOrigin`, plus the proved fixed-scalar equivalence
and `cFixed` comparison. Its private proof import uses `import all` to access that helper.
The original DAG proof is updated to record this shorter route and the explicit use of the
already available `gamma_finite` equation. Ordinary derived composition comparisons identify
the constant-tower/index-zero evaluation with ordinary level evaluation.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.ProEtale.SemilinearProperOpen.systemProperOpenInvertibility`
(node `lem-pur-system-proper-open-invertibility`). The item originally had one hole and now
has zero. Added zero holes; split off zero theorems. The private helpers
`exists_iso_with_property`, `finite_iso_normalization`,
`finite_iso_normalization_comp`, `inverse_naturality`, `inverse_natural_app`,
`iso_square_isIso`, `system_isIso_of_evaluations`, and `scalar_origin`
are proved. Dependencies retain their own existing proof obligations.

## No longer needed

Removed the two unused proof imports `Sheaf.SixFunctors.OpenTensorNormalization` and
`Sheaf.AlgebraicGeometry.TowerMateEvaluationScalars`. Their normalization results and
`Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` remain transitively needed by
`gamma_finite`; no withdrawal or global pruning of those modules is claimed.

The direct proof uses the fixed-module `fixedDerivedOrigin` helper of
`lem-sf-proetale-constructible-origin`, rather than its general quotient-specific theorem
`constructible_proEtale_origin`, avoiding an extra change between continuous and
constant-ring encodings. The quarantined `Derived.Perfect` module is not imported. The existing public imports are
preserved, so no complete module is claimed to leave the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The DAG's five-step plan needlessly reconstructs the evaluated mate word even though
`gamma_finite` already proves precisely that equality for every supplied origin. The actual
proof uses that existing equation, including its specified source and target comparisons.
The origin hypothesis is expressed using the finite-stratification fixed-module predicate;
the proof explicitly converts its local constancy and finite stalks to finite constant
models before applying the existing descent theorems. No new mathematical hypothesis,
uniform interval, Tor assumption, or coefficient flatness is used. The zero object and
empty schemes are covered by the existing descent and finite-model theorems; the inverse
naturality clause permits arbitrary target objects whenever the supplied target isomorphism
has the specified forward mate. No source-library declaration is changed.

The first delivery check found that the formerly used `Derived.Perfect` source is
quarantined despite its compiled declaration being available. The proof now uses the
current, proved `fixedDerivedOrigin` helper instead; no quarantined source is restored.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
