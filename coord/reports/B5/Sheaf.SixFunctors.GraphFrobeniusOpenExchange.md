## What changed

Replaced the sorry in `WeilConjectures.TraceFormulaCoefficientConventions.graphFrobenius_open_exchange` by a compiling adjunction-mate argument, preserving its signature and every existing definition. The private helpers identify the localized open-adjunction unit with the published exact derived unit, transport the inverse-exchange normalization into tensor coordinates, and prove naturality of exchange from naturality of restriction. The main proof applies these helpers to the two existing Cartesian Frobenius squares and then restricts to D^b_ctf.

The separate source result `Lf* kappa_Y = kappa_X Lf*` is stated at positive iterates in the new module `Sheaf.SixFunctors.SchemeGaloisPullbackNaturality`, with the canonical mixed square comparison constructed explicitly. This result concerns arbitrary model morphisms on the entire unbounded categories and contains no open extension or exchange. Its source is the final displayed equation of main-20261015 `def-pur-scheme-geometric-frobenius.md`; the extension to arbitrary model morphisms and exponent a*m follows the existing arbitrary-pullback absolute-Frobenius theorem. It is isolated because it is a separate source naturality result used by the open-exchange argument, not because of elapsed time.

Both modules were compiled together through lcompile.py. The original module also compiled alone in 37.9 seconds after repair of the inherited exact-derived-unit calculation. The canonical naturality proof still requires the normalization/coherence calculation described below; the packet is a decomposition, not a net hole reduction.

## Proved and sorry left

Closed the one original hole: `WeilConjectures.TraceFormulaCoefficientConventions.graphFrobenius_open_exchange` (`lem-trf-graph-frobenius-open-exchange`). The module now has zero sorry. The categorical mate naturality calculation, inverse-unit exchange calculation, and exact-derived-unit compatibility are proved private helpers with no holes.

Added one hole: `WeilConjectures.FiniteFieldDatum.canonicalSchemeGaloisComparison_pullback` (`lem-trf-scheme-galois-pullback-naturality`). This is a decomposition: one upper hole closed and one strictly separate restriction-naturality hole added, net zero. No other holes are added; no definitions contain sorry. Existing imported theorems retain their existing holes, which this delivery does not alter.

The private helper `canonicalComparison_normalization` now identifies the relative-Frobenius-normalized trivializations selected independently in `schemeGaloisComparison` and `absoluteFrobenius_proEtale_trivialization_pullback`: fibre-product extensionality fixes the site isomorphism and adjunction injectivity fixes the trivialization. The remaining task is to match that theorem's exact ordinary composition descent with `proEtaleConstantRingPullbackComposition` and the unit-normalized intrinsic coordinate change. The existing derived associativity theorem supplies reassociation but does not itself state these normalization identifications. The new theorem's docstring and DAG give the full tensor/section argument. Edge cases checked in that argument: empty schemes, j=id, zero coefficient module and ring, m=1, arbitrary positive m, and non-open/non-smooth morphisms. No cancellation of Frobenius or scheme-flatness assumption is used.

## No longer needed

Removed unused proof imports `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence` and `Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit` from the new naturality module. Its future composition argument still names these nodes; they are not globally pruned. Removed an unused private adjunction-normalization helper from the delivered module.

Removed private imports `Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback`, `Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit`, `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`, and `Sheaf.AlgebraicGeometry.ProEtaleConstantExact` from the main module: the separate naturality result encapsulates their restriction calculation. Replaced the original private `Sheaf.SixFunctors.OpenTensorNormalization` import by `Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction`.

The main proof no longer uses `lem-sf-open-tensor-normalization` or `Sheaf.SixFunctors.OpenTensorNormalization`: injectivity of the adjunction Hom bijection replaces derived full faithfulness and cancellation of an invertible open unit. No unit statement or unit proof step is bypassed (`sk-d-weil.realized` is empty).

The main proof no longer directly uses `prop-trf-frobenius-factorization`, `def-trf-scheme-frobenius`, `lem-weil-pbc-proetale-derived-pullback-composition`, `lem-trf-absolute-frobenius-site`, `prop-weil-pbc-proetale-constant-ring-map`, `lem-sf-proetale-tensor-composition-unit`, `prop-weil-pbc-proetale-constant-exact`, or `lem-weil-pbc-localization-universal-property` as proof dependencies. The definitions and the new naturality result still need the relevant underlying theory; these are not claimed globally pruned. Existing public imports are retained to preserve the module's published statement interface. No module is withdrawn and no target statement changes.

## Where the brief, the DAG or earlier work was wrong

The original Steps 5--7 used an invertible open unit and full faithfulness unnecessarily. The adjunction Hom equivalence suffices with any unit once the inverse exchanges satisfy the supplied restriction normalization.

The inherited sandbox's helper used the nonexistent MorphismProperty.Over.hom_ext; the available lemma is MorphismProperty.Over.Hom.ext. Removed an unnecessary final simp from exactDerivedAdjunction_unit; its dependent identity/composition terms are closed by rfl after explicit cancellation. The old docstring's claim that open-tensor normalization was not yet stated is stale; the theorem is available but unnecessary here. Existing declaration docstrings and signatures are retained.

## New nodes

`lem-trf-scheme-galois-pullback-naturality`, in `dag/nodes/sec-trace-formula/`, records the separate pullback-naturality result and its explicitly constructed tensor/intrinsic square. Its source is the blueprint's own final naturality equation in `def-pur-scheme-geometric-frobenius`, with exponent a*m supplied by the existing absolute-Frobenius naturality theorem; its four proof steps record the normalization identifications and canonical composition calculation. LeanSearch, Loogle, LeanFinder and source grep found generic scheme/adjunction/pullback results but no matching theorem for this specified trace-formula comparison. The purity module gives a related m=1 comparison under different conventions and smoothness assumptions, so cannot be applied directly. No change record is needed: existing statements, definitions and public imports are unchanged.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
