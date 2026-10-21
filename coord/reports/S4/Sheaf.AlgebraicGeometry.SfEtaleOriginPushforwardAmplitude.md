## What changed

Completed `AlgebraicGeometry.ProEtale.etaleOrigin_pushforward_amplitude` in
`Sheaf.AlgebraicGeometry.SfEtaleOriginPushforwardAmplitude`, preserving its entire
signature and all public imports. No other Lean module is changed.

Reflect the input range through the exact faithful intrinsic comparison. Apply the
proved `DerivedCategory.bounded_heart_amplitude` to the ordinary etale derived direct
image and all sheaves. Its heart interval is `[0,N]` for nonnegative N. For negative N,
negative vanishing and the hypothesis give zero cohomology on every heart image;
apply the same amplitude theorem with `c=d=i-a+1` for each desired output degree i.
Detection of zero by homology then gives the zero derived etale image. Compose the
existing bounded-below direct-image comparison, the D+/D compatibility isomorphisms,
and the canonical intrinsic realization comparison to transfer both conclusions.

Private proof imports now name the exact comparison/unit, PlusCompatibility,
homology detection, and intrinsic realization transport actually used. The existing
DAG node's proof, proof_deps and proof_origin follow this proof. No definitions,
public interfaces, target statements, source-library files, or other groups' modules
are changed. No change record or forced adaptation is needed.

Validation: the remote single-file compile passed without errors or warnings
(25.0 seconds). The delivery command performs final compilation and preflight checks.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.etaleOrigin_pushforward_amplitude`
(node `lem-sf-etale-origin-pushforward-amplitude`).

No sorry remains in the item. Added 0 holes, split off 0 statements, and introduced
no declarations. Existing imported statements remain owned by their existing nodes.

## No longer needed

Removed these private imports from the item:

- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`: the already-proved
  source comparison unit gives the faithfulness needed here; its larger classical
  essential-image characterization is unused. The corresponding dependency
  `det-pe-classical-sheaves-modules` is replaced by
  `lem-weil-pbc-comparison-grothendieck-unit`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`: this proof uses
  fixed-scalar ModuleCat-valued sheaves, whose K-injective instances already exist.
  The dependency `prop-pur-kinjective-resolutions-exist` is unnecessary here.
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`: the existing
  fixed-scalar ordinary derived functor supplies the required instances; the separate
  ringed-module scalar-map construction and dependency
  `lem-weil-pbc-module-direct-image-left-exact` are unused.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`:
  the source PlusCompatibility module supplies the directly applicable unbounded
  single-object negative-vanishing theorem. The mathematical negative-vanishing
  dependency is retained.
- `WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor`: the negative-N
  argument uses finite heart amplitude directly, so no degree-zero delta-functor
  identification or termwise-zero pushforward proof is needed. Removed dependency
  `lem-weil-pbc-right-derived-universal-delta-functor`.
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`: its larger bundled
  statement is unnecessary; the existing canonical qcqs bounded-below comparison
  `prop-weil-pbc-comparison-direct-image` is the exact component used. Removed the
  wrapper dependency `sk-thm-pe-direct-image-comparison` and retained that component.

These are dependencies unnecessary for this proof, not a claim that their modules
have no other consumers. No file is withdrawn, and no source-library declaration
is removed. No unit statement or step is bypassed: this node's unit
`sk-def-sf-admissible` has no proof steps, and its realized statement is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original plan's negative-N degree-zero argument
is valid but longer than needed: all heart-image cohomology already vanishes, so
finite amplitude suffices. The assumption `_hL` remains unchanged but its witness
is not needed, since reflected `[a,b]` support supplies boundedness below directly.
The comparison step requires both the published D+/D compatibility and the intrinsic
coefficient presentation comparison; the proof spells out those isomorphisms.

Searches were run with msearch leanfinder, loogle and grep, and with rg on both library
roots and Mathlib. No direct theorem for this full assertion was found. The proved
bounded-heart theorem and the source compatibility results provide the shorter route.
The proof handles N<0, N=0, zero inputs, and an empty output interval; it never assumes
a bound on arbitrary pro-etale sheaves.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
