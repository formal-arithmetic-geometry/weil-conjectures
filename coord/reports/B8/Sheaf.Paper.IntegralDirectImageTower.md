## What changed

Replaced the body of
`AlgebraicGeometry.ProEtale.IntegralDirectImageTower.integral_direct_image_tower`
by a complete assembly proof from strictly smaller component statements. The theorem's
signature is byte-identical to the original. The proof derives the finite base-change clause:
`CanonicalTowerComparison.hom_eq` identifies the actual strict comparison with the hom of an
isomorphism; evaluation preserves it and composition with `finiteComparison` is invertible.
It never assumes faithfulness of finite evaluations.

It also derives the two projection-endpoint constructibility clauses, rather than including
them in the projection-mate helper: constructibility of M tensor f* K is combined with direct
image preservation, and tensor preservation applies to Rf_! M and K.

The interface before the theorem moves verbatim to
`Sheaf.Paper.IntegralDirectImageTowerData`. The original publicly imports it. This breaks the
otherwise circular dependence between the interface, the component lemmas, and their assembly.
Every one of the 55 moved declarations is byte-identical, and every former public import is
retained transitively. No definitions or canonical arrows change. The inherited transparency
options are restored to `true` in the data module after a timeout/profiling check: the profiled
whole interface compiled in 48.8 seconds. This extraction was for the import graph, not a file
split to evade a compile limit. No source-library module is changed.

The independent-reader change record is
`coord/changes/B8-integral-direct-image-interface.md`. There are no existing Lean downstream
modules to adapt (`tools/downstream.py` and a namespace search). DAG parents still receive the
unchanged theorem and the unchanged full interface; no withdrawal is proposed.

Validation: all seven delivery modules compiled together through launcher lcompile. The
original interface and theorem signature were compared byte-for-byte. The complete assembly was checked against all five component statements. The final delivery
checks the same packet with its documented coefficient-transport obligation.

## Proved and sorry left

Closed the original theorem body:
`AlgebraicGeometry.ProEtale.IntegralDirectImageTower.integral_direct_image_tower`
(node `det-sp-integral-direct-image-tower`). This is a decomposition, not a sorry-free proof
of its entire dependency closure. The assembly itself has no sorry.

The following five split statements remain `:= by sorry`:

- `AlgebraicGeometry.ProEtale.IntegralDirectImageTower.normalized_geometry_limits`
  (`lem-sp-integral-tower-geometry-limits`): normalized scalar/pullback geometry, the open mate,
  and normalized ordinary/derived inverse-limit presentations; no direct-image conclusions.
- `AlgebraicGeometry.ProEtale.IntegralDirectImageTower.constructible_compactification_coherence`
  (`lem-sp-integral-tower-constructible-coherence`): only independence, identity, cocycle, and
  dense-refinement normalization on the constructible full subcategory.
- `AlgebraicGeometry.ProEtale.IntegralDirectImageTower.image_reconstruction`
  (`lem-sp-integral-tower-image-reconstruction`): only tower normalization, Tor bounds,
  reconstruction, and direct-image constructibility; no tensor/pullback or projection clause,
  and no finite-base-change clause.
- `AlgebraicGeometry.ProEtale.IntegralDirectImageTower.integral_projection_mates`
  (`lem-sp-integral-tower-projection-mates`): invertibility only of the actual proper and open
  projection maps, independently of s, q, hq, and L.

The fifth remaining hole,
`AlgebraicGeometry.ProEtale.IntegralDirectImageTower.integral_pull_tensor_constructible`
(`lem-sp-integral-tower-pull-tensor-constructible`), isolates transport of the two existing
preservation theorems to the coefficient presentation used here. It remains `:= by sorry`: the two condensed-ring constructions are not
definitionally equal as monoid objects, and applying preservation requires an explicit
normalized coefficient equivalence. The attempted direct proof was removed. The data module has zero holes and no choice of arbitrary data from an
unproved existence theorem. No axiom, unsafe implementation, or hidden definition hole is added.

## No longer needed

The proof-only imports formerly in the item module have been removed from the extracted data
interface, since none of its construction terms uses them:

- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`
- `Sheaf.SecSmoothPurity.ReductionDirectImage`
- `Sheaf.Paper.SemilinearDerivedSections`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts`
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`
- `Sheaf.CategoryTheory.RingedToposMorphism`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Paper.IntegralTensorProduct`
- `Sheaf.Paper.IntegralTensorPullback`
- `Sheaf.Paper.SmoothPurityNormalizedEquivalence`
- `Sheaf.SixFunctors.ProEtale.DerivedCompletion`

The assembly now imports only the extracted interface and the five component statements.
The dependency modules required by the future component proofs are imported directly there.
No whole DAG node or module is claimed pruned from the targets' closure: the original proof
route remains necessary below the split statements. The component statements' proof_deps
record that route. In particular, imported theorems that are still sorry are legitimate
prerequisites, not claimed finished or bypassed. All original public imports remain visible.

## Where the brief, the DAG or earlier work was wrong

The one original hole combined several independently formalizable arguments and multiple
coefficient presentations. The dependencies exist, but their recorded conclusions use
completed section modules, independent ringed-system coordinates, and embedded coefficient
rings; they do not directly construct the exact `ReductionGeometry`, `Limit`, and
`CanonicalTowerComparison` types with their prescribed generator and representative equations.
The component statements isolate these transports without weakening any original conclusion.

The original file set both transparency-respecting options to false. On the copied interface
this caused a timeout. Restoring transparency checking compiled all the original constructions.
An initial direct preservation proof hit the heartbeat limit while Lean compared the two
large coefficient presentations; the refined proof uses explicit types for that comparison.
Restoring transparency exposed the actual coefficient mismatch, rather than making the
preservation proof automatic. This is a real transport obligation, now stated explicitly.
Neither issue authorizes changing the mathematical statements, and none is changed.

The current blueprint proof paragraphs (1)-(3) and the unit's realized route are retained.
Each component's docstring records the source, full proof in words, and edge cases (zero,
empty schemes, arbitrary Tor intervals). Net holes: one original body closed, five strictly smaller holes added (net -4); this is a
decomposition and is not claimed as net sorry reduction. Each component is strictly smaller than the original
statement. No component merely renames or repackages its whole conclusion.

## New nodes

`def-sp-integral-direct-image-tower-data` records the 55 unchanged interface declarations in
the extracted data module. It introduces no new construction or existence assumption.

`lem-sp-integral-tower-geometry-limits` is the scalar/pullback and derived-limit infrastructure
needed before the direct-image theorem can even state its three geometric clauses.

`lem-sp-integral-tower-constructible-coherence` restricts the existing localizing coherence
result to the integral constructible subcategory, with its dense-refinement normalization.

`lem-sp-integral-tower-image-reconstruction` realizes proof paragraphs (1)-(2), without the
finite-base-change clause which the assembly proves formally.

`lem-sp-integral-tower-projection-mates` realizes the invertibility portion of paragraph (3),
without reasserting endpoint constructibility or any tower reconstruction conclusions.

`lem-sp-integral-tower-pull-tensor-constructible` transports the existing ordinary pullback and
tensor preservation theorems, with no smoothness, compactification, or limit hypothesis.

Change record: `coord/changes/B8-integral-direct-image-interface.md`.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
