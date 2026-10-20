## What changed

Filled `AlgebraicGeometry.Etale.nonempty_affineSpaceAmbientAdjunction` using the
existing affine trace coordinate tower, the ordinary projective-line adjunction,
and the proved `affineTraceRight_normalForm`. Proved private helpers compare
the tower's compact supports with the chosen compactification and transport a
twisted, shifted derived pullback through a change of source. Explicit functor
associators avoid expanding the derived tensor construction during elaboration.

The theorem's signature and public imports are unchanged. The DAG proof and
proof dependencies now record the existing coordinate-tower implementation.
`coord/changes/m4-affine-space-ambient-adjunction-proof.md` records the local
sheaf-monoidal instance command requested by static preflight and the unchanged
interface of the sole downstream importer; no consumer adaptation is needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.nonempty_affineSpaceAmbientAdjunction`
(`cor-amb-affine-space-adjunction`). Added zero holes and split off zero statements.
There are no remaining `sorry` declarations in the delivered module. The proof
uses existing dependency declarations, as prescribed by stage 3. The complete
proof passed the single-file server compiler in 18.1 seconds after import
pruning; delivery also runs the required preflight.

The construction includes dimension zero through the tower's identity adjunction.
It imposes no extra boundedness or constructibility condition. Zero coefficients
(including N=1), the empty base, and arbitrary positive N are covered by the
unchanged quantified statement and the existing normal-form theorem.

## No longer needed

The direct plan dependencies below are replaced by the existing tower and its
normal form: `def-weil-finite-type-morphism`, `def-weil-proper-morphism`,
`lemma-nagata-relative-affine-space-open-immersion`,
`lemma-nagata-projective-space-base-change-proper`, `def-asd-compactifiable`,
`lem-weil-pbc-open-immersion-etale`, `def-weil-pbc-etale-sum-extension`, and
`lem-asd-finite-etale-twist-line`. These facts remain available through the
reused constructions; this delivery does not withdraw their modules.

`lem-weil-pbc-inverse-image-composition-module-linear` is not applied: the
existing module-valued `leftDerivedUpperStarComp` supplies the concrete derived
composition needed here. Its direct proof import is removed.

Removed these unused or transitively available proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `WeilConjectures.Compactification.ProjectiveSpace`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`
- `Sheaf.Paper.RingedTopoiDerivedTensorPullback`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `Mathlib.CategoryTheory.Adjunction.Basic`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`

Removed obsolete top-level tool-use approvals for
`lemma-nagata-relative-affine-space-open-immersion`,
`lemma-nagata-projective-space-base-change-proper`,
`lem-weil-pbc-open-immersion-etale`, and
`lem-weil-pbc-inverse-image-composition-module-linear`; retained the other
approvals in their original order. No module is withdrawn and no source-library
declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The old plan predated the proved coordinate tower and right-normal-form API.
Those declarations already implement the polynomial-coordinate identifications,
Noetherianity, flat Tate tensor calculation, and shift addition needed here.
Reusing them follows the same affine-line/projective-line argument without
restating those results. No mathematical statement or unit route is changed.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
