## What changed

Proved `WeilConjectures.point_sections_finiteness` with its original statement unchanged.
Finite-torsion sections are finite by constructible etale origin, finite etale sections,
finite-level comparison and exact sections. Integral sections are bounded and derived
complete by the reduction Roos triangle, exact products and scalar nilpotence. The
existing derived-reduction cone comparison at exponent one supplies finite cohomology
residues. The derived-complete-module criterion gives finite generation; flat
localization then gives rational finiteness.

Retained the prior complete proofs of these steps, including the general lemma that
derived completeness passes to homology. The sandbox now contains eight Lean modules:
the item, five new proved helper modules, and two adapted existing modules. No new
unfinished theorem is introduced.

The eight canonical scalar constructions move unchanged into the existing unclaimed
`Sheaf.Paper.CompletedIntegralCoefficientGerm` prerequisite, next to its canonical
constant-to-completion map. The item keeps all eleven original public imports, so all
original public names, signatures and mathematical data remain available. The existing
`PointSectionsDerivedReduction` module already publicly imports that prerequisite;
its sole source change removes its public import of the parent finiteness theorem.
This breaks the source cycle. Its declarations, signatures and proofs are unchanged.
The change record lists the existing and new textual consumers and their current claim holders.

Refreshed the retained reduction file against current sources: the tensor-product,
bounded-flat and mixed-tensor proof imports use their current `WeilConjectures` paths.
These lines now match the repository exactly, so they are not delivery adaptations.
The earlier empty definition wrapper is removed from the sandbox rather than delivered.
The finite-torsion helper explicitly imports SfIntegralConstructible because its
fixed-universe sheafification instances are needed to elaborate the original statement;
without that import compilation reports a stuck WEqualsLocallyBijective universe constraint.

## Proved and sorry left

Verification for this repair: `lcompile.py --all` compiled all eight delivered modules
with exit code zero and no diagnostics. The source scan across live, quarantined and
sandbox modules found PointSectionsReconstruction to be the sole missing user-table row.

Original item: one hole, `WeilConjectures.point_sections_finiteness`
(`lem-weil-point-sections-finiteness`). Closed: that one hole. Item after delivery:
zero holes. Holes added: zero. Unfinished statements split off: zero.

All helper declarations are proved:

- `WeilConjectures.point_finiteSections_finite_of_constructible` and
  `WeilConjectures.point_sections_finiteness_finiteTorsion`
  (`lem-weil-point-sections-finite-torsion`).
- `WeilConjectures.point_sections_integral_cohomology_control`
  (`lem-weil-point-sections-integral-cohomology-control`).
- `DerivedCategory.isDerivedComplete_homology`
  (`lem-weil-derived-complete-homology`).
- `WeilConjectures.point_sections_finiteness_integral`
  (`lem-weil-point-sections-integral-finiteness`).
- `DerivedCategory.pointFiniteDimensional_of_flat_scalar_extension`
  (`lem-weil-point-flat-scalar-extension-finite-cohomology`).

Two pre-existing holes remain unchanged in adapted existing modules:

- `WeilConjectures.point_sections_derived_reduction`
  (`lem-pod-point-sections-derived-reduction`).
- `WeilConjectures.integralConstantQuotientRingMap_compatibility`
  (`def-weil-completed-integral-coefficients`).

The proof uses these named existing dependencies as stage 3 intends; this is not a
claim of project-wide axiom closure. No definition or private helper contains `sorry`.
The arguments cover zero complexes, negative degrees, unbounded representatives with
bounded cohomology, torsion complexes, and arbitrary cohomology transition maps.
No transition-surjectivity assumption is used. The general completeness-to-homology
lemma allows separate ring, module and localization universes.

## No longer needed

The item keeps every original public import. Removed direct proof imports:

- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`
- `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`
- `Mathlib.RingTheory.AdicCompletion.Basic`
- `Mathlib.RingTheory.Flat.Basic`
- `Mathlib.RingTheory.Flat.Localization`
- `Mathlib.RingTheory.Noetherian.Defs`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.Paper.DerivedComplete`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.FiniteRingConstructibleSheafOrigin`
- `Sheaf.RingTheory.DerivedCompleteModuleComplex`
- `Sheaf.RingTheory.DerivedCompleteModuleFinite`
- `Sheaf.RingTheory.NilpotentTorsionDerivedLimitComplete`
- `WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues`
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `WeilConjectures.AlgebraicGeometry.IsFiniteTypeEtaleModuleSheaf`
- `WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`

The finite-torsion proof uses the source library’s finite etale-section theorem and constructible-etale comparison directly. The separate finite-locally-constant-values and algebraically-closed-etale-sheaf routes are unnecessary here. Mathlib supplies flat tensor exactness and localization flatness through the proved general helper. The parent node therefore uses the finite-torsion and integral helper nodes; their lower dependencies are recorded in their own nodes. All obsolete original top-level tool_uses approvals are withdrawn. No global unreachability is claimed: the derived-reduction comparison still uses K-flat dependencies, and other items may use the removed direct imports.

The empty, never-landed PointSectionsFinitenessDefs wrapper is omitted. The reduction comparison drops its public import of PointSectionsFiniteness solely to break the source cycle; its existing coefficient-germ import supplies the same constructions. No theorem module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

Repaired the return for delivery head `4ab662d2ac`: added the omitted
`Sheaf.Paper.PointSectionsReconstruction` row to the change record's `## Users`.
The current rework record preserves this module at
`quarantine/Sheaf/Paper/PointSectionsReconstruction.lean`; it is unclaimed.
Read its existing PointSectionsFiniteness import, the reflexive finite/integral
section-functor comparisons, and its explicit use of pointIntegralSectionsAdditive.
All three referenced declarations retain identical signatures and bodies and remain
publicly reexported by the same item import. The archived consumer therefore requires
no source adaptation. It remains a needed consumer, with its archive, Lean attachment
and dependencies untouched. This repair changes the change record and this report;
the complete retained proofs and their DAG route are preserved. Refreshed all user-table
holders from the current claim records; server preflight identifies A6 as the current reduction-module holder.


The first repair preflight found that the server holds a newer A6 claim on
PointSectionsDerivedReduction than the local snapshot. Updated its change-record row
and this forced-adaptation report to name A6; the sole source adaptation remains the
import removal documented below. No Lean source changed in response to this diagnostic.

The previous report described relocation to a new definition module and replacement
of the reduction import. The retained sources had already moved the constructions into
the existing coefficient-germ prerequisite, but left an empty wrapper, stale metadata,
and an outdated report. The retained packet reconciles the sources, node and change record,
removes the wrapper, and preserves all original public imports of the item directly.

The original item statement and all eight relocated construction signatures and bodies
are unchanged. No mathematical statement is disputed. The existing reduction theorem
is a named dependency, and its original hole remains. The unit has no proof steps to
bypass; the finite/integral/rational route is retained. Other imported theorems may still
rest on existing holes, and are not counted as proved here.

## New nodes

- `def-weil-point-section-scalar-functors`: records the unchanged eight constructions
  relocated to `CompletedIntegralCoefficientGerm`, not a second definition of them.
- `lem-weil-point-sections-finite-torsion`: proved finite cohomology of finite-torsion
  point sections via etale origin and exact sections.
- `lem-weil-point-sections-integral-cohomology-control`: proved bounded support,
  derived completeness and finite residues of integral point-section cohomology.
- `lem-weil-derived-complete-homology`: proved derived completeness of every homology
  module by conjugacy of the multiplication-shift operator under product-preserving
  homology and the degree-zero single functor.
- `lem-weil-point-sections-integral-finiteness`: proved integral finite generation
  and rational finite dimensionality from cohomological control.
- `lem-weil-point-flat-scalar-extension-finite-cohomology`: proved flat scalar
  extension preserves bounded finite cohomology and gives finite dimension over a field.

All new theorem nodes are proved, with no new unfinished node. Their sources and
recorded searches are retained from the earlier packet. Change record:
`coord/changes/point-section-scalar-functors.md`.

## Forced adaptations

`Sheaf.Paper.PointSectionsDerivedReduction` (current holder A6, from server preflight) loses exactly the line
`public import Sheaf.Paper.PointSectionsFiniteness`. Its original source import graph
would contain the cycle `PointSectionsFiniteness → PointSectionsFinitenessIntegral →
PointSectionsIntegralCohomologyControl → PointSectionsDerivedReduction →
PointSectionsFiniteness`. Its existing public import of
`Sheaf.Paper.CompletedIntegralCoefficientGerm` supplies the relocated definitions,
so no replacement import or declaration edit is needed. A source import cycle is the
failure addressed here; a compile against existing artifacts cannot detect it.
The delivery tool explicitly routes pure import removal for cycle repairs to independent
review. The adapted coefficient-germ module is unclaimed and gains only the relocated
constructions and their necessary public imports.

## Forced adaptations

### Sheaf.Paper.PointSectionsDerivedReduction
Only imports removed (Sheaf.Paper.PointSectionsFiniteness), e.g. to break an import cycle; nothing else changed. CODEX verifies that the removal is needed.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
