## What changed

The original signature and docstring of
`AlgebraicGeometry.Scheme.Modules.affineOpen_cohomology_localization_zero` are unchanged.
Its proof now composes the canonical comparison of degree-zero fraction quotients,
ordinary section localization over the ambient affine open, and the inverse
canonical comparison on the target. Coefficient naturality and compatibility with
restriction prove the required equation for every numerator.

Five new modules separate the formal degree-zero argument from the geometric
restriction argument. `OpenSectionFractionPresentation` constructs an additive
quotient of actual section groups, without selecting any witnesses or postponing
any data. `OpenCohomologyZeroSections` constructs the actual canonical
`rightDerivedZeroIsoSelf`, proves finite-limit preservation, and proves coefficient
naturality. `OpenCohomologyFractionZeroComparison` proves that its direct sum takes
exactly the relation subgroup to the section relation subgroup and descends to
an additive equivalence preserving generators. `OpenCohomologyZeroRestriction`
proves compatibility with open restriction by computing both sides on the same
injective resolution, using naturality of cycles and homology, and cancelling the
canonical degree-zero isomorphisms.

`AffineOpenSectionFractionLocalization` states only the remaining ordinary-section
restriction step of the existing plan, with its source and full proof in words.
It retains the planned use of `affine_section_localization` on `U.toScheme`.
No cohomology, derived comparison or quotient comparison between cohomology and
sections remains in that statement.

All six modules compile together through `lcompile.py --all`. The new statements
include empty opens, zero coefficients, and the zero section. In the zero-section
case the positive transitions kill every fraction and the nonvanishing open is
empty; no nonzero or inhabited hypothesis has been introduced. The quotient
comparison and restriction compatibility hold for arbitrary coefficient modules,
without quasi-coherence, invertibility or affine assumptions.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.affineOpen_cohomology_localization_zero`
(node `lem-sc-invert-s-cohomology-affine-open-zero`).

The following auxiliary results are proved with no direct `sorry`:

- `AlgebraicGeometry.RingedSpace.openModuleSections_preservesFiniteLimits`.
- `AlgebraicGeometry.RingedSpace.openCohomologyZeroSectionsIso_naturality`.
- `AlgebraicGeometry.Scheme.Modules.openCohomologyFraction_zero_comparison`.
- `AlgebraicGeometry.RingedSpace.openCohomologyZeroSectionsIso_restriction`.

One new hole remains:
`AlgebraicGeometry.Scheme.Modules.affineOpen_sectionFraction_localization`
(node `lem-sc-affine-open-section-fraction-localization`, module
`Sheaf.AlgebraicGeometry.AffineOpenSectionFractionLocalization`).
Its proof is exactly `by sorry`. There are no other sorries in the delivery.

This is a decomposition: one original hole closed, one strictly simpler
ordinary-section hole added, so the delivery makes no claim of a positive net
reduction in holes. The whole degree-zero derived-functor and additive-quotient
transport is proved. Existing imported theorems may still depend on their own
recorded holes; those declarations are unchanged.

## No longer needed

The parent's direct proof import
`Sheaf.AlgebraicGeometry.AffineSectionLocalization` is replaced by the three
proof imports `OpenCohomologyFractionZeroComparison`,
`OpenCohomologyZeroRestriction`, and `AffineOpenSectionFractionLocalization`.
`AffineSectionLocalization` remains a transitive dependency of the last module,
and remains needed by its ordinary-section proof plan.

No existing module or node is pruned from the transitive proof route.
In particular, `lem-sc-affine-section-localization` and
`lem-weil-pbc-module-restriction-open-immersion-colimits` remain necessary
inside the remaining section-localization step; neither is claimed pruned.
No public import of the original module was removed or made private.
The second reading removed the unnecessary cohomology-presentation import from the
new `OpenSectionFractionPresentation` module, replacing it with the actual section,
direct-sum and additive-quotient dependencies. The cohomology comparison now imports
`CohomologyFractionPresentation` explicitly, because its statement needs it.
This removes a dependency from the section-only construction; it prunes no module
from the target closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The existing plan correctly separates
affine restriction, degree-zero comparison, and final transport. The degree-zero
comparison and quotient transport were not separate usable declarations; they
are now constructed and proved explicitly.

The local checkout does not contain the cited Stacks `.tex` or blueprint source
files. The primary Stacks pages for Tags 01PW, 09MR, 01DZ and 01E1 were read online
without creating any literature files. The recorded source paths retain the
project's source identifiers. LeanSearch was unavailable (Internal Server Error);
that failure is recorded rather than a fictitious negative search result.

The earlier attempts stopped in the delivery tool with an ImportError for
`refuse_missing`. This retry reached the import-source check, which initially
reported `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits` missing despite their source
files being present in the prescribed Mathlib checkout. A subsequent prescribed
dry run proceeded beyond that check. No tool or repository file was edited to
bypass either failure.

The saved six Lean modules were read again, and all six were recompiled together
successfully with `lcompile.py --all`, without compiler warnings. The original
statement and docstring remain unchanged, and the only direct hole is the
ordinary-section localization theorem listed above. The prescribed delivery
dry run printed OK: the delivery compiles and passes preflight except for the
second reading, which the independent second reader supplies. Nothing was pushed.

## New nodes

`def-sc-open-section-fraction-presentation` records the three real constructions
in `OpenSectionFractionPresentation`: the additive relation subgroup, its quotient,
and each numerator generator. It deliberately uses additive closure, so the
proved degree-zero comparison does not require an unproved module-span identity.

`lem-sc-open-cohomology-zero-sections` records the canonical natural isomorphism
in `OpenCohomologyZeroSections`, its finite-limit-preservation instance and its
proved naturality. The isomorphism is constructed from Mathlib, not selected
from a mere-existence theorem.

`lem-sc-open-cohomology-fraction-zero-comparison` records the proved comparison
of fraction quotients on every ambient open. Its direct-sum map, image of the
relation subgroup, and formula on quotient generators are all proved in Lean.

`lem-sc-open-cohomology-zero-restriction` records the proved compatibility with
restriction. Its argument computes the natural transformation on one injective
resolution and uses the actual canonical comparison.

`lem-sc-affine-open-section-fraction-localization` records the sole remaining
hole: transporting ordinary affine section localization along the inclusion of
an affine open. Its docstring and node give the restriction, tensor-power,
nonvanishing-open, additive-closure/module-span, and tensor-formula steps.

No existing statement or definition changes, forced adaptations, or change records.

## Second reading by U1

1. Compared every delivered module with the repository. Only the item's module
   already exists; its diff changes proof imports and the proof body only. Its
   declaration signature and docstring are byte for byte unchanged. The other five
   modules are new. No existing definition, statement, visibility, target, or unit
   record changes. No change record or forced adaptation is needed. Verdict: pass.

2. Read all six Lean modules and compiled them in import order with the prescribed
   `lcompile.py --all`, again after the import repair: no errors or warnings.
   The sole direct `sorry` is the named theorem
   `AlgebraicGeometry.Scheme.Modules.affineOpen_sectionFraction_localization`.
   All data are actual constructions: additive closure, quotient, generators,
   Mathlib's canonical derived-zero isomorphism, direct-sum map, and quotient
   transport. No arbitrary witness is selected from an unproved existence theorem.
   No forbidden declaration or kernel-check bypass occurs. A scratch module printed
   the axioms of all ten delivered declarations: only `propext`, `Classical.choice`,
   and `Quot.sound`, except that the remaining hole and its main-theorem user also
   have `sorryAx`. In particular the canonical comparison, quotient comparison and
   restriction compatibility are independently sorry-free. Verdict: pass.

3. Checked the sole split-off statement against Stacks Tags
   [01PW](https://stacks.math.columbia.edu/tag/01PW) and
   [09MR](https://stacks.math.columbia.edu/tag/09MR), and checked the degree-zero and
   restriction argument against Tags
   [01DZ](https://stacks.math.columbia.edu/tag/01DZ) and
   [01E1](https://stacks.math.columbia.edu/tag/01E1).
   It is the ordinary-section affine-open step, with no derived functor or
   cohomology fraction quotient left, and is strictly a part of the old plan.
   Its source, full proof in words, and matching node are present. For empty U
   all numerator and target groups vanish; for zero F likewise. For s = 0 the
   transition with b = 1 kills every numerator and the nonvanishing target is
   empty. For an everywhere nonvanishing s the transitions are isomorphisms and
   the fraction formula is ordinary division by s to the n-th power. No
   cancellation or nonzero assumption has slipped into the statement.
   Independently searched with Lean Finder for localization of quasi-coherent
   sections on affine opens by an invertible-sheaf section, with Loogle for
   `AlgebraicGeometry.Scheme.Modules.restrictAppIso`, and with msearch grep for
   `sectionFraction.*restrict|restrict.*sectionFraction|nonvanishing.*equiv`.
   Also searched the repository's localization/comparison modules and upstream
   module files. The hits supply restriction isomorphisms and ordinary ring
   localization, not this tensor-power fraction theorem. The existing
   `affine_section_localization` is retained as the planned geometric input;
   `nonempty_openModuleCohomology_addEquiv_restrict_H` has no required naturality
   or generator formulas. Closing the remaining hole needs substantial monoidal
   restriction and quotient glue, not an immediate application. Verdict: pass
   as a decomposition, with zero net holes closed.

4. Checked the top proof: it composes the proved fraction comparison, the ordinary
   section equivalence, and the inverse canonical comparison. Injectivity of the
   canonical target comparison, coefficient naturality, the generator formula,
   and open restriction compatibility give precisely the original equation.
   Imports are used by statements/definitions or are private proof imports.
   Repaired the section-only module's unnecessary cohomology import as described
   under No longer needed; all modules compile after that repair. Both old proof
   dependencies (`lem-sc-affine-section-localization` and
   `lem-weil-pbc-module-restriction-open-immersion-colimits`) remain in the new
   section step, so neither is falsely claimed pruned. Read
   `dag/units/sk-thm-curveestimate.json`: its realized statement remains
   `thm-sc-proper-cohomology`, with no realized proof steps to bypass here.
   The original affine-open, degree-zero comparison, and final transport route is
   preserved. Verdict: pass.

5. Read all six delivered node records alongside Lean. The parent proof and
   dependency union describe the actual three-stage composition. The comparison
   and restriction nodes name exactly the constructions used in their proofs;
   the remaining section node retains the original restriction and localization
   dependencies. New nodes carry source, searches, creation, blueprint ancestry,
   chapter/unit, Lean module and declaration records. No existing statement
   metadata is changed. Verdict: pass.

Second reading changed only imports in `OpenSectionFractionPresentation` and
`OpenCohomologyFractionZeroComparison`, and this report. The original proof is
correct as written and was retained. One original hole is closed by decomposition,
one simpler hole is added, and no module is pruned from the target closure.
