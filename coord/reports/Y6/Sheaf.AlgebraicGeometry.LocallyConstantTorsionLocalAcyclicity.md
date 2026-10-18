## What changed

Proved `AlgebraicGeometry.Etale.isLocallyAcyclicRelative_of_locallyConstant_torsion`
with its existing signature and public imports unchanged. The proof follows Stacks
Tag 0GJR: identify the canonical map on a strict-local fibre, pass from admissible
cyclic coefficients to finite abelian groups, then pass to the directed union of
finite subgroups of the geometric stalk.

Added two proved helper modules, `Sheaf.AlgebraicGeometry.StrictLocalConstantComparison`
and `Sheaf.AlgebraicGeometry.ConstantTorsionAcyclicDevissage`, and their DAG nodes.
Updated the item's proof and proof dependencies to match the Lean argument, retaining
the source proof origin. The strict-local helper proves the equality for the specified alpha map,
not merely existence of an abstract sections isomorphism. The coefficient helper
constructs the subgroup diagram and its colimit, uses Mathlib's finite abelian-group
decomposition, and applies the existing coefficient-size derived cohomology colimit theorem.
No existing statement or definition changed; no consumer adaptation or change record is needed.

Validation: the server `lcompile.py --all` compiled all three files together without
errors or warnings: coefficient devissage 11.9 seconds, strict-local comparison
16.2 seconds, and the assigned module 20.0 seconds. After restoring the original global `open`
commands and qualifying `Limits` names within the proof, the assigned module
compiled again in 15.8 seconds; the interface checker reports no existing-module
interface change. All Lean lines are at most
100 characters, both new Lean records match their declarations, and every DAG
proof-dependency list is the union of its proof steps.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.isLocallyAcyclicRelative_of_locallyConstant_torsion`
(node `lem-weil-pbc-locally-constant-torsion-local-acyclicity`).

Also proved, without holes:
- `AlgebraicGeometry.Etale.exists_strictLocalConstantComparison`
  (node `lem-weil-pbc-strict-local-constant-comparison`).
- `AlgebraicGeometry.Etale.constantTorsion_acyclic_of_cyclic`
  (node `lem-weil-pbc-constant-torsion-acyclic-devissage`).

Holes closed: 1. Holes added: 0. Holes left in the delivered Lean files: 0.
There are no admitted split-offs. Existing library dependencies are used as declared;
this delivery does not claim to close every transitive hole in the target closure.
The finite-group argument includes the empty biproduct, and the filtered diagram
includes the zero subgroup. Characteristic zero needs no coprimality restriction,
and no bounded exponent or finite stalk assumption is introduced.

## No longer needed

Removed these direct imports from the item:
- `Sheaf.Paper.StrictHenselizationFunctoriality`.
- `WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk`.
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`.
- `Sheaf.Paper.ConstantSheafSectionsLocallyConstant`.
- `Mathlib.GroupTheory.FiniteAbelian.Basic`.
- `Mathlib.CategoryTheory.Sites.GlobalSections`.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`.
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`.
- `Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift`.

Five project modules disappear from this item's import closure:
`ConstantSheafSectionsLocallyConstant`, `KInjectiveResolutions`,
`KInjectiveResolutionsExist`, `FreeSheaf`, and `StrictHenselizationClosedLift`
(with the full paths given above). This does not assert they are unused by other targets.
The four corresponding old proof nodes no longer needed on this route are
`lem-weil-pbc-constant-sheaf-sections-locally-constant`,
`def-weil-pbc-kinjective-resolutions`,
`prop-weil-pbc-kinjective-resolutions-exist`, and
`lem-weil-pbc-cohomology-filtered-colimit`.

The explicit K-injective finite-sum calculation is replaced by the already proved
additivity of the right derived functor. The coefficient-size derived cohomology
colimit theorem replaces the free-module shifted-Hom version. Strict henselian
sheafification and a split trivializing cover replace the locally constant functions
model. The canonical germ-restriction isomorphism supplies the stalk comparison,
without using the separately imported closed-lift module.

Other removed direct dependencies remain needed through the proved helpers or existing
definitions: finite abelian structure, pullback of constant and locally constant sheaves,
strict-local sections/stalks, inverse-image stalk comparison, strict-henselization
functoriality, global sections, and the derived cohomology definitions. They are not
claimed as pruned nodes. The item's top-level `tool_uses` removes the obsolete direct
approvals for `lem-weil-pbc-strict-henselization-functoriality`,
`lemma-constructible-pullback-constant`, `lem-weil-pbc-strictly-henselian-sections-stalk`,
`lem-weil-pbc-inverse-image-stalk-germ`,
`lem-weil-pbc-constant-sheaf-sections-locally-constant`,
`def-weil-pbc-kinjective-resolutions`, `def-weil-pbc-etale-cohomology`,
`lem-weil-pbc-cohomology-filtered-colimit`, and
`prop-weil-pbc-kinjective-resolutions-exist`. Their removal records the new direct route;
necessary transitive uses are described in the helper nodes.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or mathematical error was found. Two planned interfaces were
less direct than the available library APIs. The constant-sections-as-locally-constant
functions declaration has coefficients in `Type u`, whereas the geometric stalk here
lies in `Type (u + 1)`; the strict henselian sheafification argument works at the required
universe. The old colimit import describes free-module shifted-Hom cohomology; the
existing `etaleCohomology_isColimit_of_isFiltered_coefficientSize` declaration directly
handles the derived abelian cohomology functor in this statement and permits the
subgroup index in `Type (u + 1)`. Neither observation required a statement repair.

## New nodes

`lem-weil-pbc-strict-local-constant-comparison` records the geometric part of step 1
of the 0GJR argument, including the exact canonical-map compatibility. Its Lean module
is `lean/Sheaf/AlgebraicGeometry/StrictLocalConstantComparison.lean`; the theorem and
its five private categorical helper lemmas are all proved. It assumes neither torsion
nor local acyclicity, so it is strictly a part of the assigned argument.

`lem-weil-pbc-constant-torsion-acyclic-devissage` records the coefficient part of
0GJR: finite cyclic decomposition and filtered colimits on an arbitrary qcqs scheme.
Its Lean module is `lean/Sheaf/AlgebraicGeometry/ConstantTorsionAcyclicDevissage.lean`;
the theorem is proved. It contains no strict-local scheme, morphism acyclicity, geometric
point, or locally constant sheaf. Searches of the imported blueprint found no duplicate;
LeanSearch, LeanFinder and source grep are recorded for both new nodes.

The generic tool uses for the new helper nodes are
`lem-sbc-strict-henselian-etale-neighbourhood-section` (splitting a trivializing
cover over a strict local ring), `lem-weil-pbc-strict-local-germ-restriction-iso`
(the canonical stalk-to-sections comparison), and
`lem-weil-pbc-etale-directed-cohomology-colimit` (coefficient-size colimits).
They supply infrastructure below the existing 0GJR argument; no unit statement or
unit proof step is bypassed. New maintainer tool approvals are left to the reader.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
