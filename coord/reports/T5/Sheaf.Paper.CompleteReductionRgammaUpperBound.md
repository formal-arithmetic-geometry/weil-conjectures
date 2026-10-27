## What changed

Reduced the original theorem, with its statement unchanged, to two strictly separate
geometric steps: the normalized resolution of the tensor-reduction tower and the Roos
triangle on its derived reduction sections. The first is independent of completeness
and cohomological bounds; the second asserts the triangle and has no upper-bound or
completion assumption. Neither restates the original theorem.

Proved the intermediate Milnor exact-sequence theorem from the existing
`CategoryTheory.milnor_shortExact`, transporting the triangle along the specified
isomorphism. In the main proof completeness makes the specified augmentation invertible;
cancellation makes Q(a) invertible and therefore so is its derived section comparison.
For the bound, q>h+1 gives q-1>h and q>h. Both cohomology towers are zero; the additive
first right-derived inverse limit and ordinary inverse limit are zero. Exactness forces
the middle group to vanish. This is a decomposition, not a proof of the geometric inputs.

Moved the four original ordinary section constructions verbatim to
`Sheaf.Paper.CompleteReductionSectionsModel`, publicly imported by the original item,
to allow independent statement modules without import cycles. The original five public
imports remain. Change record: `coord/changes/T5-complete-reduction-sections-model.md`.
`tools/downstream.py` finds zero downstream modules and only this item using the four
names. No target signatures, definition bodies or external consumers change.

Searches used the launcher LeanFinder, Loogle, LeanSearch and grep interfaces, plus
local rg across Mathlib, WeilConjectures and Sheaf. Search results supplied generic
vanishing/derived-category tools, but no normalized reduction-section comparison.
The existing Milnor theorem is reused rather than redeclared as an unfinished result.
The source is Stacks Cohomology on Sites, Tags 0D6K, 0A07 and 0941, with the original
completion-unit construction and More on Algebra, Tags 07KY and 08U5.

## Proved and sorry left

Original holes: 1, in
`AlgebraicGeometry.ProEtale.CompleteReductionSections.complete_reduction_rgamma_upper_bound`.
Its proof is replaced by a complete assembly from the two intermediate statements.

New proved theorem:
`AlgebraicGeometry.ProEtale.CompleteReductionSections.reduction_sections_milnor`.

Two new holes, each exactly a named public theorem `:= by sorry` in its own module:

- `AlgebraicGeometry.ProEtale.CompleteReductionSections.reduction_sections_normalized_resolution`
  (node `lem-sfb-reduction-sections-normalized-resolution`).
- `AlgebraicGeometry.ProEtale.CompleteReductionSections.reduction_sections_roos_triangle`
  (node `lem-sfb-reduction-sections-roos-triangle`).

Thus 1 upper hole is decomposed into 2 strictly smaller geometric steps; the delivery
has 2 actual holes and does not claim a net sorry reduction. The shared definition module
has zero holes. Validation is through lcompile and the delivery preflight.

## No longer needed

The main proof no longer directly imports:
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`,
`Mathlib.CategoryTheory.Sites.ConstantSheaf`,
`Mathlib.CategoryTheory.Sites.Sheafification`,
`Mathlib.CategoryTheory.Sites.LeftExact`,
`Sheaf.CategoryTheory.RingedToposMorphism`,
`Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`,
`Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`,
`WeilConjectures.CategoryTheory.Triangulated.MilnorSequence`, or
`WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups`.
The new Milnor module imports the existing Milnor sequence and therefore retains its
Roos-derived-limit dependencies. The normalized comparison's proof plan retains the
internal/sectionwise equivalence, constant sheaf, sheafification, exact sheafification,
ringed-topos morphism, direct-image/limit comparison, and strict derived-limit nodes.
They are delegated to that step, not globally pruned. The unfinished normalized-resolution
module does not import these proof-plan dependencies before they are actually used.
No blueprint unit statement or realized proof step is bypassed. No module is withdrawn.

The separate zero-tower kernel/cokernel computation in the original node's final step
is unnecessary: additive functors preserve zero objects and limits of zero diagrams
are zero. The node `lem-pc-derived-limit-roos-abelian-groups` remains needed by the
existing Milnor sequence, so this is only a simplification of the final deduction.

## Where the brief, the DAG or earlier work was wrong

The stated ringed-tower comparison uses sectionwise module categories on small sites;
the item uses internal modules on a pro-etale site with independent universes and
requires a comparison normalized by the original augmentation. Applying that API is
not a single specialization. The unresolved internal/sectionwise and normalization
glue is now an explicit independent step. The original node's unit metadata points at
an older location; the current blueprint unit is under sec-six-functors-basics. The
unit's mathematical route is retained. No statement is disputed.

## New nodes

`def-sfb-complete-reduction-sections-model` attaches the four unchanged ordinary section
constructions needed in the new statements. Its source is Stacks Tags 0D6K and 0941.

`lem-sfb-reduction-sections-normalized-resolution` isolates the resolution, limit lift,
normalized derived-section comparison, and conditional invertibility of Q(a).
Its sources are Stacks Tags 0D6K, 0A07, 0941 and the existing completion augmentation.

`lem-sfb-reduction-sections-roos-triangle` identifies the section Roos fibre as the
actual derived inverse limit of canonical derived reduction sections. Its sources
are Stacks Tags 0D6K and 0941 and More on Algebra Tag 08U5.

`lem-sfb-reduction-sections-milnor` records the proved specialization and transport of
the existing Milnor sequence to the resolved reduction tower. Its sources are Stacks
Tag 0D6K and More on Algebra Tags 07KY and 08U5.

All four nodes record LeanSearch, LeanFinder/Loogle and grep searches. No imported
blueprint node states these normalized internal-module interfaces. The general Milnor
sequence already exists and is directly applied in the proved intermediate theorem.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
