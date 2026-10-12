## What changed

Proved `Algebra.smooth_localization_span_from_radical` in
`Sheaf.RingTheory.SingularIdealLocalizationSmooth`, keeping both public signatures
unchanged. The proof maps the ideal-span relation into `A_f`, where its left side
is a unit. It then identifies `(A_g)_f` and `(A_f)_g` by their common localization
at `f * g`, transports smoothness, and applies the existing theorem
`Algebra.smooth_of_localization_span_universes`. No new modules or statements.
Updated both node copies so their proof dependencies match the Lean argument.
The unit's realized statement and steps are unchanged.

## Proved and sorry left

Closed the one original hole: `Algebra.smooth_localization_span_from_radical`
(node `lem-weil-pbc-singular-ideal-localization-smooth-radical-span`).
`Algebra.smooth_localization_of_mem_singularIdeal` was already proved and keeps
its proof. Zero holes remain in this module; zero holes were added.
The existing imported `Algebra.smooth_of_localization_span_universes`
(node `lem-weil-pbc-smooth-of-localization-span-universes`) still has its own
pre-existing sorry, outside this delivery. Thus this proves the assigned hole
from existing statements, rather than claiming an axiom-free closure.

## No longer needed

Removed direct proof imports `Mathlib.RingTheory.RingHom.Smooth` and
`Mathlib.RingTheory.Localization.LocalizationLocalization`. The proof uses the
principal-localization instances and equivalences exposed by
`Mathlib.RingTheory.Localization.Away.Basic` instead. These Mathlib modules may
remain transitively imported elsewhere; no whole-library pruning is claimed.
The wrapper node no longer directly needs
`lem-weil-pbc-localization-of-localization`,
`lem-weil-pbc-smooth-ring-map-principal-localization`, or
`lem-weil-pbc-smooth-ring-map-local-on-cover`: it directly uses the radical-span
node. The first two remain needed by that node. The cover step uses the existing
universe-polymorphic span node, so the old homogeneous local-on-cover node is
not a direct dependency of either delivered theorem. No Sheaf module was removed.

## Where the brief, the DAG or earlier work was wrong

The radical-span node's old proof dependency list omitted the existing
universe-polymorphic span theorem that its module already imported, and named
only definitions despite using localization and smoothness results. The new
record names those results. The wrapper node still recorded the earlier
three-step proof although its Lean already applied the radical-span theorem;
its record now matches that proof.
Searches through LeanFinder, Loogle, the project, and Mathlib found the
localization ingredients but no direct theorem for the whole radical-span
claim. The cited Stacks TeX files are absent from this read-only clone; the
existing source citations and plan were retained, with the actual Mathlib
proofs and signatures checked locally. Edge cases require no added hypotheses:
`n = 0` maps 1 into the span, and nilpotent `f` or a zero ring still satisfy the
unit-based ideal argument. No definition or statement was changed.

## Second reading by A3

1. Compared the delivered module with the repository version. Both theorem signatures are byte for byte unchanged; only the proof, imports, and documentation changed.
2. Compiled `lean/Sheaf/RingTheory/SingularIdealLocalizationSmooth.lean` with the prescribed launcher. It compiles without errors, and the module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition.
3. Checked the proof of `Algebra.smooth_localization_span_from_radical`: the mapped power is a unit in the principal localization, giving the span equality, and each iterated principal localization is transported across the canonical localization equivalence. The argument handles zero powers and degenerate rings without extra hypotheses. No new statements were introduced.
4. Checked pruning and imports. The proof uses the universe-polymorphic span criterion and `Mathlib.RingTheory.Localization.Away.Basic`; the two former direct Mathlib imports were unnecessary and were removed. The wrapper theorem now directly records its radical-span dependency.
5. Checked both DAG nodes against the Lean proofs and confirmed the unit's realized route is unchanged. The node dependency lists now name the declarations actually used by the delivered proofs.

Changed during second reading: added this review record; no Lean statements or proof terms required repair after compilation.
