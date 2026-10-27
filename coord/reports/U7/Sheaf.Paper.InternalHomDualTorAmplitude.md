## What changed

Replaced the whole proof of
`AlgebraicGeometry.ProEtale.internalHom_dual_tor_amplitude` by an explicit
finite-cover argument, with its statement and all three existing definitions
unchanged. The empty-scheme case is proved directly from terminal sections over
empty objects. The nonempty case uses the existing, proved
`Scheme.finite_affine_proetale_refinement`, normalizes each selected model's
endpoints, takes attained finite extrema, and widens both the original and
reflected local intervals. A proved private helper applies the sheaf
local-isomorphism criterion on base changes of the affine covering, factoring
through the selected original charts. The module forgetful functor reflects
zero by faithfulness. The private helper registers localization restriction as
additive by its componentwise formula, supplying zero-morphism preservation.

The local coefficient and derived-Hom interface work is isolated as
`AlgebraicGeometry.ProEtale.scalarPerfect_chart_tor_vanishing` in the new module
`Sheaf.Paper.ScalarPerfectChartTorVanishing`. This theorem has supplied, ordered
endpoints and a model on one chart. It asserts vanishings after restriction to
that chart; it makes no global existence or descent claim. The main theorem's
finite choice of uniform endpoints, endpoint inequalities, empty case and cover
descent are complete Lean proofs. Updated the main node's proof and dependencies
accordingly. All original public imports are retained. Added only the four
proof imports used by the main argument: finite affine refinement, the new local
lemma, the existing cover-local sheaf API, and finite extrema.

## Proved and sorry left

Original item: one hole,
`AlgebraicGeometry.ProEtale.internalHom_dual_tor_amplitude`
(node `lem-sfb-internal-hom-dual-tor-amplitude`). Its proof is now complete from
the new local statement. The private helpers `isZero_sheaf_of_refined_cover`
and `isZero_sheaf_on_empty` are proved without holes.

Added one hole:
`AlgebraicGeometry.ProEtale.scalarPerfect_chart_tor_vanishing`
(node `lem-sfb-scalar-perfect-chart-tor-vanishing`). Its entire proof is
`:= by sorry`, in its own module with a source and detailed proof in words.
There are zero remaining holes in the item module and one in the delivery.
This is a decomposition: one upper hole closed, one strictly local hole added,
net zero holes closed; it is not reported as an axiom-free proof of the original
mathematical theorem. No definitions contain holes or choose arbitrary data
from an unproved existence statement.

## No longer needed

The stronger `lem-sfb-finite-scalar-perfect-refinement` /
`Sheaf.Paper.FiniteScalarPerfectRefinement` interface is not needed by this proof.
Only its already proved finite affine cover refinement is used. The original
models stay on their original charts; the affine opens are used just to certify
that the selected original charts detect vanishing. This avoids reconstructing
scalar models, splittings and representing isomorphisms on the smaller opens.

`lem-sfb-tor-interval-local-detection` /
`Sheaf.AlgebraicGeometry.ProEtaleTorIntervalLocalDetection` is not needed by this
proof: descent is proved directly for the relevant underlying abelian
cohomology sheaves. No assertion is made that either module is globally unused.

The local comparison and split-perfect dual-window mathematics remains needed
by the new chart lemma. In particular
`lem-sfb-module-object-ringed-site-derived-comparison`,
`lem-sfb-split-perfect-dual-tor-window`, exact module restriction and canonical
derived tensor pullback are not claimed to be pruned transitively. The existing approvals for the comparison, Hom restriction, exact module
restriction, tensor pullback and cover-local isomorphisms are retained. Removed
only these obsolete direct tool approvals, superseded by the local split-perfect
window calculation or the explicit global descent:
`lem-sc-finite-free-internal-hom-exact`,
`lem-pc-bounded-exact-term-hom-quasi-iso`, `lem-sp-ringed-site-tor-flat-model`,
and `lem-sfb-tor-interval-local-detection`. No new approval is added.

Removed these direct proof imports from the item module (some remain exported
transitively by its unchanged public imports or needed below the new local
lemma; removing a direct import is not a claim of whole-library pruning):

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Sites.Proetale`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact`
- `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Paper.CoefficientRingedTensorHomModel`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`
- `WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `WeilConjectures.Algebra.Homology.HomComplex`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `Sheaf.Algebra.Homology.RingedSiteTorFlatModel`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison`

## Where the brief, the DAG or earlier work was wrong

The module docstring described the older seven-step route, while the current
DAG had already been re-split into four steps. Its description of the admissible
coefficient predicate also still mentioned all continuous functions into the
algebraic closure, which the current six-case predicate no longer includes.
Updated this explanatory text without changing any signature or hypothesis.

The refinement and dual-window declarations exist and were read before the
split. They are stated for section-ring module sheaves and scalar complexes of
ordinary modules, while the assigned hypothesis uses internal condensed module
objects. The comparison theorem supplies ringed-site and internal-module Hom
and tensor comparisons, but applying these to the specific point-to-chart
scalar complex, its splittings, and the small-pro-etale localization requires
interface glue. That precise local calculation is the only remaining hole;
none of the global proof is merely renamed or moved to it.

Read the current blueprint internal-Hom stability proof, paragraphs 2--3, and
Stacks sites-cohomology.tex Tags 08JH, 08JJ, 08G1 and 07A4. Semantic searches with
LeanFinder and LeanSearch returned ordinary projective Tor or cohomological
support results; Loogle did not know the project's Tor-amplitude predicate.
Direct searches of Mathlib and both library roots found the existing
split-perfect window theorem, the finite affine refinement theorem and the
ringed-site comparison, but no theorem giving this exact internal-module chart
calculation. No unit statement or unit proof step is bypassed.

## New nodes

`lem-sfb-scalar-perfect-chart-tor-vanishing`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-scalar-perfect-chart-tor-vanishing.json`,
is attached to `Sheaf.Paper.ScalarPerfectChartTorVanishing`. It is the fixed
local signed-dual/tensor calculation, before finite-cover selection and global
vanishing detection. Its source, proof steps, Lean signature, statement
dependencies and all three kinds of Mathlib search are recorded. Its proof
uses the already declared comparison and dual-window statements and exact
restriction/tensor pullback. The comparison, pro-etale localization and tensor-pullback nodes are
generic tools already used by the old parent route or its detection proof; their uses on this new
local node are for the independent reader to approve. No approval entries were
invented.

Checked the new statement mathematically on the zero complex, rank-zero
splittings, an empty chart, and a regular coefficient module in any single
degree d: the asserted intervals are [d,d] and [-d,-d]. The proof never treats
admissible condensed coefficients as discrete constant coefficients, and does
not assume the test module is flat. No change record is needed: all existing
public signatures, definitions and public imports are unchanged.

The delivered node overlay has an acyclic 1,755-node statement/proof dependency
closure. Direct text checks confirm that `scalarExtensionComplex`,
`FiniteProjectiveCondensedModule`, and `relativeInternalHomDual` are unchanged,
and that all eight existing public import lines are identical. New Lean lines
are at most 100 characters. The final single-file compilation and delivery preflight are the remaining
validation steps. Earlier compiler runs found and resolved zero-object notation,
an isomorphism direction, the cover weak-etale instance and localization
restriction additive instance; no theorem signature was changed in these repairs.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
