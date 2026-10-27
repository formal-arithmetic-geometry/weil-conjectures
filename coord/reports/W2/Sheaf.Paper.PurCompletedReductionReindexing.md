## What changed

Replaced the sorry in AlgebraicGeometry.Scheme.purCompletedReductionReindexing by a
complete Lean reduction. The assembly proves strict diagram and derived equivalences
from the ordinary module equivalence using two generic proved helpers, constructs the completed-pullback inverse from
the actual completion unit, checks its inverse equation by cancellation, uses the
existing pure-tensor and all-transition formulas, constructs the chosen Cartesian
square, and derives invertibility of the ordinary tower mate by whiskering.

Moved the seven original map/predicate definitions into
Sheaf.Paper.PurCompletedReindexingData, publicly re-exported by the original module,
to let the strictly smaller steps import their concrete maps without an import cycle.
Change record: coord/changes/pur-completed-reindexing-data-relocation.md.
All original public imports and declaration signatures are retained. Four bodies are
verbatim; the tower-mate body calls a generic wrapper that unfolds to the identical
whiskering map. Each predicate is the same conjunction of newly named literal
clauses, which are also used by the split statements. This avoids kernel comparison across the full tensor constructions.
Local irreducibility prevents elaborator expansion of the same large definitions.
The six downstream consumers found by tools/downstream.py require no source edits.

## Proved and sorry left

One original hole closed by decomposition:
AlgebraicGeometry.Scheme.purCompletedReductionReindexing
(lem-pur-isomorphism-completed-reduction-reindexing).
The private reindexingAt, reindexingSquare and generic categorical helpers contain no holes.

Four holes added, each in its own new module with a source and complete proof in words:

- AlgebraicGeometry.Scheme.purCompletedModuleReindexing
  (lem-pur-completed-module-section-reindexing): ordinary completed-module section
  normalization and inverse functor, omitting all tower and derived assertions.
- AlgebraicGeometry.Scheme.purReindexingLimitNormalization
  (lem-pur-reindexing-limit-unit-normalization): the projection/derived-unit comparison
  and its augmentation equation; it does not assert a completed-pullback inverse.
- AlgebraicGeometry.Scheme.purReindexingOrdinaryMate
  (lem-pur-reindexing-ordinary-mate-sections): ordinary section mate only.
- AlgebraicGeometry.Scheme.purReindexingDerivedMates
  (lem-pur-reindexing-derived-mate-localization): localizing an invertible ordinary
  mate, including strict diagrams; it assumes ordinary mate invertibility.

This is a decomposition, not a net proof closure: 1 original hole replaced by 4
strictly smaller holes. No sorry remains in the item module or the data module.
No axiom, hollow definition, or source-library edit is introduced.

Validation: the data module and each of the four split statements compiled through
lcompile.py. The data's slow tower-mate kernel comparison was eliminated by the
generic wrapper. The packet uses no transparency-check-disabling options. All original
public signatures and visibility match the source, and all node Lean records match
the declarations. The predicate clauses were then named to share their fully typed expressions after
profiling exposed repeated kernel checking. The final packet compiled all five
prerequisite modules in 25-34 seconds each; the assembly then ran in 39 seconds,
with four instance-type annotations corrected for the named clauses. The corrected
assembly compiled successfully in 47.4 seconds. Delivery preflight is the remaining
required check.

## No longer needed

Removed these original private proof imports from the item:

- Sheaf.Paper.SfBcAdicRingDomain
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.Paper.KoszulReconstruction
- Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
- Sheaf.CategoryTheory.DiagramSiteRealization
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
- Mathlib.CategoryTheory.Abelian.FunctorCategory
- Mathlib.CategoryTheory.Localization.Predicate
- Mathlib.CategoryTheory.Adjunction.Mates
- Sheaf.CategoryTheory.ExactAdjointTowerModels
- Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
- Sheaf.Paper.IntegralFinitePullbackComposition
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

The direct reduction route uses the already proved levelPullIso_tensor and
completedReductionLevelPullbackIso_transition from CompletedDirectImageLimits,
and the existsUnique characterization of reductionTowerPullbackIso. Thus the item
needs no new diagram-site K-flat tensor construction. Its direct DAG proof no longer
uses lem-sf-bc-adic-ring-domain, lem-pc-kflat-resolution, def-pc-kflat-complex,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback or prop-weil-pbc-koszul-reconstruction:
the datum already supplies its coefficient facts and TowerComplete is the specified
completion-unit invertibility predicate. The other old categorical dependencies are
used by the smaller normalization nodes rather than directly by the assembly.
No entire module is withdrawn and no dependency is claimed globally unreachable;
the library may still use these imports and nodes elsewhere, including transitively.

## Where the brief, the DAG or earlier work was wrong

The plan's separate K-flat tensor construction duplicates already proved ordinary
reduction formulas. Its Koszul reconstruction invocation is unnecessary for this Lean
signature, whose completion hypothesis is TowerComplete. The ordinary module theorem
must be about the completed ring; the existing constant-ring equivalence alone does
not supply it. No mathematical statement is changed or marked disputed.

Edge cases checked at the statement level: identity and empty schemes, K = 0,
positive quotient exponent n+1 at n = 0, identity and nonconsecutive tower arrows,
unbounded complexes, and noncomplete K in the augmentation equality. Only the final
completed-pullback inverse uses completeness. There is no boundedness, constructibility,
base-linearity or extra coefficient assumption.

## New nodes

lem-pur-completed-module-section-reindexing isolates the ordinary transport step.
lem-pur-reindexing-limit-unit-normalization isolates the comparison of the actual
limit projections and quotient augmentation.
lem-pur-reindexing-ordinary-mate-sections isolates the ordinary section calculation.
lem-pur-reindexing-derived-mate-localization isolates the localization of its transpose
on modules and strict diagrams. All inherit sec-six-functors/sk-thm-sf-package,
retain the extracted source route, and have their own Lean statements and proof steps.

def-pur-completed-reindexing-data records relocation of the seven existing concrete
definitions the generic purWhiskerCompositeMap wrapper, and named literal predicate clauses,
with no new proof hole.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
