## What changed

In `Sheaf.Paper.CompleteCompactSupportProetale`, prove `cbcOpenUnit_isIso` by transporting
modules along the normalized completed slice coefficient isomorphism, deriving that module
equivalence, and composing with fully faithful localized derived extension. The existing
private module-transport proof and localized derived unit theorem are reused with private
`import all` imports.

Prove `completeCompactSupportProetale_isIso`, including its entire naturality clause, from
completed open exchange and the finite-witness form of completed proper base change.
A private proved helper converts intrinsic completeness to tower completeness by the
Koszul/quotient unit comparison. A second private proved helper assembles completed
proper exchange into its actual natural transformation, so naturality applies to every
morphism of ambient derived objects, including the second object without origin data.
The final Lean proof combines the two naturality squares using functoriality.

Add `Sheaf.Paper.CompletedOpenFiniteEtaleOrigins` for the distinct source lemma that
quotient reductions of completed-coefficient open extension retain bounded-below etale
origins. This is precisely the first paragraph's finite-origin preservation assertion;
its hypotheses need neither completeness, quasi-compactness, compatibility nor a common
lower bound. Its proof remains a named hole with a detailed source proof and DAG node.
The parent proof no longer needs to construct compatible origins for the open extension.

Validation: both sandbox modules compile through `lcompile.py`; the new origin module
took 2.7 seconds and the item took 9.9 seconds, with no warnings. The source diff
changes only the two theorem proofs, private proved helpers and proof imports.

All existing public signatures, definitions, visibility and public imports are unchanged.
No source-library module or target is edited. The main node's proof and dependencies now
record these arguments; its unfinished coherence proof plans remain.

## Proved and sorry left

Two original holes are closed:

- `AlgebraicGeometry.Scheme.cbcOpenUnit_isIso`.
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_isIso`, by reduction to the
  separately stated finite-origin preservation lemma and existing dependencies. This is
  a decomposition of the main invertibility argument, with a fully proved combining
  argument and fully proved naturality, rather than an axiom-free completion.

One hole is added:

- `AlgebraicGeometry.Scheme.cbcCompletedOpenFiniteEtaleOrigins` in
  `Sheaf.Paper.CompletedOpenFiniteEtaleOrigins`, node
  `lem-cbc-completed-open-finite-etale-origins`.

The following eleven original holes remain unchanged in the item, all attached to
`thm-cbc-complete-proetale`:

- `AlgebraicGeometry.Scheme.cbcRestrictionUnit_existsUnique`.
- `AlgebraicGeometry.Scheme.cbcPullToRestriction_isIso`.
- `AlgebraicGeometry.Scheme.cbcBetaInv_isIso`.
- `AlgebraicGeometry.Scheme.cbcOpenToPush_isIso`.
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_identity`.
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_horizontal`.
- `AlgebraicGeometry.Scheme.cbcRefinementMap_isIso`.
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_compactifications`.
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_refinement`.
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_vertical`.
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_composition_refinement`.

Thus the item has 11 of its original 13 holes left; the packet has 12 holes including
the one new, strictly narrower lemma. The two private helpers have complete proofs.
No anonymous, private or definition hole is added.

## No longer needed

Remove the following 33 unused private proof imports from the item:

- `Mathlib.Algebra.Category.Grp.FilteredColimits`.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`.
- `Mathlib.CategoryTheory.Sites.Limits`.
- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`.
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`.
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`.
- `Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`.
- `Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting`.
- `Sheaf.CategoryTheory.DiagramSiteRealization`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.
- `Sheaf.Paper.CompletedDirectImageLimits`.
- `Sheaf.Paper.CompletedPullbackReduction`.
- `Sheaf.Paper.CompletedRlimFunctor`.
- `Sheaf.Paper.ExactProductFunctorStrictLimit`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`.
- `Sheaf.Paper.KoszulReconstruction`.
- `Sheaf.Paper.PbcQbarCompletedPullback`.
- `Sheaf.Paper.RefinementExchangeCoherence`.
- `WeilConjectures.Algebra.Homology.RoosComplex`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`.
- `WeilConjectures.Compactification.CategoryBaseChange`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`.

The proof does not import `Sheaf.Paper.CompleteProetaleStrictTowerRealization`.
Naturality follows directly from the actual three-factor completed proper exchange
and the completed open exchange, and invertibility follows from their isomorphisms.
The strict realization and generic proper/open coherence dependencies remain in the
DAG for the eleven unfinished clauses; none of those nodes is withdrawn. No global
module pruning or source-library declaration removal is claimed.

## Where the brief, the DAG or earlier work was wrong

The direct strict-realization route has a Lean import cycle:
`CompleteProetaleStrictTowerRealization` publicly imports this item and uses its
section-normalized adjunction helpers. It cannot be imported back here unchanged.
This packet avoids that dependency for invertibility and naturality; the remaining
coherence route will need the shared adjunction interface factored before direct use.

The declared open comparison supplies completeness of the open extension, but no
existing declared theorem directly supplies the required finite etale origins for
arbitrary adic quotient coefficients. `ReductionOpenEtaleOrigin` supplies useful
underlying comparison maps; its main statement concerns an integral coefficient
extension datum and bounded constructibility, which cannot be imposed here.
The new lemma isolates exactly the missing assertion already present in the source.
Its proof must retain quotient-ring linearity before scalar restriction: restriction
along a quotient is not fully faithful on unbounded derived categories.

The general left-derived adjunction API introduced irrelevant flatness and universe
constraints in the open-unit argument. The existing exact localized derived adjunction
and module equivalence give the needed fully faithful left adjoint directly.

## New nodes

`lem-cbc-completed-open-finite-etale-origins` realizes the source's assertion that the
reductions of `j_!K` carry the etale witnesses `j_!L_n`. Its edge cases include the
empty open and zero quotient ring, and it requires only each antecedent's own lower
bound. Its node records all three search classes (LeanSearch, LeanFinder/Loogle,
and grep), the exact Lean statement, coefficient-linear tensor/open comparison,
constant/function transport, etale/pro-etale open comparison, and exactness argument.
No change record is needed: existing statements and definitions are untouched.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
