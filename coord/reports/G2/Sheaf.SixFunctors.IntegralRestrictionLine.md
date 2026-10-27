## What changed

The unchanged integralRestrictionLine statement now has a complete Lean assembly proof. Private proved helpers establish constructibility preservation, extension to Loc(Dbc), proper pushforward preservation, compactification transport, and comparison with every Brown right adjoint. The geometric source arguments are isolated into three smaller public theorems. The five existing definitions move verbatim to IntegralRestrictionFunctors, publicly re-exported by the item; their meanings and names are unchanged. No WeilConjectures file or target signature changes.

The item and all four new modules compiled. The final item compile was clean in 37.7 seconds. The new statements were checked at d=0, zero complexes and empty base: Tate degree zero is the unit; A^0 is canonically the base; full-subcategory preservation witnesses are proof-irrelevant. Projective and affine adjunction claims supply adjunctions only, without the other clauses of the item. No false statement or arbitrary witness is introduced.

## Proved and sorry left

Original holes: 1, integralRestrictionLine. Its proof body now has zero sorry. The private theorems twistedPull_constructible, twistedPull_localizing, properPush_localizing and properBrownComparison are fully proved; liftIso, space, properImageIso and residueUnits contain no holes. The main proof combines preservation with the two adjunctions and right-adjoint uniqueness in Lean.

This is a decomposition, not a net hole reduction: 1 original hole closed syntactically, 3 new holes added (net +2). All three remaining holes are named public theorems, each strictly a part of the source argument:

- AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction.integralTateLine_constructible — lem-sfb-integral-tate-line-constructible; only the signed line in degree zero, no functor preservation or adjunction.
- AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction.integralProjectiveLine_adjunction — lem-sfb-integral-projective-line-adjunction; only the projective adjunction, taking preservation as input, with neither Brown comparison nor affine or constructibility clauses.
- AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction.integralAffinePurity_induction — lem-sfb-integral-affine-purity-induction; only the affine compact-support adjunction by the standard chart and coordinate induction, with neither Brown comparison nor preservation conclusions.

No sorry remains in the item or in any definition. The remaining source obligations are transport from slice trivializations to the internal constructibility predicate, the integral diagonal-kernel unit/counit construction and triangles, and the affine chart/coordinate functor comparisons. Existing rational-only or ordinary finite-tower adjunctions do not type as these internal unbounded integral adjunctions. Their hypotheses and coefficient categories were checked before making these source subarguments explicit.

## No longer needed

No module is globally withdrawn or claimed pruned. Diagonal/trace, Cartesian-twist and affine-chart dependencies remain needed in the isolated source arguments; moving them out of the assembly is not global pruning. In particular no upstream declaration is removed.

The following direct imports were removed from the item:

- Mathlib.AlgebraicGeometry.ZariskisMainTheorem
- Mathlib.CategoryTheory.Adjunction.Mates
- Sheaf.AlgebraicGeometry.AffineTraceTower
- Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias
- Sheaf.Paper.CartesianCoefficients
- Sheaf.Paper.DiagonalTowerLimit
- Sheaf.Paper.FormalClosedSupportSheaves
- Sheaf.Paper.IntegralExtensionByZero
- Sheaf.Paper.IntegralOpenImageProperFormulas
- Sheaf.Paper.IntegralProperProjectionFormula
- Sheaf.Paper.LocalizingClosureCtfEqualsBc
- Sheaf.Paper.ProjectionSectionNormalization
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.Paper.TraceBaseChangeFirst
- Sheaf.Paper.TraceBaseChangeSecond

The following old direct parent proof dependencies no longer occur in the assembly; their uses in the geometric lemmas or statement interface remain recorded there:

- def-amb-affine-trace-tower
- def-sfb-dc-open-lower-shriek-adjunction
- def-weil-pbc-adjunction-mate
- def-weil-pbc-composite-adjunction
- def-weil-proper-morphism
- det-cor-int-compactness-ii-extension-zero
- det-def-localizing-closure-ctf-equals-bc
- det-lem-formal-closed-support-sheaves
- det-prop-diagonal-tower-coefficients
- det-prop-diagonal-tower-limit
- det-prop-diagonal-tower-trace
- det-prop-int-brown-adjoint
- det-thm-sf-pf-adic-projection
- lem-sfb-projection-section-normalization
- lem-sfb-trace-base-change-first
- lem-sfb-trace-base-change-second
- lem-weil-pbc-closed-immersion-proper
- lem-weil-pbc-ringed-topoi-derived-tensor-pullback
- sk-def-localizing-closure
- sk-def-sfb-constructible
- sk-def-sfb-module-pushforward-pullback
- sk-def-sp-tate-twist
- sk-prop-sfb-cartesian-coefficients
- sk-thm-sf-pf-adic

The Loc(Dctf)=Loc(Dbc) conversion is unnecessary for this assembly: both restrictions and compact-support construction already use the exact same Loc(Dbc) predicate. Zariski Main and adjunction-mate imports are unnecessary for the preservation/uniqueness glue; the geometric properness and charts use their existing declarations. No new target dependency is falsely counted as pruned.

## Where the brief, the DAG or earlier work was wrong

There is no disputed mathematical statement. The planned proof mixed the source bounded-constructible predicate with the constant-model predicate: the assembly explicitly uses adicConstructibilityPredicateComparison on the standing noetherian compact schemes. The tensor functor's triangulated instance requires its specified derived CommShift structure; that structure is now explicit. The restored item source and quarantine/rework row were read before copying. No archive is deleted. The original unit route (projective line, affine chart, coordinate induction) is preserved.

## New nodes

- def-sfb-integral-restriction-functors: records relocation of the five existing canonical functors without changing their definitions.
- lem-sfb-integral-tate-line-constructible: the local rank-one, single-stratum, degree-zero part of paragraph (3).
- lem-sfb-integral-projective-line-adjunction: the diagonal unit, integral trace counit and two triangles of paragraph (1).
- lem-sfb-integral-affine-purity-induction: the standard affine chart and dimension induction of paragraph (2).

Each new theorem has its source, complete proof in words, Lean attachment and recorded searches. Whole-blueprint searches for Tate constructibility, projective-line adjunction and affine-space induction were checked: the ordinary finite-coefficient/tower projective adjunctions have different ambient categories. None states the needed integral internal assertion. The existing compound node is retained and its proof dependencies updated to the actual assembly. Change record: coord/changes/G2-integral-restriction-functors.md.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
