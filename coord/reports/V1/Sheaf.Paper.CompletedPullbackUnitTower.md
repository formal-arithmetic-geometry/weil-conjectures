## What changed

Proved `AlgebraicGeometry.Scheme.CompletedPullbackUnitTower.completedPullbackUnitTower`
with its existing statement unchanged. The proof inverts the reduction of the
completion unit, detects invertibility through levelwise cohomology, constructs
the strict natural tower isomorphism, and identifies its components with the
specified finite projection adjuncts.

Added three proved public lemmas, each in its own module:
`CategoryTheory.AdicSites.completionUnitFiniteProjection`,
`CategoryTheory.AdicSites.completionFiniteReduction`, and
`CategoryTheory.AdicSites.reductionPullFiniteEvaluation`.
Also proved `AlgebraicGeometry.Scheme.CompletedPullbackUnitTower.inverse_finiteLimits`
by transporting finite-limit preservation through the small-model equivalences,
then using Mathlib's constructed sheaf pullback comparison.
Also proved
`AlgebraicGeometry.Scheme.CompletedPullbackUnitTower.canonicalInverseImageData_existsUnique`: the actual ring and module adjunction units
normalize the underlying comparisons, their operation graphs, and the constant
comparison. Extensionality and injectivity of the adjunction hom equivalence
prove uniqueness.
The first new lemma checks the limit/unit normalization; the second uses completeness of
restricted quotient complexes and the completion reflector; the third proves
compatibility of the specified pullback and finite-evaluation comparisons.
All new imports in the item are private proof imports. Its existing public signatures,
public imports, and non-theorem definitions are unchanged.

Repaired three complex-comparison definitions in the unclaimed module
`Sheaf.Paper.CompletionMateComparison` to retain explicit iterated complex endpoints.
Added the proved APIs `Sheaf.CategoryTheory.ComplexFunctorSquare` and
`Sheaf.Paper.QuotientTowerEvaluationComplex`. The former proves equality with the
original degreewise comparison; the latter proves that the inserted finite evaluation
comparison is the identity in each degree. Thus the normalized maps keep their
mathematical meaning. The change record is
`coord/changes/completed-pullback-explicit-complex-comparisons.md`.
The module inverse-image functor stays the unchanged `abbrev` of the base, with a
proved named additivity instance. (Reviewer correction, 2026-10-21: the delivered
`abbrev` to `def` change broke instance search for `(f.modulePull A).Additive` in the
direct importer `Sheaf.Paper.OrientedNearbyCycles`; restoring the `abbrev` costs no
measurable compile time.)
No adopted-source declaration is changed.

Validation: every delivery module compiled through `lcompile.py`. The final
finite-comparison module compiled in 53.5 seconds; the final item compiled in
30.9 seconds. No compiler time limit was changed.

The finite-quotient completeness proof includes the zero ideal, unit ideal,
zero ring, and level zero: quotient images of ideal elements are nilpotent in
all these cases. The comparison proof works for every derived input; it needs
Noetherianness only for the existing quotient section API. The original completeness
hypothesis is retained unchanged.

## Proved and sorry left

Closed the completed-tower theorem hole:
`AlgebraicGeometry.Scheme.CompletedPullbackUnitTower.completedPullbackUnitTower`
(`lem-sf-cbc-completed-pullback-unit-tower`).

Also closed the existing geometric left-exactness hole
`AlgebraicGeometry.Scheme.CompletedPullbackUnitTower.inverse_finiteLimits`
(`lem-sf-cbc-completed-pullback-unit-tower`).

Also closed the existing canonical algebraic construction hole
`AlgebraicGeometry.Scheme.CompletedPullbackUnitTower.canonicalInverseImageData_existsUnique`
(`lem-sf-cbc-completed-pullback-unit-tower`).

The three new public lemmas and all private helpers are proved. This packet closes
all three original holes, adds no holes, and splits off no holes. The item, its
three new theorem modules,
and its two new API modules have zero `sorry`. The edited existing
`CompletionMateComparison` retains its existing postponed proofs without adding or
removing any. Existing postponed proofs imported from the library remain their items.

The 21 unchanged holes in the repaired comparison module are:

- `CategoryTheory.AdicSites.Morphism.modulePull_properties`
- `CategoryTheory.AdicSites.Site.hasKInjectives`
- `CategoryTheory.AdicSites.Site.towersHasKInjectives`
- `CategoryTheory.AdicSites.Site.completion_properties`
- `CategoryTheory.AdicSites.Site.reflectorAdjunction_existsUnique`
- `CategoryTheory.AdicSites.Morphism.push_complete`
- `CategoryTheory.AdicSites.Morphism.completeAdjunction_existsUnique`
- `CategoryTheory.AdicSites.Morphism.towerModulePull_exact`
- `CategoryTheory.AdicSites.moduleSquare_existsUnique`
- `CategoryTheory.AdicSites.Site.deltaAdjunction_existsUnique`
- `CategoryTheory.AdicSites.Morphism.moduleReductionPullIso_existsUnique`
- `CategoryTheory.AdicSites.Morphism.reductionPullIso_existsUnique`
- `CategoryTheory.AdicSites.Morphism.evaluatePushIso_existsUnique`
- `CategoryTheory.AdicSites.Site.finiteModuleAdjunction_existsUnique`
- `CategoryTheory.AdicSites.Site.finiteAdjunction_existsUnique`
- `CategoryTheory.AdicSites.Site.finiteEvaluationIso_existsUnique`
- `CategoryTheory.AdicSites.Morphism.finitePullIso_existsUnique`
- `CategoryTheory.AdicSites.Morphism.finiteModuleRestrictionPullIso_existsUnique`
- `CategoryTheory.AdicSites.comparisonS_naturality`
- `CategoryTheory.AdicSites.comparisonT_naturality`
- `CategoryTheory.AdicSites.completionMateComparison`

## No longer needed

Removed these private imports from the item:

- `Sheaf.Paper.RingedTopoiTensorComparisonData`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Paper.RingedTopoiTensorComparisonConstruction`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Paper.AdicCompletionReduction`
- `Sheaf.Paper.CompletionMap`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The new finite-evaluation compatibility proof still uses K-flat resolution,
pullback preservation, and exact derived-functor factorization through its own
private imports; their underlying mathematics is retained. The normalized
`CompletionMateComparison` and quotient-presentation APIs already provide the
strict tensor construction, so this item does not reconstruct or descend it.
The new finite-completeness argument replaces the direct use of
`lemma-weil-pbc-adic-completion-reduction`. Consequently the main node no longer
has direct proof dependencies on that node,
`def-weil-pbc-canonical-ringed-tensor-comparison`,
`lem-weil-pbc-canonical-ringed-tensor-comparison-construction`,
`lem-pur-derived-change-of-rings`, or
`lem-weil-pbc-site-derived-tensor-descent`.

Removed obsolete main-node `tool_uses` entries for
`lemma-weil-pbc-adic-completion-reduction`,
`lem-weil-pbc-canonical-ringed-tensor-comparison-construction`,
`lem-pur-derived-change-of-rings`,
`lem-weil-pbc-site-derived-tensor-descent`, and
`lemma-weil-pbc-completed-pullback-reduction`.
No module is withdrawn, and no source-library declaration is removed.
These are local dependency reductions; no claim is made that another target
consumer cannot still need those modules. The unit's realized route is preserved.

## Where the brief, the DAG or earlier work was wrong

The direct adic-reduction theorem uses a coefficient/site universe presentation
that does not fit this item's small-site `AdicSites` API directly. This does not
require changing its statement: finite reduction follows from the existing
unit-preserving completion reflector and nilpotence in each quotient.

The DAG's informal identification of the finite maps needed two explicit
normalization arguments: projection of the completion unit, and finite evaluation
of the reduction/pullback comparison. The delivery proves both, rather than
identifying maps solely from isomorphic endpoints. The definition representation
repair above avoids repeatedly unfolding a composite
complex functor to compare it with its iterated form. This is a compilation repair,
with explicit proofs of the degreewise comparison identities; it weakens no statement.
The finite comparison proof uses a generic pasting lemma with functors, comparison
maps, and universal normalization laws as parameters, then instantiates it with
the specified constructions. This avoids expensive dependent-record reductions. Its private postcomposition lemma allows an arbitrary source
object; it does not require that object to lie in the localization functor image.
Since target-used definitions changed syntactically, their statement review must be
reopened to confirm that these identities preserve the intended interpretation.

## New nodes

`lem-sf-completion-unit-finite-projection` records the normalized equation between
the completion unit followed by the nth limit projection and the scalar-extension
unit. Its proof compares the ordinary limit counit on a flat-term K-flat model,
then transports the equality by naturality.

`lem-sf-completion-finite-reduction` records invertibility of finite reduction of
the completion unit and its projection equation. Quotient restrictions are
complete because ideal elements act nilpotently. The reflector's hom-set
bijection, transported through the scalar adjunction, gives invertibility by
coyoneda. It imports the preceding proved normalization lemma.

`lem-sf-reduction-pull-finite-evaluation` records the equality of the prescribed
strict and finite tensor/pullback comparisons. It proves the ordinary equation
using scalar insertion and the quotient adjunction, lifts it degreewise, and
checks the representative-normalized derived comparisons before transporting
to arbitrary objects. The existing comparison node is updated to record the
explicit complex endpoints.

`def-sf-complex-functor-square` records the construction of the explicit complex
square and its proved hom formula. `lem-sf-quotient-tower-evaluation-complex` records
the quotient evaluation comparison and its proved identity in every degree. Both
are complete constructions with proved properties and no proof holes.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
