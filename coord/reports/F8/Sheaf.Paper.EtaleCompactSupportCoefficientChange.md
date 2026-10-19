## What changed

Proved `AlgebraicGeometry.Etale.coefficientRestrictionOpenMap_isIso` in
`Sheaf.Paper.EtaleCompactSupportCoefficientChange` without changing any signature,
definition, or visibility. The inverse mate restricts to an isomorphism on the
open by `unit_mateEquiv_symm` and invertibility of the open-adjunction units. At geometric
points outside the open both its source and target vanish; the target calculation uses
the canonical scalar-restriction/pullback comparison. Geometric-stalk conservativity
then proves invertibility of each component and hence of the natural transformation.
The retained proof was rechecked against the current server snapshot with `lcompile.py`
(7.4 seconds, exit code 0). A separate `#print axioms` check reports only
`propext`, `Classical.choice`, and `Quot.sound` for the proved theorem.

## Proved and sorry left

Closed one of the item's four holes:
`AlgebraicGeometry.Etale.coefficientRestrictionOpenMap_isIso`.
Added zero holes; no decomposition or new module.

The three unchanged holes left, all attached to
`lem-fix-compact-support-coefficient-change`, are:

- `AlgebraicGeometry.Etale.compactSupportCoefficientComparisonPlus_isIso`:
  the proper-factor projection-formula argument and its identification with the
  universal B-linear comparison remain.
- `AlgebraicGeometry.Etale.nonempty_coefficientTensorModel_of_finiteTor`:
  constructing a bounded universal tensor presentation from the bounded flat model
  remains. The recorded finite-coefficient flat-model theorems use additional
  finite-field/invertibility hypotheses, so they cannot simply be applied to this
  arbitrary-scheme signature. The general upstream flat-model theorem does cover
  arbitrary schemes, but still requires constructing the scalar-extension universal
  arrow in this fixed-scalar presentation.
- `AlgebraicGeometry.ProEtale.CoefficientTensorModel.origin_of_etale_finiteTor`:
  the normalized B-linear comparison between the ordinary-etale tensor presentation
  and its pro-etale inverse image remains.

## No longer needed

The shared checkout acquired the following private proof-plan imports after the
initial sandbox copy. None is used by the completed proof, and the delivered module
compiles without them. They are omitted from this delivery:

- `Sheaf.Algebra.Homology.ChangeOfRingsTensorComparison`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.FixSiteOpenExchange`
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`
- `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`
- `Sheaf.Paper.CondensedAmbientExchange`
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.SecSmoothPurity.DirectImageScalarExchange`
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`
- `Sheaf.SecSmoothPurity.OpenScalarExchange`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`
- `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`

No public import is removed. No mathematical dependency of the other three open
proofs or of the other modules realizing the shared node is claimed obsolete: the
shared node's overall coefficient-change plan is retained. The completed proof uses
its planned open-unit normalization and the existing geometric-stalk and off-open
vanishing APIs, with no additional import.

## Where the brief, the DAG or earlier work was wrong

The assigned module and its node attachment were initially absent from the shared
checkout and became readable after synchronization. One compile request received no
server answer within 191 seconds; the retry completed successfully. Neither issue
required a repository or launcher-tool change.


On resumption, the retained open-mate proof compiled against current sources. An
additional attempt to prove tensor-model existence using the existing
`EtaleDerivedScalarTensor.scalarTensorIso` interface exceeded the single-file limit;
that experimental import and proof were removed. No signature or definition changed,
and the delivered state was compiled again successfully. The delivery dry run was
retried after a prior process exited with code 137 while acquiring its shared
worktree. No launcher script was modified.

The resumed dry run passed worktree acquisition but its compile request received
no server answer within 193 seconds. Nothing was pushed; the required dry run was
retried, following the tool diagnostic. The independent single-file compile and
axiom check above both succeeded against the current server snapshot.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
