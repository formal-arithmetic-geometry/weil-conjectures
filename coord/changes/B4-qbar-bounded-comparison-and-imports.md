# AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper

## Reason

Implement the exact scoped exception in coord/upstream-statement-exceptions.tsv
and coord/repair-notes/B4-qlbar-continuity-assignment.md (2026-10-22). The old
properness-only assertion lacked its required ambient unbounded continuity input.
STATEMENT-DISPUTED: this is an authorized correction of that unsupported
implication, not a proof of it or a claimed Lean-certified counterexample.

Preserve the name and canonical comparison, properness binder, finite-extension
result and proof, public imports, and every unrelated signature and non-theorem
body. The Qbar Shriek example must carry the matching continuity hypothesis.
No other upstream exception is exercised, and no target or data definition changes.

## Old

```lean
instance isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper [IsProper f]
    (E : FiniteIntermediateField ℓ) :
    IsIso (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f)
```

The Qbar Shriek example inferred its comparison for every compactifiable f.

## New

```lean
instance isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper [IsProper f]
    (E : FiniteIntermediateField ℓ)
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      R((f)_*⟦Profinite.continuousMapRingObj E⟧)] :
    IsIso (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f)
```

The Qbar Shriek example assumes the same coproduct preservation for
`(HasCompactification.compactification f).g`. It explicitly obtains Push from
the corrected instance and applies the unchanged formal Shriek theorem.

Proof: the proved regular condensed Qbar basis has a coefficient-universe
index I. Inverse image preserves coproducts; the existing private
scheme_basis_from_point and qbar_isIso_unit constructions transport the basis
and its scalar-unit maps to the unbounded derived categories. Scalar naturality,
conservative restriction and the unit-mate criterion identify the canonical
comparison with the I-copower comparison. The explicit continuity hypothesis
makes it invertible on every object. No new hole stands for continuity.

The node has the corrected statement, actual proof/dependencies, exact Lean
attachment and statement_change containing the previous statement and proof.
The generic basis, scalar-unit localization and mate nodes are tools rather
than replacements of the unit's finite-extension route.

## Users

The exact-name search and tools/downstream.py --uses find no external explicit
call to this instance. The only local consumer of its blanket inference was
the Qbar Shriek example, now corrected. Every direct importer was audited for
implicit coefficient comparison goals as well as explicit names.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | B4 | corrected instance and Qbar Shriek example; all other declarations unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.AlgebraicGeometry.SubfieldExtensionLocalPresentation | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.AlgebraicGeometry.CondensedDerivedTensorComparison | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.AlgebraicGeometry.ConstructibleCoconeAmbientRealization | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficients | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.LisseFiniteCoefficientModel | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CompletedCondensedCoefficients | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenClosed | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CondensedPointSupertrace | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CondensedLfpCoefficientModel | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.AmbientIndDerivedSums | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | not listed locally | bounded comparison already explicit; unchanged |
| Sheaf.Paper.CondensedStratumModelInductionStep | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CondensedFiniteModelExtensions | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CondensedFinitePresentationDescent | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CondensedLocalCoefficientAdjoints | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.AmbientIndDerivedTriangulated | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CoefficientFiniteDescentLisse | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.UniformConstructibleExtRational | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.IndHeartFullFaithfulness | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CoefficientFiniteDescentSections | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CondensedFiniteModelProofAPI | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.ProperHeartBoundReduction | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.LisseFiniteHomLift | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CondensedLocalModelGluing | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.BrownHypothesesGeneration | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.QlbarDirectImageComparison | not listed locally | bounded comparison already explicit; unchanged |
| Sheaf.Paper.QlbarTailModuleColimit | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.ProperBaseChangeRational | not listed locally | bounded comparison already explicit; unchanged |
| Sheaf.Paper.CondensedStratumModelAssembly | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.QcqsRationalIntegralLocalizingGenerators | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CartesianCoefficientsFiniteFree | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CondensedFinitePresentationMatrices | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenPiece | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.Paper.IntegralWindowCoproductComparison | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.SixFunctors.IntegralModelsGenerators | not listed locally | no coefficient push/shriek comparison or implicit IsIso goal for it; unchanged |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | not listed locally | bounded comparison already explicit; unchanged |

Among these 50 external direct importers, 46 contain no coefficient Push/Shriek
comparison or goal. Four have such mentions:

- UpstreamExtra's Compatibility proves a bounded-below component theorem directly
  from the scalar basis and bounded copower continuity, without the old instance.
- CondensedQbarBaseChangeCompatibility extracts K.property.1.1 and explicitly
  applies that bounded-below theorem, installing the resulting IsIso locally.
- ProperBaseChangeRational's existing comparison statements have lower-bound
  hypotheses and sorry proofs; they do not infer the old ambient instance.
- QlbarDirectImageComparison has a lower-bound hypothesis and an independent
  bounded-below proof retained in this sandbox for a separate submission.

No external caller fails because of the corrected premise, no consumer statement
is silently weakened, and no forced adaptation is included. The independent
bounded companion and its node are preserved under
scratchpad/retained-bounded-companion; no bounded companion change is delivered.

No node in dag/nodes cites lem-sfb-qlbar-push-iso-proper in stmt_deps, proof_deps
or a proof step's uses. The structural statement_change.citers list is empty.
The unit cites it directly; its reconciliation is documented below.

## Unit reconciliation required from the maintainer

Original sk-prop-sfb-finite-extension-compatibility clause 3: every proper f has
Qbar Push invertible on every unbounded object, hence Qbar Shriek for every
compactifiable f using only properness of the compactification's g.

Corrected clause 3: retain proper f and require explicit preservation of
coefficient-universe coproducts by its E-coefficient Rf_*. The Qbar Shriek
consequence requires the same continuity for the proper part g of the chosen
compactification. The existing independent bounded-below qcqs comparison
remains applicable when its input has a lower bound.

The original dag/units record is preserved as source history; worker delivery
cannot transport unit-record edits. The maintenance assignment authorizes this
correction and asks the independent reader and maintainer to reconcile the
unit. Its original all-unbounded assertion is NOT realized here. Unit step 1
needs the continuity proviso for Qbar Push and Shriek. Flatness, Pull, clause 2
for finite extensions, and the nonproper fold-map example remain unaffected.
sk-thm-sfb-qlbar-two-colimit cites the unit for bounded constructible descent
and base-change transport: bounded inputs admit the independent bounded-below
route, already explicit in CondensedQbarBaseChangeCompatibility. No target
statement, definition or meaning is changed.

## Validation

The initial corrected instance and Qbar Shriek example passed single-file
compilation in 24.3 seconds. The final source is being checked with the normal
single-module delivery compile and axiom probe. Larger artifact-generating
experiments timed out at 60 seconds; prefix diagnostics localized their cost
to concrete Push elaboration. They are not claimed as passed checks, and no
limit or tool was changed. No source file or proof is split in this delivery.

## Status

landed 20261022T040146-L-2812655 2026-10-22 (merge of deliver/B4/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility)
