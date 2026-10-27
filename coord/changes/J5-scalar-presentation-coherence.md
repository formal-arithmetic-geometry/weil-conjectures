# IsIntegralComparisonScalarNormalized

## Reason

Repair the scalar version of the already documented T6/S9 presentation defect.
CoefficientReductionPresentation constrains e only after finite derived evaluation.
Those functors are conservative, but are not faithful on the unbounded derived
system category. An automorphism invisible at every finite level can alter total
limit while keeping C and kappa unchanged; the strict tensor-generator formula
fixes q, so the old universal Roos equation cannot hold for both presentations.

Use the same existing IsIntegralComparisonPresentationCoherent condition already
required by pullback models. It fixes the double adjunction transpose of e to
the strict tensor-unit map determined by kappa, in the entire tower category.
coherentPrimitiveReductionPresentation supplies such a presentation for every
flat-term K-flat complex. This corrects comparison data, with no boundedness,
completeness, Tor-amplitude or residue-characteristic restriction on inputs.

For the edge test take A=Z_p, the completed countable free module B and D=product A,
with B -> D given by b_i -> p^i b_i. Its cokernel M is derived complete; the nonzero
class x=(p^i) lies in every p^n M. On A direct-sum M, the nonzero square-zero map
1 -> x gives 1+delta, invisible after every finite derived reduction. Twisting e
by reduction(1+delta) preserves the old hypotheses but changes its total limit.
See the existing full argument in the T6 PrimitiveQuotientRealizationComparisons
report and S9-pullback-presentation-coherence.md. This mathematical counterexample
is not claimed as a Lean-certified refutation.

The original direct consumer CoherentQuotientOrdinaryLift typechecked but exceeded
the 60-second limit (67 s; a profiling run took 64 s). Profiling identified expensive
coefficient-ring unfolding, including a 16.4-second section equality check. Adding
completedIntegralCommRingSheafUnrestricted and coefficientSequenceCommRingSheaf to
its existing local irreducibility list reduced the profiling compile to 34.4 s.
This is local to the proof file: no declaration, global attribute or import changes.
The final submitted source removes the profiling options and compiles in 36.3 s.

Return C-ff1d2: the proposed IntegralTowerInverseImageUnit extraction and every
associated local attribute are reverted. The review compiled the published original
in 48.0 seconds. The repaired delivery leaves that module and its node untouched
and contains neither the proposed support module nor its proposed new node.

OrdinaryQuotientPullbackTowerComparison typechecked but took 66 s twice.
Its profile isolates expensive generator conversions (6.86-second change and
8.8-second rewrite). Local unfolding experiments either hid essential generator
types or still took 68 s. The complete existing private construction is therefore
moved verbatim into OrdinaryQuotientPullbackTowerLevels (finite-level evaluation)
and OrdinaryQuotientPullbackTowerConstruction (tower assembly), imported with
import all solely for this proof. Its private names and proofs stay private; no
new mathematical statement, hole or axiom is introduced. The original module
retains its public imports, public theorem signature and complete assembly proof.

Only this scalar predicate body, its explanatory docstrings, the forced consumer
proof adaptations, and the remaining local proof optimization/private construction
split change. All
existing signatures, public imports, instances and attributes stay identical.
No WeilConjectures source file changes. The completed consumers applying scalar normalization include
PrimitiveQuotientRealizationsUnique, PrimitiveQuotientRealizationsTransport and
ScalarModelAssociativity, ScalarModelIteratedStrictCalculation and ScalarModelUnit.
Uniqueness and associativity choose a coherent
presentation. Scalar transport carries the coherence witness through the
left-adjoint comparison using unit_leftAdjointUniq_hom_app, then passes it to the
T-model normalization. These are forced proof adaptations; public statements,
visibility and public imports remain identical.

No Challenge declaration changes. The correction is in an auxiliary primitive
comparison interface used by proof data; no coefficient objects or operations
change. Any target-meaning review depending on this auxiliary model definition
must confirm the canonical coherent presentations still determine the same maps.

## Old

```lean
def IsIntegralComparisonScalarNormalized
    (S : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l L X)
    (realization : integralScalarExtensionOfUniverses l E L ι X ≅ S.reduction ⋙
      integralComparisonDerivedSequenceScalar l E L ι X ⋙ coefficientSequenceLimit l L X) :
    Prop :=
  ∀ (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P.obj),
    CoefficientReductionPresentation l E X S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ →
    ∃ q : (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l E L ι X).E.mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅ (integralScalarTowerFunctor l E L ι X).obj P.obj,
      (∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l L X).obj.obj (op (n, U.unop)))
        (x : (P.obj.X i).val.obj U),
        ((q.hom.app (op n)).f i).val.app U
          (integralComparisonRestrictedSection l L X
            ((integralComparisonSequenceScalarModel l E L ι X).E.obj (C.X i)) n U
            (integralComparisonSequenceTensorSection l E L ι X (C.X i)
              (op (n, U.unop)) s
              (integralComparisonSequenceSection l E X (C.X i) n U
                (((κ n).inv.f i).val.app U
                  (unrestrictedIntegralTensorSection l E X n (P.obj.X i) U 1 x))))) =
          integralScalarTensorSection l E L ι X n (P.obj.X i) U s x) ∧
      realization.hom.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l L X).map
          ((integralComparisonDerivedSequenceScalar l E L ι X).map e.hom) ≫
        (coefficientSequenceLimit l L X).map
          ((integralComparisonSequenceScalarModel l E L ι X).ε.app C) ≫
        (integralComparisonRoosBridge l L X ρ _).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
          (integralScalarExtensionComparisonOfUniverses l E L ι X).hom.app P
```

The existing local attribute in CoherentQuotientOrdinaryLift was:

```lean
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  constantSheaf
```

## New

```lean
def IsIntegralComparisonScalarNormalized
    (S : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l L X)
    (realization : integralScalarExtensionOfUniverses l E L ι X ≅ S.reduction ⋙
      integralComparisonDerivedSequenceScalar l E L ι X ⋙ coefficientSequenceLimit l L X) :
    Prop :=
  ∀ (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P.obj),
    CoefficientReductionPresentation l E X S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ →
    IsIntegralComparisonPresentationCoherent l E X S P.obj C e κ →
    ∃ q : (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l E L ι X).E.mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅ (integralScalarTowerFunctor l E L ι X).obj P.obj,
      (∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l L X).obj.obj (op (n, U.unop)))
        (x : (P.obj.X i).val.obj U),
        ((q.hom.app (op n)).f i).val.app U
          (integralComparisonRestrictedSection l L X
            ((integralComparisonSequenceScalarModel l E L ι X).E.obj (C.X i)) n U
            (integralComparisonSequenceTensorSection l E L ι X (C.X i)
              (op (n, U.unop)) s
              (integralComparisonSequenceSection l E X (C.X i) n U
                (((κ n).inv.f i).val.app U
                  (unrestrictedIntegralTensorSection l E X n (P.obj.X i) U 1 x))))) =
          integralScalarTensorSection l E L ι X n (P.obj.X i) U s x) ∧
      realization.hom.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l L X).map
          ((integralComparisonDerivedSequenceScalar l E L ι X).map e.hom) ≫
        (coefficientSequenceLimit l L X).map
          ((integralComparisonSequenceScalarModel l E L ι X).ε.app C) ≫
        (integralComparisonRoosBridge l L X ρ _).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
          (integralScalarExtensionComparisonOfUniverses l E L ι X).hom.app P
```

The local attribute is now:

```lean
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  constantSheaf completedIntegralCommRingSheafUnrestricted coefficientSequenceCommRingSheaf
```

OrdinaryQuotientPullbackTowerComparison keeps its two public imports and now
privately imports its extracted construction:

```lean
import all Sheaf.Paper.OrdinaryQuotientPullbackTowerConstruction
```

All private declarations formerly before its public theorem are copied verbatim
into those two new modules, separated before level_unit. The first single-module
extraction still took 77 s, requiring this finer separation. It retains the two foundational public imports needed
by the shared variable declarations; its import into the original module is private. The public theorem and its body
remain in the original module unchanged.

## Users

The earlier predicate-name-only scan found two textual mentions but missed
consumers of IntegralComparisonScalarModel.normalization. The current
`tools/downstream.py Sheaf.Paper.IntegralComparisonRealizationModels --uses
IsIntegralComparisonScalarNormalized IntegralComparisonScalarModel` scan finds
two predicate-name users and 18 model-structure users. The table below includes
every such user, every original direct importer, and every adapted module.
The two new forced adaptations are transport (unclaimed in the local mirror)
and associativity (D2, per return C-ff1d2); ExplicitScalarConeWordCoordinates
(M8) is rechecked through the repaired transport. The landing return af4aa4783 identified two consumers whose holes were filled
after the earlier review: ScalarModelIteratedStrictCalculation and ScalarModelUnit.
Both original current sources reproduce the reported rcases error against this
packet. Unit passes its existing hc witness. The iterated calculation requires an
explicit intermediate-statement correction, documented separately in
J5-iterated-scalar-presentation-coherence.md; its only caller already has hcoh.
The remaining textual users were re-scanned for normalization applications.
Both newly proved modules and their associativity/whole-counit parent compile
against the repaired interface (exit 0). The unit proof edit adds just hc;
the explicit intermediate calculation correction and its two local timing
annotations are recorded in J5-iterated-scalar-presentation-coherence.md.
The arbitrary-realization scalar normalization theorem remains disputed and is
not used here. This audit makes no claim that two predicate-name mentions
exhaust consumers of the changed model field.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AmbientComparisonSystemExistence | J5, this item | Constructs scalar normalization with explicit coherent presentations and assembles the ambient system. |
| Sheaf.Paper.AmbientQuotientScalarModelExistence | new module of J5 | Names the remaining fixed-calculus scalar-model existence step with the corrected normalization interface. |
| Sheaf.Paper.CoherentPrimitiveReductionPresentation | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.Paper.CoherentQuotientModelComparison | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.Paper.CoherentQuotientOrdinaryLift | unclaimed in local mirror | Two coefficient-ring definitions locally irreducible; repairs the direct consumer timeout without changing its interface. |
| Sheaf.Paper.CoherentQuotientReductionComparison | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.Paper.CompletedComparisonQuotientRealizationDefs | unclaimed in local mirror | Stores scalar models and reads realizations; no normalization call to adapt. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.Paper.EffectiveComparisonRealizationModels | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.Paper.EffectiveCompletionPresentationModels | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.Paper.EffectiveQuotientModelDescent | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.Paper.ExplicitScalarConeWordCoordinates | M8 (return C-ff1d2) | Current published original passes the server compile against repaired scalar transport (exit 0); unchanged copy removed from packet. |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed in local mirror | Adds whole-system coherence to scalar normalization. |
| Sheaf.Paper.IntegralComparisonScalarRealizationShifts | unclaimed in local mirror | Named theorem hole has unchanged signature; no compiled normalization call. |
| Sheaf.Paper.IntegralComparisonSystemData | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.Paper.IntegralPullbackCounitProjection | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.Paper.IntegralPullbackStrictFiniteComponent | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.Paper.IntegralPullbackSystemComparison | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.Paper.IntegralTowerInverseImageUnit | unclaimed in local mirror | Original source and DAG node unchanged; all proposed extraction and local attributes reverted. |
| Sheaf.Paper.NormalizedCompletedOperationModels | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.Paper.OrdinaryQuotientPullbackSuccessor | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.Paper.OrdinaryQuotientPullbackTowerComparison | unclaimed in local mirror | Private construction extracted into a proof-only module after repeated timeouts; public imports, theorem and assembly proof unchanged. |
| Sheaf.Paper.OrdinaryQuotientPullbackTowerConstruction | new module of J5 | Existing proved private tower assembly extracted from OrdinaryQuotientPullbackTowerComparison. |
| Sheaf.Paper.OrdinaryQuotientPullbackTowerLevels | new module of J5 | Existing proved private finite-level evaluation construction extracted from OrdinaryQuotientPullbackTowerComparison. |
| Sheaf.Paper.PodCompletionReindexCoefficientTransition | unclaimed in local mirror | Scalar model parameters/realizations; no normalization call. |
| Sheaf.Paper.PointIntegralRestrictionNatural | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.Paper.PrimitiveQuotientPullbackModelExistence | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.Paper.PrimitiveQuotientRealizationComparisons | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.Paper.PrimitiveQuotientRealizationsTransport | unclaimed in local mirror | Forced: intro hc, transport it to hcT through the adjunction unit, pass hcT to M.normalization. |
| Sheaf.Paper.PrimitiveQuotientRealizationsUnique | unclaimed in local mirror | Uses coherentPrimitiveReductionPresentation and supplies hcoh to both scalar normalization fields; theorem signature unchanged. |
| Sheaf.Paper.PrimitiveQuotientScalarModelExistence | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | {"who": "D2", "t": 1793085710.1481974, "since": "2026-10-27T07:21:50Z"} | Same canonical model and realization; no source adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed in local mirror | Scalar model parameters/realizations; no normalization call. |
| Sheaf.SixFunctors.IntegralOpenReductionDefinitions | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.TraceFormula.CounitRealizationSubstitution | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.TraceFormula.IntegralComparisonCounitCharacterization | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.TraceFormula.IsomorphismStrictQuotientModels | unclaimed in local mirror | Same canonical model and realization; no source adaptation. |
| Sheaf.TraceFormula.ScalarModelAssociativity | D2 (return C-ff1d2) | Forced: choose coherentPrimitiveReductionPresentation and pass hcoh to bEF.normalization; private import only. Also passes its existing hcoh to the corrected iterated calculation. |
| Sheaf.TraceFormula.ScalarModelIteratedStrictCalculation | unclaimed in current local mirror; E9 proof/D2 statement | Newly proved importer: explicit coherent-presentation hypothesis and bEL normalization argument; separate statement-change record; local timing annotations; compiles at 58.0 s. |
| Sheaf.TraceFormula.ScalarModelUnit | unclaimed in current local mirror | Newly proved importer: pass existing hc to bEE.normalization; statement unchanged; current source compiles at 37.6 s. |

## Status

landed 20261027T180651-L-3888388 2026-10-27 (merge of deliver/J5/Sheaf.Paper.AmbientComparisonSystemExistence)
