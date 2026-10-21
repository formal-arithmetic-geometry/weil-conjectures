# AlgebraicGeometry.Scheme.OrderedExchange universal reduction and normalization

## Reason

Restore the completed tensor-transition, augmentation and derived pullback proofs from
the prior G4 implementation. Bundle the left-derived functor, its counit and its K-flat
computation law in the existing DerivedReductionModelData API. The proved universal
property determines this pair up to its unique counit-compatible isomorphism.
The augmentation is the explicit universal lift; augmentation_normalized and
augmentation_eq_choose prove its original formula and equality with the unique
normalized choice for this reduction model.

The generic ModelPullNormalized definition exposes exactly the original normalization
formula while keeping concrete expressions abstract during checking. Inlining the full
formula into the descent interface exceeded the 60-second compile limit; the shared
predicate makes the complete file compile in 34.6 seconds. No coefficient, hypothesis,
universe or public theorem signature changes.

## Old

~~~lean
def reduction (T : Scheme.{t}) : D (A := A) T ⥤ TD (A := A) T := (reduction_exists d T).choose
~~~

~~~lean
def reductionCounit (T : Scheme.{t}) :
    DerivedCategory.Qh ⋙ reduction d T ⟶ reductionHomotopy d T :=
  (reduction_exists d T).choose_spec.choose
~~~

~~~lean
def reductionComplexCounit (T : Scheme.{t})
    (P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ) :
    (reduction d T).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((reductionModule d T).mapHomologicalComplex (.up ℤ)).obj P) :=
  AlgebraicGeometry.Scheme.reductionComplexCounit (reductionModule d T)
    (reduction d T) (reductionCounit d T) P
~~~

~~~lean
def augmentation (T : Scheme.{t}) : diagonal (A := A) T ⟶ reduction d T :=
  (augmentation_existsUnique d T).exists.choose
~~~

~~~lean
def ReductionPullNormalized
    (τ : reduction d V ⋙ exchangeConstantPull (A := A) f ≅
        pull (A := A) f ⋙ reduction d U) : Prop :=
  ∀ P : CochainComplex (reductionModules V (exchangeConstantRing V A)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := exchangeConstantRing V A) P →
        τ.hom.app (DerivedCategory.Q.obj P) ≫
            (reduction d U).map
              ((proEtaleRingDerivedPullbackFactors f
                (exchangeConstantRing V A) (exchangeConstantRing U A)
                (exchangeConstantIso f A)).hom.app P) ≫
            reductionComplexCounit d U
              (((proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
                (exchangeConstantIso f A)).mapHomologicalComplex (.up ℤ)).obj P) =
          (exchangeConstantPull (A := A) f).map (reductionComplexCounit d V P) ≫
            (exchangeTowerModulePull f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).mapDerivedCategoryFactors.hom.app
              (((reductionModule d V).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryReductionPullIso d f)
                (.up ℤ)).hom.app P)
~~~

## New

~~~lean
def reduction (T : Scheme.{t}) : D (A := A) T ⥤ TD (A := A) T :=
  (reductionData d T).reduction
~~~

~~~lean
def reductionCounit (T : Scheme.{t}) :
    DerivedCategory.Qh ⋙ reduction d T ⟶ reductionHomotopy d T :=
  (reductionData d T).counit
~~~

~~~lean
def reductionComplexCounit (T : Scheme.{t})
    (P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ) :
    (reduction d T).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((reductionModule d T).mapHomologicalComplex (.up ℤ)).obj P) :=
  (reductionData d T).complexCounit P
~~~

~~~lean
def augmentation (T : Scheme.{t}) : diagonal (A := A) T ⟶ reduction d T :=
  canonicalModelAugmentation (Functor.const ℕᵒᵖ) (reductionModule d T)
    (reductionData d T) (ordinaryAugmentation d T)
~~~

~~~lean
def ReductionPullNormalized
    (τ : reduction d V ⋙ exchangeConstantPull (A := A) f ≅
        pull (A := A) f ⋙ reduction d U) : Prop :=
  ModelPullNormalized (reductionModule d V) (reductionModule d U)
    (proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A))
    (exchangeTowerModulePull f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A))
    (reductionData d V) (reductionData d U) (ordinaryReductionPullIso d f) τ
~~~

The new ModelPullNormalized predicate is a general version of the displayed original
equation; its specialization is definitionally equal to that equation. The reduction
model is constructed from a proved theorem. No data is selected from arbitrary
unproved existence. The original augmentation choice equality is proved explicitly.

The local transparency commands follow the restored proof: completedAdicChangeData,
reductionHomotopy, completedAdicChange, pbcScalarAdjunction and
proEtaleRingModuleAdjunction are made irreducible only in their indicated local scopes.
They change elaboration cost, not the exported transparency or mathematical data.
The previous B3 local attributes on large chosen comparison definitions are no longer
needed in this implementation.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedExchangeCoherence | S9 | Quarantined source preserved; same canonical universal constructions and normalization; no adaptation. |
| Sheaf.Paper.CompletedProjectionCoherence | D2 | same canonical universal constructions and normalization; no adaptation. |
| Sheaf.Paper.CompletedPullbackUnitTower | V1 | same canonical universal constructions and normalization; no adaptation. |
| Sheaf.Paper.ExchangeFunctoriality | unclaimed | Quarantined source preserved; same canonical universal constructions and normalization; no adaptation. |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | unclaimed | Quarantined source preserved; same canonical universal constructions and normalization; no adaptation. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | unclaimed | Quarantined source preserved; same canonical universal constructions and normalization; no adaptation. |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | unclaimed | Quarantined source preserved; same canonical universal constructions and normalization; no adaptation. |
| Sheaf.Paper.ProEtaleConstantReductionTower | T4 | Six original holes closed; projection_isIso remains. |

The live downstream checks use the unchanged consumer sources against the delivered
sandbox module. The tool's name-only --uses search additionally matches unrelated
APIs with the same last segment; those do not refer to this namespace. No adopted
source module is changed. Targets depending on these canonical definitions require
the usual definition-meaning review; no target signature is changed.

## Status

landed 20261021T011040-L-2032918 2026-10-21 (merge of deliver/T4/Sheaf.Paper.ProEtaleConstantReductionTower)
