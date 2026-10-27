# PerfectProjection duplicate mixed and ordinary-unit interfaces

## Reason

The finite-total proof now uses the existing native normalized unit comparison
`proEtaleProjectionUnit_existsUnique`, and the signed-model proof uses the existing
`SignedProjectionResolution` comparisons and normalization theorem. Therefore the
item's duplicate mixed and ordinary-unit API has no remaining consumer. Prune these
fourteen declarations and their private coherence helpers. Their mathematics is already
proved in ProEtaleProjectionFormulaArrows and ProEtaleMixedProjectionMate; those
modules and their proofs remain. The unit route remains implemented by the native
coherence theorem used by the signed normalization identities. No adopted source declaration
under WeilConjectures is changed. This is pruning following API reuse, not moving
proofs or declarations to evade a compile limit.

## Old

```lean
theorem mixed_existsUnique (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel T R) (I F : CochainComplex (proEtaleRingModules T R) ℤ)
    (hF : proEtaleFlatRepresentatives T R F) :
    ∃! e : a.tensor.obj (DerivedCategory.Q.obj I, DerivedCategory.Q.obj F) ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor I F (proEtaleOrdinaryTensor T R)),
      ∀ (P : CochainComplex (proEtaleRingModules T R) ℤ)
        (hP : proEtaleFlatRepresentatives T R P) (p : P ⟶ I), QuasiIso p →
        a.tensor.map (Prod.mkHom (DerivedCategory.Q.map p) (𝟙 (DerivedCategory.Q.obj F))) ≫
          e.hom = a.representative.inv.app (⟨P, hP⟩, ⟨F, hF⟩) ≫
            DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap p (𝟙 F)
              (proEtaleOrdinaryTensor T R) (ComplexShape.up ℤ))

def mixed (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel T R) (I F : CochainComplex (proEtaleRingModules T R) ℤ)
    (hF : proEtaleFlatRepresentatives T R F) :=
  (mixed_existsUnique T R a I F hF).exists.choose

theorem ordinaryUnit_existsUnique :
    ∃! j : (proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)).obj
        (SheafOfModules.unit ((adicLisseForget Y).obj (ring d Y))) ≅
          SheafOfModules.unit ((adicLisseForget X).obj (ring d X)),
      ∀ (U : Y.ProEtᵒᵖ) (r : (ring d Y).obj.obj U),
        ((proEtaleRingModuleAdjunction f (ring d Y) (ring d X) (coefficients d f)).homEquiv
          _ _ j.hom).val.app U r =
        (proEtaleRingDirectImageMap f (ring d Y) (ring d X) (coefficients d f)).hom.app U r

def ordinaryUnit := (ordinaryUnit_existsUnique d f).exists.choose

def ordinaryRightUnit (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (M : proEtaleRingModules T R) :
    ((proEtaleOrdinaryTensor T R).obj M).obj
      (SheafOfModules.unit ((adicLisseForget T).obj R)) ≅ M :=
  letI := SheafOfModules.monoidalCategory R
  let S := PresheafOfModules.sheafification.{u + 1}
    (𝟙 ((adicLisseForget T).obj R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((adicLisseForget T).obj R).obj)
  SheafOfModules.tensorObjIsoSheafification M
      (SheafOfModules.unit ((adicLisseForget T).obj R)) ≪≫
    S.mapIso (ρ_ M.val) ≪≫ (asIso adj.counit).app M

def ordinaryTensorHom (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    {M N P Q : proEtaleRingModules T R} (v : M ⟶ N) (w : P ⟶ Q) :
    ((proEtaleOrdinaryTensor T R).obj M).obj P ⟶
      ((proEtaleOrdinaryTensor T R).obj N).obj Q :=
  letI := SheafOfModules.monoidalCategory R
  v ⊗ₘ w

theorem ordinaryRightUnit_eq (M : proEtaleRingModules T R) :
    let := SheafOfModules.monoidalCategory R
    ordinaryRightUnit T R M = ρ_ M

theorem ordinaryUnit_coherence (M : modules d Y) :
    (proEtaleOrdinaryTensorPullback f (ring d Y) (ring d X) (coefficients d f) M
      (SheafOfModules.unit ((adicLisseForget Y).obj (ring d Y)))).hom ≫
      ordinaryTensorHom X (ring d X)
        (𝟙 ((proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)).obj M))
        (ordinaryUnit d f).hom ≫
      (ordinaryRightUnit X (ring d X)
        ((proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)).obj M)).hom =
    (proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)).map
      (ordinaryRightUnit Y (ring d Y) M).hom

abbrev ordinaryPull := proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)

abbrev ordinaryPush := proEtaleRingModuleDirectImage f (ring d Y) (ring d X) (coefficients d f)

theorem Resolution.flat : proEtaleFlatRepresentatives Y (ring d Y) r.coefficient ∧
    proEtaleFlatRepresentatives X (ring d X)
      (((ordinaryPull d f).mapHomologicalComplex (.up ℤ)).obj r.coefficient)

def Resolution.targetComplex :=
  CochainComplex.mapBifunctor r.injective
    (((ordinaryPull d f).mapHomologicalComplex (.up ℤ)).obj r.coefficient)
    (proEtaleOrdinaryTensor X (ring d X))

theorem Resolution.targetComplex_isKInjective : (r.targetComplex d f K).IsKInjective

def Resolution.pushModel :
    (directImage d f).obj K ≅ DerivedCategory.Q.obj
      (((ordinaryPush d f).mapHomologicalComplex (.up ℤ)).obj r.injective) :=
  letI := r.isKInjective
  (directImage d f).mapIso r.representsK ≪≫
    (@asIso _ _ _ _ ((ordinaryPush d f).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj r.injective))
      (proEtaleRingDerivedDirectImage_kInjective f (ring d Y) (ring d X)
        (coefficients d f) r.injective)).symm
```

## New

The fourteen declarations are removed. Use the existing proEtaleMixedTensor,
proEtaleMixedTensor_existsUnique, proEtaleProjectionUnit_existsUnique and the ordinary
monoidal category's tensorHom and rightUnitor. The reused signed normalization
uses these APIs directly. The unused Resolution.flat,
Resolution.targetComplex_isKInjective and Resolution.pushModel interfaces are supplied internally by the existing signed
model_properties and comparison constructors. The original node's Lean declaration
list is updated. No module or node is withdrawn.

## Users

Downstream short-name searches and namespace-qualified searches were checked.
The only real user of any withdrawn declaration is this item. The following external
hits are unrelated fields or definitions; their source occurrences were read.
The mixed, ordinaryPull and ordinaryPush short-name matches below are also
unrelated. Their declarations and namespaces were checked.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PerfectProjectionFormula | U5 | Replace duplicate uses by the native unit and signed-model APIs. |
| Sheaf.Paper.ContinuousScalarDerivedEncoding | unclaimed | ordinaryUnit is its own structure field. |
| Sheaf.Paper.NativeWeilClosedForgetful | unclaimed | ordinaryUnit is its own structure field. |
| Sheaf.Paper.FiniteCoefficientDerivedExchangeIdentification | unclaimed | ordinaryRightUnit is its own derived-functor comparison. |
| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed | Unrelated mixed field or prose. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Unrelated mixed field or prose. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Its own ordinaryPull and mixed fields. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Unrelated mixed field or prose. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed | Uses its own LisseRationalRealization ordinaryPull. |
| Sheaf.Paper.SystemRefinementConstructibleDomain | unclaimed | Defines its own ordinaryPull. |
| Sheaf.Paper.ClosedTestScalarModelDiagrams | unclaimed | Its own sourceModel/targetModel, unrelated to Resolution.pushModel. |

The DAG mentions these names only in this item's Lean declaration list. None is a
separate realized unit step; the node and the proper-base-change unit route remain.
No consumer or target changes statement or meaning. No forced adaptation is needed.

## Status

landed 20261024T191427-L-349376 2026-10-24 (merge of deliver/U5/Sheaf.Paper.PerfectProjectionFormula)
