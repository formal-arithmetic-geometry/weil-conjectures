# Function-presentation proof scopes and constructed coefficient interface

## Reason

The stage-3 static check classifies extra universe and private-helper section-variable commands in `Sheaf.Paper.CondensedQbarFunctionPresentations` as a visible context
change. The matrix and cokernel helpers require independent category and coefficient
universes and local finite biproduct instances. All new helpers in this existing module
are private. Its original public imports, definitions, declaration signatures and
visibility are preserved. New imports are proof-only. No target statement or definition
used by a target changes meaning.

The new module `Sheaf.Paper.CondensedQbarFunctionCoefficients` contains explicit coefficient,
scalar and geometric-fiber constructions and one remaining named theorem, attached to
`lem-weil-pbc-condensed-qbar-function-coefficients`. Its fiber-data record separates real
constructed data from the four remaining proof properties. In particular, no definition
chooses arbitrary data from a mere existence theorem with an admitted proof.

## Old

Context: universes `u v`; `open CategoryTheory CategoryTheory.Limits`; scoped
`CategoryTheory.Obj`; namespace `AlgebraicGeometry.ProEtale`; local instance attribute
`Abelian.hasFiniteBiproducts`.
The original public theorem has the following exact signature:

```lean
theorem exists_condensedQbar_compatible_function_presentations
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (f : Y ⟶ X) (hf : WeaklyEtale f)
    (hcoeff : Nonempty
      (Mon.mk (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) ≅
        Mon.mk (padicAlgClSheaf X ℓ)))
    (P : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hP : Mod.IsFinitelyPresented
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) f).obj P)) :
    ∃ (C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y) (n m : ℕ)
      (B : ∀ i : C.I₀,
        Matrix (Fin n) (Fin m) (PadicAlgCl.finiteIntermediateFieldValued ℓ (C.X i))),
      (∀ (i j : C.I₀) (x : C.X i) (y : C.X j),
        (C.f i ≫ f) x = (C.f j ≫ f) y →
        Nonempty
          (((Fin n → PadicAlgCl ℓ) ⧸ LinearMap.range
            (((B i).map (condensedQbarFunctionEval x)).toLin')) ≃ₗ[PadicAlgCl ℓ]
            ((Fin n → PadicAlgCl ℓ) ⧸ LinearMap.range
              (((B j).map (condensedQbarFunctionEval y)).toLin')))) ∧
      ∀ (i : C.I₀) (V : (C.X i).Opens),
        ∃ φ : PadicAlgCl.finiteIntermediateFieldValued ℓ V.toScheme →+*
            End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.toScheme)),
          Nonempty
            ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
              ((V.ι ≫ C.f i) ≫ f)).obj P ≅
              cokernel (biproduct.matrix fun j k ↦
                φ (condensedQbarFunctionComp V.ι.base.hom (B i k j))))
```

## New

Context: universes `u v w uE`; the same namespace and opens; a local
`Abelian.hasFiniteBiproducts` instance attribute; two closed sections with variables for
private generic pullback and finite-free evaluation helpers. The local instance
attribute was already present and is retained. No global notation or
instance is added to the existing module. Its public theorem has the unchanged signature:

```lean
theorem exists_condensedQbar_compatible_function_presentations
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (f : Y ⟶ X) (hf : WeaklyEtale f)
    (hcoeff : Nonempty
      (Mon.mk (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) ≅
        Mon.mk (padicAlgClSheaf X ℓ)))
    (P : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hP : Mod.IsFinitelyPresented
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) f).obj P)) :
    ∃ (C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y) (n m : ℕ)
      (B : ∀ i : C.I₀,
        Matrix (Fin n) (Fin m) (PadicAlgCl.finiteIntermediateFieldValued ℓ (C.X i))),
      (∀ (i j : C.I₀) (x : C.X i) (y : C.X j),
        (C.f i ≫ f) x = (C.f j ≫ f) y →
        Nonempty
          (((Fin n → PadicAlgCl ℓ) ⧸ LinearMap.range
            (((B i).map (condensedQbarFunctionEval x)).toLin')) ≃ₗ[PadicAlgCl ℓ]
            ((Fin n → PadicAlgCl ℓ) ⧸ LinearMap.range
              (((B j).map (condensedQbarFunctionEval y)).toLin')))) ∧
      ∀ (i : C.I₀) (V : (C.X i).Opens),
        ∃ φ : PadicAlgCl.finiteIntermediateFieldValued ℓ V.toScheme →+*
            End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.toScheme)),
          Nonempty
            ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
              ((V.ι ≫ C.f i) ≫ f)).obj P ≅
              cokernel (biproduct.matrix fun j k ↦
                φ (condensedQbarFunctionComp V.ι.base.hom (B i k j))))
```

The new coefficient module has its own public definitions and instances. It is imported
only for the existing module's proof, so these declarations do not enter that module's
public interface. The original public function-evaluation and function-composition ring
homomorphisms retain their original bodies and signatures.

## Users

`tools/downstream.py Sheaf.Paper.CondensedQbarFunctionPresentations --uses
exists_condensedQbar_compatible_function_presentations` finds the item and
`Sheaf.Paper.CondensedQbarLfpMatrixRefinement` as the only textual users of the theorem.
The unchanged direct importer compiled against the delivery overlay in 8.2 seconds. The current transitive
importers and their claim holders are listed below; no downstream module is adapted.
The statement and public definitions they use are unchanged.

| Module | Current holder | Effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedLfpHomContinuity` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedLocalPieceHomContinuity` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | A3 | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedQbarLfpLocalTriviality` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedQbarLfpMatrixRefinement` | unclaimed | direct importer and user of the unchanged theorem; no adaptation |
| `Sheaf.Paper.CondensedSheafExtContinuity` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedStratumModelAssembly` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedStratumModelInductionStep` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedStratumModelInductionStepEmpty` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonempty` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing` | G1 | transitive importer; no adaptation |
| `Sheaf.Paper.ConstructibleCokernelsExtensions` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousConstructibleIntegralDenominators` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousConstructibleIntegralGluing` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousConstructibleIntegralImage` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousConstructibleIntegralModel` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousConstructibleIntegralSingle` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousConstructibleIntegralStratum` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousExchangeIntegralModel` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousIntegralComplexTelescope` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousIntegralExchangeSquare` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousIntegralLocalization` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousIntegralLocalizationContinuity` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousIntegralLocalizationHomology` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousIntegralLocalizationLegs` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousIntegralLocalizationMate` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousIntegralLocalizationModel` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousIntegralModuleTelescope` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousIntegralPushComparison` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.ContinuousIntegralRegularTelescope` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.IntegralConstructibleKernels` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.IntegralConstructibleNakayama` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.IntegralConstructibleSequentialHom` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.IntegralConstructibleSerre` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.IntegralConstructibleSheafHom` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.IntegralExchangeReduction` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.IntegralFiniteExchangeComparison` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.IntegralReductionConservative` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.IntegralReductionConstructible` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.IntegralResidueExchange` | unclaimed | transitive importer; no adaptation |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | unclaimed | transitive importer; no adaptation |
| `TargetsCheck` | unclaimed | transitive importer; no adaptation |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | transitive importer; no adaptation |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | transitive importer; no adaptation |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | unclaimed | transitive importer; no adaptation |

The new coefficient module has no existing library users; the delivered item imports it
for its proof. All existing modules above remain unchanged.

## Status

landed 20261016T082348-L-1529163 2026-10-16 (merge of deliver/H3/Sheaf.Paper.CondensedQbarFunctionPresentations)
the coefficient constructions, the new node and its remaining proof properties.
