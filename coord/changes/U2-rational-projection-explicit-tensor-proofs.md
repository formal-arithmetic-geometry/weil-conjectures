# Rational localizing projection formula: explicit tensor existence proofs

## Reason

The completed file initially exceeded the 60-second compile limit. Profiling found repeated
inference of the whole graded tensor and sequential tensor-colimit proof families in `Functor.leftDerivedFunctor`.
Supply the already proved `hasTensorFourShortcut`, `hasGoodTensorLeftShortcut`, and
`hasGoodTensorRightShortcut` explicitly. These are proofs of propositions, so proof irrelevance
identifies the resulting functor with the original one by definitional equality. Every binder,
universe, hypothesis, conclusion and map is retained; the explicit proof arguments remain proof-irrelevant. The explicit derived-category data arguments
are the same canonical `projectionModuleHasDerived` instances already selected by the local
interface registrations. All data and morphism types are definitionally unchanged. The textual signature checker therefore sees a change, although the
Lean types and the mate definition remain definitionally equal to the originals. The
`Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`
import becomes public because the explicit helper constants occur in public signatures.
These are the existing canonical structures and proved helpers, not replacement definitions.

The same proof arguments are explicit in the private localizing interface helper. Local instance
priorities and proved private caches for colimit existence/preservation avoid expanding graded
tensor expressions repeatedly. Direct colimit instances have higher priority than the expanded
complex-tensor aliases, including in both abstract comparison sections. The existing public projection structure aliases have the same
data as the original instances. After the concrete normalization proofs, the existing ordinary module tensor structures,
localization functor, and ordinary pullback are locally irreducible, as in the published
module-object monoidal interface. This avoids expanding their constructions when applying
that interface. All registrations are local; no global
attribute is changed.
The representative formula binds the two existing tensor-existence proofs once for each
pair of complexes, so its four tensor occurrences reuse the local proofs. These local proof lets
are definitionally irrelevant; the representative condition is exactly the same proposition.
The mate's body is unchanged verbatim. No definition used by a target changes its meaning.

## Old

```lean
import Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
```

```lean
noncomputable def moduleObjectProjectionMate
    (A : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (lowerStar Λ f).rightDerivedFunctor.obj A ⊗ B ⟶
      (lowerStar Λ f).rightDerivedFunctor.obj
        (A ⊗ (upperStar Λ f).leftDerivedFunctor.obj B)
```

```lean
theorem isIso_projectionMate_localizing_finiteExtension
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) Y)))
    (hA : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj E) X) A)
    (hB : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj E) Y) B) :
    CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj E) Y)
        ((lowerStar (Profinite.continuousCoefficientRingObj E) p).rightDerivedFunctor.obj A ⊗ B) ∧
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj E) Y)
        ((lowerStar (Profinite.continuousCoefficientRingObj E) p).rightDerivedFunctor.obj
          (A ⊗ (upperStar (Profinite.continuousCoefficientRingObj E) p).leftDerivedFunctor.obj B)) ∧
      IsIso (moduleObjectProjectionMate (Profinite.continuousCoefficientRingObj E) p A B)
```

```lean
theorem isIso_projectionMate_localizing_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)))
    (hA : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X) A)
    (hB : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y) B) :
    CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y)
        ((lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj A ⊗ B) ∧
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y)
        ((lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
          (A ⊗ (upperStar (Profinite.padicAlgClRingObj ℓ) p).leftDerivedFunctor.obj B)) ∧
      IsIso (moduleObjectProjectionMate (Profinite.padicAlgClRingObj ℓ) p A B)
```

```lean
def tensorRepresentativeFormula
    (μ : Functor.leftDerivedDerivedTensor F ⟶ Functor.derivedTensorLeftDerived F) : Prop :=
  ∀ K P : CochainComplex C ℤ,
    ∃ q : (F.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj K P) ⟶
        HomologicalComplex.tensorObj
          ((F.mapHomologicalComplex (.up ℤ)).obj K)
          ((F.mapHomologicalComplex (.up ℤ)).obj P),
      (∀ (i j n : ℤ) (h : i + j = n),
        ∃ b : F.obj (K.X i ⊗ P.X j) ⟶ F.obj (K.X i) ⊗ F.obj (P.X j),
          G (K.X i) (P.X j) b ∧
          F.map (HomologicalComplex.ιTensorObj K P i j n h) ≫ q.f n =
            b ≫ HomologicalComplex.ιTensorObj
              ((F.mapHomologicalComplex (.up ℤ)).obj K)
              ((F.mapHomologicalComplex (.up ℤ)).obj P) i j n h) ∧
      (μ.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj P) ≫
          ((Functor.derivedTensorLeftDerivedCounit F).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K)).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
        ((Functor.leftDerivedDerivedTensorCounit F).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K)).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫ DerivedCategory.Q.map q
```

## New

```lean
public import Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
```

```lean
noncomputable def moduleObjectProjectionMate
    (A : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (lowerStar Λ f).rightDerivedFunctor.obj A ⊗ B ⟶
      (lowerStar Λ f).rightDerivedFunctor.obj
        (A ⊗ (@Functor.leftDerivedFunctor _ _ _ _ _ _ _ _ _
            (hasTensorFourShortcut Λ Y)
            (hasGoodTensorLeftShortcut Λ Y)
            (hasGoodTensorRightShortcut Λ Y)
            (upperStar Λ f)
            (upperStarAdditiveShortcut Λ f)
            inferInstance inferInstance
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorLeftShortcut Λ Y M) ℤ inferInstance)
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorRightShortcut Λ Y M) ℤ inferInstance)
            (flatResolutionModulesShortcut Λ Y)
            (projectionModuleHasDerived Λ Y)
            (projectionModuleHasDerived Λ X)
            (preservesKFlatQuasiIso_upperStar Λ f)).obj B)
```

```lean
theorem isIso_projectionMate_localizing_finiteExtension
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) Y)))
    (hA : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj E) X) A)
    (hB : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj E) Y) B) :
    CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj E) Y)
        ((lowerStar (Profinite.continuousCoefficientRingObj E) p).rightDerivedFunctor.obj A ⊗ B) ∧
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj E) Y)
        ((lowerStar (Profinite.continuousCoefficientRingObj E) p).rightDerivedFunctor.obj
          (A ⊗ (@Functor.leftDerivedFunctor _ _ _ _ _ _ _ _ _
            (hasTensorFourShortcut (Profinite.continuousCoefficientRingObj E) Y)
            (hasGoodTensorLeftShortcut (Profinite.continuousCoefficientRingObj E) Y)
            (hasGoodTensorRightShortcut (Profinite.continuousCoefficientRingObj E) Y)
            (upperStar (Profinite.continuousCoefficientRingObj E) p)
            (upperStarAdditiveShortcut (Profinite.continuousCoefficientRingObj E) p)
            inferInstance inferInstance
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorLeftShortcut
                (Profinite.continuousCoefficientRingObj E) Y M) ℤ inferInstance)
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorRightShortcut
                (Profinite.continuousCoefficientRingObj E) Y M) ℤ inferInstance)
            (flatResolutionModulesShortcut (Profinite.continuousCoefficientRingObj E) Y)
            (projectionModuleHasDerived (Profinite.continuousCoefficientRingObj E) Y)
            (projectionModuleHasDerived (Profinite.continuousCoefficientRingObj E) X)
            (preservesKFlatQuasiIso_upperStar
              (Profinite.continuousCoefficientRingObj E) p)).obj B)) ∧
      IsIso (moduleObjectProjectionMate (Profinite.continuousCoefficientRingObj E) p A B)
```

```lean
theorem isIso_projectionMate_localizing_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)))
    (hA : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X) A)
    (hB : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y) B) :
    CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y)
        ((lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj A ⊗ B) ∧
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y)
        ((lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
          (A ⊗ (@Functor.leftDerivedFunctor _ _ _ _ _ _ _ _ _
            (hasTensorFourShortcut (Profinite.padicAlgClRingObj ℓ) Y)
            (hasGoodTensorLeftShortcut (Profinite.padicAlgClRingObj ℓ) Y)
            (hasGoodTensorRightShortcut (Profinite.padicAlgClRingObj ℓ) Y)
            (upperStar (Profinite.padicAlgClRingObj ℓ) p)
            (upperStarAdditiveShortcut (Profinite.padicAlgClRingObj ℓ) p)
            inferInstance inferInstance
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorLeftShortcut
                (Profinite.padicAlgClRingObj ℓ) Y M) ℤ inferInstance)
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorRightShortcut
                (Profinite.padicAlgClRingObj ℓ) Y M) ℤ inferInstance)
            (flatResolutionModulesShortcut (Profinite.padicAlgClRingObj ℓ) Y)
            (projectionModuleHasDerived (Profinite.padicAlgClRingObj ℓ) Y)
            (projectionModuleHasDerived (Profinite.padicAlgClRingObj ℓ) X)
            (preservesKFlatQuasiIso_upperStar
              (Profinite.padicAlgClRingObj ℓ) p)).obj B)) ∧
      IsIso (moduleObjectProjectionMate (Profinite.padicAlgClRingObj ℓ) p A B)
```

```lean
def tensorRepresentativeFormula
    (μ : Functor.leftDerivedDerivedTensor F ⟶ Functor.derivedTensorLeftDerived F) : Prop :=
  ∀ K P : CochainComplex C ℤ,
    letI : HomologicalComplex.HasTensor K P := inferInstance
    letI : HomologicalComplex.HasTensor
        ((F.mapHomologicalComplex (.up ℤ)).obj K)
        ((F.mapHomologicalComplex (.up ℤ)).obj P) := inferInstance
    ∃ q : (F.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj K P) ⟶
        HomologicalComplex.tensorObj
          ((F.mapHomologicalComplex (.up ℤ)).obj K)
          ((F.mapHomologicalComplex (.up ℤ)).obj P),
      (∀ (i j n : ℤ) (h : i + j = n),
        ∃ b : F.obj (K.X i ⊗ P.X j) ⟶ F.obj (K.X i) ⊗ F.obj (P.X j),
          G (K.X i) (P.X j) b ∧
          F.map (HomologicalComplex.ιTensorObj K P i j n h) ≫ q.f n =
            b ≫ HomologicalComplex.ιTensorObj
              ((F.mapHomologicalComplex (.up ℤ)).obj K)
              ((F.mapHomologicalComplex (.up ℤ)).obj P) i j n h) ∧
      (μ.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj P) ≫
          ((Functor.derivedTensorLeftDerivedCounit F).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K)).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
        ((Functor.leftDerivedDerivedTensorCounit F).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K)).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫ DerivedCategory.Q.map q
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U2 | Explicit proof arguments; same functor and mate by proof irrelevance. The finite-extension hole is proved. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | `traceProjection` uses the same mate with the same type and value; no adaptation. |
| Sheaf.Paper.TateTwistedProjection | unclaimed | Its normalized mate family and heterogeneous equalities refer to the same map; no adaptation. |

The two public projection theorems and `tensorRepresentativeFormula` have no textual downstream
users outside their own file in the current source.
`tools/downstream.py --uses` finds the two mate consumers listed above. Both uses retain the
same morphism type; no consumer hypothesis or conclusion changes. No consumer source is edited.
Both unchanged consumer sources compile against the delivered module in the artifact-producing
three-file compile set (exit code 0; every file within the enforced 60-second limit).
The owning node's `lean.statement` records the explicit-proof presentation, with its paper
statement and dependencies unchanged except the separately documented proof route update.

## Status

landed 20261026T071205-L-3882322 2026-10-26 (merge of deliver/U2/Sheaf.Paper.RationalLocalizingProjectionFormula)
