# CategoryTheory.CbcLimitNormalized and scalar/open coherence interfaces

## Reason

Return repair (2026-10-25): the proof now consumes the existential `Coherence` API
introduced by the independent normalized-square repair. The change is confined to the
private proof helper; all public signatures and construction bodies of the returned
packet are preserved. A compatibility branch also accepts the older published record.
Fresh compilation checks the unchanged consumers and an isolated copy of the new
public existential interface; these diagnostic copies are not delivered.

The original file exceeded the 60-second single-file bound when the complete proof was
elaborated. Profiling isolated a large conversion in the public theorem: the termwise image
of a composite functor was being compared with the composite of the termwise images on
concrete pro-etale module categories. `cbcComplexSquare` performs this conversion once for
abstract categories and retains exactly the original natural isomorphism. The theorem now
uses this named square. The two large normalization predicates are proposition-valued
structures with one `equation` field containing their previous predicates verbatim; this
prevents automatic expansion and supplies a small projection API. A proof of either old
predicate is converted by its constructor, and its projection recovers exactly that predicate.
No hypothesis or conclusion is added or removed.

The other changed definition bodies are definitionally equal aliases of the existing canonical
constructions. In particular restriction on the slice still uses the literal restricted rings,
the generator remains the sheafified direct-sum injection, and the derived squares and tower
adjunction use the same localization composition factors. No arbitrary witness is selected
inside a definition, and all data definitions are complete constructions.

`lean/Challenge.lean` is untouched. Any target whose meaning uses these definitions should
receive the usual statement review, checking the equation fields and these definitional aliases.
No module under `lean/WeilConjectures/` is changed.

## Old

```lean
def CbcLimitNormalized
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB)
    (lambda : LA ⋙ F.mapDerivedCategory ≅ cbcTowerDerived F ⋙ LB) : Prop :=
  ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    F.mapDerivedCategory.map (etaA.app X) ≫ lambda.hom.app (DerivedCategory.Q.obj X) ≫
        LB.map ((cbcTowerFactors F).hom.app X) =
      F.mapDerivedCategoryFactors.hom.app (limit X.asFunctor) ≫
        DerivedCategory.Q.map
          (limit.lift _ ((F.mapHomologicalComplex (.up ℤ)).mapCone (limit.cone X.asFunctor))) ≫
        etaB.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj X)
```

```lean
def CbcAugmentationCompatible
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB)
    (lambda : LA ⋙ F.mapDerivedCategory ≅ cbcTowerDerived F ⋙ LB) : Prop :=
  ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (Q : CochainComplex A ℤ)
    (gamma : (Functor.const ℕᵒᵖ).obj Q ⟶ X.asFunctor),
    F.mapDerivedCategory.map
        (DerivedCategory.Q.map (limit.lift X.asFunctor ⟨Q, gamma⟩) ≫ etaA.app X) ≫
      lambda.hom.app (DerivedCategory.Q.obj X) ≫ LB.map ((cbcTowerFactors F).hom.app X) =
    F.mapDerivedCategoryFactors.hom.app Q ≫ DerivedCategory.Q.map
      (limit.lift _ ((F.mapHomologicalComplex (.up ℤ)).mapCone ⟨Q, gamma⟩)) ≫
        etaB.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj X)
```

```lean
def cbcDerivedSquare (e : F ⋙ G ≅ H ⋙ K) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ K.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso H K
```

```lean
def cbcDerivedTowerSquare
    [HasLimits A] [HasLimits B] [HasLimits C] [HasLimits D]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{wC} (ℕᵒᵖ ⥤ C)] [HasDerivedCategory.{wD} (ℕᵒᵖ ⥤ D)]
    (e : F ⋙ G ≅ H ⋙ K) :
    cbcTowerDerived F ⋙ cbcTowerDerived G ≅ cbcTowerDerived H ⋙ cbcTowerDerived K :=
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B D).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B D).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A C).obj H) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A C).obj H) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj K) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj K) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  cbcDerivedSquare ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)
    ((Functor.whiskeringRight ℕᵒᵖ B D).obj G)
    ((Functor.whiskeringRight ℕᵒᵖ A C).obj H)
    ((Functor.whiskeringRight ℕᵒᵖ C D).obj K)
    ((Functor.whiskeringRight ℕᵒᵖ A D).mapIso e)
```

```lean
def cbcDerivedTowerAdjunction
    {A B : Type uA} [Category.{vA} A] [Category.{vA} B] [Abelian A] [Abelian B]
    [HasLimits A] [HasLimits B]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ B)]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G) :
    cbcTowerDerived F ⊣ cbcTowerDerived G :=
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction (adj.whiskerRight ℕᵒᵖ)
```

```lean
def cbcSliceScalarRestriction :
    ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U) ⥤
      ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U) :=
  scalarRestriction.{u + 1, u, u + 1} (cbcSliceCoefficientMap U a)
```

```lean
def cbcExtensionGenerator (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (N : ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)) (V : T.ProEtᵒᵖ)
    (phi : V.unop ⟶ U) (x : N.val.obj (op (Over.mk phi))) :
    ((localizedSystemExtension.{u + 1, u, 0} R U).obj N).val.obj V :=
  ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1} (𝟙
    (proEtaleModuleCoefficients R).obj)).unit.app
    ((extensionByZeroPresheaf.{u + 1} (proEtaleModuleCoefficients R) U).obj N)).app V
      (DirectSum.of (fun psi : V.unop ⟶ U ↦ N.val.obj (op (Over.mk psi))) phi x)
```

The original theorem signature:

```lean
theorem ringedOpenScalarLimitCoherence
    [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (LUR : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        R).over U)) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)))
    (etaUR : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LUR)
    (_hUR : LUR.IsRightDerivedFunctor etaUR
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        R).over U)) (.up
        ℤ)))
    (LUS : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
      S).over U)) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U)))
    (etaUS : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LUS)
    (_hUS : LUS.IsRightDerivedFunctor etaUS
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        S).over U)) (.up
        ℤ)))
    (LTR : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R)) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R)))
    (etaTR : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LTR)
    (_hTR : LTR.IsRightDerivedFunctor etaTR
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))
        (.up
        ℤ)))
    (LTS : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S)) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S)))
    (etaTS : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LTS)
    (_hTS : LTS.IsRightDerivedFunctor etaTS
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S))
        (.up
        ℤ)))
    : ∃ (e : (localizedSystemExtension.{u + 1, u, 0} S U) ⋙ (scalarRestriction.{u + 1, u, u + 1} a)
      ≅
        (cbcSliceScalarRestriction U a) ⋙
          (localizedSystemExtension.{u + 1, u, 0} R
          U))
      (d : (scalarRestriction.{u + 1, u, u + 1} a) ⋙ (localizedSystemRestriction.{u + 1, u, 0} R U)
        ≅
        (localizedSystemRestriction.{u + 1, u, 0} S U) ⋙ (cbcSliceScalarRestriction U a)),
      (∀ (N : ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U))
        (V : T.ProEtᵒᵖ) (phi : V.unop ⟶ U) (x : N.val.obj (op (Over.mk phi))),
        (e.hom.app N).val.app V (cbcExtensionGenerator U S N V phi x) =
          cbcExtensionGenerator U R
            ((cbcSliceScalarRestriction U a).obj N) V phi x) ∧
      (∀ (Q : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S)) (V : (Over U)ᵒᵖ)
        (x : ((scalarRestriction.{u + 1, u, u + 1} a ⋙ localizedSystemRestriction.{u + 1, u, 0} R
          U).obj Q).val.obj
          V),
        (d.hom.app Q).val.app V x = x) ∧
      CbcAdjunctionCompatible
        (JS := localizedSystemExtension.{u + 1, u, 0} S U)
        (JR := localizedSystemExtension.{u + 1, u, 0} R U)
        (rT := scalarRestriction.{u + 1, u, u + 1} a)
        (rU := cbcSliceScalarRestriction U a)
        (qS := localizedSystemRestriction.{u + 1, u, 0} S U)
        (qR := localizedSystemRestriction.{u + 1, u, 0} R U)
        e d (localizedSystemAdjunction.{u + 1, u, 0} S U)
        (localizedSystemAdjunction.{u + 1, u, 0} R U) ∧
      CbcAdjunctionCompatible
        (JS := (localizedSystemExtension.{u + 1, u, 0} S U).mapHomologicalComplex (.up ℤ))
        (JR := (localizedSystemExtension.{u + 1, u, 0} R U).mapHomologicalComplex (.up ℤ))
        (rT := (scalarRestriction.{u + 1, u, u + 1} a).mapHomologicalComplex (.up ℤ))
        (rU := (cbcSliceScalarRestriction U a).mapHomologicalComplex (.up ℤ))
        (qS := (localizedSystemRestriction.{u + 1, u, 0} S U).mapHomologicalComplex (.up ℤ))
        (qR := (localizedSystemRestriction.{u + 1, u, 0} R U).mapHomologicalComplex (.up ℤ))
        (NatIso.mapHomologicalComplex e (.up ℤ))
        (NatIso.mapHomologicalComplex d (.up ℤ))
        ((localizedSystemAdjunction.{u + 1, u, 0} S U).mapHomologicalComplex (.up ℤ))
        ((localizedSystemAdjunction.{u + 1, u, 0} R U).mapHomologicalComplex (.up ℤ)) ∧
      CbcAdjunctionCompatible
        (JS := cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} S U))
        (JR := cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} R U))
        (rT := cbcTowerDerived (scalarRestriction.{u + 1, u, u + 1} a))
        (rU := cbcTowerDerived (cbcSliceScalarRestriction U a))
        (qS := cbcTowerDerived (localizedSystemRestriction.{u + 1, u, 0} S U))
        (qR := cbcTowerDerived (localizedSystemRestriction.{u + 1, u, 0} R U))
        (cbcDerivedTowerSquare (localizedSystemExtension.{u + 1, u, 0} S U) (scalarRestriction.{u +
          1, u, u + 1} a)
          (cbcSliceScalarRestriction U a)
            (localizedSystemExtension.{u + 1, u, 0} R
            U) e)
        (cbcDerivedTowerSquare (scalarRestriction.{u + 1, u, u + 1} a)
          (localizedSystemRestriction.{u + 1, u, 0} R U)
          (localizedSystemRestriction.{u + 1, u, 0} S U) (cbcSliceScalarRestriction U a) d)
        (cbcDerivedTowerAdjunction (localizedSystemAdjunction.{u + 1, u, 0} S U))
        (cbcDerivedTowerAdjunction (localizedSystemAdjunction.{u + 1, u, 0} R U)) ∧
      HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        R).over U)) ∧
      HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        S).over U)) ∧
      HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))
        ∧
      HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S))
        ∧
      (∀ (I : Type (u + 1)) (N : I → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over
        U)),
        IsIso (piComparison (localizedSystemExtension.{u + 1, u, 0} S U) N)) ∧
      (∀ (I : Type (u + 1)) (N : I → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over
        U)),
        IsIso (piComparison (localizedSystemExtension.{u + 1, u, 0} R U) N)) ∧
      (∀ (I : Type (u + 1)) (N : I → ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S)),
        IsIso (piComparison (scalarRestriction.{u + 1, u, u + 1} a) N)) ∧
      (∀ (I : Type (u + 1)) (N : I → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over
        U)),
        IsIso (piComparison (cbcSliceScalarRestriction U a) N)) ∧
      ∃ (lambdaJS : LUS ⋙ (localizedSystemExtension.{u + 1, u, 0} S U).mapDerivedCategory ≅
          cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} S U) ⋙ LTS)
        (lambdarT : LTS ⋙ (scalarRestriction.{u + 1, u, u + 1} a).mapDerivedCategory ≅
          cbcTowerDerived (scalarRestriction.{u + 1, u, u + 1} a) ⋙ LTR)
        (lambdarU : LUS ⋙ (cbcSliceScalarRestriction U a).mapDerivedCategory ≅
          cbcTowerDerived (cbcSliceScalarRestriction U a) ⋙ LUR)
        (lambdaJR : LUR ⋙ (localizedSystemExtension.{u + 1, u, 0} R U).mapDerivedCategory ≅
          cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} R U) ⋙ LTR),
        CbcLimitNormalized (localizedSystemExtension.{u + 1, u, 0} S U) LUS LTS etaUS etaTS lambdaJS
          ∧
        CbcLimitNormalized (scalarRestriction.{u + 1, u, u + 1} a) LTS LTR etaTS etaTR lambdarT ∧
        CbcLimitNormalized (cbcSliceScalarRestriction U a) LUS
          LUR etaUS etaUR
          lambdarU ∧
        CbcLimitNormalized (localizedSystemExtension.{u + 1, u, 0} R U) LUR LTR etaUR etaTR lambdaJR
          ∧
        CbcAugmentationCompatible (localizedSystemExtension.{u + 1, u, 0} S U) LUS LTS
          etaUS etaTS lambdaJS ∧
        CbcAugmentationCompatible (scalarRestriction.{u + 1, u, u + 1} a) LTS LTR
          etaTS etaTR lambdarT ∧
        CbcAugmentationCompatible (cbcSliceScalarRestriction U a)
          LUS LUR
          etaUS etaUR lambdarU ∧
        CbcAugmentationCompatible (localizedSystemExtension.{u + 1, u, 0} R U) LUR LTR
          etaUR etaTR lambdaJR ∧
        ∀ M : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
          S).over U)),
          (scalarRestriction.{u + 1, u, u + 1} a).mapDerivedCategory.map (lambdaJS.hom.app M) ≫
            lambdarT.hom.app ((cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} S U)).obj M)
              ≫
            LTR.map ((cbcDerivedTowerSquare (localizedSystemExtension.{u + 1, u, 0} S U)
              (scalarRestriction.{u + 1, u, u + 1} a)
              (cbcSliceScalarRestriction U a)
                (localizedSystemExtension.{u + 1, u,
                0} R U)
              e).hom.app M) =
          (cbcDerivedSquare (localizedSystemExtension.{u + 1, u, 0} S U) (scalarRestriction.{u + 1,
            u, u + 1} a)
            (cbcSliceScalarRestriction U a) (localizedSystemExtension.{u + 1, u, 0} R U) e).hom.app
              (LUS.obj M) ≫
            (localizedSystemExtension.{u + 1, u, 0} R U).mapDerivedCategory.map (lambdarU.hom.app M)
              ≫
            lambdaJR.hom.app ((cbcTowerDerived (cbcSliceScalarRestriction U a)).obj
              M)
```

## New

```lean
structure CbcLimitNormalized
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB)
    (lambda : LA ⋙ F.mapDerivedCategory ≅ cbcTowerDerived F ⋙ LB) : Prop where
  equation : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    F.mapDerivedCategory.map (etaA.app X) ≫ lambda.hom.app (DerivedCategory.Q.obj X) ≫
        LB.map ((cbcTowerFactors F).hom.app X) =
      F.mapDerivedCategoryFactors.hom.app (limit X.asFunctor) ≫
        DerivedCategory.Q.map
          (limit.lift _ ((F.mapHomologicalComplex (.up ℤ)).mapCone (limit.cone X.asFunctor))) ≫
        etaB.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj X)
```

```lean
structure CbcAugmentationCompatible
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB)
    (lambda : LA ⋙ F.mapDerivedCategory ≅ cbcTowerDerived F ⋙ LB) : Prop where
  equation : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (Q : CochainComplex A ℤ)
    (gamma : (Functor.const ℕᵒᵖ).obj Q ⟶ X.asFunctor),
    F.mapDerivedCategory.map
        (DerivedCategory.Q.map (limit.lift X.asFunctor ⟨Q, gamma⟩) ≫ etaA.app X) ≫
      lambda.hom.app (DerivedCategory.Q.obj X) ≫ LB.map ((cbcTowerFactors F).hom.app X) =
    F.mapDerivedCategoryFactors.hom.app Q ≫ DerivedCategory.Q.map
      (limit.lift _ ((F.mapHomologicalComplex (.up ℤ)).mapCone ⟨Q, gamma⟩)) ≫
        etaB.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj X)
```

```lean
def cbcDerivedSquare (e : F ⋙ G ≅ H ⋙ K) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ K.mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso e
```

```lean
def cbcDerivedTowerSquare
    [HasLimits A] [HasLimits B] [HasLimits C] [HasLimits D]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{wC} (ℕᵒᵖ ⥤ C)] [HasDerivedCategory.{wD} (ℕᵒᵖ ⥤ D)]
    (e : F ⋙ G ≅ H ⋙ K) :
    cbcTowerDerived F ⋙ cbcTowerDerived G ≅ cbcTowerDerived H ⋙ cbcTowerDerived K :=
  CategoryTheory.NormalizedLimitSquare.towerSquare F G H K e
```

```lean
def cbcDerivedTowerAdjunction
    {A B : Type uA} [Category.{vA} A] [Category.{vA} B] [Abelian A] [Abelian B]
    [HasLimits A] [HasLimits B]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ B)]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G) :
    cbcTowerDerived F ⊣ cbcTowerDerived G :=
  CategoryTheory.RoosAdjunctionUnit.towerAdjunction adj
```

```lean
def cbcSliceScalarRestriction :
    ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U) ⥤
      ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U) :=
  RingedOpenScalar.sliceScalars.{u + 1, u, 0} U a
```

```lean
def cbcExtensionGenerator (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (N : ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)) (V : T.ProEtᵒᵖ)
    (phi : V.unop ⟶ U) (x : N.val.obj (op (Over.mk phi))) :
    ((localizedSystemExtension.{u + 1, u, 0} R U).obj N).val.obj V :=
  RingedOpenScalar.generator.{u + 1, u, 0} U R N V phi x
```

The new typed wrapper:

```lean
def cbcComplexSquare
    {A : Type uA} [Category.{vA} A] [Preadditive A]
    {B : Type uB} [Category.{vB} B] [Preadditive B]
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive] (e : F ⋙ G ≅ H ⋙ K) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ K.mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex e (.up ℤ)
```

The theorem signature with only its two complex-square expressions rewritten:

```lean
theorem ringedOpenScalarLimitCoherence
    [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (LUR : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        R).over U)) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)))
    (etaUR : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LUR)
    (_hUR : LUR.IsRightDerivedFunctor etaUR
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        R).over U)) (.up
        ℤ)))
    (LUS : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
      S).over U)) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U)))
    (etaUS : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LUS)
    (_hUS : LUS.IsRightDerivedFunctor etaUS
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        S).over U)) (.up
        ℤ)))
    (LTR : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R)) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R)))
    (etaTR : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LTR)
    (_hTR : LTR.IsRightDerivedFunctor etaTR
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))
        (.up
        ℤ)))
    (LTS : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S)) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S)))
    (etaTS : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LTS)
    (_hTS : LTS.IsRightDerivedFunctor etaTS
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S))
        (.up
        ℤ)))
    : ∃ (e : (localizedSystemExtension.{u + 1, u, 0} S U) ⋙ (scalarRestriction.{u + 1, u, u + 1} a)
      ≅
        (cbcSliceScalarRestriction U a) ⋙
          (localizedSystemExtension.{u + 1, u, 0} R
          U))
      (d : (scalarRestriction.{u + 1, u, u + 1} a) ⋙ (localizedSystemRestriction.{u + 1, u, 0} R U)
        ≅
        (localizedSystemRestriction.{u + 1, u, 0} S U) ⋙ (cbcSliceScalarRestriction U a)),
      (∀ (N : ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over U))
        (V : T.ProEtᵒᵖ) (phi : V.unop ⟶ U) (x : N.val.obj (op (Over.mk phi))),
        (e.hom.app N).val.app V (cbcExtensionGenerator U S N V phi x) =
          cbcExtensionGenerator U R
            ((cbcSliceScalarRestriction U a).obj N) V phi x) ∧
      (∀ (Q : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S)) (V : (Over U)ᵒᵖ)
        (x : ((scalarRestriction.{u + 1, u, u + 1} a ⋙ localizedSystemRestriction.{u + 1, u, 0} R
          U).obj Q).val.obj
          V),
        (d.hom.app Q).val.app V x = x) ∧
      CbcAdjunctionCompatible
        (JS := localizedSystemExtension.{u + 1, u, 0} S U)
        (JR := localizedSystemExtension.{u + 1, u, 0} R U)
        (rT := scalarRestriction.{u + 1, u, u + 1} a)
        (rU := cbcSliceScalarRestriction U a)
        (qS := localizedSystemRestriction.{u + 1, u, 0} S U)
        (qR := localizedSystemRestriction.{u + 1, u, 0} R U)
        e d (localizedSystemAdjunction.{u + 1, u, 0} S U)
        (localizedSystemAdjunction.{u + 1, u, 0} R U) ∧
      CbcAdjunctionCompatible
        (JS := (localizedSystemExtension.{u + 1, u, 0} S U).mapHomologicalComplex (.up ℤ))
        (JR := (localizedSystemExtension.{u + 1, u, 0} R U).mapHomologicalComplex (.up ℤ))
        (rT := (scalarRestriction.{u + 1, u, u + 1} a).mapHomologicalComplex (.up ℤ))
        (rU := (cbcSliceScalarRestriction U a).mapHomologicalComplex (.up ℤ))
        (qS := (localizedSystemRestriction.{u + 1, u, 0} S U).mapHomologicalComplex (.up ℤ))
        (qR := (localizedSystemRestriction.{u + 1, u, 0} R U).mapHomologicalComplex (.up ℤ))
        (cbcComplexSquare (localizedSystemExtension.{u + 1, u, 0} S U)
          (scalarRestriction.{u + 1, u, u + 1} a) (cbcSliceScalarRestriction U a)
          (localizedSystemExtension.{u + 1, u, 0} R U) e)
        (cbcComplexSquare (scalarRestriction.{u + 1, u, u + 1} a)
          (localizedSystemRestriction.{u + 1, u, 0} R U)
          (localizedSystemRestriction.{u + 1, u, 0} S U) (cbcSliceScalarRestriction U a) d)
        ((localizedSystemAdjunction.{u + 1, u, 0} S U).mapHomologicalComplex (.up ℤ))
        ((localizedSystemAdjunction.{u + 1, u, 0} R U).mapHomologicalComplex (.up ℤ)) ∧
      CbcAdjunctionCompatible
        (JS := cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} S U))
        (JR := cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} R U))
        (rT := cbcTowerDerived (scalarRestriction.{u + 1, u, u + 1} a))
        (rU := cbcTowerDerived (cbcSliceScalarRestriction U a))
        (qS := cbcTowerDerived (localizedSystemRestriction.{u + 1, u, 0} S U))
        (qR := cbcTowerDerived (localizedSystemRestriction.{u + 1, u, 0} R U))
        (cbcDerivedTowerSquare (localizedSystemExtension.{u + 1, u, 0} S U) (scalarRestriction.{u +
          1, u, u + 1} a)
          (cbcSliceScalarRestriction U a)
            (localizedSystemExtension.{u + 1, u, 0} R
            U) e)
        (cbcDerivedTowerSquare (scalarRestriction.{u + 1, u, u + 1} a)
          (localizedSystemRestriction.{u + 1, u, 0} R U)
          (localizedSystemRestriction.{u + 1, u, 0} S U) (cbcSliceScalarRestriction U a) d)
        (cbcDerivedTowerAdjunction (localizedSystemAdjunction.{u + 1, u, 0} S U))
        (cbcDerivedTowerAdjunction (localizedSystemAdjunction.{u + 1, u, 0} R U)) ∧
      HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        R).over U)) ∧
      HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
        S).over U)) ∧
      HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))
        ∧
      HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S))
        ∧
      (∀ (I : Type (u + 1)) (N : I → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over
        U)),
        IsIso (piComparison (localizedSystemExtension.{u + 1, u, 0} S U) N)) ∧
      (∀ (I : Type (u + 1)) (N : I → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over
        U)),
        IsIso (piComparison (localizedSystemExtension.{u + 1, u, 0} R U) N)) ∧
      (∀ (I : Type (u + 1)) (N : I → ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S)),
        IsIso (piComparison (scalarRestriction.{u + 1, u, u + 1} a) N)) ∧
      (∀ (I : Type (u + 1)) (N : I → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over
        U)),
        IsIso (piComparison (cbcSliceScalarRestriction U a) N)) ∧
      ∃ (lambdaJS : LUS ⋙ (localizedSystemExtension.{u + 1, u, 0} S U).mapDerivedCategory ≅
          cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} S U) ⋙ LTS)
        (lambdarT : LTS ⋙ (scalarRestriction.{u + 1, u, u + 1} a).mapDerivedCategory ≅
          cbcTowerDerived (scalarRestriction.{u + 1, u, u + 1} a) ⋙ LTR)
        (lambdarU : LUS ⋙ (cbcSliceScalarRestriction U a).mapDerivedCategory ≅
          cbcTowerDerived (cbcSliceScalarRestriction U a) ⋙ LUR)
        (lambdaJR : LUR ⋙ (localizedSystemExtension.{u + 1, u, 0} R U).mapDerivedCategory ≅
          cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} R U) ⋙ LTR),
        CbcLimitNormalized (localizedSystemExtension.{u + 1, u, 0} S U) LUS LTS etaUS etaTS lambdaJS
          ∧
        CbcLimitNormalized (scalarRestriction.{u + 1, u, u + 1} a) LTS LTR etaTS etaTR lambdarT ∧
        CbcLimitNormalized (cbcSliceScalarRestriction U a) LUS
          LUR etaUS etaUR
          lambdarU ∧
        CbcLimitNormalized (localizedSystemExtension.{u + 1, u, 0} R U) LUR LTR etaUR etaTR lambdaJR
          ∧
        CbcAugmentationCompatible (localizedSystemExtension.{u + 1, u, 0} S U) LUS LTS
          etaUS etaTS lambdaJS ∧
        CbcAugmentationCompatible (scalarRestriction.{u + 1, u, u + 1} a) LTS LTR
          etaTS etaTR lambdarT ∧
        CbcAugmentationCompatible (cbcSliceScalarRestriction U a)
          LUS LUR
          etaUS etaUR lambdarU ∧
        CbcAugmentationCompatible (localizedSystemExtension.{u + 1, u, 0} R U) LUR LTR
          etaUR etaTR lambdaJR ∧
        ∀ M : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients
          S).over U)),
          (scalarRestriction.{u + 1, u, u + 1} a).mapDerivedCategory.map (lambdaJS.hom.app M) ≫
            lambdarT.hom.app ((cbcTowerDerived (localizedSystemExtension.{u + 1, u, 0} S U)).obj M)
              ≫
            LTR.map ((cbcDerivedTowerSquare (localizedSystemExtension.{u + 1, u, 0} S U)
              (scalarRestriction.{u + 1, u, u + 1} a)
              (cbcSliceScalarRestriction U a)
                (localizedSystemExtension.{u + 1, u,
                0} R U)
              e).hom.app M) =
          (cbcDerivedSquare (localizedSystemExtension.{u + 1, u, 0} S U) (scalarRestriction.{u + 1,
            u, u + 1} a)
            (cbcSliceScalarRestriction U a) (localizedSystemExtension.{u + 1, u, 0} R U) e).hom.app
              (LUS.obj M) ≫
            (localizedSystemExtension.{u + 1, u, 0} R U).mapDerivedCategory.map (lambdarU.hom.app M)
              ≫
            lambdaJR.hom.app ((cbcTowerDerived (cbcSliceScalarRestriction U a)).obj
              M)
```

## Users

`tools/downstream.py` finds exactly the following four downstream modules. Searches for
`CbcLimitNormalized`, `CbcAugmentationCompatible`, `CbcAdjunctionCompatible`,
`cbcSliceScalarRestriction`, `cbcExtensionGenerator`, and `cbcDerivedTowerAdjunction`
find no external explicit users. `cbcDerivedSquare` and `cbcDerivedTowerSquare` are used
by the endpoint module; `cbcTowerDerived` is also used by the intermediate-tower module.
The two tower abbreviations have not changed. All four original downstream sources are
compiled against the repaired item, without adapting any of them.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingedOpenScalarLimitCoherence | X3 | proof and definition API repair |
| Sheaf.Paper.CompletedOpenEndpointLimitTransport | unclaimed | definitionally equal derived squares; no edit |
| Sheaf.Paper.CompletedSupportIntermediateTower | unclaimed | unchanged tower functor; no edit |
| Sheaf.Paper.PurStrictIntegralExchangeNormalization | unclaimed | transitive importer; no edit |
| Sheaf.Paper.SemilinearOpenClosedComplexSequence | unclaimed | transitive importer; no edit |

## Status

landed 20261024T224950-L-1836502 2026-10-24 (merge of deliver/X3/Sheaf.Paper.RingedOpenScalarLimitCoherence)
