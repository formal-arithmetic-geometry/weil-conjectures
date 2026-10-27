# CoefficientDerivedSections functor boundaries and canonical transports

## Reason

Scalar-composition equations force Lean to expand sheaf restriction, its scalar actions,
and global sections repeatedly. Full proofs exceed the 60-second file limit.
Use ordinary functor definitions and write the canonical underived identifications in the
normalization equations. This changes the presentation, with the same categories,
functors, hypotheses and canonical maps. No Challenge declaration or source-tree file changes.

## Old

```lean
abbrev coefficientModules (R : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u, u, u, u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

abbrev coefficientRestriction {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    coefficientModules S ⥤ coefficientModules R :=
  SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map a)

abbrev coefficientSections (R : Sheaf J CommRingCat.{u}) :
    coefficientModules R ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf _ ⋙ Sheaf.Γ J AddCommGrpCat.{u}

abbrev coefficientComplexRestriction {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :=
  (coefficientRestriction a).mapHomologicalComplex (ComplexShape.up ℤ)

abbrev coefficientComplexSections (R : Sheaf J CommRingCat.{u}) :
    CochainComplex (coefficientModules R) ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  (SheafOfModules.toSheaf _).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    @Functor.mapHomologicalComplex ℤ _ _ _ _ _ _ (Sheaf.Γ J AddCommGrpCat.{u})
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
        (Sheaf.Γ J AddCommGrpCat.{u}) (Sheaf.Γ_additive J AddCommGrpCat.{u}))
      (ComplexShape.up ℤ)

```

Original scalar-coherence signature:

```lean
theorem derivedSectionsScalarCoherence
    [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory.{w} (coefficientModules R)]
    [HasDerivedCategory.{w} AddCommGrpCat.{u}] :
    (∀ R : Sheaf J CommRingCat.{u},
      ∃ (g : RingedToposMorphism
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
          ((sheafCompose sectionsPointTopology
            (forget₂ CommRingCat.{u} RingCat.{u})).obj sectionsPointIntegers))
        (e : g.inverse ≅ sectionsPointSets ⋙ constantSheaf J (Type u)),
        Nonempty (g.direct ⋙ sectionsPointSets ≅ Sheaf.Γ J (Type u)) ∧
        Nonempty (g.modules ⋙ sectionsPointAbelian ≅ coefficientSections R) ∧
        ∀ (U : Cᵒᵖ) (n : ULift.{u} ℤ),
          g.ringMap.hom.app U
            ((e.inv.app ((sheafCompose sectionsPointTopology (forget RingCat.{u})).obj
              ((sheafCompose sectionsPointTopology
                (forget₂ CommRingCat.{u} RingCat.{u})).obj sectionsPointIntegers))).hom.app U
                  ((toSheafify J ((Functor.const Cᵒᵖ).obj (ULift.{u} ℤ))).app U n)) =
                    (n.down : R.obj.obj U)) ∧
    ∃ (H : ∀ R : Sheaf J CommRingCat.{u},
        DerivedCategory (coefficientModules R) ⥤ DerivedCategory AddCommGrpCat.{u})
      (η : ∀ R : Sheaf J CommRingCat.{u},
        coefficientComplexSections R ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ H R),
      (∀ R : Sheaf J CommRingCat.{u}, (H R).IsRightDerivedFunctor (η R)
        (HomologicalComplex.quasiIso (coefficientModules R) (ComplexShape.up ℤ))) ∧
      (∀ (R : Sheaf J CommRingCat.{u}) (I : CochainComplex (coefficientModules R) ℤ),
        I.IsKInjective → IsIso ((η R).app I)) ∧
      ∃ (r : ∀ {R S : Sheaf J CommRingCat.{u}}, (R ⟶ S) →
          DerivedCategory (coefficientModules S) ⥤ DerivedCategory (coefficientModules R))
        (ν : ∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S),
          DerivedCategory.Q ⋙ r a ≅ coefficientComplexRestriction a ⋙ DerivedCategory.Q)
        (σ : ∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S), H S ⟶ r a ⋙ H R),
        (∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S),
          IsIso (σ a) ∧
          (∀ M : CochainComplex (coefficientModules S) ℤ,
            (η S).app M ≫ (σ a).app (DerivedCategory.Q.obj M) =
              (η R).app ((coefficientComplexRestriction a).obj M) ≫
                (H R).map ((ν a).inv.app M)) ∧
          (∀ τ : H S ⟶ r a ⋙ H R,
            (∀ M : CochainComplex (coefficientModules S) ℤ,
              (η S).app M ≫ τ.app (DerivedCategory.Q.obj M) =
                (η R).app ((coefficientComplexRestriction a).obj M) ≫
                  (H R).map ((ν a).inv.app M)) → τ = σ a) ∧
          ∀ (I : CochainComplex (coefficientModules S) ℤ), I.IsKInjective →
          ∀ (K : CochainComplex (coefficientModules R) ℤ), K.IsKInjective →
          ∀ (j : (coefficientComplexRestriction a).obj I ⟶ K), ∀ [QuasiIso j],
            QuasiIso ((coefficientComplexSections R).map j) ∧
            (η S).app I ≫ (σ a).app (DerivedCategory.Q.obj I) ≫
              (H R).map ((ν a).hom.app I) ≫ (H R).map (DerivedCategory.Q.map j) =
                DerivedCategory.Q.map ((coefficientComplexSections R).map j) ≫
                  (η R).app K) ∧
        (∀ {R S T : Sheaf J CommRingCat.{u}} (a : R ⟶ S) (b : S ⟶ T),
          ∃ c : r (a ≫ b) ≅ r b ⋙ r a,
            (∀ M : CochainComplex (coefficientModules T) ℤ,
              c.hom.app (DerivedCategory.Q.obj M) ≫
                (r a).map ((ν b).hom.app M) ≫
                  (ν a).hom.app ((coefficientComplexRestriction b).obj M) =
                    (ν (a ≫ b)).hom.app M) ∧
            ∀ X : DerivedCategory (coefficientModules T),
              (σ (a ≫ b)).app X ≫ (H R).map (c.hom.app X) =
                (σ b).app X ≫ (σ a).app ((r b).obj X)) ∧
        ∀ R : Sheaf J CommRingCat.{u}, ∃ i : r (𝟙 R) ≅ 𝟭 _,
          (∀ M : CochainComplex (coefficientModules R) ℤ,
            i.hom.app (DerivedCategory.Q.obj M) = (ν (𝟙 R)).hom.app M) ∧
          ∀ X : DerivedCategory (coefficientModules R),
            (σ (𝟙 R)).app X ≫ (H R).map (i.hom.app X) = 𝟙 ((H R).obj X)
```

## New

The coefficient category remains the original abbreviation and uses native Mathlib
instances. Restriction, sections, and their prolongations are ordinary definitions
of the same data. `CoefficientSectionsGeometry` names exactly the old geometric clause,
including all identifications and the integer-map equation. The declarations are:

```lean
abbrev coefficientModules (R : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u, u, u, u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

def coefficientRestriction {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    coefficientModules S ⥤ coefficientModules R :=
  SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map a)

instance coefficientRestriction_additive {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    (coefficientRestriction a).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map a)).Additive

def coefficientSections (R : Sheaf J CommRingCat.{u}) :
    coefficientModules R ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf _ ⋙ Sheaf.Γ J AddCommGrpCat.{u}

instance coefficientSections_additive (R : Sheaf J CommRingCat.{u}) :
    (coefficientSections R).Additive := by
  change (SheafOfModules.toSheaf _ ⋙ Sheaf.Γ J AddCommGrpCat.{u}).Additive
  infer_instance

instance coefficientSections_preservesFiniteLimits (R : Sheaf J CommRingCat.{u}) :
    PreservesFiniteLimits (coefficientSections R) := by
  unfold coefficientSections
  infer_instance

def coefficientComplexRestriction {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :=
  (coefficientRestriction a).mapHomologicalComplex (ComplexShape.up ℤ)

def coefficientComplexSections (R : Sheaf J CommRingCat.{u}) :=
  (coefficientSections R).mapHomologicalComplex (.up ℤ)

def coefficientRestrictionComp {R S T : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ T) :
    coefficientRestriction b ⋙ coefficientRestriction a ≅ coefficientRestriction (a ≫ b) :=
  Iso.refl _

def coefficientComplexRestrictionComp {R S T : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ T) :
    coefficientComplexRestriction b ⋙ coefficientComplexRestriction a ≅
      coefficientComplexRestriction (a ≫ b) :=
  Functor.mapHomologicalComplexCompIso (coefficientRestrictionComp a b) (.up ℤ)

def coefficientRestrictionId (R : Sheaf J CommRingCat.{u}) :
    coefficientRestriction (𝟙 R) ≅ 𝟭 (coefficientModules R) := Iso.refl _

def coefficientComplexRestrictionId (R : Sheaf J CommRingCat.{u}) :
    coefficientComplexRestriction (𝟙 R) ≅ 𝟭 (CochainComplex (coefficientModules R) ℤ) :=
  NatIso.mapHomologicalComplex (coefficientRestrictionId R) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (coefficientModules R) (.up ℤ)

def coefficientRestrictionForget {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    coefficientRestriction a ⋙ SheafOfModules.toSheaf.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ≅
      SheafOfModules.toSheaf.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S) := Iso.refl _

def coefficientSectionsRestriction {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    coefficientRestriction a ⋙ coefficientSections R ≅ coefficientSections S :=
  Functor.isoWhiskerRight (coefficientRestrictionForget a) (Sheaf.Γ J AddCommGrpCat.{u})

def coefficientComplexSectionsRestriction {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    coefficientComplexSections S ≅
      coefficientComplexRestriction a ⋙ coefficientComplexSections R :=
  (Functor.mapHomologicalComplexCompIso (coefficientSectionsRestriction a) (.up ℤ)).symm

def CoefficientSectionsGeometry (R : Sheaf J CommRingCat.{u}) : Prop :=
      ∃ (g : RingedToposMorphism
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
          ((sheafCompose sectionsPointTopology
            (forget₂ CommRingCat.{u} RingCat.{u})).obj sectionsPointIntegers))
        (e : g.inverse ≅ sectionsPointSets ⋙ constantSheaf J (Type u)),
        Nonempty (g.direct ⋙ sectionsPointSets ≅ Sheaf.Γ J (Type u)) ∧
        Nonempty (g.modules ⋙ sectionsPointAbelian ≅ coefficientSections R) ∧
        ∀ (U : Cᵒᵖ) (n : ULift.{u} ℤ),
          g.ringMap.hom.app U
            ((e.inv.app ((sheafCompose sectionsPointTopology (forget RingCat.{u})).obj
              ((sheafCompose sectionsPointTopology
                (forget₂ CommRingCat.{u} RingCat.{u})).obj sectionsPointIntegers))).hom.app U
                  ((toSheafify J ((Functor.const Cᵒᵖ).obj (ULift.{u} ℤ))).app U n)) =
                    (n.down : R.obj.obj U)
```

The theorem signature is:

```lean
theorem derivedSectionsScalarCoherence
    [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory.{w} (coefficientModules R)]
    [HasDerivedCategory.{w} AddCommGrpCat.{u}] :
    (∀ R : Sheaf J CommRingCat.{u}, CoefficientSectionsGeometry R) ∧
    ∃ (H : ∀ R : Sheaf J CommRingCat.{u},
        DerivedCategory (coefficientModules R) ⥤ DerivedCategory AddCommGrpCat.{u})
      (η : ∀ R : Sheaf J CommRingCat.{u},
        coefficientComplexSections R ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ H R),
      (∀ R : Sheaf J CommRingCat.{u}, (H R).IsRightDerivedFunctor (η R)
        (HomologicalComplex.quasiIso (coefficientModules R) (ComplexShape.up ℤ))) ∧
      (∀ (R : Sheaf J CommRingCat.{u}) (I : CochainComplex (coefficientModules R) ℤ),
        I.IsKInjective → IsIso ((η R).app I)) ∧
      ∃ (r : ∀ {R S : Sheaf J CommRingCat.{u}}, (R ⟶ S) →
          DerivedCategory (coefficientModules S) ⥤ DerivedCategory (coefficientModules R))
        (ν : ∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S),
          DerivedCategory.Q ⋙ r a ≅ coefficientComplexRestriction a ⋙ DerivedCategory.Q)
        (σ : ∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S), H S ⟶ r a ⋙ H R),
        (∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S),
          IsIso (σ a) ∧
          (∀ M : CochainComplex (coefficientModules S) ℤ,
            (η S).app M ≫ (σ a).app (DerivedCategory.Q.obj M) =
              DerivedCategory.Q.map ((coefficientComplexSectionsRestriction a).hom.app M) ≫
              (η R).app ((coefficientComplexRestriction a).obj M) ≫
                (H R).map ((ν a).inv.app M)) ∧
          (∀ τ : H S ⟶ r a ⋙ H R,
            (∀ M : CochainComplex (coefficientModules S) ℤ,
              (η S).app M ≫ τ.app (DerivedCategory.Q.obj M) =
                DerivedCategory.Q.map ((coefficientComplexSectionsRestriction a).hom.app M) ≫
                  (η R).app ((coefficientComplexRestriction a).obj M) ≫
                  (H R).map ((ν a).inv.app M)) → τ = σ a) ∧
          ∀ (I : CochainComplex (coefficientModules S) ℤ), I.IsKInjective →
          ∀ (K : CochainComplex (coefficientModules R) ℤ), K.IsKInjective →
          ∀ (j : (coefficientComplexRestriction a).obj I ⟶ K), ∀ [QuasiIso j],
            QuasiIso ((coefficientComplexSections R).map j) ∧
            (η S).app I ≫ (σ a).app (DerivedCategory.Q.obj I) ≫
              (H R).map ((ν a).hom.app I) ≫ (H R).map (DerivedCategory.Q.map j) =
                DerivedCategory.Q.map ((coefficientComplexSectionsRestriction a).hom.app I) ≫
                  DerivedCategory.Q.map ((coefficientComplexSections R).map j) ≫
                    (η R).app K) ∧
        (∀ {R S T : Sheaf J CommRingCat.{u}} (a : R ⟶ S) (b : S ⟶ T),
          ∃ c : r (a ≫ b) ≅ r b ⋙ r a,
            (∀ M : CochainComplex (coefficientModules T) ℤ,
              c.hom.app (DerivedCategory.Q.obj M) ≫
                (r a).map ((ν b).hom.app M) ≫
                  (ν a).hom.app ((coefficientComplexRestriction b).obj M) ≫
                    DerivedCategory.Q.map ((coefficientComplexRestrictionComp a b).hom.app M) =
                    (ν (a ≫ b)).hom.app M) ∧
            ∀ X : DerivedCategory (coefficientModules T),
              (σ (a ≫ b)).app X ≫ (H R).map (c.hom.app X) =
                (σ b).app X ≫ (σ a).app ((r b).obj X)) ∧
        ∀ R : Sheaf J CommRingCat.{u}, ∃ i : r (𝟙 R) ≅ 𝟭 _,
          (∀ M : CochainComplex (coefficientModules R) ℤ,
            i.hom.app (DerivedCategory.Q.obj M) = (ν (𝟙 R)).hom.app M ≫
              DerivedCategory.Q.map ((coefficientComplexRestrictionId R).hom.app M)) ∧
          ∀ X : DerivedCategory (coefficientModules R),
            (σ (𝟙 R)).app X ≫ (H R).map (i.hom.app X) = 𝟙 ((H R).obj X)
```

The explicit factors transport the original equations along the canonical identity
maps on underlying abelian sheaves and their termwise lifts. The proof establishes
compatibility for sheaves, sections, complexes and localization. All hypotheses,
uniqueness, invertibility, representative formulas, and coherence normalizations stay.

Private localization constructions stay irreducible through final assembly. Finite
limit and colimit preservation is transported along the named forgetful comparison,
avoiding expansion of scalar actions. The native category instance is locally
irreducible only during final assembly. The abelian instance remains reducible to
identify its preadditive structure with the existing one.

A public filtered-colimits import restores small-site sheafification instances.
The explicit sections finite-limit instance preserves the old abbreviation's API.
A private sheaf-limits import supplies exactness of forgetting. The temporary category
wrapper was removed because it interfered with downstream native-instance inference.
Final validation is pending; the acyclic consumer already compiles unchanged in 54.7 s.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.DerivedSectionsScalarCoherence | T6 | Proves the same scalar comparison with explicit canonical transports. |
| Sheaf.CategoryTheory.RingedAcyclicResolutionDerivedMaps | unclaimed | Uses the same coefficient category and sections functor; Native-category repair restores inference; final check pending. |
| Sheaf.AlgebraicGeometry.SpaceGradedCohomologyFinite | unclaimed | Imports the item; no changed names used; Native-category repair restores inference; final check pending. |
| Sheaf.CategoryTheory.RingedSiteLeraySpectralSequence | unclaimed | Uses coefficientModules and coefficientSections; same mathematical functor. Final validation pending. |
| Sheaf.Paper.FiniteModelTopologyComparisonMaps | unclaimed | Imports the item; no changed declaration is mentioned. Final validation pending. |
| Sheaf.Paper.FiniteModelTopologyDerivedHom | unclaimed | Imports the item; no changed declaration is mentioned. Final validation pending. |
| Sheaf.Paper.SupportedRationalModelRigidityTransfer | unclaimed | Indirect importer; no changed declaration is mentioned. Final validation pending. |

The downstream tool finds no application of the scalar-coherence theorem itself.
The target statements are untouched. The definition boundary changes are submitted
for normal independent statement review.

All six DAG citers retain their canonical scalar comparison, normalization,
representative formula and coherence: `lem-coef-sequence-global-sections-evaluation`,
`lem-sfb-ringed-site-global-module-abelian-cohomology`,
`lem-sfb-ringed-sections-forget-abelian`, `lem-sfb-galois-coefficient-path-coherence`,
`lem-sfb-finite-model-topology-derived-hom`, and `lem-pur-relative-kummer-normalized-stalks`.
No unit step is removed or bypassed.

## Status

landed 20261024T191241-L-285816 2026-10-24 (merge of deliver/T6/Sheaf.CategoryTheory.DerivedSectionsScalarCoherence)
