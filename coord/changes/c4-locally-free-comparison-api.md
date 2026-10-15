# CategoryTheory.locallyFreeDualTensor and its evaluation/cohomology API

## Reason

The previous attempt repeatedly elaborated the concrete sheaf monoidal structures in its derived
Hom and naturality proofs and timed out. The repair proves the homological argument once for an
abstract abelian monoidal category, then specializes it to module sheaves. The generic argument
remains in the same module. Private helpers construct the equivalences, prove both naturality
identities and cycle normalization, and transport along the functorial K-injective resolution.
There are no new holes.

The public definitions retain their signatures and objects. Their bodies now specialize the
public `genericDualTensor`, `genericDualTensorMap`, `genericSections`, `genericTensorSections`,
`genericEvaluate` and `genericSectionsComparison` definitions. These construct the same objects
in an abstract category and make the concrete specialization a shared definitional reduction. The concrete wrappers remain shallow abbreviations so their implicit functor instances
reduce consistently; the larger generic constructions remain definitions. The evaluation and dual map use
the canonical closed-category API: `SheafOfModules.ihom_ev_app` and `SheafOfModules.pre_app`
identify them with the previous formulas. The comparison factors through the generic natural
transformation with the exact previous formula. The cached abelian, preadditive, monoidal, closed and derived additive structures are
transparent aliases of the original structures; their instance attributes are local to this module.
Using the inherited preadditive instance consistently and specializing the abstract theorem with
the literal module-sheaf category avoids expensive conversion through a local category alias.
The private functor equality `locallyFreeHypercohomology_eq_model`, proved by reflexivity,
identifies the abstract hypercohomology with the existing ringed-site functor.

No target statement changes. Any target using these definitions receives the project's semantic
re-review; the stated definitional equalities and source equalities show its meaning is preserved.

## Old

```lean
noncomputable abbrev locallyFreeDualTensor
    (P : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  letI := SheafOfModules.monoidalCategory R
  MonoidalCategory.tensorLeft (SheafOfModules.homObj (R := R) P (SheafOfModules.unit _))
```

```lean
noncomputable def locallyFreeDualTensorMap
    (P P' M N : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (p : P' ⟶ P) (f : M ⟶ N) :
    (locallyFreeDualTensor J R P).obj M ⟶ (locallyFreeDualTensor J R P').obj N :=
  letI := SheafOfModules.monoidalCategory R
  MonoidalCategory.tensorHom (SheafOfModules.homObjMap (R := R) p (𝟙 (SheafOfModules.unit _))) f
```

```lean
noncomputable abbrev locallyFreeSections :
    ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      AddCommGrpCat.{u} :=
  preadditiveCoyoneda.obj (op (SheafOfModules.unit _))
```

```lean
noncomputable abbrev locallyFreeTensorSections
    (P : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ ⥤
        CochainComplex AddCommGrpCat.{u} ℤ :=
  ((locallyFreeDualTensor J R P) ⋙ locallyFreeSections J R).mapHomologicalComplex (.up ℤ)
```

```lean
noncomputable def locallyFreeEvaluate
    (P N : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (z : SheafOfModules.unit _ ⟶ (locallyFreeDualTensor J R P).obj N) : P ⟶ N :=
  letI := SheafOfModules.monoidalCategory R
  (ρ_ P).inv ≫ P ◁ z ≫
    (α_ P (SheafOfModules.homObj (R := R) P (SheafOfModules.unit _)) N).inv ≫
    ((SheafOfModules.tensorHomEquiv P (SheafOfModules.homObj (R := R) P (SheafOfModules.unit _))
      (SheafOfModules.unit _)).symm (𝟙 _)) ▷ N ≫ (λ_ N).hom
```

```lean
noncomputable def locallyFreeSectionsComparison
    (K : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    (((locallyFreeSections J R).mapHomologicalComplex (.up ℤ)).obj K).homology 0 ⟶
      (ringedSiteZerothHypercohomology J R).obj (DerivedCategory.Q.obj K) := by
  let A := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  letI : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  let Γ := locallyFreeSections J R
  let G := Γ.mapHomologicalComplex (.up ℤ)
  let q := HomotopyCategory.quotient A (.up ℤ)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) 0
  let Hd := DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0
  let a : G ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Γ.rightDerivedFunctor :=
    (Functor.isoWhiskerRight (Γ.mapHomotopyCategoryFactors (.up ℤ))
      DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u})).inv ≫
    Functor.whiskerLeft q Γ.rightDerivedFunctorUnit ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
      Γ.rightDerivedFunctor).hom
  exact ((Functor.isoWhiskerLeft G
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0)).inv ≫
    Functor.whiskerRight a Hd).app K
```

## New

```lean
noncomputable abbrev locallyFreeDualTensor
    (P : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  genericDualTensor P
```

```lean
noncomputable def locallyFreeDualTensorMap
    (P P' M N : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (p : P' ⟶ P) (f : M ⟶ N) :
    (locallyFreeDualTensor J R P).obj M ⟶ (locallyFreeDualTensor J R P').obj N :=
  genericDualTensorMap P P' M N p f
```

```lean
noncomputable abbrev locallyFreeSections :
    ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      AddCommGrpCat.{u} :=
  genericSections
```

```lean
noncomputable abbrev locallyFreeTensorSections
    (P : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ ⥤
        CochainComplex AddCommGrpCat.{u} ℤ :=
  genericTensorSections P
```

```lean
noncomputable abbrev locallyFreeEvaluate
    (P N : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (z : SheafOfModules.unit _ ⟶ (locallyFreeDualTensor J R P).obj N) : P ⟶ N :=
  genericEvaluate P N z
```

```lean
noncomputable abbrev locallyFreeSectionsComparison
    (K : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    (((locallyFreeSections J R).mapHomologicalComplex (.up ℤ)).obj K).homology 0 ⟶
      (ringedSiteZerothHypercohomology J R).obj (DerivedCategory.Q.obj K) := by
  let A := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  exact genericSectionsComparison (A := A) K
```

## Users

The source-only `tools/downstream.py` check with all six changed declaration names lists the
15 transitive importers below. Searches for each changed declaration find only this module. The transitive
importers use the final theorem and do not unfold these definitions. No existing importing module
requires an adaptation: the signatures and their mathematical meaning are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.LocallyFreeDerivedHom | C4 | Equivalent definition bodies; complete proof specialized from an abstract categorical model. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Transitive importer; no reference to the changed definitions; statements unchanged, no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Transitive importer; no reference to the changed definitions; statements unchanged, no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | G2 | Transitive importer; no reference to the changed definitions; statements unchanged, no adaptation. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | H3 | Transitive importer; no reference to the changed definitions; statements unchanged, no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Transitive importer; no reference to the changed definitions; statements unchanged, no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Transitive importer; no reference to the changed definitions; statements unchanged, no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | Transitive importer; no reference to the changed definitions; statements unchanged, no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Transitive importer; no reference to the changed definitions; statements unchanged, no adaptation. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Transitive importer; no reference to the changed definitions; statements unchanged, no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStep | M3 | Transitive importer; no reference to the changed definitions; statements unchanged, no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Transitive importer; no reference to the changed definitions; statements unchanged, no adaptation. |
| TargetsCheck | unclaimed | Transitive importer; no reference to the changed definitions; statements unchanged, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Transitive importer; no reference to the changed definitions; statements unchanged, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Transitive importer; no reference to the changed definitions; statements unchanged, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Transitive importer; no reference to the changed definitions; statements unchanged, no adaptation. |

## Status

landed 20261015T214542-L-2274697 2026-10-15 (merge of deliver/C4/Sheaf.Algebra.Homology.LocallyFreeDerivedHom)
