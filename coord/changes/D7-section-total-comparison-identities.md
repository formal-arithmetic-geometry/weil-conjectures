# Tensor representative predicates and total-comparison identities

## Reason

Prove section_tensor_representative_exists with the exact fixed comparison maps and
make their definition-level interfaces usable without repeatedly unfolding large
localization and monoidal constructions. No target statement changes. The change is
under lean/Sheaf only; no adopted WeilConjectures declaration is modified.

The three named representative predicates give the same right-associated conjunction
as before, with every quantifier and the either-argument K-flat disjunction retained.
The internalLocalizationTensorMap component is definitionally the original native
lax localization tensorator (internalLocalizationTensorMap_app). internalTotalTensor
is the existing signed-total functor with a direct object field.
cochainTotalFunctor retains the old maps and functor laws, and cochainTotalFunctor_eq
verifies equality with the complete original uncurried functor by reflexivity.
totalTensor uses this same definitionally equal record, avoiding repeated reduction
through the two curried functor categories. sectionTotalComparison is constructed by
mapBifunctorComparison from the actual curried ordinary comparison.
sectionTotalComparison_eq proves that this map equals the old totalComparison hom:
the signed summand formula gives its normalization, and the existing uniqueness
theorem identifies the isomorphisms. Its irreducibility avoids repeatedly unfolding
large total maps; its canonical construction makes naturality usable without
repeated conversion through the chosen totalComparison.

sectionLocalizationIso is the original mapDerivedCategoryFactors, so its components
are definitionally the original sectionLocalizationComparison, whose body is preserved. The derived equivalence
and tensor constructions retain their original bodies. tensorUnit is expressed as the
image of the internal degree-zero regular module: the old native derived unit reduces
to exactly that same single-functor object. localizedTotalComparison omits a mapped
identity eqToHom(totalTensor_obj.symm). totalPullComparison omits its leading and
trailing identity transports through totalTensor_obj. Category unit laws and map_id
identify the old composites with the displayed new ones. The exposed internal total functor has definitionally the old raw
CochainComplex.mapBifunctor objects; the fixed comparison hom keeps the raw-complex types.

All changes preserve zero rings, zero complexes, empty sites, negative degrees and
identity pullbacks. The target-meaning review is reopened for target statements using
these definitions, to verify the explicit definitional equalities and identity laws.

## Old

```lean
def totalTensor (X : Scheme.{u}) :
    CochainComplex (modules Λ X) ℤ × CochainComplex (modules Λ X) ℤ ⥤
      CochainComplex (modules Λ X) ℤ :=
  Functor.uncurry.obj ((curriedTensor (modules Λ X)).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))

def tensorUnit (X : Scheme.{u}) : DerivedCategory (modules Λ X) :=
  ((derivedEquivalence Λ X).functor).obj (𝟙_ (DerivedCategory (internalModules Λ X)))

def localizedTotalComparison (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    (derivedEquivalence Λ X).functor.obj
        ((DerivedCategory.Q (C := internalModules Λ X)).obj
          (CochainComplex.mapBifunctor P Q (curriedTensor (internalModules Λ X)))) ⟶
      (DerivedCategory.Q (C := modules Λ X)).obj
        ((totalTensor Λ X).obj
          ((((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P),
            (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q))) :=
  (sectionLocalizationComparison Λ X
      (CochainComplex.mapBifunctor P Q (curriedTensor (internalModules Λ X)))).hom ≫
    (DerivedCategory.Q (C := modules Λ X)).map (totalComparison Λ X P Q).hom ≫
    (DerivedCategory.Q (C := modules Λ X)).map
      (eqToHom (totalTensor_obj Λ X
        (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)).symm)

def TensorRepresentativeCondition (X : Scheme.{u})
    (q : (((DerivedCategory.Q (C := modules Λ X)).prod
      (DerivedCategory.Q (C := modules Λ X))) ⋙ tensor Λ X) ⟶
        totalTensor Λ X ⋙ DerivedCategory.Q (C := modules Λ X)) : Prop :=
  (∀ P Q : CochainComplex (internalModules Λ X) ℤ,
        q.app
            ((((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P),
              (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)) =
          (tensor Λ X).map (Prod.mkHom
            (sectionLocalizationComparison Λ X P).inv
            (sectionLocalizationComparison Λ X Q).inv) ≫
          (tensorComparison Λ X).inv.app ((DerivedCategory.Q (C := internalModules Λ X)).obj P,
            (DerivedCategory.Q (C := internalModules Λ X)).obj Q) ≫
          ((derivedEquivalence Λ X).functor).map (Functor.LaxMonoidal.μ
            (DerivedCategory.Q (C := internalModules Λ X)) P Q) ≫
          localizedTotalComparison Λ X P Q) ∧
      (∀ P Q : CochainComplex (modules Λ X) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients P ∨
          CochainComplex.IsKFlatIndependentCoefficients Q → IsIso (q.app (P, Q))) ∧
      Nonempty (tensorUnit Λ X ≅
        (DerivedCategory.singleFunctor (modules Λ X) 0).obj (𝟙_ (modules Λ X)))

def totalPullComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    ((pullback Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((totalTensor Λ Y).obj (P, Q)) ⟶
      (totalTensor Λ X).obj
        (((pullback Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
          ((pullback Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) :=
  ((pullback Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (eqToHom (totalTensor_obj Λ Y P Q)) ≫
    HomologicalComplex.mapBifunctorComparison
      (F := curriedTensor (modules Λ Y)) (F' := curriedTensor (modules Λ X))
      (G := pullback Λ f) (G₁ := pullback Λ f) (G₂ := pullback Λ f)
      (Functor.OplaxMonoidal.δNatTrans (pullback Λ f)) (ComplexShape.up ℤ) P Q ≫
    eqToHom (totalTensor_obj Λ X
      (((pullback Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      (((pullback Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)).symm
```

## New

```lean
def totalTensor (X : Scheme.{u}) :
    CochainComplex (modules Λ X) ℤ × CochainComplex (modules Λ X) ℤ ⥤
      CochainComplex (modules Λ X) ℤ :=
  cochainTotalFunctor (curriedTensor (modules Λ X))

def tensorUnit (X : Scheme.{u}) : DerivedCategory (modules Λ X) :=
  ((derivedEquivalence Λ X).functor).obj
    ((DerivedCategory.singleFunctor (internalModules Λ X) 0).obj (𝟙_ (internalModules Λ X)))

def localizedTotalComparison (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    (derivedEquivalence Λ X).functor.obj
        ((DerivedCategory.Q (C := internalModules Λ X)).obj
          ((internalTotalTensor Λ X).obj (P, Q))) ⟶
      (DerivedCategory.Q (C := modules Λ X)).obj
        ((totalTensor Λ X).obj
          ((((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P),
            (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q))) :=
  (sectionLocalizationComparison Λ X
      ((internalTotalTensor Λ X).obj (P, Q))).hom ≫
    (DerivedCategory.Q (C := modules Λ X)).map (sectionTotalComparison Λ X P Q)

def TensorRepresentativeNormalization (X : Scheme.{u})
    (q : (((DerivedCategory.Q (C := modules Λ X)).prod
      (DerivedCategory.Q (C := modules Λ X))) ⋙ tensor Λ X) ⟶
        totalTensor Λ X ⋙ DerivedCategory.Q (C := modules Λ X)) : Prop :=
  ∀ P Q : CochainComplex (internalModules Λ X) ℤ,
        q.app
            ((((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P),
              (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)) =
          (tensor Λ X).map (Prod.mkHom
            (sectionLocalizationComparison Λ X P).inv
            (sectionLocalizationComparison Λ X Q).inv) ≫
          (tensorComparison Λ X).inv.app ((DerivedCategory.Q (C := internalModules Λ X)).obj P,
            (DerivedCategory.Q (C := internalModules Λ X)).obj Q) ≫
          ((derivedEquivalence Λ X).functor).map
            ((internalLocalizationTensorMap Λ X).app (P, Q)) ≫
          localizedTotalComparison Λ X P Q

def TensorRepresentativeIsIso (X : Scheme.{u})
    (q : (((DerivedCategory.Q (C := modules Λ X)).prod
      (DerivedCategory.Q (C := modules Λ X))) ⋙ tensor Λ X) ⟶
        totalTensor Λ X ⋙ DerivedCategory.Q (C := modules Λ X)) : Prop :=
  ∀ P Q : CochainComplex (modules Λ X) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients P ∨
          CochainComplex.IsKFlatIndependentCoefficients Q → IsIso (q.app (P, Q))

def TensorRepresentativeUnit (X : Scheme.{u}) : Prop :=
  Nonempty (tensorUnit Λ X ≅
        (DerivedCategory.singleFunctor (modules Λ X) 0).obj (𝟙_ (modules Λ X)))

def TensorRepresentativeCondition (X : Scheme.{u})
    (q : (((DerivedCategory.Q (C := modules Λ X)).prod
      (DerivedCategory.Q (C := modules Λ X))) ⋙ tensor Λ X) ⟶
        totalTensor Λ X ⋙ DerivedCategory.Q (C := modules Λ X)) : Prop :=
  TensorRepresentativeNormalization Λ X q ∧
    TensorRepresentativeIsIso Λ X q ∧ TensorRepresentativeUnit Λ X

@[local irreducible] def totalPullComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    ((pullback Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((totalTensor Λ Y).obj (P, Q)) ⟶
      (totalTensor Λ X).obj
        (((pullback Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
          ((pullback Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) :=
  HomologicalComplex.mapBifunctorComparison
    (F := curriedTensor (modules Λ Y)) (F' := curriedTensor (modules Λ X))
    (G := pullback Λ f) (G₁ := pullback Λ f) (G₂ := pullback Λ f)
    (Functor.OplaxMonoidal.δNatTrans (pullback Λ f)) (ComplexShape.up ℤ) P Q
```

The other new public APIs are cochainTotalFunctor, cochainTotalFunctor_eq,
sectionFunctorAdditive, derivedEquivalence_functor,
internalTotalTensor,
internalLocalizationTensorMap and its component equation, sectionOrdinaryTensorNaturality,
sectionOrdinaryTensorMap with its component and invertibility theorems,
sectionTotalComparison with sectionTotalComparison_eq, and sectionLocalizationIso.
They expose the actual existing constructions and their proved properties; there are
no new choices or postponed statements. The existing flat-resolution proof now uses
ordinaryTensorComparison and its already proved naturality helper directly,
instead of eliminating the large public conjunction containing those same properties.

## Users

The downstream declaration-user searches for tensorUnit, sectionLocalizationComparison,
localizedTotalComparison, TensorRepresentativeCondition and totalPullComparison were run. Importers using their existing interfaces retain their
statements; these are the direct textual consumers and changed modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | Actual-map APIs, direct-object record for the same total functor, definitionally equal unit, and removal of a mapped identity. |
| Sheaf.Paper.SectionDerivedRealization | D7 | Complete existence proof, same representative predicates, removal of identity transports, explicit resolution/descent arguments. |
| Sheaf.Paper.SectionKFlatTensorComparison | unclaimed | Its representative condition has unchanged meaning; one rewrite exposes the existing native tensorator. |
| Sheaf.Paper.SectionDerivedTensorNormalization | unclaimed | Replace obsolete identity rewrites in totalPullComparison_eq by unfolding the canonical maps and reflexivity; compiled. |
| Sheaf.Paper.InternalScalarPullbackNormalizationData | unclaimed | Existing unit/localization-factor formulas are definitionally unchanged; no statement adaptation required. |
| Sheaf.Paper.ModuleSectionDerivedComparisonSquare | unclaimed | Existing unit/localization-factor formulas are definitionally unchanged; no statement adaptation required. |
| Sheaf.Paper.SectionDerivedPushpullNormalization | unclaimed | Existing unit/localization-factor formulas are definitionally unchanged; no statement adaptation required. |
| Sheaf.Paper.SectionDerivedRepresentativeSquare | U3 | Original consumer compiled unchanged in 39.5 s. |
| Sheaf.Paper.SectionPullComputationOfRealization | unclaimed | Existing unit/localization-factor formulas are definitionally unchanged; no statement adaptation required. |
| Sheaf.Paper.SectionResolutionConjugationIdentities | G6 | Existing unit/localization-factor formulas are definitionally unchanged; no statement adaptation required. |
| Sheaf.Paper.SectionResolvingOplaxConstraintData | unclaimed | Original consumer compiled unchanged in 16.3 s. |
| Sheaf.Paper.SectionScalarComputationAll | unclaimed | Existing unit/localization-factor formulas are definitionally unchanged; no statement adaptation required. |
| Sheaf.Paper.SectionScalarComputationTransport | unclaimed | Existing unit/localization-factor formulas are definitionally unchanged; no statement adaptation required. |
| Sheaf.Paper.SectionTensorConjugateComputation | unclaimed | Existing unit/localization-factor formulas are definitionally unchanged; no statement adaptation required. |
| Sheaf.Paper.SectionTensorRightComputation | unclaimed | Tensorator-component rewrite, canonical-total equality and explicit wrapper unfold; compiled in 46.1 s. |

BoundedFlatTensorContinuity and QuotientSectionTensorNormalization are quarantined,
not withdrawn. Their archived sources and DAG attachments are preserved. The signed-total functors are definitionally the original constructions, and the
localized derived equivalence retains its original body.


The original SectionKFlatTensorComparison representative_fixed proof failed at line 197:
its final goal compared
`D.functor.map ((internalLocalizationTensorMap Λ T).app (P.obj, Q.obj)) ≫ ℓ`
with `D.functor.map (Functor.LaxMonoidal.μ DerivedCategory.Q P.obj Q.obj) ≫ ℓ`.
This adaptation adds `internalLocalizationTensorMap_app` to its existing rewrite:
`rw [h.1 P.obj Q.obj, internalLocalizationTensorMap_app]`. It unfolds precisely the
new actual-map API; the statement, visibility and all other proof steps are preserved.

The original SectionTensorRightComputation failed at its representative equation
(line 312: cached internal tensorator component versus native μ) and localized-total
formula (line 337: unfolding stopped at the irreducible sectionTotalComparison).
Its necessary proof changes use internalLocalizationTensorMap_app in the existing
representative equation and sectionTotalComparison_eq in the localized-total formula.
The subsequent wrapper compile left cochainTotalFunctor.map unexpanded in qTensor
naturality (line 345: hordQ expected that wrapped map). Its existing dsimp list now
also unfolds cochainTotalFunctor. The localized-total calculation explicitly unfolds
internalTotalTensor and the same wrapper so its source complex is the original raw total.
All signatures and the remaining computation are unchanged. This module is unclaimed.

The original SectionDerivedTensorNormalization totalPullComparison_eq failed with
`simp made no progress` after totalPullComparison no longer contained the old identity
transports. The obsolete dsimp/simp/erw sequence is replaced by
`unfold totalPullComparison sectionTotalIso; rfl`. This is the only edit in this
unclaimed consumer; its statement and visibility are unchanged.

Validation: lcompile.py accepted the final data module and complete item proof,
the repaired K-flat comparison, the repaired right-tensor computation (46.1 s),
and the repaired normalization consumer (51.6 s). Both unit consumers compiled
unchanged: SectionDerivedRepresentativeSquare (39.5 s) and
SectionResolvingOplaxConstraintData (16.3 s). Every changed file has zero sorry.
The full-record equality cochainTotalFunctor_eq is proved by reflexivity;
sectionTotalComparison_eq proves agreement with the existing chosen comparison.

## Status

landed 20261026T130328-L-3449208 2026-10-26 (merge of deliver/D7/Sheaf.Paper.SectionDerivedRealization)
