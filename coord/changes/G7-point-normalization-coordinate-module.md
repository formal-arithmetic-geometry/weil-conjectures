# WeilConjectures.PointFrobeniusNormalization coordinate definitions

## Reason

The point normalization proof uses separate lemmas about finite multiplication and identity
exchange. Those lemmas need the canonical coordinate definitions, so all 26 definitions move
verbatim into a common module, publicly reexported by the original module. No definition body,
signature, name, visibility or original theorem statement changes. This avoids an import cycle.

The new PointQuotientComparisonCoordinates module constructs canonical tower and cone comparison
data and exposes their determining equations. This avoids repeatedly transporting the unused rho
and descended-theta witnesses from the large descent theorem through the assembly proof. The tower
inverse is fixed on every section, degree and level, and both cone coordinates fix the entire cone
hom, so both isomorphisms are determined uniquely. The public existence theorem is proved from
multiplication-cone descent; the data definition refers to that named theorem. There is no hollow
definition or choice of an arbitrary object from mere existence.

The module originally has no current Lean importers (checked with tools/downstream.py); its
unfinished DAG parents still need its theorem, which is retained and proved by assembly.

## Old

The following declarations occur in Sheaf.Paper.PointFrobeniusTransportNormalization:

```lean
instance finitePullbackAdditive (n : ℕ) :
    (integralOperationsLevelPullback l E (frobeniusPointIso D).hom n).Additive :=
  integralOperationsLevelPullback_additive l E (frobeniusPointIso D).hom n

instance finiteSectionsDerived (n : ℕ) :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

abbrev finiteComplex (n : ℕ)
    (M : integralOperationsFiniteModules l E (Spec (.of D.k)) n) :=
  (CochainComplex.singleFunctor _ (0 : ℤ)).obj M

def finiteKappa (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :=
  inverseImagePullbackComparisonFiniteIntrinsic l (frobeniusPointIso D).hom E
      (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) n K

def finiteLambda (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
    (e : ((integralOperationsLevelPullback l E (frobeniusPointIso D).hom
      n).mapHomologicalComplex (.up ℤ)).obj K ≅
      ((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex (.up
          ℤ)).obj K) :=
  letI : (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).Additive :=
          integralOperationsLevelPullback_additive l E (frobeniusPointIso D).hom n
  letI : PreservesFiniteLimits (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    inverseImageFinitePullback_limits l E (frobeniusPointIso D).hom n
  letI : PreservesFiniteColimits (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    inverseImageFinitePullback_colimits l E (frobeniusPointIso D).hom n
  (Functor.mapDerivedCategoryNatIso
      (inverseImageFiniteIntrinsicPullbackComparison (frobeniusPointIso D).hom
        (Padic.coefficientExtensionRing l E (n + 1)))).symm.app
        (DerivedCategory.Q.obj K) ≪≫
    (integralOperationsLevelPullback l E (frobeniusPointIso D).hom
        n).mapDerivedCategoryFactors.app K ≪≫
    DerivedCategory.Q.mapIso e ≪≫
    ((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapDerivedCategoryFactors.app
        K).symm

def finiteDirectId (n : ℕ) :=
  (((sfIntrinsicConstantModuleAdjunction (𝟙 (Spec (.of D.k)))
    (Padic.coefficientExtensionRing l E (n +
        1))).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoLeft
        (sfIntrinsicDerivedPullbackId (Padic.coefficientExtensionRing l E (n + 1))
          (Spec (.of D.k)))).rightAdjointUniq Adjunction.id

def finiteOrdinary (n : ℕ)
    (N : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1))) :=
  (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.{u +
      2, u + 1}.map ((finiteDirectId D l E n).inv.app N) ≫
  frobeniusPointTransportFinite D l hl E n
    ((proEtaleConstantDerivedDirectImage (𝟙 (Spec (.of D.k)))
      (Padic.coefficientExtensionRing l E (n + 1))).obj N) ≫
  (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.{u +
      2, u + 1}.map
      ((FrobeniusExchange.finiteExchange (Padic.coefficientExtensionRing l E (n + 1))
        (𝟙 (Spec (.of D.k))) (𝟙 (Spec (.of D.k)))
        (frobeniusPointIso D).hom (frobeniusPointIso D).hom
        ((Category.comp_id _).trans (Category.id_comp _).symm)).app N) ≫
  (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.{u +
      2, u + 1}.map ((finiteDirectId D l E n).hom.app
      ((finiteDerivedPullback l E n (frobeniusPointIso D).hom).obj N))

def finiteSheafIso (n : ℕ)
    (M : integralOperationsFiniteModules l E (Spec (.of D.k)) n)
    (v : (inverseImageFiniteModules l E (frobeniusPointIso D).hom n).obj M ≅ M) :=
  (inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapDerivedCategoryFactors.app
      (finiteComplex D l E n M) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (inverseImageFiniteModules l E (frobeniusPointIso D).hom n) (.up ℤ) (0 : ℤ)).app M ≪≫
        (CochainComplex.singleFunctor _ (0 : ℤ)).mapIso v)

def FiniteNormalization (n : ℕ)
    (M : integralOperationsFiniteModules l E (Spec (.of D.k)) n) : Prop :=
  ∃ e : ((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n).mapHomologicalComplex
      (.up ℤ)).obj (finiteComplex D l E n M) ≅
      ((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex (.up
          ℤ)).obj (finiteComplex D l E n M),
    (∀ (i : ℤ) (U : (Spec (.of D.k)).ProEt)
      (x : ((finiteComplex D l E n M).X i).val.obj
        (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj U)))
      (b : (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.obj (op U)),
      (e.hom.f i).val.app (op U)
        (b • ((inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom n
          (finiteComplex D l E n M)).f i).val.app (op U) x) =
        (inv (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n)).hom.app
          (op U) b • x) ∧
    (inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom n
      (finiteComplex D l E n M) = e.inv) ∧
    finiteKappa D l hl E n (finiteComplex D l E n M) ≫
      (finiteLambda D l E n (finiteComplex D l E n M) e).hom = 𝟙 _ ∧
    (finiteDerivedPullback l E n (frobeniusPointIso D).hom).map
        ((finiteDirectId D l E n).hom.app (DerivedCategory.Q.obj (finiteComplex D l E n M))) =
      (FrobeniusExchange.finiteExchange (Padic.coefficientExtensionRing l E (n + 1))
        (𝟙 (Spec (.of D.k))) (𝟙 (Spec (.of D.k)))
        (frobeniusPointIso D).hom (frobeniusPointIso D).hom
        ((Category.comp_id _).trans (Category.id_comp _).symm)).app
          (DerivedCategory.Q.obj (finiteComplex D l E n M)) ≫
      (finiteDirectId D l E n).hom.app
        ((finiteDerivedPullback l E n (frobeniusPointIso D).hom).obj
          (DerivedCategory.Q.obj (finiteComplex D l E n M))) ∧
    (∀ v : (inverseImageFiniteModules l E (frobeniusPointIso D).hom n).obj M ≅ M,
      finiteOrdinary D l hl E n (DerivedCategory.Q.obj (finiteComplex D l E n M)) ≫
        (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (
      n + 1))).mapDerivedCategory.{u + 2, u + 1}.map
            ((finiteLambda D l E n (finiteComplex D l E n M) e).hom ≫ (finiteSheafIso D l E n M
              v).hom) =
        frobeniusPointFiniteSigmaDerived D l E n
          (DerivedCategory.Q.obj (finiteComplex D l E n M)) ≫
        (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (
      n + 1))).mapDerivedCategory.{u + 2, u + 1}.map (finiteSheafIso D l E n M v).hom)

abbrev integralComplex (M : integralTowerModules l E (Spec (.of D.k))) :=
  (CochainComplex.singleFunctor _ (0 : ℤ)).obj M

abbrev calculus := (FrobeniusExchange.models l E).system (Spec (.of D.k))

def systemDirectId :=
  ((FrobeniusExchange.systemAdjunction l E (𝟙 (Spec (.of D.k)))).ofNatIsoLeft
    (integralComparisonSystemUnit l E (Spec (.of D.k)))).rightAdjointUniq Adjunction.id

def integralDirectId
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :=
  (coefficientSequenceLimit l E (Spec (.of D.k))).map
      ((systemDirectId D l E).hom.app ((calculus D l E).reduction.obj N)) ≫
    GeneratorReduction.inverseOrZero ((calculus D l E).adjunction.unit.app N)

def integralDirectIdInv
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :=
  (calculus D l E).adjunction.unit.app N ≫
    (coefficientSequenceLimit l E (Spec (.of D.k))).map
      ((systemDirectId D l E).inv.app ((calculus D l E).reduction.obj N))

def integralExchange
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :=
  letI := frobeniusPointPrimeInvertible D l hl
  (FrobeniusExchange.integralExchange l E
    (FrobeniusExchange.systemDirect l E (𝟙 (Spec (.of D.k))))
    (frobeniusPointIso D).hom (frobeniusPointIso D).hom
    (FrobeniusExchange.systemExchange l E (𝟙 (Spec (.of D.k)))
      (frobeniusPointIso D).hom (frobeniusPointIso D).hom
      ((Category.comp_id _).trans (Category.id_comp _).symm))).app N

def integralOrdinary
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :=
  (pointFibreIntegralAmbient D l E).map (integralDirectIdInv D l E N.obj) ≫
    frobeniusPointTransportIntegral D l hl E
      ((FrobeniusExchange.integralDirectImage l E (𝟙 (Spec (.of D.k)))).obj N.obj) ≫
    (pointFibreIntegralAmbient D l E).map (integralExchange D l hl E N) ≫
    (pointFibreIntegralAmbient D l E).map
      (integralDirectId D l E ((integralDerivedPullback l E (frobeniusPointIso D).hom).obj N.obj))

def integralLambda
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (θ : (integralDerivedPullback l E (frobeniusPointIso D).hom).obj N ≅
      (inverseImageIntegralDerived l E (frobeniusPointIso D).hom).obj
        (((calculus D l E).reduction ⋙ coefficientSequenceLimit l E (Spec (.of D.k))).obj N))
    (ε : N ≅
      ((calculus D l E).reduction ⋙ coefficientSequenceLimit l E (Spec (.of D.k))).obj N) :=
  θ ≪≫ ((inverseImageIntegralDerived l E (frobeniusPointIso D).hom).mapIso ε).symm

def integralSheafIso (M : integralTowerModules l E (Spec (.of D.k)))
    (v : (inverseImageIntegralModules l E (frobeniusPointIso D).hom).obj M ≅ M) :=
  (inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapDerivedCategoryFactors.app
      (integralComplex D l E M) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (inverseImageIntegralModules l E (frobeniusPointIso D).hom) (.up ℤ) (0 : ℤ)).app M ≪≫
        (CochainComplex.singleFunctor _ (0 : ℤ)).mapIso v)

def IntegralQuotientNormalization
    (M : integralTowerModules l E (Spec (.of D.k))) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (_e : DerivedCategory.Q.obj P.obj ≅ DerivedCategory.Q.obj (integralComplex D l E M)),
  ∃ j : (integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P.obj ≅
      (trfInverseImageTower l E (frobeniusPointIso D).hom).obj
        ((trfQuotientTowerFunctor l E (Spec (.of D.k))).obj P.obj),
    (∀ (n : ℕ) (i : ℤ) (U : (Spec (.of D.k)).ProEt)
      (x : (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj).X i).val.obj
        (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj U)))
      (b : (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.obj (op U)),
      ((j.hom.app (op n)).f i).val.app (op U)
        (b • (((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n).obj
          (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj).X i)).val.map
            (proEtaleIsoCommaArrow (frobeniusPointIso D).hom U).op
            (integralOperationsPullbackGenerator l E (frobeniusPointIso D).hom n
              (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj).X i)
              ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj U) x))) =
        (inv (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n)).hom.app
          (op U) b • x) ∧
    (∀ (n : ℕ) (i : ℤ) (U : (Spec (.of D.k)).ProEt)
      (x : (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj).X i).val.obj
        (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj U))),
      ((j.inv.app (op n)).f i).val.app (op U) x =
        (((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n).obj
          (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj).X i)).val.map
            (proEtaleIsoCommaArrow (frobeniusPointIso D).hom U).op
            (integralOperationsPullbackGenerator l E (frobeniusPointIso D).hom n
              (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj).X i)
              ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj U) x))) ∧
  ∃ η : (trfInverseImageComplex l E (frobeniusPointIso D).hom).obj
      (integralOperationsRoos ((trfQuotientTowerFunctor l E (Spec (.of D.k))).obj P.obj)) ≅
    integralOperationsRoos ((trfInverseImageTower l E (frobeniusPointIso D).hom).obj
      ((trfQuotientTowerFunctor l E (Spec (.of D.k))).obj P.obj)),
    η.hom ≫ CochainComplex.mappingCocone.fst
        (trfInverseQuotientDifference l E (frobeniusPointIso D).hom P.obj) =
      (trfInverseImageComplex l E (frobeniusPointIso D).hom).map
        (CochainComplex.mappingCocone.fst (trfQuotientDifference l E (Spec (.of D.k)) P.obj)) ≫
      trfQuotientProductComparison l E (frobeniusPointIso D).hom P.obj ∧
    (∀ p : ℤ, η.hom.f (p + 1) ≫
        (CochainComplex.mappingCocone.snd
          (trfInverseQuotientDifference l E (frobeniusPointIso D).hom P.obj)).v
            (p + 1) p (add_neg_cancel_right p 1) =
      (inverseImageIntegralModules l E (frobeniusPointIso D).hom).map
        ((CochainComplex.mappingCocone.snd
          (trfQuotientDifference l E (Spec (.of D.k)) P.obj)).v
            (p + 1) p (add_neg_cancel_right p 1)) ≫
        (trfQuotientProductComparison l E (frobeniusPointIso D).hom P.obj).f p) ∧
    inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P.obj ≫
        integralOperationsRoosFunctor.map j.hom =
      (trfInverseImageComplex l E (frobeniusPointIso D).hom).map
        (trfStrictQuotientConeAugmentation l E (Spec (.of D.k)) P.obj) ≫ η.hom

instance integralSectionsDerived :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

instance fieldSectionsDerived (F : Type u) [Field F] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1} F)) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

abbrev rationalExtension :=
  (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
    (pointIntegralToField l E)).mapDerivedCategory.{u + 1, u + 1}

def closedExtension (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (ι : E →ₐ[ℚ_[l]] Ω) :=
  frobeniusCohomologyCoefficientExtension
    (ι.toRingHom.comp (ULift.ringEquiv : ULift.{u + 1} E ≃+* E).toRingHom)

def IntegralNormalization
    (M : integralTowerModules l E (Spec (.of D.k)))
    (hM : sfIntegralConstructible l E (Spec (.of D.k))
      (DerivedCategory.Q.obj (integralComplex D l E M))) : Prop :=
  ∃ θ : (integralDerivedPullback l E (frobeniusPointIso D).hom).obj
        (DerivedCategory.Q.obj (integralComplex D l E M)) ≅
      (inverseImageIntegralDerived l E (frobeniusPointIso D).hom).obj
        (((calculus D l E).reduction ⋙ coefficientSequenceLimit l E (Spec (.of D.k))).obj
          (DerivedCategory.Q.obj (integralComplex D l E M))),
  ∃ ε : DerivedCategory.Q.obj (integralComplex D l E M) ≅
      ((calculus D l E).reduction ⋙ coefficientSequenceLimit l E (Spec (.of D.k))).obj
        (DerivedCategory.Q.obj (integralComplex D l E M)),
    IntegralQuotientNormalization D l E M ∧
    ε.hom = (calculus D l E).adjunction.unit.app
      (DerivedCategory.Q.obj (integralComplex D l E M)) ∧
    inverseImagePullbackComparisonDerived l E (frobeniusPointIso D).hom
        (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl)
        (DerivedCategory.Q.obj (integralComplex D l E M)) ≫ θ.hom =
      (inverseImageIntegralDerived l E (frobeniusPointIso D).hom).map ε.hom ∧
    inverseImagePullbackComparisonDerived l E (frobeniusPointIso D).hom
        (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl)
        (DerivedCategory.Q.obj (integralComplex D l E M)) ≫
      (integralLambda D l E _ θ ε).hom = 𝟙 _ ∧
    (integralDerivedPullback l E (frobeniusPointIso D).hom).map
      (integralDirectId D l E (DerivedCategory.Q.obj (integralComplex D l E M))) =
      integralExchange D l hl E ⟨_, hM⟩ ≫ integralDirectId D l E
        ((integralDerivedPullback l E (frobeniusPointIso D).hom).obj
          (DerivedCategory.Q.obj (integralComplex D l E M))) ∧
    (∀ v : (inverseImageIntegralModules l E (frobeniusPointIso D).hom).obj M ≅ M,
      integralOrdinary D l hl E ⟨_, hM⟩ ≫
        (pointFibreIntegralAmbient D l E).map ((integralLambda D l E _ θ ε).hom ≫
          (integralSheafIso D l E M v).hom) =
      frobeniusPointIntegralSigmaDerived D l E
          (DerivedCategory.Q.obj (integralComplex D l E M)) ≫
        (pointFibreIntegralAmbient D l E).map (integralSheafIso D l E M v).hom ∧
      (rationalExtension l E).map (integralOrdinary D l hl E ⟨_, hM⟩) ≫
        (pointFibreRationalAmbient D l E).map ((integralLambda D l E _ θ ε).hom ≫
          (integralSheafIso D l E M v).hom) =
      (rationalExtension l E).map (frobeniusPointIntegralSigmaDerived D l E
          (DerivedCategory.Q.obj (integralComplex D l E M))) ≫
        (pointFibreRationalAmbient D l E).map (integralSheafIso D l E M v).hom ∧
      (∀ (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
        (ι : E →ₐ[ℚ_[l]] Ω),
        (closedExtension l E Ω ι).map
            ((rationalExtension l E).map (integralOrdinary D l hl E ⟨_, hM⟩)) ≫
          (closedExtension l E Ω ι).map ((pointFibreRationalAmbient D l E).map
            ((integralLambda D l E _ θ ε).hom ≫ (integralSheafIso D l E M v).hom)) =
        (closedExtension l E Ω ι).map ((rationalExtension l E).map
          (frobeniusPointIntegralSigmaDerived D l E
            (DerivedCategory.Q.obj (integralComplex D l E M)))) ≫
          (closedExtension l E Ω ι).map ((pointFibreRationalAmbient D l E).map (integralSheafIso
            D l E M v).hom)))

def coefficientRing (a : Option ℕ) :
    Sheaf (ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1} :=
  match a with
  | none => completedIntegralCommRingSheafUnrestricted.{u, u} l E (Spec (.of D.k))
  | some n => integralCoefficientCommRingSheaf.{u, u} l E (Spec (.of D.k)) n

def TensorDualNormalization (a : Option ℕ) : Prop :=
  (∀ b : pointRestrictionScalars.{u, u} l E a,
    (pointRestrictionCoefficientMap.{u, u} l E (frobeniusPointIso D).hom a).hom.app
        (op (ProEt.mk (𝟙 _)))
      ((pointRestrictionRing.{u, u} l E (Spec (.of D.k)) a).obj.map
        (pointRestrictionArrow (frobeniusPointIso D).hom).op
        (pointRestrictionScalarAt.{u, u} l E (Spec (.of D.k)) a (ProEt.mk (𝟙 _)) b)) =
      pointRestrictionScalarAt.{u, u} l E (Spec (.of D.k)) a (ProEt.mk (𝟙 _)) b) ∧
  (∀ (M N : SheafOfModules.{u + 1} ((sheafCompose
        (ProEt.topology (Spec (.of D.k))) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (coefficientRing D l E a)))
      (_hM : ∃ r : ℕ, Nonempty (M ≅ SheafOfModules.free (ULift.{u + 1} (Fin r))))
      (_hN : ∃ r : ℕ, Nonempty (N ≅ SheafOfModules.free (ULift.{u + 1} (Fin r))))
      (x : M.val.obj (op (ProEt.mk (𝟙 _)))) (y : N.val.obj (op (ProEt.mk (𝟙 _)))),
    ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} N).obj M).val.map
        (frobeniusPointRestriction D).op
        (purTensorSection (coefficientRing D l E a) M N (ProEt.mk (𝟙 _)) x y) =
      purTensorSection (coefficientRing D l E a) M N
        ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj (ProEt.mk (𝟙 _)))
        (M.val.map (frobeniusPointRestriction D).op x)
        (N.val.map (frobeniusPointRestriction D).op y)) ∧
  (∀ (M N : SheafOfModules.{u + 1} ((sheafCompose
        (ProEt.topology (Spec (.of D.k))) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (coefficientRing D l E a)))
      (_hM : ∃ r : ℕ, Nonempty (M ≅ SheafOfModules.free (ULift.{u + 1} (Fin r))))
      (_hN : N = SheafOfModules.unit _)
      (φ : (SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} (R := coefficientRing D l E a) M
        N).val.obj
        (op (ProEt.mk (𝟙 _)))) (x : M.val.obj (op (ProEt.mk (𝟙 _)))),
    N.val.map (frobeniusPointRestriction D).op (φ.app (op (Over.mk (𝟙 _))) x) =
      (((SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} (R := coefficientRing D l E a) M N).val.map
        (frobeniusPointRestriction D).op φ).app (op (Over.mk (𝟙 _))))
          (M.val.map (frobeniusPointRestriction D).op x))
```

## New

The identical 26 declarations above, with identical full names, signatures and complete bodies,
occur in Sheaf.Paper.PointFrobeniusNormalizationDefinitions. The original module publicly imports
that module. The theorem point_frobenius_transport_normalization keeps its original signature.
The common module replaces public import Sheaf.Paper.PurInverseImageTensorHom with its
PurInverseImageTensorHomDefinitions module: only the pure-tensor section convention is needed.
The complete comparison theorem and its proof dependencies are not used by the naturality proof.
No existing current Lean importer needs adapting.

The new PointQuotientComparisonCoordinates module has PointQuotientComparisonData (its two
natural isomorphisms), PointQuotientComparisonNormalized (the generator/inverse and both cone
coordinates), pointQuotientComparison_exists (proved from the existing descent theorem), and
pointQuotientComparisonData (the uniquely determined data selected from that named theorem).
The full declarations and uniqueness argument are in that module, attached to new node
def-pur-point-quotient-comparison-coordinates.

Two new proof statements are pointFiniteMultiplicationInverse (multiplication coordinates only)
and pointIdentityExchangeRecipe (identity exchange and sigma-kappa recipe only). Neither supplies
kappa-lambda cancellation, a Weil-isomorphism transport equation or the tensor/dual clause.
The final module proves these consequences using actual Lean composition and inverse identities.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PointFrobeniusTransportNormalization | G7 | Same public names reexported; complete assembly proof. |
| Sheaf.Paper.PointFrobeniusNormalizationDefinitions | G7, new | Verbatim canonical vocabulary. |
| Sheaf.Paper.PointQuotientComparisonCoordinates | G7, new | Uniquely normalized canonical comparison data and coordinate API. |
| Sheaf.Paper.PointFiniteMultiplicationInverse | G7, new | Uses common coordinate vocabulary. |
| Sheaf.Paper.PointIdentityExchangeRecipe | G7, new | Uses common coordinate vocabulary. |

No other current Lean importer was found. DAG parent obligations are preserved. Challenge.lean
statements and all definitions used in their signatures remain identical, so no target semantic
review is reopened by the relocation or the canonical data used only in this proof.

## Status

landed 20261026T023236-L-533707 2026-10-26 (merge of deliver/G7/Sheaf.Paper.PointFrobeniusTransportNormalization)
