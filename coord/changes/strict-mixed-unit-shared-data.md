# WeilConjectures.StrictDirectImageMixedUnit shared interfaces

## Reason

Relocate the existing definitions into an importable data module so the construction, scalar-linear square and finite-evaluation proof steps can import them without a cycle through the theorem they support. Every existing declaration signature and body is preserved verbatim. The original module publicly re-exports the data module, retaining its public interface. This is a proof dependency refactor, not a response to a compile-time limit.

## Old

The following declarations belonged to Sheaf.Paper.StrictDirectImageMixedUnit:

```lean
/-- The actual ordinary inverse limit of the restricted quotient system.
Source: Stacks 0941 (blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def ordinaryLimit (W : Scheme.{u}) :
    coefficientSequenceModules l E W ⥤ scalarReductionSource l E W :=
  coefficientSequenceRestriction l E W ⋙ lim

/-- Additivity inherited from exact restriction and the existing additive limit.
Source: Stacks 0941 (blueprint: lem-weil-strict-direct-image-mixed-unit). -/
instance ordinaryLimitAdditive (W : Scheme.{u}) : (ordinaryLimit l E W).Additive :=
  inferInstanceAs (coefficientSequenceRestriction l E W ⋙
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)).Additive

/-- The canonical comparison into total limit, using the exact-restriction factors
and the right-derived inverse-limit unit, on the entire complex.
Source: Stacks 0A07, 0941 (blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def totalUnit (W : Scheme.{u}) (P : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    DerivedCategory.Q.obj (((ordinaryLimit l E W).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj P) :=
  (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W).rightDerivedFunctorUnitQ
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj P) ≫
    (coefficientConstantTowerLimit l E W).map
      ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app P)

set_option genSizeOf false in
set_option genInjectivity false in
/-- The normalized comparison of the two direct-image/limit factorizations.
Its ordinary comparison is fixed on projected sections, and the derived comparison
is fixed on whole complexes by the universal derived units. In particular it is
not specified by a family of equalities after derived evaluation.
Source: Stacks 0D6E, 0A07 (blueprint: lem-weil-strict-direct-image-mixed-unit). -/
structure LimitComparison {X Y : Scheme.{u}} (f : X ⟶ Y) where
  ordinary : integralComparisonSequenceDirectImage l E f ⋙ ordinaryLimit l E Y ≅
    ordinaryLimit l E X ⋙ sfCompletedModuleDirectImage l E f
  projections : ∀ (M : coefficientSequenceModules l E X) (n : ℕ) (V : Y.ProEtᵒᵖ)
    (x : ((ordinaryLimit l E Y).obj
      ((integralComparisonSequenceDirectImage l E f).obj M)).val.obj V),
    HEq (((limit.π ((coefficientSequenceRestriction l E X).obj M) (op n)).val.app
        ((proEtaleBaseChange f).op.obj V)) (((ordinary.hom.app M).val.app V) x))
      (((limit.π ((coefficientSequenceRestriction l E Y).obj
        ((integralComparisonSequenceDirectImage l E f).obj M)) (op n)).val.app V) x)
  derived : FrobeniusExchange.systemDirect l E f ⋙ coefficientSequenceLimit l E Y ≅
    coefficientSequenceLimit l E X ⋙ sfCompletedDerivedDirectImage l E f
  normalization : ∀ P : CochainComplex (coefficientSequenceModules l E X) ℤ,
    totalUnit l E Y
        (((integralComparisonSequenceDirectImage l E f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (coefficientSequenceLimit l E Y).map
        ((integralComparisonSequenceDirectImage l E f).rightDerivedFunctorUnitQ P) ≫
      derived.hom.app (DerivedCategory.Q.obj P) =
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P) ≫
      (sfCompletedModuleDirectImage l E f).rightDerivedFunctorUnitQ
        (((ordinaryLimit l E X).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (sfCompletedDerivedDirectImage l E f).map (totalUnit l E X P)

/-- Reduction of the specified strict image: transpose its normalized reconstruction
through the actual reduction/total-limit adjunction. This defines a whole-system map.
Source: Stacks 07A6; DAG proof Step 2
(blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def reductionMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SY : CoefficientDerivedSystemCalculus l E Y) (C : LimitComparison l E f)
    (I : IntegralModel l E f) (K : sfIntegralConstructibleCategory l E X) :
    SY.reduction.obj (I.image.obj K).obj ⟶
      (FrobeniusExchange.systemDirect l E f).obj (SX.reduction.obj K.obj) :=
  SY.reduction.map (I.reconstruction.inv.app K ≫
      (sfCompletedDerivedDirectImage l E f).map (SX.adjunction.unit.app K.obj) ≫
      C.derived.inv.app (SX.reduction.obj K.obj)) ≫
    SY.adjunction.counit.app
      ((FrobeniusExchange.systemDirect l E f).obj (SX.reduction.obj K.obj))

/-- The finite geometric reduction mate, transported through strict reconstruction.
Source: Stacks 07A6; DAG proof Step 2
(blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def finiteReduction {X Y : Scheme.{u}} (f : X ⟶ Y) (I : IntegralModel l E f)
    (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :
    (scalarReductionDerivedExtension l E Y n).obj (I.image.obj K).obj ⟶
      sfFiniteDerivedDirectImage l E f K.obj n :=
  (scalarReductionDerivedExtension l E Y n).map (I.reconstruction.inv.app K) ≫
    ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _).symm
      ((sfCompletedDerivedDirectImage l E f).map
        ((derivedScalarExtensionRestrictionAdjunction l E X n).choose.unit.app K.obj) ≫
        (sfDerivedRestrictionComparison l E f n).hom.app
          ((scalarReductionDerivedExtension l E X n).obj K.obj))

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Exact restriction along the actual map of quotient-ring systems.
Source: Stacks 03CZ, 0941 (blueprint: lem-weil-strict-direct-image-mixed-unit). -/
abbrev restriction (W : Scheme.{u}) :=
  SemilinearSections.resD.{u+1, u, u+1}
    (SemilinearSections.systemMap.{u+1, u, u+1} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
      (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
      (integralScalarQuotientSheafMap l E L ι W)
      (coefficientExtensionQuotient_naturality l E L ι W))

/-- The mixed system unit, formed using the actual scalar adjunction and the
normalized reduction counit, before evaluation.
Source: Stacks 07A6; DAG proof Step 3
(blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def mixedUnit (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus l E W)
    (SL : CoefficientDerivedSystemCalculus l L W) (A : CoefficientExtensionSystems l E L ι W)
    (d : CoefficientExtensionReductionData l E L ι W SE SL A)
    (M : DerivedCategory (scalarReductionSource l E W)) :
    SE.reduction.obj M ⟶ (restriction l E L ι W).obj
      (SL.reduction.obj ((integralScalarExtensionOfUniverses l E L ι W).obj M)) :=
  A.scalar.adjunction.unit.app (SE.reduction.obj M) ≫
    (restriction l E L ι W).map
      ((coefficientExtensionReductionIso l E L ι W SE SL A d).inv.app M)

/-- The intrinsic finite restriction comparison with the prescribed K-injective
normalization; the dependency record refers to precisely this theorem.
Source: Stacks 0D6E (blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def finiteRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.le_add_left 1 n)
  (proEtaleDerivedDirectImage_restrictScalars f
    (integralScalarQuotientMap l E L ι n)).choose

/-- Restriction on the actual abelian coefficient-system categories.
Source: Stacks 03CZ, 0941 (blueprint: lem-weil-strict-direct-image-mixed-unit). -/
abbrev ordinaryRestriction (W : Scheme.{u}) :=
  SemilinearSections.res.{u+1, u, u+1}
    (SemilinearSections.systemMap.{u+1, u, u+1} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
      (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
      (integralScalarQuotientSheafMap l E L ι W)
      (coefficientExtensionQuotient_naturality l E L ι W))

/-- Additivity of restriction uses the existing sectionwise restriction instance.
Source: Stacks 03CZ (blueprint: lem-weil-strict-direct-image-mixed-unit). -/
instance ordinaryRestrictionAdditive (W : Scheme.{u}) :
    (ordinaryRestriction l E L ι W).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars _).Additive

/-- Termwise localization of the ordinary normalized restriction comparison.
The sectionwise additive structures are supplied by the owning operation node.
Source: Stacks 0D6E (blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def restrictionComparisonComplex {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : integralComparisonSequenceDirectImage l L f ⋙ ordinaryRestriction l E L ι Y ≅
      ordinaryRestriction l E L ι X ⋙ integralComparisonSequenceDirectImage l E f) :=
  letI : (integralComparisonSequenceDirectImage l E f).Additive :=
    FrobeniusExchange.systemDirect_additive l E f
  letI : (integralComparisonSequenceDirectImage l L f).Additive :=
    FrobeniusExchange.systemDirect_additive l L f
  NatIso.mapHomologicalComplex c (.up ℤ)

set_option genSizeOf false in
set_option genInjectivity false in
/-- Restriction/direct-image comparison on the entire ringed sequence site.
The ordinary comparison is identity on sections and the derived comparison has
its universal derived-unit normalization, rather than arbitrary evaluations.
Source: Stacks 0D6E; DAG proof Step 1
(blueprint: lem-weil-strict-direct-image-mixed-unit). -/
structure RestrictionComparison {X Y : Scheme.{u}} (f : X ⟶ Y) where
  ordinary : integralComparisonSequenceDirectImage l L f ⋙ ordinaryRestriction l E L ι Y ≅
    ordinaryRestriction l E L ι X ⋙ integralComparisonSequenceDirectImage l E f
  sections : ∀ (M : coefficientSequenceModules l L X) (V : (ℕ × Y.ProEt)ᵒᵖ)
    (x : ((integralComparisonSequenceDirectImage l L f ⋙
      ordinaryRestriction l E L ι Y).obj M).val.obj V),
    HEq (((ordinary.hom.app M).val.app V) x) x
  derived : FrobeniusExchange.systemDirect l L f ⋙ restriction l E L ι Y ≅
    restriction l E L ι X ⋙ FrobeniusExchange.systemDirect l E f
  normalization : ∀ P : CochainComplex (coefficientSequenceModules l L X) ℤ,
    (restriction l E L ι Y).map
        ((integralComparisonSequenceDirectImage l L f).rightDerivedFunctorUnitQ P) ≫
      derived.hom.app (DerivedCategory.Q.obj P) ≫
      (FrobeniusExchange.systemDirect l E f).map
        ((ordinaryRestriction l E L ι X).mapDerivedCategoryFactors.hom.app P) =
    (ordinaryRestriction l E L ι Y).mapDerivedCategoryFactors.hom.app
        (((integralComparisonSequenceDirectImage l L f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((restrictionComparisonComplex l E L ι f ordinary).hom.app P) ≫
      (integralComparisonSequenceDirectImage l E f).rightDerivedFunctorUnitQ
        (((ordinaryRestriction l E L ι X).mapHomologicalComplex (.up ℤ)).obj P)

/-- Finite evaluation of the system mixed unit equals the specified completed
mixed unit, with the exact restriction comparison written explicitly.
Source: Stacks 07A6; DAG proof Step 3
(blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def MixedEvaluation (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus l E W)
    (SL : CoefficientDerivedSystemCalculus l L W) (A : CoefficientExtensionSystems l E L ι W)
    (d : CoefficientExtensionReductionData l E L ι W SE SL A) : Prop :=
  ∀ (M : DerivedCategory (scalarReductionSource l E W)) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E W n).map (mixedUnit l E L ι W SE SL A d M) ≫
      (SemilinearSections.restrictionEvaluation.{u+1, u, u+1} (ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
        (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
        (integralScalarQuotientSheafMap l E L ι W)
        (coefficientExtensionQuotient_naturality l E L ι W) n).hom.app
          (SL.reduction.obj ((integralScalarExtensionOfUniverses l E L ι W).obj M)) ≫
      (proEtaleCoefficientRestrictScalars W
        (integralScalarQuotientMap l E L ι n)).mapDerivedCategory.map
          ((SL.reductionEvaluation n).hom.app
            ((integralScalarExtensionOfUniverses l E L ι W).obj M)) =
    (SE.reductionEvaluation n).hom.app M ≫ sfMixedCompletedReductionUnit l E L ι W n M

/-- Evaluation of reconstruction's system mate is the canonical finite geometric
mate. Together with the actual total-limit counit this fixes the projections r_n.
Source: Stacks 07A6, 0A07; DAG proof Step 2
(blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def ReductionEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SY : CoefficientDerivedSystemCalculus l E Y) (C : LimitComparison l E f)
    (I : IntegralModel l E f) : Prop :=
  ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E Y n).map (reductionMap l E f SX SY C I K) ≫
      (FrobeniusExchange.systemDirectEvaluation l E f n).app (SX.reduction.obj K.obj) ≫
      (proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n+1))).map
        ((SX.reductionEvaluation n).hom.app K.obj) =
    (SY.reductionEvaluation n).hom.app (I.image.obj K).obj ≫ finiteReduction l E f I K n

/-- Finite evaluation of restriction comparison is precisely the normalized
ordinary finite comparison, including its direction and all evaluation transports.
Source: Stacks 0D6E; DAG proof Steps 1 and 6
(blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def RestrictionEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : RestrictionComparison l E L ι f) : Prop :=
  ∀ (N : coefficientSequenceDerived l L X) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E Y n).map (C.derived.inv.app N) ≫
      (SemilinearSections.restrictionEvaluation.{u+1, u, u+1} (ProEt.topology Y)
        (integralCoefficientCommRingSheaf l E Y) (coefficientSequenceCommRingTransition l E Y)
        (integralCoefficientCommRingSheaf l L Y) (coefficientSequenceCommRingTransition l L Y)
        (integralScalarQuotientSheafMap l E L ι Y)
        (coefficientExtensionQuotient_naturality l E L ι Y) n).hom.app
          ((FrobeniusExchange.systemDirect l L f).obj N) ≫
      (proEtaleCoefficientRestrictScalars Y
        (integralScalarQuotientMap l E L ι n)).mapDerivedCategory.map
          ((FrobeniusExchange.systemDirectEvaluation l L f n).app N) =
    (FrobeniusExchange.systemDirectEvaluation l E f n).app
        ((restriction l E L ι X).obj N) ≫
      (proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n+1))).map
        ((SemilinearSections.restrictionEvaluation.{u+1, u, u+1} (ProEt.topology X)
          (integralCoefficientCommRingSheaf l E X) (coefficientSequenceCommRingTransition l E X)
          (integralCoefficientCommRingSheaf l L X) (coefficientSequenceCommRingTransition l L X)
          (integralScalarQuotientSheafMap l E L ι X)
          (coefficientExtensionQuotient_naturality l E L ι X) n).hom.app N) ≫
      (finiteRestriction l E L ι f n).hom.app
        ((coefficientSequenceDerivedEvaluation l L X n).obj N)

/-- The finite reductions are adjuncts of the actual projections of a Roos
limit triangle for the specified tower, under the normalized reconstruction.
Source: Bhatt--Scholze 6.5; Stacks 0A07, 07A6
(blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def StrictProjections {X Y : Scheme.{u}} (f : X ⟶ Y) (I : IntegralModel l E f) : Prop :=
  ∀ K : sfIntegralConstructibleCategory l E X,
    ∃ hprod : HasProduct (sfDirectImageTerm l E f K.obj),
    ∃ R : @SfIntegralDirectImage l _ E _ _ _ X Y f K.obj hprod,
    ∃ q : (I.image.obj K).obj ≅ R.obj,
    ∀ n : ℕ, finiteReduction l E f I K n =
      (scalarReductionDerivedExtension l E Y n).map q.hom ≫
        sfDirectImageReductionComparison l E f R n

/-- The displayed mixed-unit equality, together with uniqueness of its B-linear
lift through the universal source unit. All positive exponents occur as n+1.
Source: Stacks 0B56, 07A6; DAG proof Step 6
(blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def FiniteLaws {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : IntegralModel l E f) (J : IntegralModel l L f)
    (b : I.image ⋙ sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y ≅
      sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X ⋙ J.image) : Prop :=
  ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    (sfMixedCompletedReductionUnit l E L ι Y n (I.image.obj K).obj ≫
      (proEtaleCoefficientRestrictScalars Y
        (integralScalarQuotientMap l E L ι n)).mapDerivedCategory.map
          ((scalarReductionDerivedExtension l L Y n).map ((b.hom.app K).hom) ≫
            finiteReduction l L f J
              ((sfConstructibleIntegralScalarExtension 0 l
                (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K) n) =
      finiteReduction l E f I K n ≫
        (proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n+1))).map
          (sfMixedCompletedReductionUnit l E L ι X n K.obj) ≫
        (finiteRestriction l E L ι f n).hom.app
          ((scalarReductionDerivedExtension l L X n).obj
            ((integralScalarExtensionOfUniverses l E L ι X).obj K.obj))) ∧
    (∀ Z : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l L (n+1)),
      Function.Bijective (fun z :
        (scalarReductionDerivedExtension l L Y n).obj
            ((integralScalarExtensionOfUniverses l E L ι Y).obj (I.image.obj K).obj) ⟶ Z ↦
        sfMixedCompletedReductionUnit l E L ι Y n (I.image.obj K).obj ≫
          (proEtaleCoefficientRestrictScalars Y
            (integralScalarQuotientMap l E L ι n)).mapDerivedCategory.map z))

/-- Simultaneous system normalization. All auxiliary comparisons have their
ordinary-section and whole-complex derived normalizations. The central equality
is an equality in D(A_bullet), retaining quotient transitions and scalar association.
Source: Stacks 0B56, 0D6E, 07A6; DAG proof Steps 1--5
(blueprint: lem-weil-strict-direct-image-mixed-unit). -/
def CoherentLaws {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : IntegralModel l E f) (J : IntegralModel l L f)
    (b : I.image ⋙ sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y ≅
      sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X ⋙ J.image) : Prop :=
  ∃ (EX : CoefficientDerivedSystemCalculus l E X),
  ∃ (EY : CoefficientDerivedSystemCalculus l E Y),
  ∃ (LX : CoefficientDerivedSystemCalculus l L X),
  ∃ (LY : CoefficientDerivedSystemCalculus l L Y),
  ∃ (AX : CoefficientExtensionSystems l E L ι X),
  ∃ (AY : CoefficientExtensionSystems l E L ι Y),
  ∃ (dX : CoefficientExtensionReductionData l E L ι X EX LX AX),
  ∃ (dY : CoefficientExtensionReductionData l E L ι Y EY LY AY),
  ∃ (CE : LimitComparison l E f),
  ∃ (CL : LimitComparison l L f),
  ∃ (restrictionComparison : RestrictionComparison l E L ι f),
  Nonempty (CoefficientDerivedSystemCoherence l E X EX) ∧
  Nonempty (CoefficientDerivedSystemCoherence l E Y EY) ∧
  Nonempty (CoefficientDerivedSystemCoherence l L X LX) ∧
  Nonempty (CoefficientDerivedSystemCoherence l L Y LY) ∧
  (StrictProjections l E f I) ∧
  (StrictProjections l L f J) ∧
  (RestrictionEvaluation l E L ι f restrictionComparison) ∧
  (ReductionEvaluation l E f EX EY CE I) ∧
  (ReductionEvaluation l L f LX LY CL J) ∧
  (MixedEvaluation l E L ι X EX LX AX dX) ∧
  (MixedEvaluation l E L ι Y EY LY AY dY) ∧
  (∀ K : sfIntegralConstructibleCategory l E X,
    IsIso (reductionMap l E f EX EY CE I K)) ∧
  (∀ K : sfIntegralConstructibleCategory l L X,
    IsIso (reductionMap l L f LX LY CL J K)) ∧
  (∀ K : sfIntegralConstructibleCategory l E X,
    mixedUnit l E L ι Y EY LY AY dY (I.image.obj K).obj ≫
      (restriction l E L ι Y).map
        (LY.reduction.map ((b.hom.app K).hom) ≫
          reductionMap l L f LX LY CL J
            ((sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K)) =
    reductionMap l E f EX EY CE I K ≫
      (FrobeniusExchange.systemDirect l E f).map
        (mixedUnit l E L ι X EX LX AX dX K.obj) ≫
      restrictionComparison.derived.inv.app
        (LX.reduction.obj ((integralScalarExtensionOfUniverses l E L ι X).obj K.obj))) ∧
  (∀ (K : sfIntegralConstructibleCategory l E X)
    (Z : coefficientSequenceDerived l L Y),
    Function.Bijective (fun z : LY.reduction.obj
        ((integralScalarExtensionOfUniverses l E L ι Y).obj (I.image.obj K).obj) ⟶ Z ↦
      mixedUnit l E L ι Y EY LY AY dY (I.image.obj K).obj ≫
        (restriction l E L ι Y).map z))
```

## New

The same declarations and bodies, verbatim, belong to Sheaf.Paper.StrictDirectImageMixedUnitData. The original module adds `public import Sheaf.Paper.StrictDirectImageMixedUnitData`. The theorem and its elaborated type retain their original names and signatures. No definition changes meaning, so no target statement review is reopened.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.StrictDirectImageMixedUnit | H4 | Imports the unchanged interfaces and proves its theorem by assembly. |
| Sheaf.Paper.StrictMixedSystemModels | new, H4 | Uses the shared normalized model definitions. |
| Sheaf.Paper.StrictMixedScalarSquare | new, H4 | Uses the shared comparison and reduction maps. |
| Sheaf.Paper.StrictMixedFiniteEvaluation | new, H4 | Uses the unchanged law predicates. |

`tools/downstream.py Sheaf.Paper.StrictDirectImageMixedUnit` reports zero existing downstream modules. A declaration search finds CoherentLaws used only in the item. No existing consumer requires adaptation.

## Status

landed 20261025T202159-L-2688115 2026-10-25 (merge of deliver/H4/Sheaf.Paper.StrictDirectImageMixedUnit)
