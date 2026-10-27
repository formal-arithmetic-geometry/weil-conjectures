# WeilConjectures.TrfStalkCompositorTowerData and the compositor module interface

## Reason

The strict finite construction and its derived descent need the original data types
without importing the theorem that combines them. Move the original twelve data
and predicate declarations to `Sheaf.Paper.TraceStalkCompositorTowerData` and publicly
reexport that module from the original module. Their names, binders, types,
definition bodies and visibility stay identical. No mathematical definition or
target statement changes. Add the strict finite subrecord, its coherence predicate,
and the explicit forgetful projection `toStrict`; these contain no proof holes.
The two new construction modules import the data module and are proof imports of
the original module, avoiding an import cycle.

## Old

The following interface was declared in
`Sheaf.Paper.TraceStalkCompositorTowerRealization` (verbatim):

```lean
def trfSystemTower (X : Scheme.{u}) :=
  (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex

/-- Geometric stalks of the whole coefficient diagram, with integral constant scalars.
Source: Stacks 0F4F (blueprint: lem-trf-stalk-compositor-tower-realization). -/
def trfSystemStalkTower (D : FiniteFieldDatum.{u}) {X : Scheme.{u}}
    (v : Spec (.of D.k) ⟶ X) :=
  trfSystemTower l E X ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj
    ((integralCoefficientModuleStalkFunctor l E v).mapHomologicalComplex (.up ℤ))

/-- Point sections of one strict coefficient diagram.
Source: Stacks 05V1 (blueprint: lem-trf-stalk-compositor-tower-realization). -/
def trfSystemPointSections (D : FiniteFieldDatum.{u}) :=
  trfSystemTower l E (Spec (.of D.k)) ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj
    ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ))

/-- The finite pullback of the whole system followed by its geometric stalk tower.
Source: Stacks 0F4F (blueprint: lem-trf-stalk-compositor-tower-realization). -/
def trfSystemPullbackStalkTower (D : FiniteFieldDatum.{u}) {X Y : Scheme.{u}}
    (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y) :=
  (integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ) ⋙
    trfSystemStalkTower l E D v

/-- Sections of the actual finite pullback system to the geometric point.
Source: Stacks 05V1 (blueprint: lem-trf-stalk-compositor-tower-realization). -/
def trfSystemSectionTower (D : FiniteFieldDatum.{u}) {X : Scheme.{u}}
    (v : Spec (.of D.k) ⟶ X) :=
  (integralComparisonSequencePullback l E v).mapHomologicalComplex (.up ℤ) ⋙
    trfSystemPointSections l E D

/-- Localized Roos realization of a geometric stalk tower, using both cone coordinates.
Source: Stacks 0941 (blueprint: lem-trf-stalk-compositor-tower-realization). -/
def trfSystemStalkRoos (D : FiniteFieldDatum.{u}) {X : Scheme.{u}}
    (v : Spec (.of D.k) ⟶ X) :=
  trfSystemStalkTower l E D v ⋙ integralOperationsRoosFunctor ⋙ trfIntegralModuleQ l E

/-- Canonical passage from sections of the total limit to the section-tower cone.
The two-coordinate map is scalarRoosMap, rather than a triangle filler.
Source: Stacks 0941 (blueprint: lem-trf-stalk-compositor-tower-realization). -/
def trfSystemSectionsRoosArrow (D : FiniteFieldDatum.{u})
    (I : IntegralComparisonSystem.{u} l)
    (C : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ) :=
  (pointFibreIntegralAmbient D l E).map
      (integralComparisonRoosBridge l E _ ((I.coefficient E).roos _) C).hom ≫
    (trfIntegralSectionsFactors l E D).hom.app
      (integralOperationsRoos ((trfSystemTower l E _).obj C)) ≫
    (trfIntegralModuleQ l E).map
      (scalarRoosMap (pointIntegralSections l E D.k) ((trfSystemTower l E _).obj C))

/-- The coefficient-module derived category with the published small Hom universe.
Source: blueprint size convention
(blueprint: lem-trf-stalk-compositor-tower-realization). -/
abbrev trfStalkDerived :=
  @DerivedCategory
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian _)

/-- The finite germ isomorphisms, their section coordinates, and reparametrizations
on whole strict systems. Their normalizations are asserted in the theorem below.
Source: Stacks 0F4F, 05V1
(blueprint: lem-trf-stalk-compositor-tower-realization). -/
structure TrfStalkCompositorTowerData (D : FiniteFieldDatum.{u})
    (I : IntegralComparisonSystem.{u} l) where
  /-- Unit-normalized finite evaluation of the system inverse image. -/
  finitePullback : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ),
    integralComparisonSequencePullback l E f ⋙ coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E X n ⋙
        proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f
  /-- Finite pullback-stalk comparison, natural on whole complexes of systems. -/
  c : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y),
    trfSystemPullbackStalkTower l E D f v ≅ trfSystemStalkTower l E D (v ≫ f)
  /-- Section-coordinate comparison at every geometric point. -/
  e : ∀ {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X),
    trfSystemSectionTower l E D v ≅ trfSystemStalkTower l E D v
  /-- Reindexing by a field automorphism on the same strict system. -/
  r : ∀ {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X) (α : D.k ≃+* D.k),
    trfSystemStalkTower l E D v ≅ trfSystemStalkTower l E D
      (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v)
  /-- Descent of stalk Roos realization to the ordinary system derived category. -/
  realization : ∀ {X : Scheme.{u}} (_v : Spec (.of D.k) ⟶ X),
    coefficientSequenceDerived l E X ⥤
      trfStalkDerived l E
  /-- Its comparison with the actual cone on every strict complex of systems. -/
  factors : ∀ {X : Scheme.{u}} (_v : Spec (.of D.k) ⟶ X),
    DerivedCategory.Q ⋙ realization _v ≅ trfSystemStalkRoos l E D _v
  /-- Derived finite comparison, normalized by c before realization. -/
  comparison : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y),
    integralComparisonDerivedSequencePullback l E f ⋙ realization v ≅ realization (v ≫ f)
  /-- Reparametrization descended from the diagonal strict cone map. -/
  derivedR : ∀ {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X) (α : D.k ≃+* D.k),
    realization v ≅ realization (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v)
  /-- Identity-point stalk is final-object sections on the entire system. -/
  gamma : trfSystemPointSections l E D ≅
    trfSystemStalkTower l E D (𝟙 (Spec (.of D.k)))
  /-- Sections of total limit compared with realized system stalks. -/
  sections : ∀ {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X),
    integralComparisonDerivedSequencePullback l E v ⋙
        coefficientSequenceLimit l E (Spec (.of D.k)) ⋙ pointFibreIntegralAmbient D l E ≅
      realization v
  /-- Integral point-stalk identification on the full constructible category. -/
  integral : ∀ {X : Scheme.{u}}
    [_hX : ∀ x : X, Invertible (l : X.residueField x)] (v : Spec (.of D.k) ⟶ X),
    (sfIntegralConstructible l E X).ι ⋙ trfCompletedPointFibre l E D v ≅
      (sfIntegralConstructible l E X).ι ⋙
        ((I.coefficient E).system X).reduction ⋙ realization v

/-- The section image of eta followed by the finite section-coordinate comparison.
Eta is the whole-system counit construction, not independently chosen reductions.
Source: Stacks 0941, 0F4F
(blueprint: lem-trf-stalk-compositor-tower-realization). -/
def trfNestedStalkRealization (D : FiniteFieldDatum.{u})
    (I : IntegralComparisonSystem.{u} l) (S : TrfStalkCompositorTowerData l E D I)
    {X Y : Scheme.{u}}
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hS : ∀ z : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField z)]
    (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y) (K : sfIntegralConstructibleCategory l E X) :=
  (pointFibreIntegralAmbient D l E).map
      (@integralComparisonEta l _ E _ _ _ I X Y (Spec (.of D.k)) hX hY hS v f K).hom ≫
    (S.sections v).hom.app
      ((integralComparisonDerivedSequencePullback l E f).obj
        (((I.coefficient E).system X).reduction.obj K.obj))

/-- Normalizations and strict whole-diagram identities for the stalk compositors.
Every finite map is the published germ map; the integral arrows use the specified
entire-system eta and the diagonal Roos map. Equality after independent reductions
is never used as a substitute for equality of systems.
Source: Stacks 0F4F, 05V1, 0941 and blueprint Local powers (b)
(blueprint: lem-trf-stalk-compositor-tower-realization). -/
structure TrfStalkCompositorTowerCoherent (D : FiniteFieldDatum.{u})
    (I : IntegralComparisonSystem.{u} l) (S : TrfStalkCompositorTowerData l E D I) : Prop where
  /-- The finite evaluation identification preserves every inverse-image unit generator. -/
  finiteUnit : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ)
    (M : coefficientSequenceModules l E X) (U : X.ProEt)
    (x : M.val.obj (op (n, U))),
    ((S.finitePullback f n).hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
        (coefficientEvaluationSection l E Y
          ((integralComparisonSequencePullback l E f).obj M) n
          (op ((proEtaleBaseChange f).obj U))
          (integralComparisonSequenceGenerator l E f M n U x)) =
      ((proEtaleConstantRingAdjunction (Padic.coefficientExtensionRing l E (n + 1)) f).unit.app
        ((coefficientSequenceEvaluation l E X n).obj M)).val.app (op U)
          (coefficientEvaluationSection l E X M n (op U) x)
  /-- At every degree and exponent the strict map is exactly the finite germ comparison. -/
  finiteGerm : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ) (n : ℕ) (i : ℤ),
    HEq ((((S.c f v).hom.app C).app (op n)).f i).hom.toFun
      (((finiteCoefficientModuleStalkFunctor v
          (Padic.coefficientExtensionRing l E (n + 1))).map
          ((S.finitePullback f n).hom.app (C.X i))) ≫
        (proEtalePullbackStalkComparison (Padic.coefficientExtensionRing l E (n + 1))
          f v).hom.app ((coefficientSequenceEvaluation l E X n).obj (C.X i))).hom.toFun
  /-- Identity-point sections map to the germ represented by the final neighbourhood. -/
  pointGerm : ∀ (C : CochainComplex
      (coefficientSequenceModules l E (Spec (.of D.k))) ℤ) (n : ℕ) (i : ℤ)
    (x : ((((trfSystemTower l E _).obj C).obj (op n)).X i).val.obj
      (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
    (((S.gamma.hom.app C).app (op n)).f i) x =
      (colimit.ι ((proEtaleGeometricNeighbourhoodForget (𝟙 (Spec (.of D.k)))).op ⋙
        ((((trfSystemTower l E _).obj C).obj (op n)).X i).val.presheaf)
          (op (proEtaleConstantGermNeighbourhood (𝟙 (Spec (.of D.k)))))) x
  /-- The section coordinate is identity-point sections followed by the finite germ map. -/
  sectionGerm : ∀ {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ),
    HEq ((S.e v).hom.app C)
      ((S.gamma.hom.app
          (((integralComparisonSequencePullback l E v).mapHomologicalComplex (.up ℤ)).obj C)) ≫
        (S.c v (𝟙 (Spec (.of D.k)))).hom.app C)
  /-- Realized finite comparison is the localization of the strict cone map. -/
  comparisonFactors : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ),
    (S.comparison f v).hom.app (DerivedCategory.Q.obj C) ≫
        (S.factors (v ≫ f)).hom.app C =
      (S.realization v).map
          ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app C) ≫
        (S.factors v).hom.app
          (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C) ≫
        (trfIntegralModuleQ l E).map (integralOperationsRoosMap ((S.c f v).hom.app C))
  /-- Sections-to-stalk realization uses both canonical product coordinates. -/
  sectionsFactors : ∀ {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ),
    (S.sections v).hom.app (DerivedCategory.Q.obj C) ≫ (S.factors v).hom.app C =
      (pointFibreIntegralAmbient D l E).map
          ((coefficientSequenceLimit l E _).map
            ((integralComparisonSequencePullback l E v).mapDerivedCategoryFactors.hom.app C)) ≫
        trfSystemSectionsRoosArrow l E D I
          (((integralComparisonSequencePullback l E v).mapHomologicalComplex (.up ℤ)).obj C) ≫
        (trfIntegralModuleQ l E).map (integralOperationsRoosMap ((S.e v).hom.app C))
  /-- The integral comparison is fixed by the defining pullback and the section comparison. -/
  integralNormalized : ∀ {X : Scheme.{u}}
    [_hX : ∀ x : X, Invertible (l : X.residueField x)] (v : Spec (.of D.k) ⟶ X)
    (K : sfIntegralConstructibleCategory l E X),
    (S.integral v).hom.app K =
      (pointFibreIntegralAmbient D l E).map
          (((I.coefficient E).pullback v).realization.hom.app K.obj) ≫
        (S.sections v).hom.app (((I.coefficient E).system X).reduction.obj K.obj)
  /-- The finite section-coordinate equation, on the entire strict diagram. -/
  finiteSections : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ),
    (S.e (v ≫ f)).hom.app C =
      (trfSystemPointSections l E D).map
          ((NatIso.mapHomologicalComplex (integralComparisonSequenceComposition l E v f)
            (.up ℤ)).hom.app C) ≫
        (S.e v).hom.app
          (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C) ≫
        (S.c f v).hom.app C
  /-- Iterated finite pullbacks obey the actual finite compositor on the same tower. -/
  finiteComposition : ∀ {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (w : Spec (.of D.k) ⟶ Z) (C : CochainComplex (coefficientSequenceModules l E X) ℤ),
    HEq ((S.c (h ≫ f) w).hom.app C)
      ((trfSystemStalkTower l E D w).map
          ((NatIso.mapHomologicalComplex (integralComparisonSequenceComposition l E h f)
            (.up ℤ)).hom.app C) ≫
        (S.c h w).hom.app
          (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C) ≫
        (S.c f (w ≫ h)).hom.app C)
  /-- The identity comparison becomes the identity strict map under the canonical unit. -/
  finiteIdentity : ∀ (X : Scheme.{u}) (v : Spec (.of D.k) ⟶ X)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ),
    HEq ((S.c (𝟙 X) v).hom.app C)
      ((trfSystemStalkTower l E D v).map
        ((NatIso.mapHomologicalComplex (integralComparisonSequenceUnit l E X)
          (.up ℤ)).hom.app C))
  /-- R leaves the neighbourhood and the section unchanged, only its lift is reindexed. -/
  reparamGerm : ∀ {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X) (α : D.k ≃+* D.k)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ) (n : ℕ) (i : ℤ),
    HEq ((((S.r v α).hom.app C).app (op n)).f i).hom.toFun
      ((proEtaleStalkReparam (Padic.coefficientExtensionRing l E (n + 1)) v α).hom.app
        ((coefficientSequenceEvaluation l E X n).obj (C.X i))).hom.toFun
  /-- The reparametrization square commutes as a strict tower square. -/
  reparamSquare : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y)
    (α : D.k ≃+* D.k) (C : CochainComplex (coefficientSequenceModules l E X) ℤ),
    HEq ((S.c f v).hom.app C ≫ (S.r (v ≫ f) α).hom.app C)
      ((S.r v α).hom.app
          (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C) ≫
        (S.c f (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v)).hom.app C)
  /-- The specified integral compositor inverse is the realized finite tower comparison. -/
  integralCompositor : ∀ {X Y : Scheme.{u}}
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hS : ∀ z : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField z)]
    (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y) (K : sfIntegralConstructibleCategory l E X),
    (pointFibreIntegralAmbient D l E).map
        (@integralComparisonComposition l _ E _ _ _ I X Y
          (Spec (.of D.k)) hX hY hS v f K).inv ≫
        (S.integral (v ≫ f)).hom.app K =
      @trfNestedStalkRealization l _ E _ _ _ D I S X Y hX hY hS f v K ≫
        (S.comparison f v).hom.app (((I.coefficient E).system X).reduction.obj K.obj)
  /-- Reparametrization after localization is exactly its strict diagonal cone map. -/
  reparamFactors : ∀ {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X) (α : D.k ≃+* D.k)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ),
    (S.derivedR v α).hom.app (DerivedCategory.Q.obj C) ≫
        (S.factors (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v)).hom.app C =
      (S.factors v).hom.app C ≫
        (trfIntegralModuleQ l E).map (integralOperationsRoosMap ((S.r v α).hom.app C))
  /-- The realized square is carried from the strict square, before evaluation. -/
  realizedReparam : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y)
    (α : D.k ≃+* D.k) (C : coefficientSequenceDerived l E X),
    HEq ((S.comparison f v).hom.app C ≫ (S.derivedR (v ≫ f) α).hom.app C)
      ((S.derivedR v α).hom.app ((integralComparisonDerivedSequencePullback l E f).obj C) ≫
        (S.comparison f (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v)).hom.app C)
  /-- Nested counit identifications carry the last factor to J_w of the compositor. -/
  integralIteration : ∀ {X Y Z : Scheme.{u}}
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    [hS : ∀ z : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField z)]
    (h : Z ⟶ Y) (f : Y ⟶ X) (w : Spec (.of D.k) ⟶ Z)
    (K : sfIntegralConstructibleCategory l E X),
    (trfCompletedPointFibre l E D w).map
        (@integralComparisonComposition l _ E _ _ _ I X Y Z hX hY hZ h f K).hom ≫
        @trfNestedStalkRealization l _ E _ _ _ D I S Y Z hY hZ hS h w
          ((constructibleIntegralPullback l E f).obj K) ≫
        (S.realization w).map
          ((integralComparisonDerivedSequencePullback l E h).map
            ((integralComparisonPullbackCounit l E f
              ((I.coefficient E).system X) ((I.coefficient E).system Y)
              ((I.coefficient E).roos Y) ((I.coefficient E).pullback f)).app K.obj)) =
      @trfNestedStalkRealization l _ E _ _ _ D I S X Z hX hZ hS (h ≫ f) w K ≫
        (S.realization w).map
          ((integralComparisonSystemComposition l E h f).hom.app
            (((I.coefficient E).system X).reduction.obj K.obj))
  /-- Identity comparison agrees with the finite unit on the whole derived system. -/
  realizedIdentity : ∀ (X : Scheme.{u}) (v : Spec (.of D.k) ⟶ X)
    (C : coefficientSequenceDerived l E X),
    HEq ((S.comparison (𝟙 X) v).hom.app C)
      ((S.realization v).map ((integralComparisonSystemUnit l E X).hom.app C))
  /-- Integral unit normalization at s, using the same completeness unit and finite unit. -/
  integralPointUnit : ∀
    [hS : ∀ z : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField z)]
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))),
    (S.integral (𝟙 (Spec (.of D.k)))).hom.app N =
      (pointFibreIntegralAmbient D l E).map
          (@integralComparisonUnit l _ E _ _ _ I (Spec (.of D.k)) hS N).hom ≫
        (pointFibreIntegralAmbient D l E).map
          (((I.coefficient E).system (Spec (.of D.k))).adjunction.unit.app N.obj) ≫
        (pointFibreIntegralAmbient D l E).map
          ((coefficientSequenceLimit l E _).map
            ((integralComparisonSystemUnit l E _).inv.app
              (((I.coefficient E).system _).reduction.obj N.obj))) ≫
        (S.sections (𝟙 (Spec (.of D.k)))).hom.app
          (((I.coefficient E).system _).reduction.obj N.obj)

/-- Agreement with every simultaneous K-flat quotient presentation and every
normalized comparison of the bounded-quotient realization dependency. The arrow
identity includes arbitrary derived changes of representative through q, q' and
localization, not only agreement of individual finite reductions.
Source: Stacks 0F4F, 0941; blueprint Local powers (b)
(blueprint: lem-trf-stalk-compositor-tower-realization). -/
def TrfStalkCompositorQuotientCompatible (D : FiniteFieldDatum.{u})
    (I : IntegralComparisonSystem.{u} l) (S : TrfStalkCompositorTowerData l E D I) : Prop :=
  ∀ (X : Scheme.{u}) [_hX : ∀ x : X, Invertible (l : X.residueField x)]
    (v : Spec (.of D.k) ⟶ X) (K : sfIntegralConstructibleCategory l E X)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (a : ((I.coefficient E).system X).reduction.obj (DerivedCategory.Q.obj P.obj) ≅
      DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P.obj),
    CoefficientReductionPresentation l E X
      ((I.coefficient E).system X).toCoefficientDerivedSystemReduction P.obj P.property.1 C a κ →
    ∀ (γ : ∀ n : ℕ, pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ≅
        finiteCoefficientModuleStalkFunctor (𝟙 (Spec (.of D.k)))
          (Padic.coefficientExtensionRing l E (n + 1)))
      (δ : ∀ n : ℕ, integralOperationsLevelPullback l E v n ⋙
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ≅
          finiteCoefficientModuleStalkFunctor v (Padic.coefficientExtensionRing l E (n + 1)))
      (eP : trfQuotientSectionTower l E v ≅ trfQuotientStalkTower l E v),
      TrfQuotientGermNormalized l E D v γ δ eP →
      ∃ z : (trfSystemStalkTower l E D v).obj C ≅
          (trfQuotientStalkTower l E v).obj P.obj,
        (∀ (n : ℕ) (i : ℤ),
          HEq ((z.hom.app (op n)).f i).hom.toFun
            ((finiteCoefficientModuleStalkFunctor v
              (Padic.coefficientExtensionRing l E (n + 1))).map ((κ n).hom.f i)).hom.toFun) ∧
        (S.integral v).hom.app K ≫
            (S.realization v).map
              (((I.coefficient E).system X).reduction.map q.inv ≫ a.hom) ≫
            (S.factors v).hom.app C ≫
            (trfIntegralModuleQ l E).map (integralOperationsRoosMap z.hom) =
          trfQuotientStalkRealizationArrow l E D v eP K.obj P q
```

## New

The same declarations, with exactly the same bodies and signatures, are declared
in `Sheaf.Paper.TraceStalkCompositorTowerData`. Only their docstring node tags now
refer to `def-trf-stalk-compositor-tower-data`. The original module reexports them:

```lean
public import Sheaf.Paper.TraceStalkCompositorTowerData
import Sheaf.Paper.TraceStrictStalkTowers
import Sheaf.Paper.TraceStalkTowerDescent
```

The new strict subrecord and projection are:

```lean
/-- The finite part of stalk-compositor data, before Roos realization or localization.
Source: Stacks 0F4F and 05V1
(blueprint: def-trf-stalk-compositor-tower-data). -/
structure TrfStrictStalkTowerData (D : FiniteFieldDatum.{u}) where
  /-- Unit-normalized finite evaluation of the system inverse image. -/
  finitePullback : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ),
    integralComparisonSequencePullback l E f ⋙ coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E X n ⋙
        proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f
  /-- Finite pullback-stalk comparison, natural on whole complexes of systems. -/
  c : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y),
    trfSystemPullbackStalkTower l E D f v ≅ trfSystemStalkTower l E D (v ≫ f)
  /-- Section-coordinate comparison at every geometric point. -/
  e : ∀ {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X),
    trfSystemSectionTower l E D v ≅ trfSystemStalkTower l E D v
  /-- Reindexing by a field automorphism on the same strict system. -/
  r : ∀ {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X) (α : D.k ≃+* D.k),
    trfSystemStalkTower l E D v ≅ trfSystemStalkTower l E D
      (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v)
  /-- Identity-point stalk is final-object sections on the entire system. -/
  gamma : trfSystemPointSections l E D ≅
    trfSystemStalkTower l E D (𝟙 (Spec (.of D.k)))

/-- The unit, germ and composition normalizations on the strict finite diagrams.
Source: Stacks 0F4F and 05V1
(blueprint: def-trf-stalk-compositor-tower-data). -/
structure TrfStrictStalkTowerCoherent (D : FiniteFieldDatum.{u})
    (T : TrfStrictStalkTowerData l E D) : Prop where
  /-- The finite evaluation identification preserves every inverse-image unit generator. -/
  finiteUnit : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ)
    (M : coefficientSequenceModules l E X) (U : X.ProEt)
    (x : M.val.obj (op (n, U))),
    ((T.finitePullback f n).hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
        (coefficientEvaluationSection l E Y
          ((integralComparisonSequencePullback l E f).obj M) n
          (op ((proEtaleBaseChange f).obj U))
          (integralComparisonSequenceGenerator l E f M n U x)) =
      ((proEtaleConstantRingAdjunction (Padic.coefficientExtensionRing l E (n + 1)) f).unit.app
        ((coefficientSequenceEvaluation l E X n).obj M)).val.app (op U)
          (coefficientEvaluationSection l E X M n (op U) x)
  /-- At every degree and exponent the strict map is exactly the finite germ comparison. -/
  finiteGerm : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ) (n : ℕ) (i : ℤ),
    HEq ((((T.c f v).hom.app C).app (op n)).f i).hom.toFun
      (((finiteCoefficientModuleStalkFunctor v
          (Padic.coefficientExtensionRing l E (n + 1))).map
          ((T.finitePullback f n).hom.app (C.X i))) ≫
        (proEtalePullbackStalkComparison (Padic.coefficientExtensionRing l E (n + 1))
          f v).hom.app ((coefficientSequenceEvaluation l E X n).obj (C.X i))).hom.toFun
  /-- Identity-point sections map to the germ represented by the final neighbourhood. -/
  pointGerm : ∀ (C : CochainComplex
      (coefficientSequenceModules l E (Spec (.of D.k))) ℤ) (n : ℕ) (i : ℤ)
    (x : ((((trfSystemTower l E _).obj C).obj (op n)).X i).val.obj
      (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
    (((T.gamma.hom.app C).app (op n)).f i) x =
      (colimit.ι ((proEtaleGeometricNeighbourhoodForget (𝟙 (Spec (.of D.k)))).op ⋙
        ((((trfSystemTower l E _).obj C).obj (op n)).X i).val.presheaf)
          (op (proEtaleConstantGermNeighbourhood (𝟙 (Spec (.of D.k)))))) x
  /-- The section coordinate is identity-point sections followed by the finite germ map. -/
  sectionGerm : ∀ {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ),
    HEq ((T.e v).hom.app C)
      ((T.gamma.hom.app
          (((integralComparisonSequencePullback l E v).mapHomologicalComplex (.up ℤ)).obj C)) ≫
        (T.c v (𝟙 (Spec (.of D.k)))).hom.app C)
  /-- The finite section-coordinate equation, on the entire strict diagram. -/
  finiteSections : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ),
    (T.e (v ≫ f)).hom.app C =
      (trfSystemPointSections l E D).map
          ((NatIso.mapHomologicalComplex (integralComparisonSequenceComposition l E v f)
            (.up ℤ)).hom.app C) ≫
        (T.e v).hom.app
          (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C) ≫
        (T.c f v).hom.app C
  /-- Iterated finite pullbacks obey the actual finite compositor on the same tower. -/
  finiteComposition : ∀ {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (w : Spec (.of D.k) ⟶ Z) (C : CochainComplex (coefficientSequenceModules l E X) ℤ),
    HEq ((T.c (h ≫ f) w).hom.app C)
      ((trfSystemStalkTower l E D w).map
          ((NatIso.mapHomologicalComplex (integralComparisonSequenceComposition l E h f)
            (.up ℤ)).hom.app C) ≫
        (T.c h w).hom.app
          (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C) ≫
        (T.c f (w ≫ h)).hom.app C)
  /-- The identity comparison becomes the identity strict map under the canonical unit. -/
  finiteIdentity : ∀ (X : Scheme.{u}) (v : Spec (.of D.k) ⟶ X)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ),
    HEq ((T.c (𝟙 X) v).hom.app C)
      ((trfSystemStalkTower l E D v).map
        ((NatIso.mapHomologicalComplex (integralComparisonSequenceUnit l E X)
          (.up ℤ)).hom.app C))
  /-- R leaves the neighbourhood and the section unchanged, only its lift is reindexed. -/
  reparamGerm : ∀ {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X) (α : D.k ≃+* D.k)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ) (n : ℕ) (i : ℤ),
    HEq ((((T.r v α).hom.app C).app (op n)).f i).hom.toFun
      ((proEtaleStalkReparam (Padic.coefficientExtensionRing l E (n + 1)) v α).hom.app
        ((coefficientSequenceEvaluation l E X n).obj (C.X i))).hom.toFun
  /-- The reparametrization square commutes as a strict tower square. -/
  reparamSquare : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y)
    (α : D.k ≃+* D.k) (C : CochainComplex (coefficientSequenceModules l E X) ℤ),
    HEq ((T.c f v).hom.app C ≫ (T.r (v ≫ f) α).hom.app C)
      ((T.r v α).hom.app
          (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C) ≫
        (T.c f (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v)).hom.app C)

/-- Forget the derived realization and keep precisely the strict germ diagram.
Source: Stacks 0F4F (blueprint: def-trf-stalk-compositor-tower-data). -/
def TrfStalkCompositorTowerData.toStrict {D : FiniteFieldDatum.{u}}
    {I : IntegralComparisonSystem.{u} l} (S : TrfStalkCompositorTowerData l E D I) :
    TrfStrictStalkTowerData l E D where
  finitePullback := S.finitePullback
  c := S.c
  e := S.e
  r := S.r
  gamma := S.gamma
```

## Users

`tools/downstream.py` with all thirteen original declaration names reports only
the original module as a textual user, and one downstream module. No consumer
adaptation is needed: public reexport preserves the existing import interface.
No module held by another group is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TraceStalkCompositorTowerRealization | K9 | Reexports identical data; complete assembly proof replaces its hole. |
| Sheaf.Paper.SourceSectionStalkConeComparison | K6 | Import remains valid; no declaration or file changed. |

## Status

landed 20261025T095605-L-3451337 2026-10-25 (merge of deliver/K9/Sheaf.Paper.TraceStalkCompositorTowerRealization)
