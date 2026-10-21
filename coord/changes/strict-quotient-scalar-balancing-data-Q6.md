# StrictScalarBalancing declaration ownership

## Reason

The pullback-only result needs the same concrete module and tower operations as the
augmentation proof. Put their existing definitions in a shared data module to avoid
an import cycle. This is a dependency extraction, not a compile-time workaround.
All declaration names, universes, signatures, visibility, instance attributes and
bodies are preserved. Only their blueprint ownership tags and file location change.
The root module publicly imports the data module, retaining its full public API.
No target statement or interpretation changes.

## Old

In `lean/Sheaf/Paper/StrictQuotientScalarBalancing.lean`:

```lean
/-- The published small pro-etale topology, equivalent to the original site.
Source: size convention and Stacks 09A5
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
abbrev topology (T : Scheme.{u}) := proEtaleModelTopology T

/-- Constant (false) or completed (true) coefficients, using the existing actual limit.
Source: strict coefficient supplement, coefficient notation; Stacks 099L
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
abbrev ring (T : Scheme.{u}) (d : AdicCoefficientDatum A) (b : Bool) :=
  coefficients (topology T) A d.ideal b

/-- The canonical scalar map, given by the existing quotient cone.
Source: strict coefficient supplement; Stacks 093M
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
abbrev scalar (T : Scheme.{u}) (d : AdicCoefficientDatum A) :=
  coefficientMap (topology T) A d.ideal

/-- The existing actual derived strict reduction functor.
Source: strict coefficient supplement, R^a and R^0; Stacks 06YY
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
abbrev reduction (T : Scheme.{u}) (d : AdicCoefficientDatum A) (b : Bool) :=
  (quotientPresentation (topology T) A d.ideal b).tower

/-- Exact constant diagrams, descended to the standard derived localizations.
Source: strict coefficient supplement, Delta; Stacks 015F
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
def delta (T : Scheme.{u}) (d : AdicCoefficientDatum A) (b : Bool) :
    D (ring T d b) ⥤ TD (ring T d b) :=
  letI := HasDerivedCategory.standard (Mod (ring T d b))
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (ring T d b))
  (constantTower (topology T) (ring T d b)).mapDerivedCategory

/-- Its exact localization comparison, retaining the constant transition maps.
Source: strict coefficient supplement, Delta; Stacks 015F
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
def deltaFactors (T : Scheme.{u}) (d : AdicCoefficientDatum A) (b : Bool) :
    Q (ring T d b) ⋙ delta T d b ≅
      (constantTower (topology T) (ring T d b)).mapHomologicalComplex (.up ℤ) ⋙
        TQ (ring T d b) :=
  letI := HasDerivedCategory.standard (Mod (ring T d b))
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (ring T d b))
  (constantTower (topology T) (ring T d b)).mapDerivedCategoryFactors

/-- The actual geometric inverse image on the transported sites.
Source: pro-etale inverse image and Stacks 00VC
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
abbrev inverse {U V : Scheme.{u}} (f : U ⟶ V) :=
  (proEtaleModelBaseChange f).sheafPullback (Type (u + 1)) (topology V) (topology U)

/-- Equivalence transport gives the base change its finite-limit structure.
Source: Stacks 09A5 (blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
instance modelBaseChangeLimits {U V : Scheme.{u}} (f : U ⟶ V) :
    PreservesFiniteLimits (proEtaleModelBaseChange f) :=
  letI : (AsSmall.down : proEtaleSiteModel V ⥤ V.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := V.ProEt)).inverse.IsEquivalence
  letI : (AsSmall.up : U.ProEt ⥤ proEtaleSiteModel U).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := U.ProEt)).functor.IsEquivalence
  inferInstanceAs (PreservesFiniteLimits
    ((AsSmall.down : proEtaleSiteModel V ⥤ V.ProEt) ⋙ proEtaleBaseChange f ⋙ AsSmall.up))

/-- Flatness of the site functor is inherited from finite-limit preservation.
Source: Stacks 00X6 (blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
instance modelBaseChangeFlat {U V : Scheme.{u}} (f : U ⟶ V) :
    RepresentablyFlat (proEtaleModelBaseChange f) := flat_of_preservesFiniteLimits _

/-- Left exactness of the sheaf inverse image on the published small models.
Source: Stacks 00X6 (blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
instance inverseLimits {U V : Scheme.{u}} (f : U ⟶ V) :
    PreservesFiniteLimits (inverse f) :=
  Functor.sheafPullbackConstruction.preservesFiniteLimits
    (proEtaleModelBaseChange f) (Type (u + 1)) (topology V) (topology U)

/-- Its specified algebraic lift, constructed from the geometric adjunction.
Source: constant-completion-equivalence, algebraic inverse-image construction
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
def inverseData {U V : Scheme.{u}} (f : U ⟶ V) : InverseImageData (inverse f) :=
  Classical.choice (inverseImageData_exists (inverse f)
    ((proEtaleModelBaseChange f).sheafPushforwardContinuous (Type (u + 1))
      (topology V) (topology U))
    ((proEtaleModelBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
      (topology V) (topology U)))

/-- The projection-defined completed coefficient map or constant coefficient map.
Source: strict coefficient supplement; finite projections define the completed map
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
def coefficient {U V : Scheme.{u}} (f : U ⟶ V) (d : AdicCoefficientDatum A)
    (b : Bool) : (inverseData f).rings.obj (ring V d b) ⟶ ring U d b :=
  match b with
  | false => constantMap (inverseData f) A
  | true => completedMap (inverseData f) A d.ideal

/-- The actual ordinary module pullback along the specified coefficient map.
Source: strict coefficient supplement, ordinary ringed operations; Stacks 03D2
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
abbrev modulePull {U V : Scheme.{u}} (f : U ⟶ V) (d : AdicCoefficientDatum A)
    (b : Bool) := pull (inverseData f) (coefficient f d b)

/-- Termwise application to strict diagrams, before localization.
Source: strict coefficient supplement, strict diagram operations
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
abbrev towerPull {U V : Scheme.{u}} (f : U ⟶ V) (d : AdicCoefficientDatum A)
    (b : Bool) : (ℕᵒᵖ ⥤ Mod (ring V d b)) ⥤ (ℕᵒᵖ ⥤ Mod (ring U d b)) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (modulePull f d b)

/-- The normalized universal derived operations; computation is on every complex
because inverse image along the coefficient isomorphisms is exact.
Source: strict coefficient supplement, L and script L; Stacks 015F, 06YY
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
structure PullModel {U V : Scheme.{u}} (f : U ⟶ V) (d : AdicCoefficientDatum A)
    (b : Bool) where
  ordinary : D (ring V d b) ⥤ D (ring U d b)
  diagrams : TD (ring V d b) ⥤ TD (ring U d b)
  ordinaryFactors : Q (ring V d b) ⋙ ordinary ≅
    (modulePull f d b).mapHomologicalComplex (.up ℤ) ⋙ Q (ring U d b)
  diagramFactors : TQ (ring V d b) ⋙ diagrams ≅
    (towerPull f d b).mapHomologicalComplex (.up ℤ) ⋙ TQ (ring U d b)
  ordinaryUniversal : ordinary.IsLeftDerivedFunctor ordinaryFactors.hom
    (HomologicalComplex.quasiIso (Mod (ring V d b)) (.up ℤ))
  diagramUniversal : diagrams.IsLeftDerivedFunctor diagramFactors.hom
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Mod (ring V d b)) (.up ℤ))


/-- Apply an ordinary commuting square to complexes using the canonical composition
comparisons. Source: strict coefficient supplement, representative computations
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
def complexSquare {C₀ C₁ C₂ C₃ : Type (u + 2)}
    [Category.{u + 1} C₀] [Category.{u + 1} C₁]
    [Category.{u + 1} C₂] [Category.{u + 1} C₃]
    [Preadditive C₀] [Preadditive C₁] [Preadditive C₂] [Preadditive C₃]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₃) (H : C₀ ⥤ C₂) (K : C₂ ⥤ C₃)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive] (e : F ⋙ G ≅ H ⋙ K) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ K.mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ K)) (.up ℤ)).symm

/-- The prescribed ordinary balancing on complexes of strict towers. The existing
comparison sends every s tensor x to the same section and includes every transition.
Source: strict coefficient supplement, steps 1--3; Stacks 03EK, 06YY
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
def balanceComplex (T : Scheme.{u}) (d : AdicCoefficientDatum A) :=
  letI := d.noetherian
  reductionTowerComparisonComplex (topology T) A d.ideal

/-- Constant diagrams commute with restriction by identity on their underlying sections
and every transition. Source: strict coefficient supplement, step 3
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
def constantRestrictionComplex (T : Scheme.{u}) (d : AdicCoefficientDatum A) :=
  complexSquare (res (scalar T d)) (constantTower (topology T) (ring T d false))
    (constantTower (topology T) (ring T d true)) (tres (scalar T d)) (Iso.refl _)

/-- Canonical ordinary pullback/reduction reassociation is specified by insertion on
all local sections, before localization. This fixes its direction as R_U u^* to
u^* R_V and retains all strict transitions.
Source: strict coefficient supplement, steps 4--5; Stacks 03EL, 07A4
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
def PullReductionNormalized {U V : Scheme.{u}} (f : U ⟶ V)
    (d : AdicCoefficientDatum A) (b : Bool)
    (e : modulePull f d b ⋙ ConstantCompletion.reductionTower (topology U) A d.ideal b ≅
      ConstantCompletion.reductionTower (topology V) A d.ideal b ⋙ towerPull f d b) : Prop :=
  ∀ (M : Mod (ring V d b)) (n : ℕ),
    pullInsertion (inverseData f) (coefficient f d b) M ≫
        insertion (finiteMap (topology U) A d.ideal b n) ((modulePull f d b).obj M) ≫
        (underlying (ring U d b)).map ((e.hom.app M).app (op n)) =
      (inverse f).map (insertion (finiteMap (topology V) A d.ideal b n) M) ≫
        pullInsertion (inverseData f) (coefficient f d b)
          ((ConstantCompletion.reduction (topology V) A d.ideal b n).obj M)

/-- The derived reassociation is normalized by the ordinary strict comparison and
by the two universal reduction computations. Source: strict coefficient supplement,
step 5; Stacks 07A4, 06YY
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
def PullReductionComputes {U V : Scheme.{u}} (f : U ⟶ V)
    (d : AdicCoefficientDatum A) (b : Bool) (p : PullModel f d b)
    (e : modulePull f d b ⋙ ConstantCompletion.reductionTower (topology U) A d.ideal b ≅
      ConstantCompletion.reductionTower (topology V) A d.ideal b ⋙ towerPull f d b)
    (τ : p.ordinary ⋙ reduction U d b ≅ reduction V d b ⋙ p.diagrams) : Prop :=
  ∀ P : Cx (ring V d b), P.IsAcyclicTensorKFlat →
    (∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) →
    DerivedTowerComparisonFormula p.ordinaryFactors.symm
      (quotientPresentation (topology U) A d.ideal b).comparison
      (complexSquare (modulePull f d b)
        (ConstantCompletion.reductionTower (topology U) A d.ideal b)
        (ConstantCompletion.reductionTower (topology V) A d.ideal b) (towerPull f d b) e)
      p.diagramFactors.symm (quotientPresentation (topology V) A d.ideal b).comparison τ P

/-- Whisker a square with strict diagrams using explicit composition comparisons.
Source: strict coefficient supplement, diagram scalar comparison; Stacks 015F
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
def towerSquare {C₀ C₁ C₂ C₃ : Type (u + 2)}
    [Category.{u + 1} C₀] [Category.{u + 1} C₁]
    [Category.{u + 1} C₂] [Category.{u + 1} C₃]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₃) (H : C₀ ⥤ C₂) (K : C₂ ⥤ C₃)
    (e : F ⋙ G ≅ H ⋙ K) :
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj F ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj G ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj H ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj K :=
  Functor.whiskeringRightObjCompIso F G ≪≫
    (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso e ≪≫
    (Functor.whiskeringRightObjCompIso H K).symm

/-- The canonical pullback equation and its ordinary and derived normalizations.
All the pullbacks are actual module inverse images with the specified coefficient
maps. No arbitrary isomorphism or extra hypothesis on the ambient input is used.
Source: strict coefficient supplement, steps 4--7; Stacks 03EL, 07A4
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
structure PullCompatibility {U V : Scheme.{u}} (f : U ⟶ V) (d : AdicCoefficientDatum A)
    (ρV : reduction V d true ⋙ tdres (scalar V d) ≅
      dres (scalar V d) ⋙ reduction V d false)
    (ρU : reduction U d true ⋙ tdres (scalar U d) ≅
      dres (scalar U d) ⋙ reduction U d false) where
  completed : PullModel f d true
  constant : PullModel f d false
  ordinaryScalar : modulePull f d true ⋙ res (scalar U d) ≅
    res (scalar V d) ⋙ modulePull f d false
  ordinaryScalar_normalized :
    ordinaryScalar.inv = ordinaryPullComparison (inverseData f) A d.ideal
  a : completed.ordinary ⋙ dres (scalar U d) ≅ dres (scalar V d) ⋙ constant.ordinary
  a_computes : ∀ P : Cx (ring V d true), P.IsAcyclicTensorKFlat →
    (∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) →
    DerivedPullComparisonFormula (Q (ring V d true)) (Q (ring V d false))
      (Q (ring U d true)) (Q (ring U d false))
      (res (scalar V d)) (res (scalar U d)) (modulePull f d false) (modulePull f d true)
      (resFactors (scalar V d)) constant.ordinaryFactors.hom ordinaryScalar.inv
      completed.ordinaryFactors.hom (resFactors (scalar U d)) a.inv P
  p : completed.diagrams ⋙ tdres (scalar U d) ≅ tdres (scalar V d) ⋙ constant.diagrams
  p_computes : ∀ P : CochainComplex (ℕᵒᵖ ⥤ Mod (ring V d true)) ℤ,
    DerivedPullComparisonFormula (TQ (ring V d true)) (TQ (ring V d false))
      (TQ (ring U d true)) (TQ (ring U d false))
      (tres (scalar V d)) (tres (scalar U d)) (towerPull f d false) (towerPull f d true)
      (tresFactors (scalar V d)) constant.diagramFactors.hom
      (towerSquare (res (scalar V d)) (modulePull f d false)
        (modulePull f d true) (res (scalar U d)) ordinaryScalar.symm).hom
      completed.diagramFactors.hom (tresFactors (scalar U d)) p.inv P
  ordinaryCompleted :
    modulePull f d true ⋙ ConstantCompletion.reductionTower (topology U) A d.ideal true ≅
      ConstantCompletion.reductionTower (topology V) A d.ideal true ⋙ towerPull f d true
  ordinaryCompleted_normalized : PullReductionNormalized f d true ordinaryCompleted
  ordinaryConstant :
    modulePull f d false ⋙ ConstantCompletion.reductionTower (topology U) A d.ideal false ≅
      ConstantCompletion.reductionTower (topology V) A d.ideal false ⋙ towerPull f d false
  ordinaryConstant_normalized : PullReductionNormalized f d false ordinaryConstant
  τ : completed.ordinary ⋙ reduction U d true ≅ reduction V d true ⋙ completed.diagrams
  τ_computes : PullReductionComputes f d true completed ordinaryCompleted τ
  constantReassociation :
    constant.ordinary ⋙ reduction U d false ≅ reduction V d false ⋙ constant.diagrams
  constantReassociation_computes :
    PullReductionComputes f d false constant ordinaryConstant constantReassociation
  equation : ∀ L : D (ring V d true),
    (tdres (scalar U d)).map (τ.hom.app L) ≫
        p.hom.app ((reduction V d true).obj L) ≫
        constant.diagrams.map (ρV.hom.app L) =
      ρU.hom.app (completed.ordinary.obj L) ≫
        (reduction U d false).map (a.hom.app L) ≫
        constantReassociation.hom.app ((dres (scalar V d)).obj L)

/-- The representative normalization of strict scalar balancing.
Source: strict coefficient supplement, steps 2--3; Stacks 06YY
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
def BalancingComputes (T : Scheme.{u}) (d : AdicCoefficientDatum A)
    (ρ : reduction T d true ⋙ tdres (scalar T d) ≅
      dres (scalar T d) ⋙ reduction T d false) : Prop :=
  ∀ P : Cx (ring T d true), P.IsAcyclicTensorKFlat →
    (∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) →
    DerivedTowerComparisonFormula (resFactors (scalar T d))
      (quotientPresentation (topology T) A d.ideal false).comparison (balanceComplex T d)
      (tresFactors (scalar T d)) (quotientPresentation (topology T) A d.ideal true).comparison
      ρ.symm P

/-- The strict quotient augmentation is the localization of insertion of the unit.
Source: strict coefficient supplement, step 3; Stacks 03EK
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
def AugmentationComputes (T : Scheme.{u}) (d : AdicCoefficientDatum A) (b : Bool)
    (η : delta T d b ⟶ reduction T d b) : Prop :=
  ∀ P : Cx (ring T d b), P.IsAcyclicTensorKFlat →
    (∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) →
    η.app ((Q (ring T d b)).obj P) ≫
        (quotientPresentation (topology T) A d.ideal b).comparison.app P =
      (deltaFactors T d b).hom.app P ≫ (TQ (ring T d b)).map
        ((NatTrans.mapHomologicalComplex
          (reductionUnit (topology T) A d.ideal b) (.up ℤ)).app P)

/-- Restriction of a constant tower is the same constant tower on every complex.
Source: strict coefficient supplement, step 3; Stacks 015F
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
def DeltaRestrictionComputes (T : Scheme.{u}) (d : AdicCoefficientDatum A)
    (δ : delta T d true ⋙ tdres (scalar T d) ≅ dres (scalar T d) ⋙ delta T d false) :
    Prop :=
  ∀ P : Cx (ring T d true),
    DerivedTowerComparisonFormula (resFactors (scalar T d)) (deltaFactors T d false).hom
      (constantRestrictionComplex T d) (tresFactors (scalar T d))
      (deltaFactors T d true).hom δ.symm P

/-- The full natural strict balancing, with the specified representative map, strict
quotient augmentation and pullback square on every ambient object.
Source: strict coefficient supplement, steps 1--7; Stacks 03EK, 03EL, 06YY
(blueprint: lem-weil-pbc-strict-quotient-scalar-balancing). -/
structure Balancing (d : AdicCoefficientDatum A) where
  ρ : ∀ T : Scheme.{u}, reduction T d true ⋙ tdres (scalar T d) ≅
    dres (scalar T d) ⋙ reduction T d false
  ρ_computes : ∀ T : Scheme.{u}, BalancingComputes T d (ρ T)
  augmentation : ∀ (T : Scheme.{u}) (b : Bool), delta T d b ⟶ reduction T d b
  augmentation_computes : ∀ (T : Scheme.{u}) (b : Bool),
    AugmentationComputes T d b (augmentation T b)
  deltaRestriction : ∀ T : Scheme.{u}, delta T d true ⋙ tdres (scalar T d) ≅
    dres (scalar T d) ⋙ delta T d false
  deltaRestriction_computes : ∀ T : Scheme.{u},
    DeltaRestrictionComputes T d (deltaRestriction T)
  augmentation_equation : ∀ (T : Scheme.{u}) (L : D (ring T d true)),
    (tdres (scalar T d)).map ((augmentation T true).app L) ≫ (ρ T).hom.app L =
      (deltaRestriction T).hom.app L ≫
        (augmentation T false).app ((dres (scalar T d)).obj L)
  pullback : ∀ {U V : Scheme.{u}} (f : U ⟶ V), Nonempty (PullCompatibility f d (ρ V) (ρ U))
```

## New

The same declarations now belong to
`lean/Sheaf/Paper/StrictQuotientScalarBalancingData.lean`, with the following verbatim
bodies (the blueprint tag points to the new data node):

```lean
/-- The published small pro-etale topology, equivalent to the original site.
Source: size convention and Stacks 09A5
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
abbrev topology (T : Scheme.{u}) := proEtaleModelTopology T

/-- Constant (false) or completed (true) coefficients, using the existing actual limit.
Source: strict coefficient supplement, coefficient notation; Stacks 099L
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
abbrev ring (T : Scheme.{u}) (d : AdicCoefficientDatum A) (b : Bool) :=
  coefficients (topology T) A d.ideal b

/-- The canonical scalar map, given by the existing quotient cone.
Source: strict coefficient supplement; Stacks 093M
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
abbrev scalar (T : Scheme.{u}) (d : AdicCoefficientDatum A) :=
  coefficientMap (topology T) A d.ideal

/-- The existing actual derived strict reduction functor.
Source: strict coefficient supplement, R^a and R^0; Stacks 06YY
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
abbrev reduction (T : Scheme.{u}) (d : AdicCoefficientDatum A) (b : Bool) :=
  (quotientPresentation (topology T) A d.ideal b).tower

/-- Exact constant diagrams, descended to the standard derived localizations.
Source: strict coefficient supplement, Delta; Stacks 015F
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
def delta (T : Scheme.{u}) (d : AdicCoefficientDatum A) (b : Bool) :
    D (ring T d b) ⥤ TD (ring T d b) :=
  letI := HasDerivedCategory.standard (Mod (ring T d b))
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (ring T d b))
  (constantTower (topology T) (ring T d b)).mapDerivedCategory

/-- Its exact localization comparison, retaining the constant transition maps.
Source: strict coefficient supplement, Delta; Stacks 015F
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
def deltaFactors (T : Scheme.{u}) (d : AdicCoefficientDatum A) (b : Bool) :
    Q (ring T d b) ⋙ delta T d b ≅
      (constantTower (topology T) (ring T d b)).mapHomologicalComplex (.up ℤ) ⋙
        TQ (ring T d b) :=
  letI := HasDerivedCategory.standard (Mod (ring T d b))
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (ring T d b))
  (constantTower (topology T) (ring T d b)).mapDerivedCategoryFactors

/-- The actual geometric inverse image on the transported sites.
Source: pro-etale inverse image and Stacks 00VC
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
abbrev inverse {U V : Scheme.{u}} (f : U ⟶ V) :=
  (proEtaleModelBaseChange f).sheafPullback (Type (u + 1)) (topology V) (topology U)

/-- Equivalence transport gives the base change its finite-limit structure.
Source: Stacks 09A5 (blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
instance modelBaseChangeLimits {U V : Scheme.{u}} (f : U ⟶ V) :
    PreservesFiniteLimits (proEtaleModelBaseChange f) :=
  letI : (AsSmall.down : proEtaleSiteModel V ⥤ V.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := V.ProEt)).inverse.IsEquivalence
  letI : (AsSmall.up : U.ProEt ⥤ proEtaleSiteModel U).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := U.ProEt)).functor.IsEquivalence
  inferInstanceAs (PreservesFiniteLimits
    ((AsSmall.down : proEtaleSiteModel V ⥤ V.ProEt) ⋙ proEtaleBaseChange f ⋙ AsSmall.up))

/-- Flatness of the site functor is inherited from finite-limit preservation.
Source: Stacks 00X6 (blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
instance modelBaseChangeFlat {U V : Scheme.{u}} (f : U ⟶ V) :
    RepresentablyFlat (proEtaleModelBaseChange f) := flat_of_preservesFiniteLimits _

/-- Left exactness of the sheaf inverse image on the published small models.
Source: Stacks 00X6 (blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
instance inverseLimits {U V : Scheme.{u}} (f : U ⟶ V) :
    PreservesFiniteLimits (inverse f) :=
  Functor.sheafPullbackConstruction.preservesFiniteLimits
    (proEtaleModelBaseChange f) (Type (u + 1)) (topology V) (topology U)

/-- Its specified algebraic lift, constructed from the geometric adjunction.
Source: constant-completion-equivalence, algebraic inverse-image construction
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
def inverseData {U V : Scheme.{u}} (f : U ⟶ V) : InverseImageData (inverse f) :=
  Classical.choice (inverseImageData_exists (inverse f)
    ((proEtaleModelBaseChange f).sheafPushforwardContinuous (Type (u + 1))
      (topology V) (topology U))
    ((proEtaleModelBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
      (topology V) (topology U)))

/-- The projection-defined completed coefficient map or constant coefficient map.
Source: strict coefficient supplement; finite projections define the completed map
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
def coefficient {U V : Scheme.{u}} (f : U ⟶ V) (d : AdicCoefficientDatum A)
    (b : Bool) : (inverseData f).rings.obj (ring V d b) ⟶ ring U d b :=
  match b with
  | false => constantMap (inverseData f) A
  | true => completedMap (inverseData f) A d.ideal

/-- The actual ordinary module pullback along the specified coefficient map.
Source: strict coefficient supplement, ordinary ringed operations; Stacks 03D2
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
abbrev modulePull {U V : Scheme.{u}} (f : U ⟶ V) (d : AdicCoefficientDatum A)
    (b : Bool) := pull (inverseData f) (coefficient f d b)

/-- Termwise application to strict diagrams, before localization.
Source: strict coefficient supplement, strict diagram operations
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
abbrev towerPull {U V : Scheme.{u}} (f : U ⟶ V) (d : AdicCoefficientDatum A)
    (b : Bool) : (ℕᵒᵖ ⥤ Mod (ring V d b)) ⥤ (ℕᵒᵖ ⥤ Mod (ring U d b)) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (modulePull f d b)

/-- The normalized universal derived operations; computation is on every complex
because inverse image along the coefficient isomorphisms is exact.
Source: strict coefficient supplement, L and script L; Stacks 015F, 06YY
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
structure PullModel {U V : Scheme.{u}} (f : U ⟶ V) (d : AdicCoefficientDatum A)
    (b : Bool) where
  ordinary : D (ring V d b) ⥤ D (ring U d b)
  diagrams : TD (ring V d b) ⥤ TD (ring U d b)
  ordinaryFactors : Q (ring V d b) ⋙ ordinary ≅
    (modulePull f d b).mapHomologicalComplex (.up ℤ) ⋙ Q (ring U d b)
  diagramFactors : TQ (ring V d b) ⋙ diagrams ≅
    (towerPull f d b).mapHomologicalComplex (.up ℤ) ⋙ TQ (ring U d b)
  ordinaryUniversal : ordinary.IsLeftDerivedFunctor ordinaryFactors.hom
    (HomologicalComplex.quasiIso (Mod (ring V d b)) (.up ℤ))
  diagramUniversal : diagrams.IsLeftDerivedFunctor diagramFactors.hom
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Mod (ring V d b)) (.up ℤ))


/-- Apply an ordinary commuting square to complexes using the canonical composition
comparisons. Source: strict coefficient supplement, representative computations
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
def complexSquare {C₀ C₁ C₂ C₃ : Type (u + 2)}
    [Category.{u + 1} C₀] [Category.{u + 1} C₁]
    [Category.{u + 1} C₂] [Category.{u + 1} C₃]
    [Preadditive C₀] [Preadditive C₁] [Preadditive C₂] [Preadditive C₃]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₃) (H : C₀ ⥤ C₂) (K : C₂ ⥤ C₃)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive] (e : F ⋙ G ≅ H ⋙ K) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ K.mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ K)) (.up ℤ)).symm

/-- The prescribed ordinary balancing on complexes of strict towers. The existing
comparison sends every s tensor x to the same section and includes every transition.
Source: strict coefficient supplement, steps 1--3; Stacks 03EK, 06YY
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
def balanceComplex (T : Scheme.{u}) (d : AdicCoefficientDatum A) :=
  letI := d.noetherian
  reductionTowerComparisonComplex (topology T) A d.ideal

/-- Constant diagrams commute with restriction by identity on their underlying sections
and every transition. Source: strict coefficient supplement, step 3
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
def constantRestrictionComplex (T : Scheme.{u}) (d : AdicCoefficientDatum A) :=
  complexSquare (res (scalar T d)) (constantTower (topology T) (ring T d false))
    (constantTower (topology T) (ring T d true)) (tres (scalar T d)) (Iso.refl _)

/-- Canonical ordinary pullback/reduction reassociation is specified by insertion on
all local sections, before localization. This fixes its direction as R_U u^* to
u^* R_V and retains all strict transitions.
Source: strict coefficient supplement, steps 4--5; Stacks 03EL, 07A4
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
def PullReductionNormalized {U V : Scheme.{u}} (f : U ⟶ V)
    (d : AdicCoefficientDatum A) (b : Bool)
    (e : modulePull f d b ⋙ ConstantCompletion.reductionTower (topology U) A d.ideal b ≅
      ConstantCompletion.reductionTower (topology V) A d.ideal b ⋙ towerPull f d b) : Prop :=
  ∀ (M : Mod (ring V d b)) (n : ℕ),
    pullInsertion (inverseData f) (coefficient f d b) M ≫
        insertion (finiteMap (topology U) A d.ideal b n) ((modulePull f d b).obj M) ≫
        (underlying (ring U d b)).map ((e.hom.app M).app (op n)) =
      (inverse f).map (insertion (finiteMap (topology V) A d.ideal b n) M) ≫
        pullInsertion (inverseData f) (coefficient f d b)
          ((ConstantCompletion.reduction (topology V) A d.ideal b n).obj M)

/-- The derived reassociation is normalized by the ordinary strict comparison and
by the two universal reduction computations. Source: strict coefficient supplement,
step 5; Stacks 07A4, 06YY
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
def PullReductionComputes {U V : Scheme.{u}} (f : U ⟶ V)
    (d : AdicCoefficientDatum A) (b : Bool) (p : PullModel f d b)
    (e : modulePull f d b ⋙ ConstantCompletion.reductionTower (topology U) A d.ideal b ≅
      ConstantCompletion.reductionTower (topology V) A d.ideal b ⋙ towerPull f d b)
    (τ : p.ordinary ⋙ reduction U d b ≅ reduction V d b ⋙ p.diagrams) : Prop :=
  ∀ P : Cx (ring V d b), P.IsAcyclicTensorKFlat →
    (∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) →
    DerivedTowerComparisonFormula p.ordinaryFactors.symm
      (quotientPresentation (topology U) A d.ideal b).comparison
      (complexSquare (modulePull f d b)
        (ConstantCompletion.reductionTower (topology U) A d.ideal b)
        (ConstantCompletion.reductionTower (topology V) A d.ideal b) (towerPull f d b) e)
      p.diagramFactors.symm (quotientPresentation (topology V) A d.ideal b).comparison τ P

/-- Whisker a square with strict diagrams using explicit composition comparisons.
Source: strict coefficient supplement, diagram scalar comparison; Stacks 015F
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
def towerSquare {C₀ C₁ C₂ C₃ : Type (u + 2)}
    [Category.{u + 1} C₀] [Category.{u + 1} C₁]
    [Category.{u + 1} C₂] [Category.{u + 1} C₃]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₃) (H : C₀ ⥤ C₂) (K : C₂ ⥤ C₃)
    (e : F ⋙ G ≅ H ⋙ K) :
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj F ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj G ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj H ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj K :=
  Functor.whiskeringRightObjCompIso F G ≪≫
    (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso e ≪≫
    (Functor.whiskeringRightObjCompIso H K).symm

/-- The canonical pullback equation and its ordinary and derived normalizations.
All the pullbacks are actual module inverse images with the specified coefficient
maps. No arbitrary isomorphism or extra hypothesis on the ambient input is used.
Source: strict coefficient supplement, steps 4--7; Stacks 03EL, 07A4
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
structure PullCompatibility {U V : Scheme.{u}} (f : U ⟶ V) (d : AdicCoefficientDatum A)
    (ρV : reduction V d true ⋙ tdres (scalar V d) ≅
      dres (scalar V d) ⋙ reduction V d false)
    (ρU : reduction U d true ⋙ tdres (scalar U d) ≅
      dres (scalar U d) ⋙ reduction U d false) where
  completed : PullModel f d true
  constant : PullModel f d false
  ordinaryScalar : modulePull f d true ⋙ res (scalar U d) ≅
    res (scalar V d) ⋙ modulePull f d false
  ordinaryScalar_normalized :
    ordinaryScalar.inv = ordinaryPullComparison (inverseData f) A d.ideal
  a : completed.ordinary ⋙ dres (scalar U d) ≅ dres (scalar V d) ⋙ constant.ordinary
  a_computes : ∀ P : Cx (ring V d true), P.IsAcyclicTensorKFlat →
    (∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) →
    DerivedPullComparisonFormula (Q (ring V d true)) (Q (ring V d false))
      (Q (ring U d true)) (Q (ring U d false))
      (res (scalar V d)) (res (scalar U d)) (modulePull f d false) (modulePull f d true)
      (resFactors (scalar V d)) constant.ordinaryFactors.hom ordinaryScalar.inv
      completed.ordinaryFactors.hom (resFactors (scalar U d)) a.inv P
  p : completed.diagrams ⋙ tdres (scalar U d) ≅ tdres (scalar V d) ⋙ constant.diagrams
  p_computes : ∀ P : CochainComplex (ℕᵒᵖ ⥤ Mod (ring V d true)) ℤ,
    DerivedPullComparisonFormula (TQ (ring V d true)) (TQ (ring V d false))
      (TQ (ring U d true)) (TQ (ring U d false))
      (tres (scalar V d)) (tres (scalar U d)) (towerPull f d false) (towerPull f d true)
      (tresFactors (scalar V d)) constant.diagramFactors.hom
      (towerSquare (res (scalar V d)) (modulePull f d false)
        (modulePull f d true) (res (scalar U d)) ordinaryScalar.symm).hom
      completed.diagramFactors.hom (tresFactors (scalar U d)) p.inv P
  ordinaryCompleted :
    modulePull f d true ⋙ ConstantCompletion.reductionTower (topology U) A d.ideal true ≅
      ConstantCompletion.reductionTower (topology V) A d.ideal true ⋙ towerPull f d true
  ordinaryCompleted_normalized : PullReductionNormalized f d true ordinaryCompleted
  ordinaryConstant :
    modulePull f d false ⋙ ConstantCompletion.reductionTower (topology U) A d.ideal false ≅
      ConstantCompletion.reductionTower (topology V) A d.ideal false ⋙ towerPull f d false
  ordinaryConstant_normalized : PullReductionNormalized f d false ordinaryConstant
  τ : completed.ordinary ⋙ reduction U d true ≅ reduction V d true ⋙ completed.diagrams
  τ_computes : PullReductionComputes f d true completed ordinaryCompleted τ
  constantReassociation :
    constant.ordinary ⋙ reduction U d false ≅ reduction V d false ⋙ constant.diagrams
  constantReassociation_computes :
    PullReductionComputes f d false constant ordinaryConstant constantReassociation
  equation : ∀ L : D (ring V d true),
    (tdres (scalar U d)).map (τ.hom.app L) ≫
        p.hom.app ((reduction V d true).obj L) ≫
        constant.diagrams.map (ρV.hom.app L) =
      ρU.hom.app (completed.ordinary.obj L) ≫
        (reduction U d false).map (a.hom.app L) ≫
        constantReassociation.hom.app ((dres (scalar V d)).obj L)

/-- The representative normalization of strict scalar balancing.
Source: strict coefficient supplement, steps 2--3; Stacks 06YY
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
def BalancingComputes (T : Scheme.{u}) (d : AdicCoefficientDatum A)
    (ρ : reduction T d true ⋙ tdres (scalar T d) ≅
      dres (scalar T d) ⋙ reduction T d false) : Prop :=
  ∀ P : Cx (ring T d true), P.IsAcyclicTensorKFlat →
    (∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) →
    DerivedTowerComparisonFormula (resFactors (scalar T d))
      (quotientPresentation (topology T) A d.ideal false).comparison (balanceComplex T d)
      (tresFactors (scalar T d)) (quotientPresentation (topology T) A d.ideal true).comparison
      ρ.symm P

/-- The strict quotient augmentation is the localization of insertion of the unit.
Source: strict coefficient supplement, step 3; Stacks 03EK
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
def AugmentationComputes (T : Scheme.{u}) (d : AdicCoefficientDatum A) (b : Bool)
    (η : delta T d b ⟶ reduction T d b) : Prop :=
  ∀ P : Cx (ring T d b), P.IsAcyclicTensorKFlat →
    (∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) →
    η.app ((Q (ring T d b)).obj P) ≫
        (quotientPresentation (topology T) A d.ideal b).comparison.app P =
      (deltaFactors T d b).hom.app P ≫ (TQ (ring T d b)).map
        ((NatTrans.mapHomologicalComplex
          (reductionUnit (topology T) A d.ideal b) (.up ℤ)).app P)

/-- Restriction of a constant tower is the same constant tower on every complex.
Source: strict coefficient supplement, step 3; Stacks 015F
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
def DeltaRestrictionComputes (T : Scheme.{u}) (d : AdicCoefficientDatum A)
    (δ : delta T d true ⋙ tdres (scalar T d) ≅ dres (scalar T d) ⋙ delta T d false) :
    Prop :=
  ∀ P : Cx (ring T d true),
    DerivedTowerComparisonFormula (resFactors (scalar T d)) (deltaFactors T d false).hom
      (constantRestrictionComplex T d) (tresFactors (scalar T d))
      (deltaFactors T d true).hom δ.symm P

/-- The full natural strict balancing, with the specified representative map, strict
quotient augmentation and pullback square on every ambient object.
Source: strict coefficient supplement, steps 1--7; Stacks 03EK, 03EL, 06YY
(blueprint: def-weil-pbc-strict-quotient-scalar-balancing-data). -/
structure Balancing (d : AdicCoefficientDatum A) where
  ρ : ∀ T : Scheme.{u}, reduction T d true ⋙ tdres (scalar T d) ≅
    dres (scalar T d) ⋙ reduction T d false
  ρ_computes : ∀ T : Scheme.{u}, BalancingComputes T d (ρ T)
  augmentation : ∀ (T : Scheme.{u}) (b : Bool), delta T d b ⟶ reduction T d b
  augmentation_computes : ∀ (T : Scheme.{u}) (b : Bool),
    AugmentationComputes T d b (augmentation T b)
  deltaRestriction : ∀ T : Scheme.{u}, delta T d true ⋙ tdres (scalar T d) ≅
    dres (scalar T d) ⋙ delta T d false
  deltaRestriction_computes : ∀ T : Scheme.{u},
    DeltaRestrictionComputes T d (deltaRestriction T)
  augmentation_equation : ∀ (T : Scheme.{u}) (L : D (ring T d true)),
    (tdres (scalar T d)).map ((augmentation T true).app L) ≫ (ρ T).hom.app L =
      (deltaRestriction T).hom.app L ≫
        (augmentation T false).app ((dres (scalar T d)).obj L)
  pullback : ∀ {U V : Scheme.{u}} (f : U ⟶ V), Nonempty (PullCompatibility f d (ρ V) (ρ U))
```

The original module publicly imports `Sheaf.Paper.StrictQuotientScalarBalancingData`.
Its theorem `strictQuotientScalarBalancing` keeps its exact original type.

## Users

`tools/downstream.py Sheaf.Paper.StrictQuotientScalarBalancing --uses
StrictScalarBalancing` now reports two downstream modules:
`Sheaf.Paper.QuotientDiagramScalarProjection` and
`Sheaf.Paper.CompletedScalarUnitAdjunction` (both landed during this session).
The former uses `ring`, `scalar`, `reduction`, `PullModel`, `PullCompatibility` and `Balancing`
from the root module. The public data import supplies the identical declarations;
all signatures, defining terms, names and instances are unchanged. Every original
public import is also retained verbatim in the root. No consumer edit is necessary.
Both consumers are unclaimed in the current local queue. The latter uses topology,
ring, scalar, reduction and Balancing to define completion and normalized scalar
adjunction comparisons. These are exactly the same public declarations through the
new data import. Both consumers' statements have the same meaning after extraction.
The independent reader can compile their original sources against the delivered
data module and root; no adaptation is proposed.

The unfinished DAG parent is retained and continues to refer to the original theorem
node. This is not a withdrawal. The new pullback module imports the data module.
The unused plain import of `Sheaf.Paper.FlatCommonQuotientReductionTower` is dropped from
the root (reviewer correction); the integral-models unit realizes that node through other
importers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.StrictQuotientScalarBalancing | Q6 | Publicly imports unchanged definitions |
| Sheaf.Paper.StrictQuotientPullbackCompatibility | Q6 (new) | Uses the shared data |
| Sheaf.Paper.QuotientDiagramScalarProjection | unclaimed | Identical imported API; no edit |
| Sheaf.Paper.CompletedScalarUnitAdjunction | unclaimed | Identical imported API; no edit |

## Status

landed 20261021T154751-L-3171030 2026-10-21 (merge of deliver/Q6/Sheaf.Paper.StrictQuotientScalarBalancing)
