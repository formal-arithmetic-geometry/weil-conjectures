# WeilConjectures.ZlOpenTExact.AllStages

## Reason

The original module times out at 60 seconds while elaborating AllStages. Respecting
local irreducibility reduces the elaboration cost but exposes unresolved family
instances through named stage wrappers. Supply the existing category structures,
pointwise additive shifts, and the already existentially selected CommShift structures
explicitly. Cache the canonical ordinary derived-functor shift as the proved instance
`WeilConjectures.ZlOpenTExact.ordinaryOpenShift`; it introduces no choice or assumption.

The earlier transparency settings are also restored to the default before
OpenAdjunctionNormalization. No declaration is split to evade the time limit.

The named stage `GeneralAlgebraicallyClosedCoefficients.Stage` has precisely the
existing rational category, shift and pretriangulated structures. The proved
`stageStandardTStructure` definition reexports the same rational standard t-structure
at that named stage, avoiding repeated conversion between the two presentations.
AllStages now uses the stage presentation consistently, with the canonical localization
shift supplied explicitly. No existential witness, equation or conclusion is removed.

## Old

```lean
def AllStages
    (S : SfCompactSupportCoefficientAction l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) Ω
      (Compactification.ofIsOpenImmersion j)) : Prop :=
  ∃ (invertibleU : ∀ x : U, Invertible (l : U.residueField x)),
  letI := invertibleU;
  ∃ (invertibleX : ∀ x : X, Invertible (l : X.residueField x)),
  letI := invertibleX;
  ∃ (tU : ∀ E : Index l Ω,
    Triangulated.TStructure (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U)),
  ∃ (tX : ∀ E : Index l Ω,
    Triangulated.TStructure (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X)),
  (∀ E : Index l Ω, (tU E).bounded = ⊤) ∧
  (∀ E : Index l Ω, (tX E).bounded = ⊤) ∧
  (∀ (E : Index l Ω) (n : ℤ),
    (tU E).le n = sfIntegralStandardClass l (Coefficient.{u} l Ω E) U true n ∧
    (tU E).ge n = sfIntegralStandardClass l (Coefficient.{u} l Ω E) U false n) ∧
  (∀ (E : Index l Ω) (n : ℤ),
    (tX E).le n = sfIntegralStandardClass l (Coefficient.{u} l Ω E) X true n ∧
    (tX E).ge n = sfIntegralStandardClass l (Coefficient.{u} l Ω E) X false n) ∧
  ∃ (integralShift : ∀ E : Index l Ω, (integral D l hl j (Coefficient.{u} l Ω E)).CommShift ℤ),
  letI := integralShift;
  ∃ (rationalShift : ∀ E : Index l Ω, (S.system.Φ E).CommShift ℤ),
  letI := rationalShift;
  ∃ (commonShift : S.system.functor.CommShift ℤ),
  letI := commonShift;
  ∃ (scalarShiftU : ∀ (E L : Index l Ω) (h : E ≤ L),
    ((stageSystem l Ω U).T h).CommShift ℤ),
  letI := scalarShiftU;
  ∃ (scalarShiftX : ∀ (E L : Index l Ω) (h : E ≤ L),
    ((stageSystem l Ω X).T h).CommShift ℤ),
  letI := scalarShiftX;
  ∃ (inclusionShiftU : ∀ E : Index l Ω, ((stageSystem l Ω U).ι E).CommShift ℤ),
  letI := inclusionShiftU;
  ∃ (inclusionShiftX : ∀ E : Index l Ω, ((stageSystem l Ω X).ι E).CommShift ℤ),
  letI := inclusionShiftX;
  (∀ (E L : Index l Ω) (h : E ≤ L),
    scalarShiftU E L h = scalarShift l Ω U E L h ∧
    scalarShiftX E L h = scalarShift l Ω X E L h) ∧
  (∀ E : Index l Ω,
    inclusionShiftU E = stageInclusionShift l Ω U E ∧
    inclusionShiftX E = stageInclusionShift l Ω X E) ∧
  ∃ (integralComparisons : ∀ E : Index l Ω,
    Comparisons (tU E) (tX E) (integral D l hl j (Coefficient.{u} l Ω E))),
  ∃ (rationalComparisons : ∀ E : Index l Ω,
    Comparisons (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) U D hl)
      (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) X D hl) (S.system.Φ E)),
  ∃ (commonComparisons :
    Comparisons (sfCommonStageStandardTStructure l U Ω D hl)
      (sfCommonStageStandardTStructure l X Ω D hl) S.system.functor),
  ∃ (ambientU : ∀ E : Index l Ω,
    Comparisons (tU E) DerivedCategory.TStructure.t (sfIntegralConstructible l
      (Coefficient.{u} l Ω E) U).ι),
  ∃ (ambientX : ∀ E : Index l Ω,
    Comparisons (tX E) DerivedCategory.TStructure.t (sfIntegralConstructible l
      (Coefficient.{u} l Ω E) X).ι),
  ∃ (ordinary : ∀ E : Index l Ω,
    Comparisons DerivedCategory.TStructure.t DerivedCategory.TStructure.t
      (ordinaryOpen l (Coefficient.{u} l Ω E) j)),
  (∀ E : Index l Ω,
    SquareCompatible (integralComparisons E) (ordinary E) (ambientU E) (ambientX E)
      (identification D l hl j (Coefficient.{u} l Ω E))) ∧
  (∀ E : Index l Ω,
    PreservesFiniteLimits (PurCompactSupport.openExtension
      (PurCompactSupport.completed.{u} l (Coefficient.{u} l Ω E)) j) ∧
    PreservesFiniteColimits (PurCompactSupport.openExtension
      (PurCompactSupport.completed.{u} l (Coefficient.{u} l Ω E)) j)) ∧
  (∀ (E : Index l Ω) (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U),
    IsSfDerivedComplete l (Coefficient.{u} l Ω E) X
      ((ordinaryOpen l (Coefficient.{u} l Ω E) j).obj K.obj)) ∧
  (∀ (E : Index l Ω)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U),
    sfIntegralConstructible l (Coefficient.{u} l Ω E) X
      ((ordinaryOpen l (Coefficient.{u} l Ω E) j).obj K.obj)) ∧
  (∀ (E : Index l Ω) (b : Bool) (n : ℤ)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U),
    sfIntegralStandardClass l (Coefficient.{u} l Ω E) U b n K →
      sfIntegralStandardClass l (Coefficient.{u} l Ω E) X b n
        ((integral D l hl j (Coefficient.{u} l Ω E)).obj K)) ∧
  (∀ E : Index l Ω, OpenAdjunctionNormalization D l hl j (Coefficient.{u} l Ω E)) ∧
  ∃ (localizationU : ∀ E : Index l Ω,
    Comparisons (tU E) (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) U D hl)
      (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) U)),
  ∃ (localizationX : ∀ E : Index l Ω,
    Comparisons (tX E) (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) X D hl)
      (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X)),
  ∃ (rationalization : ∀ E : Index l Ω,
    sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) U ⋙ S.system.Φ E ≅
      integral D l hl j (Coefficient.{u} l Ω E) ⋙
        sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X),
  (∀ (E : Index l Ω)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U),
    HEq ((rationalization E).hom.app K)
      (𝟙 ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
        ((integral D l hl j (Coefficient.{u} l Ω E)).obj K)))) ∧
  (∀ E : Index l Ω,
    SquareCompatible (localizationU E) (localizationX E)
      (integralComparisons E) (rationalComparisons E) (rationalization E)) ∧
  ∃ (integralScalarU : ∀ (E L : Index l Ω) (h : E ≤ L),
    Comparisons (tU E) (tU L) (integralTransition l Ω U E L h)),
  ∃ (integralScalarX : ∀ (E L : Index l Ω) (h : E ≤ L),
    Comparisons (tX E) (tX L) (integralTransition l Ω X E L h)),
  (∀ (E L : Index l Ω) (h : E ≤ L),
    SquareCompatible (integralComparisons E) (integralComparisons L)
      (integralScalarU E L h) (integralScalarX E L h) (S.integralBeta h)) ∧
  ∃ (scalarModelU : ∀ (E L : Index l Ω) (h : E ≤ L),
    ScalarModel l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) U),
  ∃ (scalarModelX : ∀ (E L : Index l Ω) (h : E ≤ L),
    ScalarModel l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) X),
  (∀ (E L : Index l Ω) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U),
    ((S.integralBeta h).hom.app K).hom ≫
        (identification D l hl j (Coefficient.{u} l Ω L)).hom.app
          ((integralTransition l Ω U E L h).obj K) ≫
        (ordinaryOpen l (Coefficient.{u} l Ω L) j).map
          ((scalarRealization l Ω U E L h (scalarModelU E L h)).hom.app K) =
      (scalarRealization l Ω X E L h (scalarModelX E L h)).hom.app
          ((integral D l hl j (Coefficient.{u} l Ω E)).obj K) ≫
        (pbcDerivedExtend (completedCoefficientMap l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) X)).map
            ((identification D l hl j (Coefficient.{u} l Ω E)).hom.app K) ≫
        (PurCompactSupport.openComparison (PurCompactSupport.completedChange l
          (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h)) j).app K.obj) ∧
  ∃ (scalarU : ∀ (E L : Index l Ω) (h : E ≤ L),
    Comparisons (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) U D hl)
      (sfRationalStandardTStructure l (Coefficient.{u} l Ω L) U D hl)
        ((stageSystem l Ω U).T h)),
  ∃ (scalarX : ∀ (E L : Index l Ω) (h : E ≤ L),
    Comparisons (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) X D hl)
      (sfRationalStandardTStructure l (Coefficient.{u} l Ω L) X D hl)
        ((stageSystem l Ω X).T h)),
  (∀ (E L : Index l Ω) (h : E ≤ L),
    SquareCompatible (rationalComparisons E) (rationalComparisons L)
      (scalarU E L h) (scalarX E L h) (S.system.β h)) ∧
  ∃ (inclusionU : ∀ E : Index l Ω,
    Comparisons (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) U D hl)
      (sfCommonStageStandardTStructure l U Ω D hl) ((stageSystem l Ω U).ι E)),
  ∃ (inclusionX : ∀ E : Index l Ω,
    Comparisons (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) X D hl)
      (sfCommonStageStandardTStructure l X Ω D hl) ((stageSystem l Ω X).ι E)),
  (∀ E : Index l Ω,
    SquareCompatible (inclusionU E) (inclusionX E) (rationalComparisons E)
      commonComparisons (S.system.ιCompFunctorIso E)) ∧
  (∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M),
    CompositeCompatible (scalarU E L h) (scalarU L M k) (scalarU E M (h.trans k))
      ((stageSystem l Ω U).assoc h k) ∧
    CompositeCompatible (scalarX E L h) (scalarX L M k) (scalarX E M (h.trans k))
      ((stageSystem l Ω X).assoc h k)) ∧
  (∀ (E L : Index l Ω) (h : E ≤ L),
    CompositeCompatible (scalarU E L h) (inclusionU L) (inclusionU E)
      ((stageSystem l Ω U).transIso h) ∧
    CompositeCompatible (scalarX E L h) (inclusionX L) (inclusionX E)
      ((stageSystem l Ω X).transIso h)) ∧
  True

```

## New

```lean
/-- The canonical shift comparison of exact ordinary open extension.
Source: Mathlib's exact derived functor construction
(blueprint: lem-zl-open-extension-texact-coefficient-stages). -/
instance ordinaryOpenShift (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] : (ordinaryOpen l E j).CommShift ℤ :=
  inferInstance

attribute [local irreducible] ordinaryOpenShift

/-- The standard rational t-structure on the named coefficient stage.
The named stage carries the same category and shift structures as its rational model.
Source: blueprint Part 2; the standard coefficient stages
(blueprint: lem-zl-open-extension-texact-coefficient-stages). -/
def stageStandardTStructure (T : Scheme.{u})
    [T.Over (Spec (.of D.k))] [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))] (E : Index l Ω) :
    Triangulated.TStructure (GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :=
  sfRationalStandardTStructure l (Coefficient.{u} l Ω E) T D hl

attribute [local irreducible] stageStandardTStructure

def AllStages
    (S : SfCompactSupportCoefficientAction l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) Ω
      (Compactification.ofIsOpenImmersion j)) : Prop :=
  ∃ (invertibleU : ∀ x : U, Invertible (l : U.residueField x)),
  letI := invertibleU;
  ∃ (invertibleX : ∀ x : X, Invertible (l : X.residueField x)),
  letI := invertibleX;
  ∃ (tU : ∀ E : Index l Ω,
    Triangulated.TStructure (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U)),
  ∃ (tX : ∀ E : Index l Ω,
    Triangulated.TStructure (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X)),
  (∀ E : Index l Ω, (tU E).bounded = ⊤) ∧
  (∀ E : Index l Ω, (tX E).bounded = ⊤) ∧
  (∀ (E : Index l Ω) (n : ℤ),
    (tU E).le n = sfIntegralStandardClass l (Coefficient.{u} l Ω E) U true n ∧
    (tU E).ge n = sfIntegralStandardClass l (Coefficient.{u} l Ω E) U false n) ∧
  (∀ (E : Index l Ω) (n : ℤ),
    (tX E).le n = sfIntegralStandardClass l (Coefficient.{u} l Ω E) X true n ∧
    (tX E).ge n = sfIntegralStandardClass l (Coefficient.{u} l Ω E) X false n) ∧
  ∃ (integralShift : ∀ E : Index l Ω, (integral D l hl j (Coefficient.{u} l Ω E)).CommShift ℤ),
  letI := integralShift;
  ∃ (rationalShift : ∀ E : Index l Ω, (S.system.Φ E).CommShift ℤ),
  letI := rationalShift;
  ∃ (commonShift : S.system.functor.CommShift ℤ),
  letI := commonShift;
  ∃ (scalarShiftU : ∀ (E L : Index l Ω) (h : E ≤ L),
    ((stageSystem l Ω U).T h).CommShift ℤ),
  letI := scalarShiftU;
  ∃ (scalarShiftX : ∀ (E L : Index l Ω) (h : E ≤ L),
    ((stageSystem l Ω X).T h).CommShift ℤ),
  letI := scalarShiftX;
  ∃ (inclusionShiftU : ∀ E : Index l Ω, ((stageSystem l Ω U).ι E).CommShift ℤ),
  letI := inclusionShiftU;
  ∃ (inclusionShiftX : ∀ E : Index l Ω, ((stageSystem l Ω X).ι E).CommShift ℤ),
  letI := inclusionShiftX;
  (∀ (E L : Index l Ω) (h : E ≤ L),
    scalarShiftU E L h = scalarShift l Ω U E L h ∧
    scalarShiftX E L h = scalarShift l Ω X E L h) ∧
  (∀ E : Index l Ω,
    inclusionShiftU E = stageInclusionShift l Ω U E ∧
    inclusionShiftX E = stageInclusionShift l Ω X E) ∧
  ∃ (integralComparisons : ∀ E : Index l Ω,
    Comparisons (tU E) (tX E) (integral D l hl j (Coefficient.{u} l Ω E))),
  ∃ (rationalComparisons : ∀ E : Index l Ω,
    @Comparisons
      _ _ _ _ _ (fun _n ↦ inferInstance) _ _ _ _ _ _ (fun _n ↦ inferInstance) _
      (stageStandardTStructure D l hl Ω U E)
      (stageStandardTStructure D l hl Ω X E)
      (S.system.Φ E) (rationalShift E)),
  ∃ (commonComparisons :
    Comparisons (sfCommonStageStandardTStructure l U Ω D hl)
      (sfCommonStageStandardTStructure l X Ω D hl) S.system.functor),
  ∃ (ambientU : ∀ E : Index l Ω,
    @Comparisons
      _ _ _ _ _ (fun _n ↦ inferInstance) _ _ _ _ _ _ (fun _n ↦ inferInstance) _
      (tU E) DerivedCategory.TStructure.t
      (sfIntegralConstructible l (Coefficient.{u} l Ω E) U).ι
      (ObjectProperty.commShiftι _ (A := ℤ))),
  ∃ (ambientX : ∀ E : Index l Ω,
    @Comparisons
      _ _ _ _ _ (fun _n ↦ inferInstance) _ _ _ _ _ _ (fun _n ↦ inferInstance) _
      (tX E) DerivedCategory.TStructure.t
      (sfIntegralConstructible l (Coefficient.{u} l Ω E) X).ι
      (ObjectProperty.commShiftι _ (A := ℤ))),
  ∃ (ordinary : ∀ E : Index l Ω,
    @Comparisons _ _ _ _ _ (fun _n ↦ inferInstance) _
      _ _ _ _ _ (fun _n ↦ inferInstance) _
      DerivedCategory.TStructure.t DerivedCategory.TStructure.t
      (ordinaryOpen l (Coefficient.{u} l Ω E) j)
      (ordinaryOpenShift l j (Coefficient.{u} l Ω E))),
  (∀ E : Index l Ω,
    @SquareCompatible
      (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (DerivedCategory (scalarReductionSource l (Coefficient.{u} l Ω E) U))
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (DerivedCategory (scalarReductionSource l (Coefficient.{u} l Ω E) X))
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      _ _ _ _
      _ (integralShift E)
      (ordinaryOpen l (Coefficient.{u} l Ω E) j) (ordinaryOpenShift l j (Coefficient.{u} l Ω E))
      _ (ObjectProperty.commShiftι _ (A := ℤ))
      _ (ObjectProperty.commShiftι _ (A := ℤ))
      (integralComparisons E) (ordinary E) (ambientU E) (ambientX E)
      (identification D l hl j (Coefficient.{u} l Ω E))) ∧
  (∀ E : Index l Ω,
    PreservesFiniteLimits (PurCompactSupport.openExtension
      (PurCompactSupport.completed.{u} l (Coefficient.{u} l Ω E)) j) ∧
    PreservesFiniteColimits (PurCompactSupport.openExtension
      (PurCompactSupport.completed.{u} l (Coefficient.{u} l Ω E)) j)) ∧
  (∀ (E : Index l Ω) (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U),
    IsSfDerivedComplete l (Coefficient.{u} l Ω E) X
      ((ordinaryOpen l (Coefficient.{u} l Ω E) j).obj K.obj)) ∧
  (∀ (E : Index l Ω)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U),
    sfIntegralConstructible l (Coefficient.{u} l Ω E) X
      ((ordinaryOpen l (Coefficient.{u} l Ω E) j).obj K.obj)) ∧
  (∀ (E : Index l Ω) (b : Bool) (n : ℤ)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U),
    sfIntegralStandardClass l (Coefficient.{u} l Ω E) U b n K →
      sfIntegralStandardClass l (Coefficient.{u} l Ω E) X b n
        ((integral D l hl j (Coefficient.{u} l Ω E)).obj K)) ∧
  (∀ E : Index l Ω, OpenAdjunctionNormalization D l hl j (Coefficient.{u} l Ω E)) ∧
  ∃ (localizationU : ∀ E : Index l Ω,
    @Comparisons
      _ _ _ _ _ (fun _n ↦ inferInstance) _ _ _ _ _ _ (fun _n ↦ inferInstance) _
      (tU E) (stageStandardTStructure D l hl Ω U E)
      (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) U)
      (sfRationalLocalizationCommShift l (Coefficient.{u} l Ω E) U)),
  ∃ (localizationX : ∀ E : Index l Ω,
    @Comparisons
      _ _ _ _ _ (fun _n ↦ inferInstance) _ _ _ _ _ _ (fun _n ↦ inferInstance) _
      (tX E) (stageStandardTStructure D l hl Ω X E)
      (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X)
      (sfRationalLocalizationCommShift l (Coefficient.{u} l Ω E) X)),
  ∃ (rationalization : ∀ E : Index l Ω,
    sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) U ⋙ S.system.Φ E ≅
      integral D l hl j (Coefficient.{u} l Ω E) ⋙
        sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X),
  (∀ (E : Index l Ω)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U),
    HEq ((rationalization E).hom.app K)
      (𝟙 ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
        ((integral D l hl j (Coefficient.{u} l Ω E)).obj K)))) ∧
  (∀ E : Index l Ω,
    @SquareCompatible
      (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω U E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      _ _ _ _
      _ (sfRationalLocalizationCommShift l (Coefficient.{u} l Ω E) U)
      _ (sfRationalLocalizationCommShift l (Coefficient.{u} l Ω E) X)
      _ (integralShift E) _ (rationalShift E)
      (localizationU E) (localizationX E)
      (integralComparisons E) (rationalComparisons E) (rationalization E)) ∧
  ∃ (integralScalarU : ∀ (E L : Index l Ω) (h : E ≤ L),
    Comparisons (tU E) (tU L) (integralTransition l Ω U E L h)),
  ∃ (integralScalarX : ∀ (E L : Index l Ω) (h : E ≤ L),
    Comparisons (tX E) (tX L) (integralTransition l Ω X E L h)),
  (∀ (E L : Index l Ω) (h : E ≤ L),
    SquareCompatible (integralComparisons E) (integralComparisons L)
      (integralScalarU E L h) (integralScalarX E L h) (S.integralBeta h)) ∧
  ∃ (scalarModelU : ∀ (E L : Index l Ω) (h : E ≤ L),
    ScalarModel l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) U),
  ∃ (scalarModelX : ∀ (E L : Index l Ω) (h : E ≤ L),
    ScalarModel l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) X),
  (∀ (E L : Index l Ω) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) U),
    ((S.integralBeta h).hom.app K).hom ≫
        (identification D l hl j (Coefficient.{u} l Ω L)).hom.app
          ((integralTransition l Ω U E L h).obj K) ≫
        (ordinaryOpen l (Coefficient.{u} l Ω L) j).map
          ((scalarRealization l Ω U E L h (scalarModelU E L h)).hom.app K) =
      (scalarRealization l Ω X E L h (scalarModelX E L h)).hom.app
          ((integral D l hl j (Coefficient.{u} l Ω E)).obj K) ≫
        (pbcDerivedExtend (completedCoefficientMap l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) X)).map
            ((identification D l hl j (Coefficient.{u} l Ω E)).hom.app K) ≫
        (PurCompactSupport.openComparison (PurCompactSupport.completedChange l
          (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h)) j).app K.obj) ∧
  ∃ (scalarU : ∀ (E L : Index l Ω) (h : E ≤ L),
    @Comparisons
      _ _ _ _ _ (fun _n ↦ inferInstance) _ _ _ _ _ _ (fun _n ↦ inferInstance) _
      (stageStandardTStructure D l hl Ω U E)
      (stageStandardTStructure D l hl Ω U L)
      ((stageSystem l Ω U).T h) (scalarShiftU E L h)),
  ∃ (scalarX : ∀ (E L : Index l Ω) (h : E ≤ L),
    @Comparisons
      _ _ _ _ _ (fun _n ↦ inferInstance) _ _ _ _ _ _ (fun _n ↦ inferInstance) _
      (stageStandardTStructure D l hl Ω X E)
      (stageStandardTStructure D l hl Ω X L)
      ((stageSystem l Ω X).T h) (scalarShiftX E L h)),
  (∀ (E L : Index l Ω) (h : E ≤ L),
    @SquareCompatible
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω U E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω U L)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      _ _ _ _
      _ (rationalShift E) _ (rationalShift L) _ (scalarShiftU E L h) _ (scalarShiftX E L h)
      (rationalComparisons E) (rationalComparisons L)
      (scalarU E L h) (scalarX E L h) (S.system.β h)) ∧
  ∃ (inclusionU : ∀ E : Index l Ω,
    @Comparisons
      _ _ _ _ _ (fun _n ↦ inferInstance) _ _ _ _ _ _ (fun _n ↦ inferInstance) _
      (stageStandardTStructure D l hl Ω U E)
      (sfCommonStageStandardTStructure l U Ω D hl)
      ((stageSystem l Ω U).ι E) (inclusionShiftU E)),
  ∃ (inclusionX : ∀ E : Index l Ω,
    @Comparisons
      _ _ _ _ _ (fun _n ↦ inferInstance) _ _ _ _ _ _ (fun _n ↦ inferInstance) _
      (stageStandardTStructure D l hl Ω X E)
      (sfCommonStageStandardTStructure l X Ω D hl)
      ((stageSystem l Ω X).ι E) (inclusionShiftX E)),
  (∀ E : Index l Ω,
    @SquareCompatible
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω U E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (generalAlgebraicallyClosedConstructibleCategory l Ω U)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (generalAlgebraicallyClosedConstructibleCategory l Ω X)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      _ _ _ _
      _ (inclusionShiftU E) _ (inclusionShiftX E) _ (rationalShift E) _ _
      (inclusionU E) (inclusionX E) (rationalComparisons E)
      commonComparisons (S.system.ιCompFunctorIso E)) ∧
  (∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M),
    @CompositeCompatible
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω U E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω U L)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω U M)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      _ _ _
      _ (scalarShiftU E L h) _ (scalarShiftU L M k) _ (scalarShiftU E M (h.trans k))
      (scalarU E L h) (scalarU L M k) (scalarU E M (h.trans k))
      ((stageSystem l Ω U).assoc h k) ∧
    @CompositeCompatible
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X M)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      _ _ _
      _ (scalarShiftX E L h) _ (scalarShiftX L M k) _ (scalarShiftX E M (h.trans k))
      (scalarX E L h) (scalarX L M k) (scalarX E M (h.trans k))
      ((stageSystem l Ω X).assoc h k)) ∧
  (∀ (E L : Index l Ω) (h : E ≤ L),
    @CompositeCompatible
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω U E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω U L)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (generalAlgebraicallyClosedConstructibleCategory l Ω U)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      _ _ _
      _ (scalarShiftU E L h) _ (inclusionShiftU L) _ (inclusionShiftU E)
      (scalarU E L h) (inclusionU L) (inclusionU E)
      ((stageSystem l Ω U).transIso h) ∧
    @CompositeCompatible
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      (generalAlgebraicallyClosedConstructibleCategory l Ω X)
        inferInstance inferInstance inferInstance inferInstance
        (fun _n ↦ inferInstance) inferInstance
      _ _ _
      _ (scalarShiftX E L h) _ (inclusionShiftX L) _ (inclusionShiftX E)
      (scalarX E L h) (inclusionX L) (inclusionX E)
      ((stageSystem l Ω X).transIso h)) ∧
  True
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ZlOpenExtensionTExact | W4 | Sole consumer of AllStages; explicit canonical instance arguments preserve the proposition and all conclusions. |

`tools/downstream.py Sheaf.Paper.ZlOpenExtensionTExact --uses
WeilConjectures.ZlOpenTExact.AllStages` reports zero external downstream modules and
only this item as a declaration consumer. No target uses this definition in its
statement. The original main theorem signature and all five public imports stay
verbatim. No forced adaptation of another group's module is needed.

## Status

landed 20261025T164659-L-1051085 2026-10-25 (merge of deliver/W4/Sheaf.Paper.ZlOpenExtensionTExact)
