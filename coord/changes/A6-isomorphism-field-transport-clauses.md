# WeilConjectures.isomorphismFieldTransport and its clause records

## Reason

To state strictly smaller localization and descent steps without an import cycle,
move the four clause declarations to a public interface module and reexport that
module from the assigned module. Every original public signature and definition
body is preserved. No source-library module or target is changed. The original
existence theorem is assembled from finite-stage transport, scalar compatibility
and common-stage descent; the genuine residual descent obligation is explicit.

## Old

The following declarations were in Sheaf.Paper.IsomorphismFieldTransport:

```lean
structure IsomorphismFieldTransportStage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) where
  coefficient_projection : ∀ n : ℕ,
    inverseImageCompletedCoefficientMap l E g ≫
      limit.π (integralCoefficientSheafSystem l E X) (Opposite.op n) =
        inverseImageCompletedCoefficientComponent l E g n
  moduleEquivalence : (inverseImageIntegralModules l E g).IsEquivalence
  moduleAdditive : (inverseImageIntegralModules l E g).Additive
  moduleLimits : PreservesFiniteLimits (inverseImageIntegralModules l E g)
  moduleColimits : PreservesFiniteColimits (inverseImageIntegralModules l E g)
  moduleEpsilon : inverseImageIntegralModules l E g ⋙
    inverseImageIntegralModules l E (inv g) ≅ 𝟭 (integralTowerModules l E Y)
  module_epsilon_formula : ∀ M : integralTowerModules l E Y,
    moduleEpsilon.hom.app M = (pullbackIdentityModuleCounit l E g).hom.app M
  integralEquivalence : (constructibleIntegralPullback l E g).IsEquivalence
  integralShift : (constructibleIntegralPullback l E g).CommShift ℤ
  lambda : constructibleIntegralPullback l E g ⋙ (sfIntegralConstructible l E X).ι ≅
    (sfIntegralConstructible l E Y).ι ⋙ inverseImageIntegralDerived l E g
  lambda_formula : ∀ K : sfIntegralConstructibleCategory l E Y,
    HEq (lambda.hom.app K) (pullbackIdentityLambda l E g hX hY K).hom
  lambda_shift :
    (fun [_s : (constructibleIntegralPullback l E g).CommShift ℤ] ↦
      NatTrans.CommShift lambda.hom ℤ) (_s := integralShift)
  integralExact :
    (fun [_s : (constructibleIntegralPullback l E g).CommShift ℤ] ↦
      (constructibleIntegralPullback l E g).IsTriangulated) (_s := integralShift)
  integralLinear : (constructibleIntegralPullback l E g).Linear
    (Padic.coefficientExtensionIntegers l E)
  epsilon : constructibleIntegralPullback l E g ⋙
    constructibleIntegralPullback l E (inv g) ≅ 𝟭 (sfIntegralConstructibleCategory l E Y)
  epsilon_formula : ∀ K : sfIntegralConstructibleCategory l E Y,
    HEq (epsilon.hom.app K).hom (pullbackIdentityEpsilon l E g K).hom
  rationalEquivalence : (rationalDerivedPullback l E g).IsEquivalence
  rationalShift : (rationalDerivedPullback l E g).CommShift ℤ
  rational_shift_formula : ∀ K : sfIntegralConstructibleCategory l E Y,
    HEq (((rationalDerivedPullback l E g).commShiftIso
      (self := rationalShift) (1 : ℤ)).hom.app
        ((sfRationalConstructibleLocalization l E Y).obj K))
      ((sfRationalConstructibleLocalization l E X).map
        (((constructibleIntegralPullback l E g).commShiftIso
          (self := integralShift) (1 : ℤ)).hom.app K))
  rationalExact :
    (fun [_s : (rationalDerivedPullback l E g).CommShift ℤ] ↦
      (rationalDerivedPullback l E g).IsTriangulated) (_s := rationalShift)
  rationalAdditive : (rationalDerivedPullback l E g).Additive
  rational_object : ∀ K : sfRationalConstructibleCategory l E Y,
    (rationalDerivedPullback l E g).obj K =
      ⟨(constructibleIntegralPullback l E g).obj K.obj⟩
  rational_tensor : ∀ (K M : sfIntegralConstructibleCategory l E Y) (f : K ⟶ M)
    (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
    HEq ((rationalDerivedPullback l E g).map
      (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
        (sfRationalConstructibleLocalization l E Y).obj K ⟶
          (sfRationalConstructibleLocalization l E Y).obj M))
      (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
        (constructibleIntegralPullback l E g).map f)
  rationalEpsilon : rationalDerivedPullback l E g ⋙ rationalDerivedPullback l E (inv g) ≅
    𝟭 (sfRationalConstructibleCategory l E Y)
  rational_epsilon_formula : ∀ K : sfRationalConstructibleCategory l E Y,
    HEq (rationalEpsilon.hom.app K)
      ((sfRationalConstructibleLocalization l E Y).map (epsilon.hom.app K.obj))

/-- The scalar inverse equation for the prescribed completed scalar/pullback maps.
Source: scalar paragraph, inverse automorphism argument
(blueprint: lem-pod-isomorphism-field-transport). -/
def isomorphismFieldTransportScalarLaw
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ K : sfIntegralConstructibleCategory l E Y,
    HEq
      ((integralPullbackScalarComparison l E L ι (inv g)
          ((constructibleIntegralPullback l E g).obj K)).hom.hom ≫
        (integralDerivedPullback l L (inv g)).map
          (integralPullbackScalarComparison l E L ι g K).hom.hom ≫
        (pullbackIdentityEpsilon l L g
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj K)).hom)
      ((integralScalarExtensionOfUniverses l E L ι Y).map
        (pullbackIdentityEpsilon l E g K).hom)

/-- Localization of the inverse/scalar equation on every rational object. Naturality
of the natural isomorphisms ranges over all localized arrows.
Source: rational and scalar paragraphs, inverse automorphism argument
(blueprint: lem-pod-isomorphism-field-transport). -/
def isomorphismFieldTransportRationalScalarLaw
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (SE : IsomorphismFieldTransportStage l E g hX hY)
    (SL : IsomorphismFieldTransportStage l L g hX hY) : Prop :=
  ∀ K : sfRationalConstructibleCategory l E Y,
    (rationalPullbackScalarComparison l E L ι (inv g)).hom.app
        ((rationalDerivedPullback l E g).obj K) ≫
      (rationalDerivedPullback l L (inv g)).map
        ((rationalPullbackScalarComparison l E L ι g).hom.app K) ≫
      SL.rationalEpsilon.hom.app
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K) =
    (sfRationalScalarExtension l E Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map (SE.rationalEpsilon.hom.app K)

/-- Common-stage clauses use the actual quotient arrows and inclusion of the localized
finite-stage epsilon. Source: final common-stage paragraphs, inverse automorphism argument
(blueprint: lem-pod-isomorphism-field-transport). -/
structure IsomorphismFieldTransportCommon
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (S : ∀ E : Index l Ω,
      IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) g hX hY) where
  equivalence : (commonStageDerivedPullback l Ω g).IsEquivalence
  shift : (commonStageDerivedPullback l Ω g).CommShift ℤ
  exact :
    (fun [_s : (commonStageDerivedPullback l Ω g).CommShift ℤ] ↦
      (commonStageDerivedPullback l Ω g).IsTriangulated) (_s := shift)
  additive : (commonStageDerivedPullback l Ω g).Additive
  stageComparison : ∀ E : Index l Ω,
    inclusion (Y := Y) E ⋙ commonStageDerivedPullback l Ω g ≅
      rationalDerivedPullback l (Coefficient.{u} l Ω E) g ⋙ inclusion (Y := X) E
  stage_comparison_formula : ∀ (E : Index l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
    HEq ((stageComparison E).hom.app K) (𝟙 ((commonStagePullbackObject l Ω g
      ((inclusion (Y := Y) E).obj K))))
  stage_shift : ∀ E : Index l Ω,
    @NatTrans.CommShift _ _ _ _ _ _ (stageComparison E).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _
        (inclusion (Y := Y) E) (commonStageDerivedPullback l Ω g) ℤ _ _ _ _
        (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift
          (l := l) (Ω := Ω) (Y := Y) E) shift)
      (@Functor.CommShift.comp _ _ _ _ _ _
        (rationalDerivedPullback l (Coefficient.{u} l Ω E) g) (inclusion (Y := X) E)
        ℤ _ _ _ _ (S E).rationalShift
        (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift
          (l := l) (Ω := Ω) (Y := X) E))
  object_formula : ∀ P : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
    (commonStageDerivedPullback l Ω g).obj P = commonStagePullbackObject l Ω g P
  arrow_formula : ∀ (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : Index l Ω) (hP : P.stage ≤ L) (hQ : Q.stage ≤ L)
    (f : P.toStage hP ⟶ Q.toStage hQ),
    HEq ((commonStageDerivedPullback l Ω g).map (ofHom P Q L hP hQ f))
      (ofHom (commonStagePullbackObject l Ω g P) (commonStagePullbackObject l Ω g Q)
        L hP hQ ((commonStagePullbackComparison l Ω g P L hP).hom ≫
          (rationalDerivedPullback l (Coefficient.{u} l Ω L) g).map f ≫
          (commonStagePullbackComparison l Ω g Q L hQ).inv))
  epsilon : commonStageDerivedPullback l Ω g ⋙ commonStageDerivedPullback l Ω (inv g) ≅
    𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω Y)
  epsilon_formula : ∀ P : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
    HEq (epsilon.hom.app P)
      ((inclusion (Y := Y) P.stage).map ((S P.stage).rationalEpsilon.hom.app P.obj))
```

## New

The following declarations are in Sheaf.Paper.IsomorphismFieldTransportClauses:

```lean
structure IsomorphismFieldTransportStage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) where
  coefficient_projection : ∀ n : ℕ,
    inverseImageCompletedCoefficientMap l E g ≫
      limit.π (integralCoefficientSheafSystem l E X) (Opposite.op n) =
        inverseImageCompletedCoefficientComponent l E g n
  moduleEquivalence : (inverseImageIntegralModules l E g).IsEquivalence
  moduleAdditive : (inverseImageIntegralModules l E g).Additive
  moduleLimits : PreservesFiniteLimits (inverseImageIntegralModules l E g)
  moduleColimits : PreservesFiniteColimits (inverseImageIntegralModules l E g)
  moduleEpsilon : inverseImageIntegralModules l E g ⋙
    inverseImageIntegralModules l E (inv g) ≅ 𝟭 (integralTowerModules l E Y)
  module_epsilon_formula : ∀ M : integralTowerModules l E Y,
    moduleEpsilon.hom.app M = (pullbackIdentityModuleCounit l E g).hom.app M
  integralEquivalence : (constructibleIntegralPullback l E g).IsEquivalence
  integralShift : (constructibleIntegralPullback l E g).CommShift ℤ
  lambda : constructibleIntegralPullback l E g ⋙ (sfIntegralConstructible l E X).ι ≅
    (sfIntegralConstructible l E Y).ι ⋙ inverseImageIntegralDerived l E g
  lambda_formula : ∀ K : sfIntegralConstructibleCategory l E Y,
    HEq (lambda.hom.app K) (pullbackIdentityLambda l E g hX hY K).hom
  lambda_shift :
    (fun [_s : (constructibleIntegralPullback l E g).CommShift ℤ] ↦
      NatTrans.CommShift lambda.hom ℤ) (_s := integralShift)
  integralExact :
    (fun [_s : (constructibleIntegralPullback l E g).CommShift ℤ] ↦
      (constructibleIntegralPullback l E g).IsTriangulated) (_s := integralShift)
  integralLinear : (constructibleIntegralPullback l E g).Linear
    (Padic.coefficientExtensionIntegers l E)
  epsilon : constructibleIntegralPullback l E g ⋙
    constructibleIntegralPullback l E (inv g) ≅ 𝟭 (sfIntegralConstructibleCategory l E Y)
  epsilon_formula : ∀ K : sfIntegralConstructibleCategory l E Y,
    HEq (epsilon.hom.app K).hom (pullbackIdentityEpsilon l E g K).hom
  rationalEquivalence : (rationalDerivedPullback l E g).IsEquivalence
  rationalShift : (rationalDerivedPullback l E g).CommShift ℤ
  rational_shift_formula : ∀ K : sfIntegralConstructibleCategory l E Y,
    HEq (((rationalDerivedPullback l E g).commShiftIso
      (self := rationalShift) (1 : ℤ)).hom.app
        ((sfRationalConstructibleLocalization l E Y).obj K))
      ((sfRationalConstructibleLocalization l E X).map
        (((constructibleIntegralPullback l E g).commShiftIso
          (self := integralShift) (1 : ℤ)).hom.app K))
  rationalExact :
    (fun [_s : (rationalDerivedPullback l E g).CommShift ℤ] ↦
      (rationalDerivedPullback l E g).IsTriangulated) (_s := rationalShift)
  rationalAdditive : (rationalDerivedPullback l E g).Additive
  rational_object : ∀ K : sfRationalConstructibleCategory l E Y,
    (rationalDerivedPullback l E g).obj K =
      ⟨(constructibleIntegralPullback l E g).obj K.obj⟩
  rational_tensor : ∀ (K M : sfIntegralConstructibleCategory l E Y) (f : K ⟶ M)
    (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
    HEq ((rationalDerivedPullback l E g).map
      (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
        (sfRationalConstructibleLocalization l E Y).obj K ⟶
          (sfRationalConstructibleLocalization l E Y).obj M))
      (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
        (constructibleIntegralPullback l E g).map f)
  rationalEpsilon : rationalDerivedPullback l E g ⋙ rationalDerivedPullback l E (inv g) ≅
    𝟭 (sfRationalConstructibleCategory l E Y)
  rational_epsilon_formula : ∀ K : sfRationalConstructibleCategory l E Y,
    HEq (rationalEpsilon.hom.app K)
      ((sfRationalConstructibleLocalization l E Y).map (epsilon.hom.app K.obj))

/-- The scalar inverse equation for the prescribed completed scalar/pullback maps.
Source: scalar paragraph, inverse automorphism argument
(blueprint: def-pod-isomorphism-field-transport-clauses). -/
def isomorphismFieldTransportScalarLaw
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ K : sfIntegralConstructibleCategory l E Y,
    HEq
      ((integralPullbackScalarComparison l E L ι (inv g)
          ((constructibleIntegralPullback l E g).obj K)).hom.hom ≫
        (integralDerivedPullback l L (inv g)).map
          (integralPullbackScalarComparison l E L ι g K).hom.hom ≫
        (pullbackIdentityEpsilon l L g
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj K)).hom)
      ((integralScalarExtensionOfUniverses l E L ι Y).map
        (pullbackIdentityEpsilon l E g K).hom)

/-- Localization of the inverse/scalar equation on every rational object. Naturality
of the natural isomorphisms ranges over all localized arrows.
Source: rational and scalar paragraphs, inverse automorphism argument
(blueprint: def-pod-isomorphism-field-transport-clauses). -/
def isomorphismFieldTransportRationalScalarLaw
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (SE : IsomorphismFieldTransportStage l E g hX hY)
    (SL : IsomorphismFieldTransportStage l L g hX hY) : Prop :=
  ∀ K : sfRationalConstructibleCategory l E Y,
    (rationalPullbackScalarComparison l E L ι (inv g)).hom.app
        ((rationalDerivedPullback l E g).obj K) ≫
      (rationalDerivedPullback l L (inv g)).map
        ((rationalPullbackScalarComparison l E L ι g).hom.app K) ≫
      SL.rationalEpsilon.hom.app
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K) =
    (sfRationalScalarExtension l E Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map (SE.rationalEpsilon.hom.app K)

/-- Common-stage clauses use the actual quotient arrows and inclusion of the localized
finite-stage epsilon. Source: final common-stage paragraphs, inverse automorphism argument
(blueprint: def-pod-isomorphism-field-transport-clauses). -/
structure IsomorphismFieldTransportCommon
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (S : ∀ E : Index l Ω,
      IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) g hX hY) where
  equivalence : (commonStageDerivedPullback l Ω g).IsEquivalence
  shift : (commonStageDerivedPullback l Ω g).CommShift ℤ
  exact :
    (fun [_s : (commonStageDerivedPullback l Ω g).CommShift ℤ] ↦
      (commonStageDerivedPullback l Ω g).IsTriangulated) (_s := shift)
  additive : (commonStageDerivedPullback l Ω g).Additive
  stageComparison : ∀ E : Index l Ω,
    inclusion (Y := Y) E ⋙ commonStageDerivedPullback l Ω g ≅
      rationalDerivedPullback l (Coefficient.{u} l Ω E) g ⋙ inclusion (Y := X) E
  stage_comparison_formula : ∀ (E : Index l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
    HEq ((stageComparison E).hom.app K) (𝟙 ((commonStagePullbackObject l Ω g
      ((inclusion (Y := Y) E).obj K))))
  stage_shift : ∀ E : Index l Ω,
    @NatTrans.CommShift _ _ _ _ _ _ (stageComparison E).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _
        (inclusion (Y := Y) E) (commonStageDerivedPullback l Ω g) ℤ _ _ _ _
        (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift
          (l := l) (Ω := Ω) (Y := Y) E) shift)
      (@Functor.CommShift.comp _ _ _ _ _ _
        (rationalDerivedPullback l (Coefficient.{u} l Ω E) g) (inclusion (Y := X) E)
        ℤ _ _ _ _ (S E).rationalShift
        (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift
          (l := l) (Ω := Ω) (Y := X) E))
  object_formula : ∀ P : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
    (commonStageDerivedPullback l Ω g).obj P = commonStagePullbackObject l Ω g P
  arrow_formula : ∀ (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : Index l Ω) (hP : P.stage ≤ L) (hQ : Q.stage ≤ L)
    (f : P.toStage hP ⟶ Q.toStage hQ),
    HEq ((commonStageDerivedPullback l Ω g).map (ofHom P Q L hP hQ f))
      (ofHom (commonStagePullbackObject l Ω g P) (commonStagePullbackObject l Ω g Q)
        L hP hQ ((commonStagePullbackComparison l Ω g P L hP).hom ≫
          (rationalDerivedPullback l (Coefficient.{u} l Ω L) g).map f ≫
          (commonStagePullbackComparison l Ω g Q L hQ).inv))
  epsilon : commonStageDerivedPullback l Ω g ⋙ commonStageDerivedPullback l Ω (inv g) ≅
    𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω Y)
  epsilon_formula : ∀ P : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
    HEq (epsilon.hom.app P)
      ((inclusion (Y := Y) P.stage).map ((S P.stage).rationalEpsilon.hom.app P.obj))
```

The original module publicly imports the new module, preserving all declaration
names, definitions, visibility and public availability. Its theorem statement is
unchanged. Proof-only imports introduce the three smaller steps and the scalar
comparison agreement. The existing public imports are retained through Clauses. The redundant private
SfIntegralConstructibleTriangulated import is removed: it is already public via
SfRationalizationKaroubi and SfIntegralConstructibleLinear.
No global definition or instance changes meaning. All new private helpers are
proved; there is no new chosen object with unspecified data. The choices of finite
stage packages have normalized lambda and epsilon components prescribed by the
original clauses, and merely select realizations of those fixed data.

The clause file retains the original generation settings (`genInjectivity false`
and `genSizeOfSpec false`), including the original generated size and constructor
metadata. Its elaboration uses these file-local settings:

```lean
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.privateModule false
```

The two transparency settings tighten the original file's `false` settings.
The other proof modules use the same elaboration settings and disable generation
of unnecessary size/constructor metadata for their new private helpers. No public
instance or attribute is added or removed by these file-local commands. Profiling
was used to identify repeated typeclass inference and was removed before delivery.
The original instance-removal attributes are retained in the clause and parent
contexts. These commands do not change importing modules' options.

## Users

Source audit using tools/downstream.py/leanindex: 707 downstream modules.
The table lists every transitive consumer and marks the textual direct users.
All retain the same public declarations and bodies through the public reexport.
No consumer needs adaptation, and no held module is edited. The independent reader
and maintainer global build can check the unchanged consumers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IsomorphismFieldTransport | A6 | Original theorem assembled; clauses reexported. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.DeligneLaumon.ContinuousCoefficientGeometricCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.DeligneLaumon.FiniteStageFibreVanishing | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.DeligneLaumon.NormalizedContinuousCoefficientFamily | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.DeligneLaumon.NormalizedStratifiedEmbeddedLattices | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.DeligneLaumon.OrdinarySectionScalarComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.DeligneLaumon.RawHeartAdicComparisonBridge | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.DeligneLaumon.RawHeartAdicStrataBridge | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.FourierTransform.FourierDeligneTransform | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicClosureScalarCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicCommonStageFibreTransport | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicCommonStageFibreZeroMap | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicCommonStageHeartExactness | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicFibreComparisonData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicFiniteConstructibilityComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicFiniteRealizationCocone | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicFiniteRealizationData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicFiniteScalarCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicNormalizedFibreCommonStage | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicNormalizedFibreCommonStageData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicNormalizedFibreData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicNormalizedFibreExactness | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicNormalizedFibrePullback | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicNormalizedFibreScalar | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicRealizationFamilyData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicReindexingCore | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicReindexingFunctoriality | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicReindexingHom | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicReindexingTensor | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicStratifiedPullbackInterface | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AffineSpaceProductDomain | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | E3 | Transitive importer; unchanged interface. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.AutomorphismConstructibleStageEquivalence | B6 | Direct uses of isomorphismFieldTransport; unchanged interface. |
| Sheaf.Paper.AutomorphismSquareRationalScalar | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.BarrettIndRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalFiltrationDiagramFibres | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalFiltrationExactDiagram | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalFrontierExistence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalLisseWeilFrontierData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalLocalFrobeniusData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalLocalFrobeniusIterateComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalRawLisseCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalRawLisseCommonDescent | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalRawLisseCommonFibres | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalRawLisseCommonRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalRawLisseCommonRestriction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalRawLisseCommonSystem | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalRawLisseFiniteConstruction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalRawLisseFiniteOperations | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalRawLisseIntrinsicFibrePullback | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalRawLisseOperations | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalRawLissePointFibres | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalRawLisseRealizationData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalRawLisseScalarCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalRealizationLocalSpectrum | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalRealizationPunctualPurity | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalRealizedAnchorEigenvalue | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalSuccessiveRestrictions | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalSystemRawLisseRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalTwoFibreCommonData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalTwoFibreScalarData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalWeilCoherentDiagramStages | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalWeilFiltrationTransportData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalWeilFiniteDiagramDescent | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalWeilPrescribedIsomorphismLifts | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClassicalWeilRestrictionExistence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ClopenPrescribedWeilFiltration | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Direct uses of isomorphismFieldTransport; unchanged interface. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CommonStageOpenHeartAdjunction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | M2 | Transitive importer; unchanged interface. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CompactSupportCondensedRealization | Y2 | Transitive importer; unchanged interface. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CompactSupportProjectionFormula | Y3 | Transitive importer; unchanged interface. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CompactSupportRealizationFactorization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CompletedContinuousHomHypotheses | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CompletedLocalFibreComparisonData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CompletedPullbackFractionDescent | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CondensedExceptionalCounitRepresentation | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CondensedExceptionalRealizationProperties | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CondensedExceptionalReconstructionData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CondensedExceptionalRefinementCounits | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CondensedExceptionalSystemRecognition | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CondensedOpenCoefficientModels | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CondensedOpenCounitRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CondensedOpenUnitComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantDirectImageTowerRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantExtensionCyclicSheetPartition | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | U6 | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantExtensionRestrictionLocalConjugacy | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantExtensionReturnData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantExtensionReturnExactFunctor | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantExtensionReturnLocalSpectra | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantExtensionReturnTransportComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantExtensionSheetCoefficientEquivalences | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantExtensionSheetCommonStageEquivalences | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantExtensionSheetGeometry | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantExtensionSheetHeartData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantExtensionSheetTensorSplitting | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantExtensionWeilHeartData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | F7 | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstructibleMateCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstructiblePullbackTExact | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstructibleRationalHomComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ConstructibleTruncations | unclaimed | Direct uses of IsomorphismFieldTransportStage, isomorphismFieldTransport; unchanged interface. |
| Sheaf.Paper.ConstructibleWeilModelSquares | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CoordinateAdjunctionComposition | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CoordinateCartierBoundarySign | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CoordinateProductPresentations | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CoordinateSectionArrows | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CoordinateSectionProductRecursion | Z6 | Transitive importer; unchanged interface. |
| Sheaf.Paper.CoordinateSectionProjection | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CoordinateSectionProjectiveTrace | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CoordinateSectionSiteTransport | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CoordinateSectionTensorTrace | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CoordinateSupportedProductRecursion | N1 | Transitive importer; unchanged interface. |
| Sheaf.Paper.CoordinateTowerCompactTranspose | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CoordinateTowerExceptionalCompositors | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CoordinateTowerNormalizationData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CoordinateTowerNormalizationFusion | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CoordinateZeroBaseChange | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CurveClassicalFiltrationPullback | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CurveClassicalPullbackExists | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CurveRestrictionFiltrationData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.CurveRestrictionLocalPowers | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.DerivedTensorRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Direct uses of isomorphismFieldTransport; unchanged interface. |
| Sheaf.Paper.FieldCohomologyPerfectDescent | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FilteredCondensedCanonicalComparisons | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FilteredCondensedCounitBijective | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FilteredCondensedCounitFiniteFormula | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FilteredCondensedRepresentingPair | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FilteredCondensedRepresentingPairData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteFreeCompactComposition | Q2 | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteFreeCompactSupportData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteFreeCompactSupportGeometricSquares | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteFreeCompactSupportSiteSquare | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FinitePurityCounitSystem | S3 | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteRationalHeartComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteSheafH0Augmentation | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | Direct uses of IsomorphismFieldTransportStage, isomorphismFieldTransport; unchanged interface. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.FrobeniusPullbackOrdinaryExchange | unclaimed | Direct uses of IsomorphismFieldTransportStage, IsomorphismFieldTransportCommon, isomorphismFieldTransport; unchanged interface. |
| Sheaf.Paper.FrobeniusSquareExchange | V4 | Transitive importer; unchanged interface. |
| Sheaf.Paper.FrobeniusSystemExchangeInverse | F1 | Transitive importer; unchanged interface. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.GeometricCommonStageDirectImage | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.GeometricQuotientWeilCompositionSeries | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.GlobalIdentityNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.GlobalVerdierDualityData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.IdentityCompactificationLimitComparisons | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.IdentityCompactificationSystemMate | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.IntegralLissePullbackNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.IntegralPurityCounitReduction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.IntegralSectionsPerfectReduction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.IntegralSemilinearGermSquare | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.IntrinsicConstructibleFibreExactness | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.IntrinsicLocalLatticeComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.IteratedPurityScalarPasting | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.KummerSiteCohomologyNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LisseFieldNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LisseLatticeChoiceExistence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LisseLatticeHeartLift | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LisseLatticeHeartLiftData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LisseLatticeLisseDescent | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LisseLatticeNormalizedRealizations | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LisseLatticeRealizationFaithful | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LisseLatticeSingleComparisons | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LissePointNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LissePointSectionsRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LisseRationalRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LisseTensorPullbackRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LisseTensorPullbackRealizationData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LocalFrobeniusLargeCoefficients | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LocalFrobeniusLargeCompositionAssociativity | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LocalFrobeniusLargeCompositionCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LocalFrobeniusLargeScalarTower | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LocalFrobeniusLargeTransportAddition | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LocalFrobeniusLargeTransportNaturality | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LocalFrobeniusLargeWeilAddition | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LocalFrobeniusStepCompatibility | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.LocallyFiniteAdicConstructibleRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.MixedCupCoefficientChange | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.MixedCupCoefficientSquare | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.MixedCupFieldCoordinates | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.MixedCupFieldNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.MixedCupFieldOperations | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.MixedCupOperationComparisons | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.MixedCupRingedNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.MixedCupTensorClosure | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.MixedCupTensorComparisons | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.MixedCupTensorElementary | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.MixedCupTensorNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NativeWeilLocalizingBrownAdjoints | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NormalizedFieldPurityTrace | K4 | Transitive importer; unchanged interface. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NormalizedHeartRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NormalizedLatticeFiniteFree | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NormalizedPullbackCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NormalizedPullbackNaturality | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.NormalizedPullbackObjects | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.OpenWeilCarrierRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.OpenWeilCoefficientFibres | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.OpenWeilFiniteStageFrobenius | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.OpenWeilGeometricFibres | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.OpenWeilPunctualSpectrum | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.OrientationCoordinateBoundaryPullback | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.OrientationCoordinateModelBoundary | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.OrientationLocalResidue | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PointFiniteMultiplicationInverse | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PointFrobeniusNormalizationDefinitions | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PointFrobeniusTransportNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PointIdentityExchangeRecipe | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PointQuotientComparisonCoordinates | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PointRealizationStandardCohomology | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PointScalarPunctualSpectrum | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PointWeilAlgebraicFlag | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PointWeilHeartFlagData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PointWeilPairingCoordinates | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PointWeilTensorRepresentatives | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PointWeilTransportUnitShift | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ProjectionFormulaCoherence | V5 | Transitive importer; unchanged interface. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ProperSupportCoefficientAdjunction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ProperSupportFiniteAdjunction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ProperWeilIterateGermFormula | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurCoordinateRepresentingFamily | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurIntegralRepresentingPair | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurIntegralRepresentingPairData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurIntegralSupportComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurIntegralSupportComparisonData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurIntegralSupportDerivedComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurIntegralSupportOrdinaryComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurSupportPresentationAlpha | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurityAffineLineBoundaryRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurityAffineLineOrientationData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurityKummerTriangleConcentration | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurityTateDatum | K1 | Transitive importer; unchanged interface. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | V3 | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalAmbientPullComposition | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalAmbientPullModels | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalBalancedFreePullback | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalContinuousComparisonCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalContinuousFiltrationModels | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalContinuousPullbackTransport | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalModuleRealizationFunctor | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalOrdinaryCohomologyTensor | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalPullSingleComputation | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalRealizationFiniteConeModels | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalRealizationHomTransport | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalRealizationScalarCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalScalarBalancedLocalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalScalarCompletionUnitSquare | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalScalarMixedUnitCancellation | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalStratumPullbackData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalStratumPullbackModels | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RealWeights | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ReconstructedBrownMateLaws | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ReconstructedPairRefinementData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ReconstructedRefinementCommon | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ReconstructedRefinementSingleDegree | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ReconstructedRefinementTraceSquare | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ReconstructedRefinementTraceTransport | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RefinementFiniteOriginEvaluation | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RelativeKummerSiteNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RelativeKunnethClosedFibre | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RelativeKunnethConstructions | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed | Direct uses of IsomorphismFieldTransportStage, IsomorphismFieldTransportCommon, isomorphismFieldTransport; unchanged interface. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ScalarFibreCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ScalarFibreComponentData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ScalarFibreComponents | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ScalarFibreNaturality | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SectionsRationalModelComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SemilinearCommonOrdinaryCubes | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SemilinearCommonRefinementCubes | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SemilinearCommonSupportCubes | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | K3 | Transitive importer; unchanged interface. |
| Sheaf.Paper.SemilinearExchangeCubeCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SemilinearExchangeCubeData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Direct uses of isomorphismFieldTransport; unchanged interface. |
| Sheaf.Paper.SemilinearGermIterationDescent | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SemilinearRationalOrdinaryCubes | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SemilinearRationalRefinementCubes | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SemilinearRationalSupportCubes | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SfAdicCommonStageDescentEquivalence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SfNormalizedCommonStageWeilSquares | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SfNormalizedRationalClosedComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SfNormalizedRationalWeilSquares | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | C5 | Transitive importer; unchanged interface. |
| Sheaf.Paper.SfQbarLocalizationCommonStage | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SfRecollementReductionBoundary | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.SmoothPurityFieldExtension | U4 | Transitive importer; unchanged interface. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TensorHeartSpecialization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TensorHomExchange | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TowerTracePurityComparison | P4 | Transitive importer; unchanged interface. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistFrobeniusScalar | A8 | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedCoordinateSectionCore | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedCoordinateSectionSign | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.VerdierHomChainComposition | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.VerdierHomChainCompositionData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.VerdierIdentityProjection | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | T2 | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilGenericLissity | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilGeometricFiberProperties | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilIndOpenRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilIndOpenRepresentability | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilIndProperHigherRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilIndProperHigherRepresentability | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilIndProperOpenHigher | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilIndSheafCategory | unclaimed | Direct uses of isomorphismFieldTransport; unchanged interface. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilPullbackFibreReturn | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ZlCanonicalImmersionPunctualSpectrum | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ZlCanonicalImmersionStalkConjugacy | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ZlImmersionFilteredReductionTransport | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ZlImmersionRestrictionAssembly | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ZlImmersionWeilLocalData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ZlOpenExtensionAssembly | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ZlOpenWeilUnitEmptyFibre | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ZlSfPbcNormalizedHeartModel | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ZlWeilPullCompositorEquivariance | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.CoefVerdierWeilData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.CoefWeilExceptionalCompatibility | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.CoefWeilLeftExchangeCompatibility | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.CoefWeilNormalizedDuality | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.CompletedTensorSlotShiftLaws | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.FiniteMappingAdjunctionData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescent | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentIsIso | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.FrobeniusCohomologyRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.FrobeniusCohomologyRealizationTransport | G1 | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | H1 | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.OpenClosedWeilMateCoefficient | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.OpenClosedWeilMateCompletion | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.OpenClosedWeilMateData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.OpenClosedWeilMateDescent | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.OpenClosedWeilMateFinite | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.OpenClosedWeilMateIntegral | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.RamifiedScalarPreparation | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.RamifiedScalarSupportCompatibility | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.SystemTensorShiftCoherence | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.TraceFormula.CompactDirectPowerTransportNormalization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.TraceFormula.FrobeniusCompactPowerExchange | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.TraceFormula.FrobeniusProperPowerExchange | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.TraceFormula.LocalNormalizationStrictRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.WeilSheaf.NativeExceptionalLeftModels | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.WeilSheaf.NativeExceptionalPointUnit | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.WeilSheaf.NativeExceptionalStructuralTransport | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.WeilSheaf.OrdinaryClosedPresentation | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.WeilSheaf.StructuralOmegaHomPairs | unclaimed | Transitive importer; unchanged interface. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Transitive importer; unchanged interface. |

## Status

landed 20261026T065118-L-2694757 2026-10-26 (merge of deliver/A6/Sheaf.Paper.IsomorphismFieldTransport)
