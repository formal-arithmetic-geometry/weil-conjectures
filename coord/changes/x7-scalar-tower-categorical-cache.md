# ScalarExtensionTower categorical interfaces

## Reason

Concrete composite functor types repeatedly unfold the signed total tensor and module
category structures. The original statement-only composition takes about 21 seconds,
and the concrete comparison record and route definitions each repeat the same work.
Abstract categorical composites and a generic comparison record cache these types.
No map, coefficient inclusion, transition, normalization condition, or target is changed.
The record has exactly the same four fields; its carrier is now an explicit specialization
of ComparisonData. No external user names its old generated constructors or recursors.
Tensor remains definitionally the same signed total functor, with an explicit type.
Unit and composition unfold to the original equations. The five-map normalization
uses HEq to avoid expensive conversion of the final morphism's presentation. Its
fixed endpoints are the original definitionally equal morphism type, so heq_iff_eq
proves equivalence to the original equation; the private proved lemma
fiveStepEquation_iff_eq checks that equivalence. This changes a predicate's syntax,
not its mathematical strength. No Challenge declaration signature changes.
DerivedSigmaModel is locally irreducible after its definition; the existence proof
unfolds it explicitly. This prevents later declarations from expanding its equation.

## Old

```lean
abbrev tensor (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) :=
  coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf.{u, u} l E W)
```

```lean
structure Comparisons where
  /-- Scalar tensor comparison for all coefficient extensions. -/
  sigma : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    [Field B] [Algebra ℚ_[l] B] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u}),
    tensor l A W ⋙ scalar l A B i W ≅
      (scalar l A B i W).prod (scalar l A B i W) ⋙ tensor l B W
  /-- The comparison sends b tensor (x tensor y) to (b tensor x) tensor (1 tensor y). -/
  sigma_formula : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u})
    (P Q : Complex l A W) (p q : ℤ) (U : (ℕ × W.ProEt)ᵒᵖ)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l B W).obj.obj U)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
    (((sigma A B i W).hom.app (P, Q)).f (p + q)).val.app U
      (integralComparisonSequenceTensorSection.{u, u} l A B i W
        (((tensor l A W).obj (P, Q)).X (p + q)) U b
        (generator l A W P Q p q U x y)) =
      generator l B W ((scalar l A B i W).obj P) ((scalar l A B i W).obj Q) p q U
        (integralComparisonSequenceTensorSection.{u, u} l A B i W (P.X p) U b x)
        (integralComparisonSequenceTensorSection.{u, u} l A B i W (Q.X q) U 1 y)
  /-- Finite tensor-pullback comparisons on whole quotient diagrams. -/
  c : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y : Scheme.{u}} (f : X ⟶ Y),
    tensor l A Y ⋙ pull l A f ≅ (pull l A f).prod (pull l A f) ⋙ tensor l A X
  /-- The inverse-image unit formula, extended to arbitrary target coefficients. -/
  c_formula : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : Complex l A Y) (p q : ℤ) (n : ℕ) (U : Y.ProEt)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l A X).obj.obj
      (op (n, (Scheme.proEtaleBaseChange f).obj U)))
    (x : (P.X p).val.obj (op (n, U))) (y : (Q.X q).val.obj (op (n, U))),
    (((c A f).hom.app (P, Q)).f (p + q)).val.app
      (op (n, (Scheme.proEtaleBaseChange f).obj U))
      (b • pullSection l A f
        (((tensor l A Y).obj (P, Q)).X (p + q)) n U
        (generator l A Y P Q p q (op (n, U)) x y)) =
      generator l A X ((pull l A f).obj P) ((pull l A f).obj Q) p q
        (op (n, (Scheme.proEtaleBaseChange f).obj U))
        (b • pullSection l A f (P.X p) n U x)
        (pullSection l A f (Q.X q) n U y)
```

```lean
def leftRoute {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.isoWhiskerLeft (tensor l E Y) (kappa l E L ι f) ≪≫
    Functor.isoWhiskerRight ((comparisons l).sigma E L ι Y) (pull l L f) ≪≫
    Functor.isoWhiskerLeft ((scalar l E L ι Y).prod (scalar l E L ι Y))
      ((comparisons l).c L f)
```

```lean
def rightRoute {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.isoWhiskerRight ((comparisons l).c E f) (scalar l E L ι X) ≪≫
    Functor.isoWhiskerLeft ((pull l E f).prod (pull l E f)) ((comparisons l).sigma E L ι X) ≪≫
    Functor.isoWhiskerRight (NatIso.prod (kappa l E L ι f) (kappa l E L ι f)) (tensor l L X)
```

```lean
theorem unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (kappa l E E (AlgHom.id ℚ_[l] E) f ≪≫
      Functor.isoWhiskerRight (scalarUnit l E Y) (pull l E f) =
        Functor.isoWhiskerLeft (pull l E f) (scalarUnit l E X)) ∧
    ((comparisons l).sigma E E (AlgHom.id ℚ_[l] E) Y ≪≫
      Functor.isoWhiskerRight (NatIso.prod (scalarUnit l E Y) (scalarUnit l E Y)) (tensor l E Y) =
      Functor.isoWhiskerLeft (tensor l E Y) (scalarUnit l E Y)) := by
  constructor
  · have h := congrArg (fun a ↦ NatIso.mapHomologicalComplex a (.up ℤ))
      (scalar_pull_unit l E f)
    exact h
  · exact scalarExtensionTensorUnit l E Y
      ((comparisons l).sigma E E (AlgHom.id ℚ_[l] E) Y)
      (fun P Q p q V x y ↦
        (comparisons l).sigma_formula E E (AlgHom.id ℚ_[l] E) Y P Q p q V 1 x y)
```

```lean
theorem composition (F : Type u) [Field F] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F] (j : L →ₐ[ℚ_[l]] F)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Functor.isoWhiskerRight (kappa l E L ι f) (scalar l L F j X) ≪≫
      Functor.isoWhiskerLeft (scalar l E L ι Y) (kappa l L F j f) ≪≫
      Functor.isoWhiskerRight (scalarComp l E L ι F j Y) (pull l F f) =
      Functor.isoWhiskerLeft (pull l E f) (scalarComp l E L ι F j X) ≪≫
        kappa l E F (j.comp ι) f) ∧
    (Functor.isoWhiskerRight ((comparisons l).sigma E L ι Y) (scalar l L F j Y) ≪≫
      Functor.isoWhiskerLeft ((scalar l E L ι Y).prod (scalar l E L ι Y))
        ((comparisons l).sigma L F j Y) ≪≫
      Functor.isoWhiskerRight (NatIso.prod (scalarComp l E L ι F j Y)
        (scalarComp l E L ι F j Y)) (tensor l F Y) =
      Functor.isoWhiskerLeft (tensor l E Y) (scalarComp l E L ι F j Y) ≪≫
        (comparisons l).sigma E F (j.comp ι) Y) := by
  sorry
```

```lean
def IsTensorModelNormalized (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l E W)
    (realization : integralCompletedTensor.{u, u} l E W ≅ S.reduction.prod S.reduction ⋙
      S.systemClosed.tensor ⋙ coefficientSequenceLimit.{u, u} l E W) : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory)
    (C D : Complex l E W)
    (eC : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (eD : S.reduction.obj (DerivedCategory.Q.obj Q.obj) ≅ DerivedCategory.Q.obj D)
    (κC : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj P.obj)
    (κD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj Q.obj)
    (hC : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E W) C)
    (hD : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E W) D),
    CoefficientReductionPresentation.{u, u} l E W S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C eC κC →
    CoefficientReductionPresentation.{u, u} l E W S.toCoefficientDerivedSystemReduction
      Q.obj Q.property.1 D eD κD →
    ∃ q : (((coefficientSequenceRestriction.{u, u} l E W).mapHomologicalComplex (.up ℤ)).obj
        ((tensor l E W).obj (C, D))).asFunctor ≅
      (integralOperationsTensorTowerFunctor.{u, u} l E W).obj (P.obj, Q.obj),
      (∀ (n : ℕ) (p r : ℤ) (U : W.ProEtᵒᵖ)
        (x : (C.X p).val.obj (op (n, U.unop)))
        (y : (D.X r).val.obj (op (n, U.unop))),
        ((q.hom.app (op n)).f (p + r)).val.app U
          (integralComparisonRestrictedSection.{u, u} l E W
            (((tensor l E W).obj (C, D)).X (p + r)) n U
            (generator l E W C D p r (op (n, U.unop)) x y)) =
          integralTensorGenerator l E W P.obj Q.obj n p r U
            (((κC n).hom.f p).val.app U (coefficientEvaluationSection.{u, u} l E W (C.X p) n U x))
            (((κD n).hom.f r).val.app U
              (coefficientEvaluationSection.{u, u} l E W (D.X r) n U y))) ∧
      realization.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (coefficientSequenceLimit.{u, u} l E W).map
          (S.systemClosed.tensor.map (Prod.mkHom eC.hom eD.hom)) ≫
        (coefficientSequenceLimit.{u, u} l E W).map
          ((S.systemTensorModel.iso _ _ _ C D hC hD).inv) ≫
        (integralComparisonRoosBridge.{u, u} l E W ρ ((tensor l E W).obj (C, D))).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
        (integralCompletedTensorComparison.{u, u} l E W).hom.app (P, Q)
```

## New

```lean
def leftRouteCore {C D A B : Type*}
    [Category C] [Category D] [Category A] [Category B]
    (T : C × C ⥤ C) (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (F : C ⥤ D) (G : C ⥤ A) (H : D ⥤ B) (K : A ⥤ B)
    (k : F ⋙ H ≅ G ⋙ K) (s : T ⋙ G ≅ G.prod G ⋙ TA)
    (c : TA ⋙ K ≅ K.prod K ⋙ TB) :
    T ⋙ F ⋙ H ≅ G.prod G ⋙ K.prod K ⋙ TB :=
  Functor.isoWhiskerLeft T k ≪≫ Functor.isoWhiskerRight s K ≪≫
    Functor.isoWhiskerLeft (G.prod G) c
```

```lean
def rightRouteCore {C D A B : Type*}
    [Category C] [Category D] [Category A] [Category B]
    (T : C × C ⥤ C) (TD : D × D ⥤ D) (TB : B × B ⥤ B)
    (F : C ⥤ D) (G : C ⥤ A) (H : D ⥤ B) (K : A ⥤ B)
    (k : F ⋙ H ≅ G ⋙ K) (s : TD ⋙ H ≅ H.prod H ⋙ TB)
    (c : T ⋙ F ≅ F.prod F ⋙ TD) :
    T ⋙ F ⋙ H ≅ G.prod G ⋙ K.prod K ⋙ TB :=
  Functor.isoWhiskerRight c H ≪≫ Functor.isoWhiskerLeft (F.prod F) s ≪≫
    Functor.isoWhiskerRight (NatIso.prod k k) TB
```

```lean
def UnitSquare {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (U : C ⥤ C) (V : D ⥤ D)
    (k : F ⋙ V ≅ U ⋙ F) (u : U ≅ 𝟭 C) (v : V ≅ 𝟭 D) : Prop :=
  k ≪≫ Functor.isoWhiskerRight u F = Functor.isoWhiskerLeft F v
```

```lean
def TensorUnitSquare {C : Type*} [Category C] (T : C × C ⥤ C)
    (U : C ⥤ C) (s : T ⋙ U ≅ U.prod U ⋙ T) (u : U ≅ 𝟭 C) : Prop :=
  s ≪≫ Functor.isoWhiskerRight (NatIso.prod u u) T = Functor.isoWhiskerLeft T u
```

```lean
def CompositionSquare {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    (p : A ⥤ B) (q : C ⥤ D) (r : E ⥤ F)
    (s : A ⥤ C) (t : C ⥤ E) (v : A ⥤ E)
    (s' : B ⥤ D) (t' : D ⥤ F) (v' : B ⥤ F)
    (k : p ⋙ s' ≅ s ⋙ q) (h : q ⋙ t' ≅ t ⋙ r)
    (d : p ⋙ v' ≅ v ⋙ r) (a : s ⋙ t ≅ v) (b : s' ⋙ t' ≅ v') : Prop :=
  Functor.isoWhiskerRight k t' ≪≫ Functor.isoWhiskerLeft s h ≪≫
      Functor.isoWhiskerRight a r = Functor.isoWhiskerLeft p b ≪≫ d
```

```lean
def TensorCompositionSquare {A B C : Type*} [Category A] [Category B] [Category C]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TC : C × C ⥤ C)
    (s : A ⥤ B) (t : B ⥤ C) (v : A ⥤ C)
    (a : s ⋙ t ≅ v) (k : TA ⋙ s ≅ s.prod s ⋙ TB)
    (h : TB ⋙ t ≅ t.prod t ⋙ TC) (d : TA ⋙ v ≅ v.prod v ⋙ TC) : Prop :=
  Functor.isoWhiskerRight k t ≪≫ Functor.isoWhiskerLeft (s.prod s) h ≪≫
      Functor.isoWhiskerRight (NatIso.prod a a) TC = Functor.isoWhiskerLeft TA a ≪≫ d
```

```lean
def FiveStepEquation {C : Type*} [Category C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) (e : F ⟶ G)
    {α : Type*} (f : α) : Prop := HEq (a ≫ b ≫ c ≫ d ≫ e) f
```

```lean
def tensor (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) : Complex l E W × Complex l E W ⥤ Complex l E W :=
  coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf.{u, u} l E W)
```

```lean
abbrev scalar (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u}) :
    Complex l E W ⥤ Complex l L W :=
  (integralComparisonSequenceScalarModel.{u, u} l E L ι W).E.mapHomologicalComplex (.up ℤ)
```

```lean
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) : Complex l E Y ⥤ Complex l E X :=
  (integralComparisonSequencePullback.{u, u} l E f).mapHomologicalComplex (.up ℤ)
```

```lean
abbrev generator (W : Scheme.{u}) (P Q : Complex l E W) (p q : ℤ)
    (U : (ℕ × W.ProEt)ᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((tensor l E W).obj (P, Q)).X (p + q)).val.obj U :=
  coefficientTensorGenerator.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf.{u, u} l E W) P Q p q (p + q) rfl U x y
```

```lean
def ScalarFormula (sigma : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    [Field B] [Algebra ℚ_[l] B] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u}),
    tensor l A W ⋙ scalar l A B i W ≅
      (scalar l A B i W).prod (scalar l A B i W) ⋙ tensor l B W) : Prop :=
  ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u})
    (P Q : Complex l A W) (p q : ℤ) (U : (ℕ × W.ProEt)ᵒᵖ)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l B W).obj.obj U)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
    (((sigma A B i W).hom.app (P, Q)).f (p + q)).val.app U
      (integralComparisonSequenceTensorSection.{u, u} l A B i W
        (((tensor l A W).obj (P, Q)).X (p + q)) U b
        (generator l A W P Q p q U x y)) =
      generator l B W ((scalar l A B i W).obj P) ((scalar l A B i W).obj Q) p q U
        (integralComparisonSequenceTensorSection.{u, u} l A B i W (P.X p) U b x)
        (integralComparisonSequenceTensorSection.{u, u} l A B i W (Q.X q) U 1 y)
```

```lean
def PullFormula (c : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y : Scheme.{u}} (f : X ⟶ Y),
    tensor l A Y ⋙ pull l A f ≅ (pull l A f).prod (pull l A f) ⋙ tensor l A X) : Prop :=
  ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : Complex l A Y) (p q : ℤ) (n : ℕ) (U : Y.ProEt)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l A X).obj.obj
      (op (n, (Scheme.proEtaleBaseChange f).obj U)))
    (x : (P.X p).val.obj (op (n, U))) (y : (Q.X q).val.obj (op (n, U))),
    (((c A f).hom.app (P, Q)).f (p + q)).val.app
      (op (n, (Scheme.proEtaleBaseChange f).obj U))
      (b • pullSection l A f
        (((tensor l A Y).obj (P, Q)).X (p + q)) n U
        (generator l A Y P Q p q (op (n, U)) x y)) =
      generator l A X ((pull l A f).obj P) ((pull l A f).obj Q) p q
        (op (n, (Scheme.proEtaleBaseChange f).obj U))
        (b • pullSection l A f (P.X p) n U x)
        (pullSection l A f (Q.X q) n U y)
```

```lean
structure ComparisonData (Sigma Pullback : Type*)
    (sigmaFormula : Sigma → Prop) (pullFormula : Pullback → Prop) where
  sigma : Sigma
  sigma_formula : sigmaFormula sigma
  c : Pullback
  c_formula : pullFormula c
```

```lean
abbrev Comparisons :=
  ComparisonData (∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    [Field B] [Algebra ℚ_[l] B] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u}),
    tensor l A W ⋙ scalar l A B i W ≅
      (scalar l A B i W).prod (scalar l A B i W) ⋙ tensor l B W)
    (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y : Scheme.{u}} (f : X ⟶ Y),
    tensor l A Y ⋙ pull l A f ≅ (pull l A f).prod (pull l A f) ⋙ tensor l A X)
    (ScalarFormula l) (PullFormula l)
```

```lean
def leftRoute {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor l E Y ⋙ pull l E f ⋙ scalar l E L ι X ≅
      (scalar l E L ι Y).prod (scalar l E L ι Y) ⋙
        (pull l L f).prod (pull l L f) ⋙ tensor l L X :=
  leftRouteCore (tensor l E Y) (tensor l L Y) (tensor l L X)
    (pull l E f) (scalar l E L ι Y) (scalar l E L ι X) (pull l L f)
    (kappa l E L ι f) ((comparisons l).sigma E L ι Y) ((comparisons l).c L f)
```

```lean
def rightRoute {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor l E Y ⋙ pull l E f ⋙ scalar l E L ι X ≅
      (scalar l E L ι Y).prod (scalar l E L ι Y) ⋙
        (pull l L f).prod (pull l L f) ⋙ tensor l L X :=
  rightRouteCore (tensor l E Y) (tensor l E X) (tensor l L X)
    (pull l E f) (scalar l E L ι Y) (scalar l E L ι X) (pull l L f)
    (kappa l E L ι f) ((comparisons l).sigma E L ι X) ((comparisons l).c E f)
```

```lean
theorem unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    UnitSquare (pull l E f) (scalar l E E (AlgHom.id ℚ_[l] E) Y)
      (scalar l E E (AlgHom.id ℚ_[l] E) X) (kappa l E E (AlgHom.id ℚ_[l] E) f)
      (scalarUnit l E Y) (scalarUnit l E X) ∧
    TensorUnitSquare (tensor l E Y) (scalar l E E (AlgHom.id ℚ_[l] E) Y)
      ((comparisons l).sigma E E (AlgHom.id ℚ_[l] E) Y) (scalarUnit l E Y)
```

```lean
theorem composition (F : Type u) [Field F] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F] (j : L →ₐ[ℚ_[l]] F)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CompositionSquare (pull l E f) (pull l L f) (pull l F f)
      (scalar l E L ι Y) (scalar l L F j Y) (scalar l E F (j.comp ι) Y)
      (scalar l E L ι X) (scalar l L F j X) (scalar l E F (j.comp ι) X)
      (kappa l E L ι f) (kappa l L F j f) (kappa l E F (j.comp ι) f)
      (scalarComp l E L ι F j Y) (scalarComp l E L ι F j X) ∧
    TensorCompositionSquare (tensor l E Y) (tensor l L Y) (tensor l F Y)
      (scalar l E L ι Y) (scalar l L F j Y) (scalar l E F (j.comp ι) Y)
      (scalarComp l E L ι F j Y) ((comparisons l).sigma E L ι Y)
      ((comparisons l).sigma L F j Y) ((comparisons l).sigma E F (j.comp ι) Y)
```

```lean
def IsTensorModelNormalized (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l E W)
    (realization : integralCompletedTensor.{u, u} l E W ≅ S.reduction.prod S.reduction ⋙
      S.systemClosed.tensor ⋙ coefficientSequenceLimit.{u, u} l E W) : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory)
    (C D : Complex l E W)
    (eC : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (eD : S.reduction.obj (DerivedCategory.Q.obj Q.obj) ≅ DerivedCategory.Q.obj D)
    (κC : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj P.obj)
    (κD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj Q.obj)
    (hC : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E W) C)
    (hD : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E W) D),
    CoefficientReductionPresentation.{u, u} l E W S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C eC κC →
    CoefficientReductionPresentation.{u, u} l E W S.toCoefficientDerivedSystemReduction
      Q.obj Q.property.1 D eD κD →
    ∃ q : (((coefficientSequenceRestriction.{u, u} l E W).mapHomologicalComplex (.up ℤ)).obj
        ((tensor l E W).obj (C, D))).asFunctor ≅
      (integralOperationsTensorTowerFunctor.{u, u} l E W).obj (P.obj, Q.obj),
      (∀ (n : ℕ) (p r : ℤ) (U : W.ProEtᵒᵖ)
        (x : (C.X p).val.obj (op (n, U.unop)))
        (y : (D.X r).val.obj (op (n, U.unop))),
        ((q.hom.app (op n)).f (p + r)).val.app U
          (integralComparisonRestrictedSection.{u, u} l E W
            (((tensor l E W).obj (C, D)).X (p + r)) n U
            (generator l E W C D p r (op (n, U.unop)) x y)) =
          integralTensorGenerator l E W P.obj Q.obj n p r U
            (((κC n).hom.f p).val.app U (coefficientEvaluationSection.{u, u} l E W (C.X p) n U x))
            (((κD n).hom.f r).val.app U
              (coefficientEvaluationSection.{u, u} l E W (D.X r) n U y))) ∧
      FiveStepEquation
        (realization.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
        ((coefficientSequenceLimit.{u, u} l E W).map
          (S.systemClosed.tensor.map (Prod.mkHom eC.hom eD.hom)))
        ((coefficientSequenceLimit.{u, u} l E W).map
          ((S.systemTensorModel.iso _ _ _ C D hC hD).inv))
        ((integralComparisonRoosBridge.{u, u} l E W ρ
          ((tensor l E W).obj (C, D))).hom)
        (DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom))
        ((integralCompletedTensorComparison.{u, u} l E W).hom.app (P, Q))
```

## Users

The downstream.py textual search over all changed public names lists the modules below.
Most matches are names in other namespaces. All mathematical arguments are unchanged.
No consumer adaptation is included. The concrete consumers are checked separately.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.DeligneLaumon.ContinuousCoefficientGeometricCoherence | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.DeligneLaumon.FiniteStageFibreVanishing | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | C9 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicCommonStageHomTranspose | Q5 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicFibreComparisonData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicFiniteRealizationCocone | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | X2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicNormalizedFibreCommonStage | G6 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicNormalizedFibreData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicNormalizedFibrePullback | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicNormalizedFibreScalar | K4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicPurityRootComparisons | A2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicPurityScalarNaturality | R2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicPurityTwistReduction | X9 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicRealizationFamilyData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | B9 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | P3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdmissibleHomSubstitution | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AffineCommonProjectiveCharts | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AffineDiagonalIntegrationOrientation | P2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AffineLineCompositeTranspose | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | K4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AffineSpacePurityComposition | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AffineSpaceThomMap | E3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | D4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.AutomorphismConstructibleStageEquivalence | A4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.BaseChangedLineTraceEvaluation | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | F7 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.BrownTowerBoundedTransport | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.BrownTowerGeometricTransport | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | Q1 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CanonicalTateArrowNaturality | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ChartExceptionalCounitEquation | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ClassicalLisseWeilFrontierData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ClassicalLocalFrobeniusData | F6 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ClassicalLocalFrobeniusIterateComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ClassicalRawLisseCoherence | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ClassicalRawLisseCommonRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ClassicalRawLisseCommonSystem | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ClassicalRawLisseOperations | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ClassicalRawLissePointFibres | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ClassicalRawLisseRealizationData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ClassicalRawLisseScalarCoherence | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ClassicalSystemRawLisseRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ClassicalTwoFibreScalarData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ClopenSystemFiniteRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CoefTowerCoaugmentation | R5 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CoefficientDualModelTransport | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CoefficientEvaluationNaturality | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CoefficientGammaRepresentatives | V7 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CoherentRationalPullbackIdentity | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CommonStagePointReturn | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CommonStageRestrictionTensorDescent | U6 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompactSupportCondensedRealization | Y5 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompactSupportLimitEquationRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompactSupportProjectionFormula | F4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompactSupportReductionAdjoint | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompactSupportScalarCoordinates | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompactSupportScalarLimitReduction | E2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompactSupportScalarProjectionIdentification | Y3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompactSupportScalarShiftNormalization | Q2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompactSupportStrictScalarComposition | D7 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompactSupportSystemTransposeNormalization | J2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompactSupportTowerReduction | J9 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompleteProjectionMateDescent | C8 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompletedComparisonQuotientRealization | unclaimed | Uses the same comparisons and composites; unchanged consumer compile requested. |
| Sheaf.Paper.CompletedComparisonQuotientRealizationDefs | unclaimed | Uses the same comparisons and composites; unchanged consumer compile requested. |
| Sheaf.Paper.CompletedHomScalarTranspose | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompletedInverseImageScalarCounit | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | U2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompletedUnitAdmissible | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompletedUnitMultiplicationComponents | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompletedUnitPullbackData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompletedUnitPullbackTower | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompletedUnitReduction | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompletedUnitScalarNaturality | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompletedUnitStrictComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CompositionTensorMate | G8 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | D6 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ConcreteProjectionFieldDescent | A2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ConcreteProjectionReductionSquare | D7 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ConstantExtensionSheetHeartData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ConstantGeometricStalkUnit | E6 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ConstantWeilStructure | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ConstructibleMateCoherence | N1 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ConstructibleProjectiveChartRefinement | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CoordinateSectionArrows | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CoordinateSectionProjection | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | R2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | K9 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.DerivedTensorRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.DiagonalAffineTraceCoordinates | S3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.DiagonalOrdinaryOrientationGluing | N4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.DiagonalOrdinaryOrientationNormalization | U5 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.DiagonalOrientationRefinement | T8 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.DifferenceCoordinateSectionIdentifications | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.DualBaseChange | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.DualizingSigmaCocycleLocality | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y7 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.EvenLineProductIntegrationMaps | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ExchangeFunctoriality | R6 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ExplicitExceptionalPreservation | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FdCompletionInverseScalarCoherence | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FdIntegralInverseScalarCocycle | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FdPullbackAugmentationCounitMatching | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FdPullbackSignedShiftWordTransport | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FieldShriekCompositionQcqs | R3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FieldShriekSystemCoherence | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FieldShriekSystemModels | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | V6 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | P8 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteCompactSupportEvaluationRefinement | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteOrientationReduction | M6 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteProjectionExchangeData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteProjectionOpenAssembly | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteProjectionRefinementLeft | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteProjectionTensorSquare | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteRationalHeartComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteReductionAffineOrientation | A4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteReductionComparisons | C3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteReductionOfPurity | Q3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteRestrictionDiagramNaturality | S2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteSheafH0Augmentation | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteTargetChangeCoherence | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteTorStability | J2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FiniteTripleProductNormalForms | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FixProjectionCompactificationComparison | J2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FourierArtinSchreierProperties | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FrameworkPbcComparisonData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FrameworkPbcComparisonSystem | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FrameworkPbcIntegralComparisonLaws | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FrameworkPbcPullbackScalarBridge | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FrameworkPbcRawComparisonData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FrameworkPbcRawComparisonLaws | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | Y5 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | H5 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FrobeniusPullbackOrdinaryExchange | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.FrobeniusSquareExchange | H6 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.GeneralChartComparisons | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.GeometricOperations | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.GlobalVerdierDualityData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IdentificationCoefficientTransport | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IdentityCompactificationSystemMate | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IntegralClosedSupportNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IntegralComparisonSystemData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IntegralDirectImageTower | B8 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IntegralLissePullbackNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IntegralOpenSupportNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | G8 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IntegralPullbackReductionCounit | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IntegralPullbackResolutionMatching | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IntegralReconstructionComparisons | D8 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IntegralScalarIsomorphismExchange | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IntegralSupportFunctorNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IntegralSupportNormalizationData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IntegrationExponentTransposeTransport | V7 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IsomorphismDerivedPullback | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IsomorphismFiniteExchangeCoherence | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IsomorphismScalarComparisonAgreement | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.IteratedReturnTransportScalarCalculus | H3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.LisseFieldNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.LisseLatticeHeartLiftData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.LissePointNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.LissePointSectionsRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.LisseRationalRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.LisseTensorPullbackRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.LisseTensorPullbackRealizationData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | X3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.LocalFrobeniusLargeCoefficients | U9 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.LocalizationScalarUnit | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.MiddleExchangeProjectionBaseChange | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.MixedCupCoefficientChange | E5 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.MixedCupNormalizedScalars | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.NormalizedPullbackCoherence | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.NormalizedPullbackObjects | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.OpenExceptionalScalarLocality | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.OpenScalarCounitSquare | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.OrderedAffineTransposeProjection | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.OrientationPerfectLines | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.OrientedDoubleHomCancellation | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.OrientedPerfectDuality | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PerfectDualPairAndTateStability | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PfReductionProperOpenIdentities | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PodCompletionReindexCoefficientTransition | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PodCounitScalarWordCoordinates | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PodHomChainCounitFormula | H1 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PodReconstructionRawRationalNaturality | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PodReindexingCompletedEvaluationReflection | Y6 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PodReindexingCompletionUnitTensor | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PodReindexingHomCoefficientDescent | J4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PointAutomorphismDerivedTransportInverse | V2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PointAutomorphismTransportScalarExtension | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PointExactDerivedModel | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PointFrobeniusTransportNormalization | G7 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PointRealizationStandardCohomology | C4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PointRestrictionWholeRoosSquare | G4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PointScalarCompatibleTransportTransfer | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PointSignedCyclotomicAction | A3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PointSystemNormalizedComparisonData | H3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | W8 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PointSystemRoosTransport | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PointSystemTransportDescent | X5 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PointTateFiberCoefficientComparisons | T8 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PointWeilPairingRealization | C3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ProEtaleScalarMateNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ProductExchangeCounitCoordinates | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ProductOpenTensorProjection | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ProjectionFiniteReduction | H8 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ProjectionFormulaCoherence | Y5 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ProjectionPurityAgreement | N2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ProjectionReductionPresentation | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | P4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ProjectionWeilTensorDomainBridge | X6 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PullbackIdentitiesScalarExtension | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PurIntegralRepresentingPair | B9 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PurIntegralSupportComparisonData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | V6 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PurStrictIntegralExchangeNormalization | T1 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PurTateUnitFlatModelDomains | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PurityConjugatesTowerReduction | N2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.PuritySectionRestrictionData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RationalCoefficientCategoryComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RationalCoverReflectsIso | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RationalEvaluationCover | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RationalOrdinaryCohomologyTensor | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RationalPullbackFibreComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RationalScalarCompletionUnitSquare | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | Z9 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ReindexingSystemHomReductionSquare | T4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RelativeKummerSiteNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | Q8 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | X7 | Own item; exact four fields and equations retained, with equivalent normalization predicate. |
| Sheaf.Paper.SemilinearExchangeCubeCoherence | X5 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SemilinearExchangeReindexing | U2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SemilinearExchangeReindexingData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SfFieldMateDomain | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SfFrameworkThetaShiftCompatibility | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SfNormalizedRationalClosedComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SfNormalizedRationalWeilSquares | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | R2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | U9 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SfPackageQbarAdjunctionMapDescent | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SfQbarLocalizationCommonStage | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SfQbarLocalizationFiniteData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SfRationalLocalizationOrthogonality | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | D8 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SmoothPurityMap | B4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SmoothPurityScalarExtension | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | H4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | A7 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | C8 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SmoothPurityTowerGamma | Q4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SmoothPurityTowerGluing | F3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | B2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.StrictDirectImageMixedUnit | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.StrictLineHeartAssembly | R9 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.StrictReductionCompactSupportNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SystemClopenMateIdentification | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SystemOperationExchangeRealization | G2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.SystemTensorPresentationIdentification | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TensorAdjunctionExchange | C3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TensorHeartSpecialization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TensorHomExchange | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TowerAdjointCompositorRealization | M4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TowerReductionShiftCompatibility | W9 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | H9 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | F3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TraceStalkCompositorTowerData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TraceStalkCompositorTowerRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TwistFrobeniusScalar | J7 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.TwistedPullbackTowerDomain | F8 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.UnboundedCoefficientPullbackModel | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.UnshiftedLineUnitTower | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | Q1 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.VectorIntegrationChartCoordinates | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.VectorIntegrationSiteComparison | P5 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.VerdierCompositionMateNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.VerdierExchange | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.VerdierHomChainComposition | Y7 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.WfTensorCompletionFrobenius | J3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.WholeTowerIntegralPullbackComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | S4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ZlFrameworkOpenExchange | N2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ZlImmersionFilteredReductionTransport | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | P8 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ZlOpenCompactSupportRestriction | G7 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ZlOpenExtensionTExact | W4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ZlOpenWeilUnitEmptyFibre | S9 | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ZlSfPbcNormalizedHeartModel | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SecSmoothPurity.OpenScalarRestrictedTransposeExpansion | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SecSmoothPurity.ProEtaleCoefficientTowerNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SecSmoothPurity.ProEtaleProjectionMateIdentification | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SecSmoothPurity.ProEtaleScalarBalancingChain | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | C9 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SecSmoothPurity.ReductionExceptional | K5 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SecSmoothPurity.ScalarAssociatorConjugate | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SecSmoothPurity.SupportedScalarTorInterval | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.AmbientExactClopenComparison | R4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | H4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.AmbientUnderivedClopenPasting | S1 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.CoefficientDualizingClosedDescent | A4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.CompactifiedProperTowerExchange | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.CompletedProjectionExchangeRealization | P2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | U7 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.CompositionProjectionMate | U7 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.FiniteAdjunctionCoefficientUnitData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.FiniteExceptional | S2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.FiniteMappingAdjunctionData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.FrobeniusPointTransport | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.GeneratorReductionStatement | T7 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.IntegralBasicRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.IntegralBasicRealizationData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.IntegralComparisonRecursionLaws | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | Q9 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.IntegralExpressionCoefficientSquares | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.IntegralExpressionRecursion | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.IntegralRealizationAssemblyData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.IntegralSupportTowerNormalization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.KunnethFirstOpenSubstitution | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.KunnethSecondOpenSubstitution | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | A5 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.OpenInterchangeReductionSquares | E3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.ProductCompactificationIdentity | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.ProductSystemUniformRealizationDomain | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | C2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.ProjectionRefinementDescent | E2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.ProjectionSystemCoherence | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | J3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.RefinementProjectionCounit | T3 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.TensorAdjunctionReductionSquares | C2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.TensorHomTranspositionData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.TriangleProjectionNormalForm | T4 | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.VerdierExchangeData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.WeilSheaf.DualRealizationComparison | F2 | Textual match in other namespaces; no change in meaning. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | X5 | Textual match in other namespaces; no change in meaning. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.WeilSheaf.NativeExceptionalPointUnit | unclaimed | Textual match in other namespaces; no change in meaning. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed | Textual match in other namespaces; no change in meaning. |

## Status

landed 20261025T164754-L-1079185 2026-10-25 (merge of deliver/X7/Sheaf.Paper.ScalarExtensionTowerCoherence)
