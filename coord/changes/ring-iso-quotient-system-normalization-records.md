# SheafOfModules.QuotientIsoTransport normalization records

## Reason

The concrete dependent records generate expensive recursors and projection types
containing the entire sheaf, abelian and derived-category instance stacks. Full
proof compilation exceeded the 60-second file limit. Parameterize the three
records by their data types and normalization predicates, and instantiate them
through the existing public names. Named predicates retain every original clause.
The replacement does not change the mathematical assertion, its quantifiers,
its data or its normalization requirements. Additivity remains an instance for
recorded reductions. No Challenge target signature is edited.

`transport` is also a named definition rather than a reducible abbreviation. Its
body remains exactly inverse scalar restriction. Its additive and finite limit
and colimit preservation instances are stated and proved explicitly, so instance
search can use the named functor without expanding scalar restriction repeatedly.
`moduleWeakSheafify` exposes the existing sheafification adjunction directly; it
adds no assumption.

## Old

```lean
structure ScalarSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (A : SystemScalarModel a) (B : SystemScalarModel b) where
  restriction : restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) ⋙
      transport e ≅ transport e' ⋙
        restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)
  ordinary : A.model.E ⋙ transport e' ≅ transport e ⋙ B.model.E
  derived : A.model.T ⋙ (transport e').mapDerivedCategory ≅
    (transport e).mapDerivedCategory ⋙ B.model.T
  /-- All normalization and coherence equations, in the order of the statement. -/
  conditions :
    (∀ (M : Modules R') (U : Cᵒᵖ) (x : M.val.obj U),
      (restriction.hom.app M).val.app U x = x) ∧
    (∀ (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (r : R'.obj.obj U),
      (ordinary.hom.app M).val.app U (systemModelTmul A.model M U r x) =
        systemModelTmul B.model ((transport e).obj M) U (e'.hom.hom.app U r) x) ∧
    (∀ (M : Modules R) (N : Modules R') (f : A.model.E.obj M ⟶ N),
      B.ordinaryAdj.homEquiv _ _ (ordinary.inv.app M ≫ (transport e').map f) =
        (transport e).map (A.ordinaryAdj.homEquiv _ _ f) ≫ restriction.hom.app N) ∧
    (∀ (P : CochainComplex (Modules R) ℤ),
      derived.hom.app (DerivedCategory.Q.obj P) ≫
          B.model.T.map ((transport e).mapDerivedCategoryFactors.hom.app P) ≫
          B.model.ε.app (((transport e).mapHomologicalComplex (.up ℤ)).obj P) =
        (transport e').mapDerivedCategory.map (A.model.ε.app P) ≫
          (transport e').mapDerivedCategoryFactors.hom.app
            ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)) ∧
    (∀ (M : DerivedCategory (Modules R)) (N : DerivedCategory (Modules R'))
      (f : A.model.T.obj M ⟶ N),
      B.adjunction.homEquiv _ _ (derived.inv.app M ≫ (transport e').mapDerivedCategory.map f) =
        (transport e).mapDerivedCategory.map (A.adjunction.homEquiv _ _ f) ≫
          (derivedSquare a b e e' restriction).hom.app N)

/-- The actual strict reduction, with its sheafified pure tensors, all horizontal
maps and the universal derived reduction into the ordinary derived system category.
Source: Stacks 03EK, 06YY; sequence-site refinement of def-pur-section-invariant
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
structure Reduction (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) where
  ordinary : Modules c.pt ⥤ StrictRingSystem B
  [additive : ordinary.Additive]
  evaluation : ∀ n : ℕ, ordinary ⋙ systemEvaluation B n ≅ (A (c.π.app (op n))).model.E
  derived : DerivedCategory (Modules c.pt) ⥤ DerivedCategory (StrictRingSystem B)
  counit : DerivedCategory.Q ⋙ derived ⟶
    ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  derivedEvaluation : ∀ n : ℕ,
    derived ⋙ derivedSystemEvaluation B n ≅ (A (c.π.app (op n))).model.T
  /-- All normalization and coherence equations, in the order of the statement. -/
  conditions :
    (∀ (M : Modules c.pt) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
      (r : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
      ((evaluation m).hom.app M).val.app U
        (((ordinary.obj M).transition h).val.app U
          (((evaluation n).inv.app M).val.app U
            (systemModelTmul (A (c.π.app (op n))).model M U r x))) =
        systemModelTmul (A (c.π.app (op m))).model M U
          ((B.map (homOfLE h).op).hom.app U r) x) ∧
    (derived.IsLeftDerivedFunctor counit (HomologicalComplex.quasiIso _ (.up ℤ))) ∧
    (Functor.HasPointwiseLeftDerivedFunctor
      (ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        (HomologicalComplex.quasiIso _ (.up ℤ))) ∧
    (∀ (P : CochainComplex (Modules c.pt) ℤ),
      P.IsKFlatIndependentCoefficients → (∀ i : ℤ, IsFlatOnSite (R := c.pt) (P.X i)) →
        IsIso (counit.app P)) ∧
    (∀ (n : ℕ) (P : CochainComplex (Modules c.pt) ℤ),
      (derivedEvaluation n).hom.app (DerivedCategory.Q.obj P) ≫
          (A (c.π.app (op n))).model.ε.app P =
        (derivedSystemEvaluation B n).map (counit.app P) ≫
          (systemEvaluation B n).mapDerivedCategoryFactors.hom.app
            ((ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (evaluation n) (.up ℤ)).hom.app P))

attribute [instance] Reduction.additive


structure CoherentTransport (R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (a : R ≅ S)
    (c : Cone R) (d : Cone S) (e : c.pt ≅ d.pt)
    (A : SystemScalarAssignment (J := J)) where
  equivalence : StrictRingSystem R ≌ StrictRingSystem S
  [additive : equivalence.functor.Additive]
  [limits : PreservesFiniteLimits equivalence.functor]
  [colimits : PreservesFiniteColimits equivalence.functor]
  derivedEquivalence : DerivedCategory (StrictRingSystem R) ≌ DerivedCategory (StrictRingSystem S)
  localization : DerivedCategory.Q ⋙ derivedEquivalence.functor ≅
    equivalence.functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  level : ∀ n : ℕ, equivalence.functor ⋙ systemEvaluation S n ≅
    systemEvaluation R n ⋙ transport (a.app (op n))
  derivedLevel : ∀ n : ℕ, derivedEquivalence.functor ⋙ derivedSystemEvaluation S n ≅
    derivedSystemEvaluation R n ⋙ (transport (a.app (op n))).mapDerivedCategory
  reductionR : Reduction R c A
  reductionS : Reduction S d A
  reduction : reductionR.ordinary ⋙ equivalence.functor ≅ transport e ⋙ reductionS.ordinary
  derivedReduction : reductionR.derived ⋙ derivedEquivalence.functor ≅
    (transport e).mapDerivedCategory ⋙ reductionS.derived
  projection : ∀ n : ℕ, ScalarSquare (c.π.app (op n)) (d.π.app (op n)) e (a.app (op n))
    (A (c.π.app (op n))) (A (d.π.app (op n)))
  quotient : ∀ {m n : ℕ} (h : m ≤ n),
    ScalarSquare (R.map (homOfLE h).op) (S.map (homOfLE h).op)
      (a.app (op n)) (a.app (op m))
      (A (R.map (homOfLE h).op)) (A (S.map (homOfLE h).op))
  /-- All normalization and coherence equations, in the order of the statement. -/
  conditions :
    (∀ (M : StrictRingSystem R) (n : ℕ),
      (equivalence.functor.obj M).level n = (transport (a.app (op n))).obj (M.level n)) ∧
    (∀ (M : StrictRingSystem R) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ),
      HEq (fun x ↦ ((equivalence.functor.obj M).transition h).val.app U x)
        (fun x ↦ (M.transition h).val.app U x)) ∧
    (∀ {M N : StrictRingSystem R} (f : M ⟶ N) (n : ℕ) (U : Cᵒᵖ),
      HEq (fun x ↦ ((equivalence.functor.map f).app n).val.app U x)
        (fun x ↦ (f.app n).val.app U x)) ∧
    (derivedEquivalence.functor = equivalence.functor.mapDerivedCategory) ∧
    (HEq localization equivalence.functor.mapDerivedCategoryFactors) ∧
    (∀ (n : ℕ) (M : StrictRingSystem R) (U : Cᵒᵖ) (x : M.level n |>.val.obj U),
      HEq (((level n).inv.app M).val.app U x) x) ∧
    (∀ (n : ℕ) (P : CochainComplex (StrictRingSystem R) ℤ),
      (derivedLevel n).hom.app (DerivedCategory.Q.obj P) ≫
          (transport (a.app (op n))).mapDerivedCategory.map
            ((systemEvaluation R n).mapDerivedCategoryFactors.hom.app P) ≫
          (transport (a.app (op n))).mapDerivedCategoryFactors.hom.app
            (((systemEvaluation R n).mapHomologicalComplex (.up ℤ)).obj P) =
        (derivedSystemEvaluation S n).map (localization.hom.app P) ≫
          (systemEvaluation S n).mapDerivedCategoryFactors.hom.app
            ((equivalence.functor.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (level n) (.up ℤ)).hom.app P)) ∧
    (∀ (M : Modules c.pt) (n : ℕ) (U : Cᵒᵖ)
      (r : (R.obj (op n)).obj.obj U) (x : M.val.obj U),
      HEq (((systemEvaluation S n).map (reduction.hom.app M)).val.app U
        (((level n).inv.app (reductionR.ordinary.obj M)).val.app U
          (((reductionR.evaluation n).inv.app M).val.app U
            (systemModelTmul (A (c.π.app (op n))).model M U r x))))
        (((reductionS.evaluation n).inv.app ((transport e).obj M)).val.app U
          (systemModelTmul (A (d.π.app (op n))).model ((transport e).obj M) U
            ((a.app (op n)).hom.hom.app U r) x))) ∧
    (∀ (P : CochainComplex (Modules c.pt) ℤ),
      derivedReduction.hom.app (DerivedCategory.Q.obj P) ≫
          reductionS.derived.map ((transport e).mapDerivedCategoryFactors.hom.app P) ≫
          reductionS.counit.app (((transport e).mapHomologicalComplex (.up ℤ)).obj P) =
        derivedEquivalence.functor.map (reductionR.counit.app P) ≫
          localization.hom.app ((reductionR.ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex reduction (.up ℤ)).hom.app P)) ∧
    (∀ (n : ℕ) (M : systemLevel R n),
      (transport (a.app (op n))).map
          (((systemTensorCoherence A).ordinaryUnit R n).hom.app M) =
        (quotient (Nat.le_refl n)).ordinary.hom.app M ≫
          ((systemTensorCoherence A).ordinaryUnit S n).hom.app
            ((transport (a.app (op n))).obj M)) ∧
    (∀ {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) (M : systemLevel R n),
      (transport (a.app (op l))).map
          (((systemTensorCoherence A).ordinaryAssoc R h k).hom.app M) ≫
          (quotient (h.trans k)).ordinary.hom.app M =
        (quotient h).ordinary.hom.app ((systemTensor A R k).obj M) ≫
          (systemTensor A S h).map ((quotient k).ordinary.hom.app M) ≫
          ((systemTensorCoherence A).ordinaryAssoc S h k).hom.app
            ((transport (a.app (op n))).obj M)) ∧
    (∀ (n : ℕ) (M : DerivedCategory (systemLevel R n)),
      (transport (a.app (op n))).mapDerivedCategory.map
          (((systemTensorCoherence A).derivedUnit R n).hom.app M) =
        (quotient (Nat.le_refl n)).derived.hom.app M ≫
          ((systemTensorCoherence A).derivedUnit S n).hom.app
            ((transport (a.app (op n))).mapDerivedCategory.obj M)) ∧
    (∀ {l m n : ℕ} (h : l ≤ m) (k : m ≤ n)
      (M : DerivedCategory (systemLevel R n)),
      (transport (a.app (op l))).mapDerivedCategory.map
          (((systemTensorCoherence A).derivedAssoc R h k).hom.app M) ≫
          (quotient (h.trans k)).derived.hom.app M =
        (quotient h).derived.hom.app ((systemDerivedTensor A R k).obj M) ≫
          (systemDerivedTensor A S h).map ((quotient k).derived.hom.app M) ≫
          ((systemTensorCoherence A).derivedAssoc S h k).hom.app
            ((transport (a.app (op n))).mapDerivedCategory.obj M)) ∧
    (∀ (n : ℕ) (M : DerivedCategory (StrictRingSystem R)),
      adjointTransition A R (Nat.le_refl n) M =
        ((systemTensorCoherence A).derivedUnit R n).hom.app ((derivedSystemEvaluation R n).obj M)) ∧
    (∀ (n : ℕ) (M : DerivedCategory (StrictRingSystem S)),
      adjointTransition A S (Nat.le_refl n) M =
        ((systemTensorCoherence A).derivedUnit S n).hom.app ((derivedSystemEvaluation S n).obj M)) ∧
    (∀ {l m n : ℕ} (h : l ≤ m) (k : m ≤ n)
      (M : DerivedCategory (StrictRingSystem R)),
      ((systemTensorCoherence A).derivedAssoc R h k).inv.app ((derivedSystemEvaluation R n).obj M) ≫
          (systemDerivedTensor A R h).map (adjointTransition A R k M) ≫
          adjointTransition A R h M = adjointTransition A R (h.trans k) M) ∧
    (∀ {l m n : ℕ} (h : l ≤ m) (k : m ≤ n)
      (M : DerivedCategory (StrictRingSystem S)),
      ((systemTensorCoherence A).derivedAssoc S h k).inv.app ((derivedSystemEvaluation S n).obj M) ≫
          (systemDerivedTensor A S h).map (adjointTransition A S k M) ≫
          adjointTransition A S h M = adjointTransition A S (h.trans k) M) ∧
    (∀ (M : DerivedCategory (StrictRingSystem R)) {m n : ℕ} (h : m ≤ n),
      (quotient h).derived.inv.app ((derivedSystemEvaluation R n).obj M) ≫
          (transport (a.app (op m))).mapDerivedCategory.map (adjointTransition A R h M) ≫
          (derivedLevel m).inv.app M =
        (systemDerivedTensor A S h).map ((derivedLevel n).inv.app M) ≫
          adjointTransition A S h (derivedEquivalence.functor.obj M)) ∧
    (∀ (M : DerivedCategory (StrictRingSystem R)),
      (∀ (m n : ℕ) (h : m ≤ n), IsIso (adjointTransition A R h M)) ↔
        ∀ (m n : ℕ) (h : m ≤ n),
          IsIso (adjointTransition A S h (derivedEquivalence.functor.obj M)))

```

## New

```lean
/-- Use the specified sheafification adjunction directly.
Source: Stacks 03DA (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
theorem moduleWeakSheafify : HasWeakSheafify J AddCommGrpCat.{w} :=
  HasSheafify.isRightAdjoint

attribute [local instance 20000] moduleWeakSheafify

/-- Module sheaves in the coefficient universe, using the recorded category.
Source: Stacks 03DA (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
abbrev Modules (R : Sheaf J CommRingCat.{w}) :=
  ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)

/-- Scalar transport is literally restriction along the inverse ring isomorphism.
Source: Stacks 03CZ (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def transport {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) : Modules R ⥤ Modules S :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map a.inv)

/-- Additivity for inverse scalar restriction.
Source: Stacks 03D7 (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
instance transportAdditive {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    (transport a).Additive := by
  unfold transport
  infer_instance

/-- Preservation of finite limits for inverse scalar restriction.
Source: Stacks 03D7 (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
instance transportLimits {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    PreservesFiniteLimits (transport a) := by
  unfold transport
  infer_instance

/-- Preservation of finite colimits for inverse scalar restriction.
Source: Stacks 03D7 (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
instance transportColimits {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    PreservesFiniteColimits (transport a) := by
  unfold transport
  infer_instance

attribute [local instance 21000] transportAdditive transportLimits transportColimits

/-- The canonical derived comparison for an exact commuting square.
Source: Stacks 015F (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def derivedSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (rho : restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) ⋙
        transport e ≅ transport e' ⋙
          restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)) :
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).mapDerivedCategory ⋙
        (transport e).mapDerivedCategory ≅
      (transport e').mapDerivedCategory ⋙
        (restrictScalars
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso rho ≪≫ Functor.mapDerivedCategoryCompIso _ _

/-- Abstract comparison data with its specified normalization predicate.
Source: Stacks 03D7, 015F and 06YY
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
structure ScalarComparisonData
    (X0 : Sort*)
    (X1 : Sort*)
    (X2 : Sort*)
    (P : ∀ (restriction : X0) (ordinary : X1) (derived : X2), Prop) where
  restriction : X0
  ordinary : X1
  derived : X2
  conditions : P restriction ordinary derived

/-- Normalized scalar comparison for one commuting coefficient square. The Hom
identities identify the entire adjunctions and therefore both their units and counits.
Source: Stacks 03D7, 03EK, 06YY, 07A6
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def ScalarSquareConditions {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (A : SystemScalarModel a) (B : SystemScalarModel b)
    (restriction : restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) ⋙
      transport e ≅ transport e' ⋙
        restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b))
    (ordinary : A.model.E ⋙ transport e' ≅ transport e ⋙ B.model.E)
    (derived : A.model.T ⋙ (transport e').mapDerivedCategory ≅
    (transport e).mapDerivedCategory ⋙ B.model.T) : Prop :=
  (∀ (M : Modules R') (U : Cᵒᵖ) (x : M.val.obj U),
      (restriction.hom.app M).val.app U x = x) ∧
    (∀ (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (r : R'.obj.obj U),
      (ordinary.hom.app M).val.app U (systemModelTmul A.model M U r x) =
        systemModelTmul B.model ((transport e).obj M) U (e'.hom.hom.app U r) x) ∧
    (∀ (M : Modules R) (N : Modules R') (f : A.model.E.obj M ⟶ N),
      B.ordinaryAdj.homEquiv _ _ (ordinary.inv.app M ≫ (transport e').map f) =
        (transport e).map (A.ordinaryAdj.homEquiv _ _ f) ≫ restriction.hom.app N) ∧
    (∀ (P : CochainComplex (Modules R) ℤ),
      derived.hom.app (DerivedCategory.Q.obj P) ≫
          B.model.T.map ((transport e).mapDerivedCategoryFactors.hom.app P) ≫
          B.model.ε.app (((transport e).mapHomologicalComplex (.up ℤ)).obj P) =
        (transport e').mapDerivedCategory.map (A.model.ε.app P) ≫
          (transport e').mapDerivedCategoryFactors.hom.app
            ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)) ∧
    (∀ (M : DerivedCategory (Modules R)) (N : DerivedCategory (Modules R'))
      (f : A.model.T.obj M ⟶ N),
      B.adjunction.homEquiv _ _ (derived.inv.app M ≫ (transport e').mapDerivedCategory.map f) =
        (transport e).mapDerivedCategory.map (A.adjunction.homEquiv _ _ f) ≫
          (derivedSquare a b e e' restriction).hom.app N)

/-- Normalized scalar comparison for one commuting coefficient square. The Hom
identities identify the entire adjunctions and therefore both their units and counits.
Source: Stacks 03D7, 03EK, 06YY, 07A6
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
abbrev ScalarSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (A : SystemScalarModel a) (B : SystemScalarModel b) :=
  ScalarComparisonData
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) ⋙
      transport e ≅ transport e' ⋙
        restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b))
    (A.model.E ⋙ transport e' ≅ transport e ⋙ B.model.E)
    (A.model.T ⋙ (transport e').mapDerivedCategory ≅
    (transport e).mapDerivedCategory ⋙ B.model.T)
    (fun restriction ordinary derived ↦
      ScalarSquareConditions a b e e' A B  restriction ordinary derived)

/-- Abstract comparison data with its specified normalization predicate.
Source: Stacks 03D7, 015F and 06YY
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
structure ReductionComparisonData
    (X0 : Sort*)
    (X1 : ∀ (ordinary : X0), Sort*)
    (X2 : ∀ (ordinary : X0), Sort*)
    (X3 : Sort*)
    (X4 : ∀ (ordinary : X0) (additive : X1 ordinary) (derived : X3), Sort*)
    (X5 : ∀ (derived : X3), Sort*)
    (P : ∀ (ordinary : X0) (additive : X1 ordinary) (evaluation : X2 ordinary)
      (derived : X3) (counit : X4 ordinary additive derived)
      (derivedEvaluation : X5 derived), Prop) where
  ordinary : X0
  additive : X1 ordinary
  evaluation : X2 ordinary
  derived : X3
  counit : X4 ordinary additive derived
  derivedEvaluation : X5 derived
  conditions : P ordinary additive evaluation derived counit derivedEvaluation

/-- The actual strict reduction, with its sheafified pure tensors, all horizontal
maps and the universal derived reduction into the ordinary derived system category.
Source: Stacks 03EK, 06YY; sequence-site refinement of def-pur-section-invariant
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def ReductionConditions (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J))
    (ordinary : Modules c.pt ⥤ StrictRingSystem B)
    [additive : ordinary.Additive]
    (evaluation : ∀ n : ℕ, ordinary ⋙ systemEvaluation B n ≅ (A (c.π.app (op n))).model.E)
    (derived : DerivedCategory (Modules c.pt) ⥤ DerivedCategory (StrictRingSystem B))
    (counit : DerivedCategory.Q ⋙ derived ⟶
    ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (derivedEvaluation : ∀ n : ℕ,
    derived ⋙ derivedSystemEvaluation B n ≅ (A (c.π.app (op n))).model.T) : Prop :=
  (∀ (M : Modules c.pt) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
      (r : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
      ((evaluation m).hom.app M).val.app U
        (((ordinary.obj M).transition h).val.app U
          (((evaluation n).inv.app M).val.app U
            (systemModelTmul (A (c.π.app (op n))).model M U r x))) =
        systemModelTmul (A (c.π.app (op m))).model M U
          ((B.map (homOfLE h).op).hom.app U r) x) ∧
    (derived.IsLeftDerivedFunctor counit (HomologicalComplex.quasiIso _ (.up ℤ))) ∧
    (Functor.HasPointwiseLeftDerivedFunctor
      (ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        (HomologicalComplex.quasiIso _ (.up ℤ))) ∧
    (∀ (P : CochainComplex (Modules c.pt) ℤ),
      P.IsKFlatIndependentCoefficients → (∀ i : ℤ, IsFlatOnSite (R := c.pt) (P.X i)) →
        IsIso (counit.app P)) ∧
    (∀ (n : ℕ) (P : CochainComplex (Modules c.pt) ℤ),
      (derivedEvaluation n).hom.app (DerivedCategory.Q.obj P) ≫
          (A (c.π.app (op n))).model.ε.app P =
        (derivedSystemEvaluation B n).map (counit.app P) ≫
          (systemEvaluation B n).mapDerivedCategoryFactors.hom.app
            ((ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (evaluation n) (.up ℤ)).hom.app P))

/-- The actual strict reduction, with its sheafified pure tensors, all horizontal
maps and the universal derived reduction into the ordinary derived system category.
Source: Stacks 03EK, 06YY; sequence-site refinement of def-pur-section-invariant
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
abbrev Reduction (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) :=
  ReductionComparisonData
    (Modules c.pt ⥤ StrictRingSystem B)
    (fun ordinary ↦
      ordinary.Additive)
    (fun ordinary ↦
      ∀ n : ℕ, ordinary ⋙ systemEvaluation B n ≅ (A (c.π.app (op n))).model.E)
    (DerivedCategory (Modules c.pt) ⥤ DerivedCategory (StrictRingSystem B))
    (fun ordinary additive derived ↦
      letI := additive; DerivedCategory.Q ⋙ derived ⟶
    ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (fun derived ↦
      ∀ n : ℕ,
    derived ⋙ derivedSystemEvaluation B n ≅ (A (c.π.app (op n))).model.T)
    (fun ordinary additive evaluation derived counit derivedEvaluation ↦
      ReductionConditions B c A (additive := additive) ordinary evaluation derived counit
        derivedEvaluation)

/-- The reduction's recorded additive structure.
Source: Stacks 03EK (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
instance Reduction.additive (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (D : Reduction B c A) : D.ordinary.Additive :=
  ReductionComparisonData.additive D

/-- The canonical adjoint of the actual derived transition. No inverse limit is used.
Source: Stacks 07A6 (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def adjointTransition (A : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n)
    (M : DerivedCategory (StrictRingSystem B)) :=
  ((systemDerivedTensorAdj A B h).homEquiv _ _).symm ((systemDerivedTransition B h).app M)

/-- Abstract comparison data with its specified normalization predicate.
Source: Stacks 03D7, 015F and 06YY
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
structure TransportComparisonData
    (X0 : Sort*)
    (X1 : ∀ (equivalence : X0), Sort*)
    (X2 : ∀ (equivalence : X0), Sort*)
    (X3 : ∀ (equivalence : X0), Sort*)
    (X4 : Sort*)
    (X5 : ∀ (equivalence : X0) (additive : X1 equivalence) (derivedEquivalence : X4), Sort*)
    (X6 : ∀ (equivalence : X0), Sort*)
    (X7 : ∀ (derivedEquivalence : X4), Sort*)
    (X8 : Sort*)
    (X9 : Sort*)
    (X10 : ∀ (equivalence : X0) (reductionR : X8) (reductionS : X9), Sort*)
    (X11 : ∀ (derivedEquivalence : X4) (reductionR : X8) (reductionS : X9), Sort*)
    (X12 : Sort*)
    (X13 : Sort*)
    (P : ∀ (equivalence : X0) (additive : X1 equivalence) (limits : X2 equivalence)
      (colimits : X3 equivalence) (derivedEquivalence : X4)
      (localization : X5 equivalence additive derivedEquivalence) (level : X6 equivalence)
      (derivedLevel : X7 derivedEquivalence) (reductionR : X8) (reductionS : X9)
      (reduction : X10 equivalence reductionR reductionS)
      (derivedReduction : X11 derivedEquivalence reductionR reductionS)
      (projection : X12) (quotient : X13), Prop) where
  equivalence : X0
  additive : X1 equivalence
  limits : X2 equivalence
  colimits : X3 equivalence
  derivedEquivalence : X4
  localization : X5 equivalence additive derivedEquivalence
  level : X6 equivalence
  derivedLevel : X7 derivedEquivalence
  reductionR : X8
  reductionS : X9
  reduction : X10 equivalence reductionR reductionS
  derivedReduction : X11 derivedEquivalence reductionR reductionS
  projection : X12
  quotient : X13
  conditions : P equivalence additive limits colimits derivedEquivalence localization level
    derivedLevel reductionR reductionS reduction derivedReduction projection quotient

/-- Complete strict-system coefficient transport, including the normalization of
localization, reduction and every adjoint transition.
Source: def-pur-section-invariant, finite-clopen expansion; Stacks 03D7 and 015F
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def CoherentTransportConditions (R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (a : R ≅ S)
    (c : Cone R) (d : Cone S) (e : c.pt ≅ d.pt)
    (A : SystemScalarAssignment (J := J))
    (equivalence : StrictRingSystem R ≌ StrictRingSystem S)
    [additive : equivalence.functor.Additive]
    [limits : PreservesFiniteLimits equivalence.functor]
    [colimits : PreservesFiniteColimits equivalence.functor]
    (derivedEquivalence :
      DerivedCategory (StrictRingSystem R) ≌ DerivedCategory (StrictRingSystem S))
    (localization : DerivedCategory.Q ⋙ derivedEquivalence.functor ≅
    equivalence.functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (level : ∀ n : ℕ, equivalence.functor ⋙ systemEvaluation S n ≅
    systemEvaluation R n ⋙ transport (a.app (op n)))
    (derivedLevel : ∀ n : ℕ, derivedEquivalence.functor ⋙ derivedSystemEvaluation S n ≅
    derivedSystemEvaluation R n ⋙ (transport (a.app (op n))).mapDerivedCategory)
    (reductionR : Reduction R c A)
    (reductionS : Reduction S d A)
    (reduction : reductionR.ordinary ⋙ equivalence.functor ≅ transport e ⋙ reductionS.ordinary)
    (derivedReduction : reductionR.derived ⋙ derivedEquivalence.functor ≅
    (transport e).mapDerivedCategory ⋙ reductionS.derived)
    (projection : ∀ n : ℕ, ScalarSquare (c.π.app (op n)) (d.π.app (op n)) e (a.app (op n))
    (A (c.π.app (op n))) (A (d.π.app (op n))))
    (quotient : ∀ {m n : ℕ} (h : m ≤ n),
    ScalarSquare (R.map (homOfLE h).op) (S.map (homOfLE h).op)
      (a.app (op n)) (a.app (op m))
      (A (R.map (homOfLE h).op)) (A (S.map (homOfLE h).op))) : Prop :=
  (∀ (M : StrictRingSystem R) (n : ℕ),
      (equivalence.functor.obj M).level n = (transport (a.app (op n))).obj (M.level n)) ∧
    (∀ (M : StrictRingSystem R) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ),
      HEq (fun x ↦ ((equivalence.functor.obj M).transition h).val.app U x)
        (fun x ↦ (M.transition h).val.app U x)) ∧
    (∀ {M N : StrictRingSystem R} (f : M ⟶ N) (n : ℕ) (U : Cᵒᵖ),
      HEq (fun x ↦ ((equivalence.functor.map f).app n).val.app U x)
        (fun x ↦ (f.app n).val.app U x)) ∧
    (derivedEquivalence.functor = equivalence.functor.mapDerivedCategory) ∧
    (HEq localization equivalence.functor.mapDerivedCategoryFactors) ∧
    (∀ (n : ℕ) (M : StrictRingSystem R) (U : Cᵒᵖ) (x : M.level n |>.val.obj U),
      HEq (((level n).inv.app M).val.app U x) x) ∧
    (∀ (n : ℕ) (P : CochainComplex (StrictRingSystem R) ℤ),
      (derivedLevel n).hom.app (DerivedCategory.Q.obj P) ≫
          (transport (a.app (op n))).mapDerivedCategory.map
            ((systemEvaluation R n).mapDerivedCategoryFactors.hom.app P) ≫
          (transport (a.app (op n))).mapDerivedCategoryFactors.hom.app
            (((systemEvaluation R n).mapHomologicalComplex (.up ℤ)).obj P) =
        (derivedSystemEvaluation S n).map (localization.hom.app P) ≫
          (systemEvaluation S n).mapDerivedCategoryFactors.hom.app
            ((equivalence.functor.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (level n) (.up ℤ)).hom.app P)) ∧
    (∀ (M : Modules c.pt) (n : ℕ) (U : Cᵒᵖ)
      (r : (R.obj (op n)).obj.obj U) (x : M.val.obj U),
      HEq (((systemEvaluation S n).map (reduction.hom.app M)).val.app U
        (((level n).inv.app (reductionR.ordinary.obj M)).val.app U
          (((reductionR.evaluation n).inv.app M).val.app U
            (systemModelTmul (A (c.π.app (op n))).model M U r x))))
        (((reductionS.evaluation n).inv.app ((transport e).obj M)).val.app U
          (systemModelTmul (A (d.π.app (op n))).model ((transport e).obj M) U
            ((a.app (op n)).hom.hom.app U r) x))) ∧
    (∀ (P : CochainComplex (Modules c.pt) ℤ),
      derivedReduction.hom.app (DerivedCategory.Q.obj P) ≫
          reductionS.derived.map ((transport e).mapDerivedCategoryFactors.hom.app P) ≫
          reductionS.counit.app (((transport e).mapHomologicalComplex (.up ℤ)).obj P) =
        derivedEquivalence.functor.map (reductionR.counit.app P) ≫
          localization.hom.app ((reductionR.ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex reduction (.up ℤ)).hom.app P)) ∧
    (∀ (n : ℕ) (M : systemLevel R n),
      (transport (a.app (op n))).map
          (((systemTensorCoherence A).ordinaryUnit R n).hom.app M) =
        (quotient (Nat.le_refl n)).ordinary.hom.app M ≫
          ((systemTensorCoherence A).ordinaryUnit S n).hom.app
            ((transport (a.app (op n))).obj M)) ∧
    (∀ {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) (M : systemLevel R n),
      (transport (a.app (op l))).map
          (((systemTensorCoherence A).ordinaryAssoc R h k).hom.app M) ≫
          (quotient (h.trans k)).ordinary.hom.app M =
        (quotient h).ordinary.hom.app ((systemTensor A R k).obj M) ≫
          (systemTensor A S h).map ((quotient k).ordinary.hom.app M) ≫
          ((systemTensorCoherence A).ordinaryAssoc S h k).hom.app
            ((transport (a.app (op n))).obj M)) ∧
    (∀ (n : ℕ) (M : DerivedCategory (systemLevel R n)),
      (transport (a.app (op n))).mapDerivedCategory.map
          (((systemTensorCoherence A).derivedUnit R n).hom.app M) =
        (quotient (Nat.le_refl n)).derived.hom.app M ≫
          ((systemTensorCoherence A).derivedUnit S n).hom.app
            ((transport (a.app (op n))).mapDerivedCategory.obj M)) ∧
    (∀ {l m n : ℕ} (h : l ≤ m) (k : m ≤ n)
      (M : DerivedCategory (systemLevel R n)),
      (transport (a.app (op l))).mapDerivedCategory.map
          (((systemTensorCoherence A).derivedAssoc R h k).hom.app M) ≫
          (quotient (h.trans k)).derived.hom.app M =
        (quotient h).derived.hom.app ((systemDerivedTensor A R k).obj M) ≫
          (systemDerivedTensor A S h).map ((quotient k).derived.hom.app M) ≫
          ((systemTensorCoherence A).derivedAssoc S h k).hom.app
            ((transport (a.app (op n))).mapDerivedCategory.obj M)) ∧
    (∀ (n : ℕ) (M : DerivedCategory (StrictRingSystem R)),
      adjointTransition A R (Nat.le_refl n) M =
        ((systemTensorCoherence A).derivedUnit R n).hom.app ((derivedSystemEvaluation R n).obj M)) ∧
    (∀ (n : ℕ) (M : DerivedCategory (StrictRingSystem S)),
      adjointTransition A S (Nat.le_refl n) M =
        ((systemTensorCoherence A).derivedUnit S n).hom.app ((derivedSystemEvaluation S n).obj M)) ∧
    (∀ {l m n : ℕ} (h : l ≤ m) (k : m ≤ n)
      (M : DerivedCategory (StrictRingSystem R)),
      ((systemTensorCoherence A).derivedAssoc R h k).inv.app ((derivedSystemEvaluation R n).obj M) ≫
          (systemDerivedTensor A R h).map (adjointTransition A R k M) ≫
          adjointTransition A R h M = adjointTransition A R (h.trans k) M) ∧
    (∀ {l m n : ℕ} (h : l ≤ m) (k : m ≤ n)
      (M : DerivedCategory (StrictRingSystem S)),
      ((systemTensorCoherence A).derivedAssoc S h k).inv.app ((derivedSystemEvaluation S n).obj M) ≫
          (systemDerivedTensor A S h).map (adjointTransition A S k M) ≫
          adjointTransition A S h M = adjointTransition A S (h.trans k) M) ∧
    (∀ (M : DerivedCategory (StrictRingSystem R)) {m n : ℕ} (h : m ≤ n),
      (quotient h).derived.inv.app ((derivedSystemEvaluation R n).obj M) ≫
          (transport (a.app (op m))).mapDerivedCategory.map (adjointTransition A R h M) ≫
          (derivedLevel m).inv.app M =
        (systemDerivedTensor A S h).map ((derivedLevel n).inv.app M) ≫
          adjointTransition A S h (derivedEquivalence.functor.obj M)) ∧
    (∀ (M : DerivedCategory (StrictRingSystem R)),
      (∀ (m n : ℕ) (h : m ≤ n), IsIso (adjointTransition A R h M)) ↔
        ∀ (m n : ℕ) (h : m ≤ n),
          IsIso (adjointTransition A S h (derivedEquivalence.functor.obj M)))

/-- Complete strict-system coefficient transport, including the normalization of
localization, reduction and every adjoint transition.
Source: def-pur-section-invariant, finite-clopen expansion; Stacks 03D7 and 015F
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
abbrev CoherentTransport (R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (a : R ≅ S)
    (c : Cone R) (d : Cone S) (e : c.pt ≅ d.pt)
    (A : SystemScalarAssignment (J := J)) :=
  TransportComparisonData
    (StrictRingSystem R ≌ StrictRingSystem S)
    (fun equivalence ↦
      equivalence.functor.Additive)
    (fun equivalence ↦
      PreservesFiniteLimits equivalence.functor)
    (fun equivalence ↦
      PreservesFiniteColimits equivalence.functor)
    (DerivedCategory (StrictRingSystem R) ≌ DerivedCategory (StrictRingSystem S))
    (fun equivalence additive derivedEquivalence ↦
      letI := additive; DerivedCategory.Q ⋙ derivedEquivalence.functor ≅
    equivalence.functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (fun equivalence ↦
      ∀ n : ℕ, equivalence.functor ⋙ systemEvaluation S n ≅
    systemEvaluation R n ⋙ transport (a.app (op n)))
    (fun derivedEquivalence ↦
      ∀ n : ℕ, derivedEquivalence.functor ⋙ derivedSystemEvaluation S n ≅
    derivedSystemEvaluation R n ⋙ (transport (a.app (op n))).mapDerivedCategory)
    (Reduction R c A)
    (Reduction S d A)
    (fun equivalence reductionR reductionS ↦
      reductionR.ordinary ⋙ equivalence.functor ≅ transport e ⋙ reductionS.ordinary)
    (fun derivedEquivalence reductionR reductionS ↦
      reductionR.derived ⋙ derivedEquivalence.functor ≅
    (transport e).mapDerivedCategory ⋙ reductionS.derived)
    (∀ n : ℕ, ScalarSquare (c.π.app (op n)) (d.π.app (op n)) e (a.app (op n))
    (A (c.π.app (op n))) (A (d.π.app (op n))))
    (∀ {m n : ℕ} (h : m ≤ n),
    ScalarSquare (R.map (homOfLE h).op) (S.map (homOfLE h).op)
      (a.app (op n)) (a.app (op m))
      (A (R.map (homOfLE h).op)) (A (S.map (homOfLE h).op)))
    (fun equivalence additive limits colimits derivedEquivalence localization level derivedLevel
      reductionR reductionS reduction derivedReduction projection quotient ↦
      CoherentTransportConditions R S a c d e A (additive := additive) (limits := limits)
        (colimits := colimits) equivalence derivedEquivalence localization level derivedLevel
        reductionR reductionS reduction derivedReduction projection quotient)
```

## Users

`tools/downstream.py Sheaf.Paper.RingIsoQuotientSystemTransport --uses
ScalarSquare Reduction CoherentTransport` reports zero downstream modules and
only this module's internal uses of each name. The eight original node
attachments remain; the generic packaging and predicates are attached to the
same node. No source-library module is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingIsoQuotientSystemTransport | H8 | Constructors and field access use the equivalent generic records; the full proof is supplied. |

## Status

landed 20261025T051848-L-4168525 2026-10-25 (merge of deliver/H8/Sheaf.Paper.RingIsoQuotientSystemTransport)
