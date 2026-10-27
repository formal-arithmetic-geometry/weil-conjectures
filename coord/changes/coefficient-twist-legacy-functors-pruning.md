# CoefficientTwistsDetailed legacy functors

## Reason

The current coefficient-twists unit is realized by
`Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`, as recorded in
`def-coefficient-twists-detailed.json`. Its integral functor uses the retained
signed line and exact ordinary sheaf tensor. Its rational and algebraically
closed functors use the existing intrinsic `rationalDerivedTensor` and
`commonStageDerivedTensor`, respectively, with the same retained integral
coefficient object and its field images. Thus the old independent rational and
common-stage functor branch in this module duplicates a route no current
consumer or active node uses. Remove that branch and its private-to-this-branch
linear-functor theorem, rather than prove additional comparisons for it.

The retained `integralComplexTwist`, `integralCoefficientTwist`,
`rationalCoefficientTwist`, signed lines, four coefficient-family data and
`coefficientTateTwists` are unchanged. The normalized scalar maps, their identity
and composition theorems, ordinary sheaf comparison, and its derived comparison
are retained. The ordinary sheaf comparison is proved in this delivery.
No target signature or definition used in a target changes its meaning.
No declaration under `lean/WeilConjectures/` is changed or removed.

This is not a withdrawal justified only by zero current Lean importers. The
replacement integral/rational/common-stage construction is already the unit's
recorded realization. Active DAG statements, proof steps, dependencies and Lean
attachments have no reference to the removed declarations; historical review
hole lists are preserved. All 32 quarantine archives listed in the current
`coord/rework.tsv` were checked as well, with no references. Consequently no
parent dependency edit or node attachment edit is needed for this cleanup.

## Old

The following are the exact old definitions and statements, with their original
proofs where included in the removed contiguous blocks:

```lean
/-- The completed tensor twist is linear for the canonical coefficient action.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: the coefficient action is the recorded constant-section action
integralCoefficientLinear. On local pure tensors, applying a coefficient to the
first factor before or after the tensor map gives the same balanced tensor.
Sheafification preserves this equality. The termwise identity descends through
the quasi-isomorphism localization, proving linearity on every derived arrow. -/
theorem integralComplexTwist_linear_statement (m : ℤ) :
    (integralComplexTwist D ℓ hℓ E S m).Linear
      (Padic.coefficientExtensionIntegers ℓ E) := by
  let A := Padic.coefficientExtensionIntegers ℓ E
  let C := integralTowerModules ℓ E S
  let : Linear A C := coefficientModuleLinear ℓ E S
  have ht : (integralSheafTwist ℓ E S m).Linear A := by
    let O : Sheaf (ProEt.topology S) RingCat.{u + 1} :=
      (sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (completedIntegralCommRingSheafUnrestricted ℓ E S)
    let N : integralTowerModules ℓ E S := coefficientTwistLine S
      (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m
    let : Linear A (SheafOfModules.{u + 1} O) := coefficientModuleLinear ℓ E S
    let adj := PresheafOfModules.sheafificationAdjunction (R := O) (𝟙 O.obj)
    constructor
    intro M M' f a
    change (PresheafOfModules.sheafification (R := O) (𝟙 O.obj)).map
        (SheafOfModules.siteTensorHom.{u, u + 1, u + 1, u + 1} (a • f).val N.val) =
      a • (PresheafOfModules.sheafification (R := O) (𝟙 O.obj)).map
        (SheafOfModules.siteTensorHom.{u, u + 1, u + 1, u + 1} f.val N.val)
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    have hn := adj.unit.naturality
      (SheafOfModules.siteTensorHom.{u, u + 1, u + 1, u + 1} (a • f).val N.val)
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    dsimp only [Functor.comp_map]
    rw [← hn]
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    have hf := adj.unit.naturality
      (SheafOfModules.siteTensorHom.{u, u + 1, u + 1, u + 1} f.val N.val)
    have hf' := congrArg (fun h => (h.app U).hom (x ⊗ₜ y)) hf
    change ((adj.unit.app
        (SheafOfModules.siteTensorPresheaf.{u, u + 1, u + 1, u + 1} M'.val N.val)).app U).hom
        ((integralScalarConstant ℓ E S U a • (f.val.app U).hom x) ⊗ₜ y) =
      integralScalarConstant ℓ E S U a •
        ((PresheafOfModules.sheafification (R := O) (𝟙 O.obj)).map
          (SheafOfModules.siteTensorHom.{u, u + 1, u + 1, u + 1} f.val N.val)).val.app U
            ((adj.unit.app
              (SheafOfModules.siteTensorPresheaf.{u, u + 1, u + 1, u + 1} M.val N.val)).app U
              (x ⊗ₜ y))
    erw [← TensorProduct.smul_tmul'
      (R := (completedIntegralCommRingSheafUnrestricted ℓ E S).obj.obj U)
      (R' := (completedIntegralCommRingSheafUnrestricted ℓ E S).obj.obj U), map_smul]
    exact congrArg (fun z => integralScalarConstant ℓ E S U a • z) hf'
  have hs : integralCoefficientLinear ℓ E S = coefficientDerivedLinear ℓ E S := by
    apply coefficientLinear_ext
    intro K K' a f
    rw [(integralCoefficientLinear_existsUnique ℓ E S).exists.choose_spec]
    rw [coefficientDerived_eq]
    rfl
  change @Functor.Linear _ _ _ _ _ _ _ _ (integralCoefficientLinear ℓ E S)
    (integralCoefficientLinear ℓ E S) (integralSheafTwist ℓ E S m).mapDerivedCategory
  rw [hs]
  let : Linear A (DerivedCategory C) := coefficientDerivedLinear ℓ E S
  let : DerivedCategory.Q.Linear A := Localization.functor_linear A
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ _) (HomologicalComplex.quasiIso C (.up ℤ))
  exact (Localization.functor_linear_iff DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) A
    ((integralSheafTwist ℓ E S m).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (integralSheafTwist ℓ E S m).mapDerivedCategory).mp inferInstance
```

```lean
/-- Tensor by an integral twisting line preserves the complete constructible category.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: locally trivialize the rank-one twisting line. Tensor is then the identity
on the completed-coefficient category and its finite reductions. Derived completeness,
constructibility and the common bounded cohomological interval are local properties,
so the same properties hold after gluing. -/
theorem integralComplexTwist_constructible (m : ℤ)
    (K : boundedConstructibleDerivedCompleteIntegralCategory D ℓ hℓ E S) :
    boundedConstructibleDerivedCompleteIntegral D ℓ hℓ E S
      ((integralComplexTwist D ℓ hℓ E S m).obj K.obj) := by
  sorry

/-- Rational twisting is integral tensor on the integral representative, then localization.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def rationalComplexTwist (m : ℤ) (K : rationalConstructibleCategory D ℓ hℓ E S) :
    rationalConstructibleCategory D ℓ hℓ E S :=
  (rationalConstructibleLocalization D ℓ hℓ E S).obj
    ⟨(integralComplexTwist D ℓ hℓ E S m).obj K.obj.obj,
      integralComplexTwist_constructible D ℓ hℓ E S m K.obj⟩

/-- The canonical endofunctor on the bounded integral constructible category.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
The object map is the completed integral tensor functor restricted by its
constructibility theorem, and the arrow map is the same derived tensor map.
-/
noncomputable def integralConstructibleComplexTwistFunctor (m : ℤ) :
    boundedConstructibleDerivedCompleteIntegralCategory D ℓ hℓ E S ⥤
      boundedConstructibleDerivedCompleteIntegralCategory D ℓ hℓ E S :=
  ObjectProperty.lift _
    ((boundedConstructibleDerivedCompleteIntegral D ℓ hℓ E S).ι ⋙
      integralComplexTwist D ℓ hℓ E S m)
    (fun K => integralComplexTwist_constructible D ℓ hℓ E S m K)

/-- The restricted integral twist is linear on the full constructible subcategory.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: integralComplexTwist_linear_statement gives the equality on all ambient
arrows. The full subcategory inherits that action by integralConstructibleLinear.
Its faithful inclusion gives the same equality for restricted arrows. -/
theorem integralConstructibleComplexTwistFunctor_linear_statement (m : ℤ) :
    (integralConstructibleComplexTwistFunctor D ℓ hℓ E S m).Linear
      (Padic.coefficientExtensionIntegers ℓ E) := by
  let : (integralComplexTwist D ℓ hℓ E S m).Linear
      (Padic.coefficientExtensionIntegers ℓ E) :=
    integralComplexTwist_linear_statement D ℓ hℓ E S m
  constructor
  intro K K' f a
  apply (boundedConstructibleDerivedCompleteIntegral D ℓ hℓ E S).ι.map_injective
  exact (integralComplexTwist D ℓ hℓ E S m).map_smul a f.hom

/-- The restricted integral twist is additive on the full constructible subcategory.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: exact sheaf tensor is additive, and its derived functor retains additivity.
The full subcategory's arrow addition is ambient addition, so restriction
preserves the additive identity. -/
theorem integralConstructibleComplexTwistFunctor_additive_statement (m : ℤ) :
    (integralConstructibleComplexTwistFunctor D ℓ hℓ E S m).Additive := by
  let : (integralComplexTwist D ℓ hℓ E S m).Additive := by
    dsimp only [integralComplexTwist]
    infer_instance
  dsimp only [integralConstructibleComplexTwistFunctor]
  infer_instance

/-- The canonical rational Tate-twist endofunctor, obtained by extending the
integral tensor functor through the raw scalar localization.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
noncomputable def rationalComplexTwistFunctor (m : ℤ) :
    rationalConstructibleCategory D ℓ hℓ E S ⥤
      rationalConstructibleCategory D ℓ hℓ E S := by
  letI : Linear (Padic.coefficientExtensionIntegers ℓ E)
      (completedIntegralDerivedCategory ℓ E S D hℓ) :=
    completedIntegralLinear D ℓ hℓ E S
  letI : (integralComplexTwist D ℓ hℓ E S m).Additive := by
    dsimp [integralComplexTwist]
    infer_instance
  letI : (integralComplexTwist D ℓ hℓ E S m).Linear
      (Padic.coefficientExtensionIntegers ℓ E) :=
    integralComplexTwist_linear_statement D ℓ hℓ E S m
  let F := integralConstructibleComplexTwistFunctor D ℓ hℓ E S m
  letI : F.Additive := integralConstructibleComplexTwistFunctor_additive_statement D ℓ hℓ E S m
  letI : F.Linear (Padic.coefficientExtensionIntegers ℓ E) :=
    integralConstructibleComplexTwistFunctor_linear_statement D ℓ hℓ E S m
  exact CategoryTheory.ScalarLocalization.map
    (Padic.coefficientExtensionIntegers ℓ E)
    (boundedConstructibleDerivedCompleteIntegralCategory D ℓ hℓ E S)
    (Padic.coefficientExtensionUniformizer ℓ E) F

/-- Its object map is the displayed integral-representative construction.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: ScalarLocalization.map applies the integral functor to the same integral
object. ObjectProperty.lift uses the displayed ambient tensor object and its
constructibility proof. Membership proofs agree by proof irrelevance. -/
theorem rationalComplexTwistFunctor_obj (m : ℤ)
    (K : rationalConstructibleCategory D ℓ hℓ E S) :
    (rationalComplexTwistFunctor D ℓ hℓ E S m).obj K =
      rationalComplexTwist D ℓ hℓ E S m K := by
  rfl

/-- The rational functor's action on every localized pure tensor.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: ScalarLocalization.map uses TensorProduct.map with the identity on the
localized scalar factor and the integral functor's linear Hom map. Evaluating
this map on a pure tensor gives the displayed formula. The endpoint casts
are the same object assignments, so the formula is recorded as HEq. -/
theorem rationalComplexTwistFunctor_map
    (m : ℤ)
    (K M : boundedConstructibleDerivedCompleteIntegralCategory D ℓ hℓ E S)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer ℓ E))
    (f : K ⟶ M) :
    HEq
      ((rationalComplexTwistFunctor D ℓ hℓ E S m).map
        (a ⊗ₜ[Padic.coefficientExtensionIntegers ℓ E] f :
          (rationalConstructibleLocalization D ℓ hℓ E S).obj K ⟶
            (rationalConstructibleLocalization D ℓ hℓ E S).obj M))
      (a ⊗ₜ[Padic.coefficientExtensionIntegers ℓ E]
        (integralConstructibleComplexTwistFunctor D ℓ hℓ E S m).map f :
        (rationalConstructibleLocalization D ℓ hℓ E S).obj
              ((integralConstructibleComplexTwistFunctor D ℓ hℓ E S m).obj K) ⟶
          (rationalConstructibleLocalization D ℓ hℓ E S).obj
              ((integralConstructibleComplexTwistFunctor D ℓ hℓ E S m).obj M)) := by
  apply heq_of_eq
  exact LinearMap.baseChange_tmul _ a f
```

```lean
/-- Restrict the normalized derived comparison to the full integral categories.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: both composites preserve the full subcategories. Their full inclusion
lifts the ambient comparison and inverse uniquely. Equality of the underlying
hom components fixes the lift, by faithfulness. -/
theorem twistIntegralScalarComparison_existsUnique (m : ℤ) :
    ∃! b : integralConstructibleComplexTwistFunctor D ℓ hℓ E S m ⋙
        integralConstructibleScalarExtension D ℓ hℓ E L ι S ≅
      integralConstructibleScalarExtension D ℓ hℓ E L ι S ⋙
        integralConstructibleComplexTwistFunctor D ℓ hℓ L S m,
      ∀ K, (b.hom.app K).hom =
        (twistDerivedScalarComparison D ℓ hℓ E S L ι m).hom.app K.obj := by
  let c := twistDerivedScalarComparison D ℓ hℓ E S L ι m
  let b : integralConstructibleComplexTwistFunctor D ℓ hℓ E S m ⋙
        integralConstructibleScalarExtension D ℓ hℓ E L ι S ≅
      integralConstructibleScalarExtension D ℓ hℓ E L ι S ⋙
        integralConstructibleComplexTwistFunctor D ℓ hℓ L S m :=
    NatIso.ofComponents
      (fun K => (boundedConstructibleDerivedCompleteIntegral D ℓ hℓ L S).isoMk
        (c.app K.obj))
      (fun f => by
        apply (boundedConstructibleDerivedCompleteIntegral D ℓ hℓ L S).ι.map_injective
        exact c.hom.naturality f.hom)
  refine ⟨b, fun _ => rfl, ?_⟩
  intro b' hb'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (boundedConstructibleDerivedCompleteIntegral D ℓ hℓ L S).ι.map_injective
  exact hb' K

/-- The restricted comparison, with its fixed ambient hom components.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def twistIntegralScalarComparison (m : ℤ) :=
  (twistIntegralScalarComparison_existsUnique D ℓ hℓ E S L ι m).exists.choose

/-- Localize the fixed integral comparison; every component is tensor with one.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: tensor each integral component and inverse with one. Integral naturality
is linear for the coefficient inclusion, so extends to localized pure tensors
and then sums. Inverse equations persist. Equality of components uniquely fixes
this natural isomorphism in the raw scalar-localized category. -/
theorem twistRationalOrdinaryComparison_existsUnique (m : ℤ) :
    ∃! b : rationalComplexTwistFunctor D ℓ hℓ E S m ⋙
        rationalOrdinaryScalarExtension D ℓ hℓ E S L ι ≅
      rationalOrdinaryScalarExtension D ℓ hℓ E S L ι ⋙
        rationalComplexTwistFunctor D ℓ hℓ L S m,
      ∀ K, HEq (b.hom.app K)
        ((1 : Localization.Away (Padic.coefficientExtensionUniformizer ℓ L)) ⊗ₜ[
          Padic.coefficientExtensionIntegers ℓ L]
          (twistIntegralScalarComparison D ℓ hℓ E S L ι m).hom.app K.obj) := by
  let R := Padic.coefficientExtensionIntegers ℓ E
  let T := Padic.coefficientExtensionIntegers ℓ L
  let A := boundedConstructibleDerivedCompleteIntegralCategory D ℓ hℓ E S
  let B := boundedConstructibleDerivedCompleteIntegralCategory D ℓ hℓ L S
  let p := Padic.coefficientExtensionUniformizer ℓ E
  let q := Padic.coefficientExtensionUniformizer ℓ L
  let F := integralConstructibleComplexTwistFunctor D ℓ hℓ E S m
  let H := integralConstructibleComplexTwistFunctor D ℓ hℓ L S m
  let : F.Additive := integralConstructibleComplexTwistFunctor_additive_statement D ℓ hℓ E S m
  let : F.Linear R := integralConstructibleComplexTwistFunctor_linear_statement D ℓ hℓ E S m
  let : H.Additive := integralConstructibleComplexTwistFunctor_additive_statement D ℓ hℓ L S m
  let : H.Linear T := integralConstructibleComplexTwistFunctor_linear_statement D ℓ hℓ L S m
  let c := twistIntegralScalarComparison D ℓ hℓ E S L ι m
  have hs (K M : A) (a : Localization.Away p) (f : K ⟶ M) :
      rationalScalarHom D ℓ hℓ E S L ι K M (a ⊗ₜ[R] f) =
        rationalCoefficientMap ℓ E L ι a ⊗ₜ[T]
          (integralConstructibleScalarExtension D ℓ hℓ E L ι S).map f :=
    (rationalScalarHom_existsUnique D ℓ hℓ E S L ι K M).exists.choose_spec a f
  have hF (K M : A) (a : Localization.Away p) (f : K ⟶ M) :
      ScalarLocalization.mapHom R A p F K M (a ⊗ₜ[R] f) = a ⊗ₜ[R] F.map f :=
    LinearMap.baseChange_tmul _ a f
  have hH (K M : B) (a : Localization.Away q) (f : K ⟶ M) :
      ScalarLocalization.mapHom T B q H K M (a ⊗ₜ[T] f) = a ⊗ₜ[T] H.map f :=
    LinearMap.baseChange_tmul _ a f
  let b : rationalComplexTwistFunctor D ℓ hℓ E S m ⋙
        rationalOrdinaryScalarExtension D ℓ hℓ E S L ι ≅
      rationalOrdinaryScalarExtension D ℓ hℓ E S L ι ⋙
        rationalComplexTwistFunctor D ℓ hℓ L S m :=
    NatIso.ofComponents
      (fun K => (rationalConstructibleLocalization D ℓ hℓ L S).mapIso (c.app K.obj))
      (fun {K M} f => by
        change ScalarLocalization.composition T B q _ _ _
            (1 ⊗ₜ[T] c.hom.app M.obj)
            (rationalScalarHom D ℓ hℓ E S L ι _ _
              (ScalarLocalization.mapHom R A p F _ _ f)) =
          ScalarLocalization.composition T B q _ _ _
            (ScalarLocalization.mapHom T B q H _ _
              (rationalScalarHom D ℓ hℓ E S L ι _ _ f))
            (1 ⊗ₜ[T] c.hom.app K.obj)
        induction f using TensorProduct.induction_on with
        | zero => simp only [map_zero, LinearMap.zero_apply]
        | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]
        | tmul a f =>
          rw [hF, hs, hs, hH, ScalarLocalization.composition_tmul,
            ScalarLocalization.composition_tmul, one_mul, mul_one]
          exact congrArg (fun k => rationalCoefficientMap ℓ E L ι a ⊗ₜ[T] k)
            (c.hom.naturality f))
  refine ⟨b, fun _ => HEq.rfl, ?_⟩
  intro b' hb'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq (hb' K)

/-- The localized tensor comparison with its integral normalization.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def twistRationalOrdinaryComparison (m : ℤ) :=
  (twistRationalOrdinaryComparison_existsUnique D ℓ hℓ E S L ι m).exists.choose

/-- The comparison with published completed scalar extension, obtained by conjugating
ordinary tensor comparison by the recorded completion comparison.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def rationalTwistScalarComparison (m : ℤ) :
    rationalComplexTwistFunctor D ℓ hℓ E S m ⋙ rationalScalarExtension D ℓ hℓ E S L ι ≅
      rationalScalarExtension D ℓ hℓ E S L ι ⋙ rationalComplexTwistFunctor D ℓ hℓ L S m :=
  Functor.isoWhiskerLeft _ (rationalOrdinaryComparison D ℓ hℓ E S L ι).symm ≪≫
    twistRationalOrdinaryComparison D ℓ hℓ E S L ι m ≪≫
    Functor.isoWhiskerRight (rationalOrdinaryComparison D ℓ hℓ E S L ι) _
```

```lean
/-- The identity rational comparison is normalized by the published scalar unit.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: the identity semilinear map is the identity on every signed line. The
ordinary tensor comparison consequently sends s tensor (x tensor y) to
(s tensor x) tensor y. The multiplication scalar unit turns both sides into
s*x tensor y. Derivation, full restriction and Hom localization preserve the
equation; conjugation by the completion comparisons gives the displayed unit. -/
theorem rationalTwistScalarComparison_unit (m : ℤ)
    (K : rationalConstructibleCategory D ℓ hℓ E S) :
    (rationalTwistScalarComparison D ℓ hℓ E S E (AlgHom.id (Padic ℓ) E) m).hom.app K =
      (rationalConstructibleScalarUnit ℓ E S D hℓ).hom.app
          ((rationalComplexTwistFunctor D ℓ hℓ E S m).obj K) ≫
        (rationalComplexTwistFunctor D ℓ hℓ E S m).map
          ((rationalConstructibleScalarUnit ℓ E S D hℓ).inv.app K) := by
  sorry
```

```lean
/-- Twist an algebraically closed coefficient object on its displayed finite stage.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def algebraicClosureComplexTwist (m : ℤ)
    (K : algebraicallyClosedConstructibleCategory D ℓ hℓ Ω S) :
    algebraicallyClosedConstructibleCategory D ℓ hℓ Ω S :=
  ⟨K.stage, rationalComplexTwist D ℓ hℓ (AlgebraicallyClosedCoefficients.Coefficient ℓ Ω K.stage)
    S m K.obj⟩

/-- The canonical stagewise twist functors used by the common-stage category.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
noncomputable def coefficientTwistStageFunctor (m : ℤ)
    (F : Padic.FiniteCoefficientFields ℓ Ω) :
    AlgebraicallyClosedCoefficients.Stage D ℓ hℓ Ω S F ⥤
      AlgebraicallyClosedCoefficients.Stage D ℓ hℓ Ω S F :=
  rationalComplexTwistFunctor D ℓ hℓ
    (AlgebraicallyClosedCoefficients.Coefficient ℓ Ω F) S m

/-- Scalar-extension comparisons are the canonical rational tensor comparisons,
transported to the named stage transitions.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
noncomputable def coefficientTwistStageComparison (m : ℤ) :
    ∀ {F G : AlgebraicallyClosedCoefficients.Index ℓ Ω} (h : F ≤ G),
      coefficientTwistStageFunctor D ℓ hℓ S Ω m F ⋙
          AlgebraicallyClosedCoefficients.stageTransition D ℓ hℓ Ω S F G h ≅
        AlgebraicallyClosedCoefficients.stageTransition D ℓ hℓ Ω S F G h ⋙
          coefficientTwistStageFunctor D ℓ hℓ S Ω m G :=
  fun {F G} h ↦
    Functor.isoWhiskerLeft _
      (eqToIso ((AlgebraicallyClosedCoefficients.stageSystem_existsUnique
        D ℓ hℓ Ω S).exists.choose_spec.1 F G h)) ≪≫
    rationalTwistScalarComparison D ℓ hℓ
      (AlgebraicallyClosedCoefficients.Coefficient ℓ Ω F) S
      (AlgebraicallyClosedCoefficients.Coefficient ℓ Ω G)
      (AlgebraicallyClosedCoefficients.coefficientInclusion ℓ Ω F G h) m ≪≫
    Functor.isoWhiskerRight
      (eqToIso ((AlgebraicallyClosedCoefficients.stageSystem_existsUnique
        D ℓ hℓ Ω S).exists.choose_spec.1 F G h)).symm _


/-- The fixed stage comparisons satisfy the common-stage tower equation.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: the normalized signed-line maps compose by twistScalarMaps_composition.
On an iterated local scalar tensor both comparison paths send
b tensor (a tensor (x tensor y)) to (b*ι(a) tensor x) tensor c(y).
Local tensor generation gives the ordinary square with the published scalar
associator. Exact derivation, full restriction and rationalization preserve it.
Expand rationalOrdinaryComparison conjugations and cancel adjacent inverses
by naturality. Transport along stageSystem_existsUnique to obtain the displayed
equation for the actual stage system. Repeated stages are included; the scalar
unit normalization is rationalTwistScalarComparison_unit. -/
theorem coefficientTwistStageComparison_coherent (m : ℤ) :
    CategoryTheory.StageSystem.pairFunctorCoherent
      (AlgebraicallyClosedCoefficients.stageSystem D ℓ hℓ Ω S)
      (AlgebraicallyClosedCoefficients.stageSystem D ℓ hℓ Ω S)
      (fun F => coefficientTwistStageFunctor D ℓ hℓ S Ω m F)
      (coefficientTwistStageComparison D ℓ hℓ S Ω m) := by
  sorry

/-- The canonical common-stage Tate-twist endofunctor.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
noncomputable def algebraicClosureComplexTwistFunctor (m : ℤ) :
    algebraicallyClosedConstructibleCategory D ℓ hℓ Ω S ⥤
      algebraicallyClosedConstructibleCategory D ℓ hℓ Ω S :=
  (CategoryTheory.StageSystem.coefficientPairFunctor_exists
    (AlgebraicallyClosedCoefficients.stageSystem D ℓ hℓ Ω S)
    (AlgebraicallyClosedCoefficients.stageSystem D ℓ hℓ Ω S)
    (fun F => coefficientTwistStageFunctor D ℓ hℓ S Ω m F)
    (coefficientTwistStageComparison D ℓ hℓ S Ω m)
    (coefficientTwistStageComparison_coherent D ℓ hℓ S Ω m)).exists.choose

/-- The common-stage functor has the displayed object assignment.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: the object clause of coefficientPairFunctor_exists keeps the source
stage and applies its rational twist. rationalComplexTwistFunctor_obj identifies
this object with the integral-representative formula at that same stage. -/
theorem algebraicClosureComplexTwistFunctor_obj (m : ℤ)
    (K : algebraicallyClosedConstructibleCategory D ℓ hℓ Ω S) :
    (algebraicClosureComplexTwistFunctor D ℓ hℓ S Ω m).obj K =
      algebraicClosureComplexTwist D ℓ hℓ S Ω m K := by
  have h := (CategoryTheory.StageSystem.coefficientPairFunctor_exists
    (AlgebraicallyClosedCoefficients.stageSystem D ℓ hℓ Ω S)
    (AlgebraicallyClosedCoefficients.stageSystem D ℓ hℓ Ω S)
    (fun F => coefficientTwistStageFunctor D ℓ hℓ S Ω m F)
    (coefficientTwistStageComparison D ℓ hℓ S Ω m)
    (coefficientTwistStageComparison_coherent D ℓ hℓ S Ω m)).exists.choose_spec.1 K
  refine h.trans ?_
  cases K with
  | mk F K =>
    change _ = CategoryTheory.StageSystem.PairCategory.mk F _
    rfl

/-- The representative formula is part of the descended functor datum: it fixes
the morphism action, rather than specifying objects alone.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: apply the representative clause of coefficientPairFunctor_exists to
the chosen functor. Its formula conjugates the stagewise map by the fixed
source and target comparisons. The preceding coherence theorem makes this
independent of subsequent common-stage enlargement. Every arrow is represented,
so the formula specifies the entire descended morphism action. -/
theorem algebraicClosureComplexTwistFunctor_map_exists (m : ℤ) :
    ∀ {P Q : algebraicallyClosedConstructibleCategory D ℓ hℓ Ω S}
      (M : AlgebraicallyClosedCoefficients.Index ℓ Ω)
      (hP : P.stage ≤ M) (hQ : Q.stage ≤ M)
      (f : P.toStage hP ⟶ Q.toStage hQ),
      HEq ((algebraicClosureComplexTwistFunctor D ℓ hℓ S Ω m).map
        (CategoryTheory.StageSystem.PairCategory.mkHom M hP hQ f))
        (CategoryTheory.StageSystem.PairCategory.mkHom
          (X := ⟨P.stage,
            (coefficientTwistStageFunctor D ℓ hℓ S Ω m P.stage).obj P.obj⟩)
          (Y := ⟨Q.stage,
            (coefficientTwistStageFunctor D ℓ hℓ S Ω m Q.stage).obj Q.obj⟩)
          M hP hQ
          ((coefficientTwistStageComparison D ℓ hℓ S Ω m hP).hom.app P.obj ≫
            (coefficientTwistStageFunctor D ℓ hℓ S Ω m M).map f ≫
            (coefficientTwistStageComparison D ℓ hℓ S Ω m hQ).inv.app Q.obj)) := by
  exact (CategoryTheory.StageSystem.coefficientPairFunctor_exists
    (AlgebraicallyClosedCoefficients.stageSystem D ℓ hℓ Ω S)
    (AlgebraicallyClosedCoefficients.stageSystem D ℓ hℓ Ω S)
    (fun F => coefficientTwistStageFunctor D ℓ hℓ S Ω m F)
    (coefficientTwistStageComparison D ℓ hℓ S Ω m)
    (coefficientTwistStageComparison_coherent D ℓ hℓ S Ω m)).exists.choose_spec.2
```

## New

Remove these 22 unused declarations, with no replacement hole or new statement:

- `WeilConjectures.integralComplexTwist_linear_statement`
- `WeilConjectures.integralComplexTwist_constructible`
- `WeilConjectures.rationalComplexTwist`
- `WeilConjectures.integralConstructibleComplexTwistFunctor`
- `WeilConjectures.integralConstructibleComplexTwistFunctor_linear_statement`
- `WeilConjectures.integralConstructibleComplexTwistFunctor_additive_statement`
- `WeilConjectures.rationalComplexTwistFunctor`
- `WeilConjectures.rationalComplexTwistFunctor_obj`
- `WeilConjectures.rationalComplexTwistFunctor_map`
- `WeilConjectures.twistIntegralScalarComparison_existsUnique`
- `WeilConjectures.twistIntegralScalarComparison`
- `WeilConjectures.twistRationalOrdinaryComparison_existsUnique`
- `WeilConjectures.twistRationalOrdinaryComparison`
- `WeilConjectures.rationalTwistScalarComparison`
- `WeilConjectures.rationalTwistScalarComparison_unit`
- `WeilConjectures.algebraicClosureComplexTwist`
- `WeilConjectures.coefficientTwistStageFunctor`
- `WeilConjectures.coefficientTwistStageComparison`
- `WeilConjectures.coefficientTwistStageComparison_coherent`
- `WeilConjectures.algebraicClosureComplexTwistFunctor`
- `WeilConjectures.algebraicClosureComplexTwistFunctor_obj`
- `WeilConjectures.algebraicClosureComplexTwistFunctor_map_exists`

The already recorded replacement constructions are
`sfIntegralTwistingFunctor`, `sfRationalTwistingFunctor` and
`sfQbarTwistingFunctor` in `IntrinsicCoefficientTwistsUnrestricted`. Their
coefficient objects and the finite-level branch remain available. No existing
consumer needs an adaptation.

Retain the public import `Sheaf.CategoryTheory.StageSystemFunctorDescent`:
`QbarTwistCommonStage` uses that reexported interface. Remove the unused proof
import `Sheaf.Paper.ScalarExtensionDualLocalIso` and private access import
`all Sheaf.Paper.IntegralConstructibleLinear`. The ordinary public import of
`Sheaf.Paper.IntegralConstructibleLinear` stays, since the retained definitions
use its instances. Add only proof imports for the proved ordinary tensor
comparison; these imports change no public signature.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CoefficientTwistsDetailed` | A4 | Remove the unused branch and its internal consumers together. Retain and prove the shared ordinary tensor comparison. |

`tools/downstream.py Sheaf.Paper.CoefficientTwistsDetailed --uses ...` traversed
all 3,491 transitive importers and reported only this module for the branch
names. The additionally removed `integralComplexTwist_linear_statement` was
checked separately by whole-word searches of both active Lean roots. The same
whole-word audit checked all 22 names in both roots, active DAG fields and all
quarantine paths. No external user or forced adaptation was found. Public
instances such as `completedIntegralLinear` are retained, including those whose
uses can be implicit rather than named.

## Status

landed 20261026T065042-L-2679916 2026-10-26 (merge of deliver/A4/Sheaf.Paper.CoefficientTwistsDetailed)
