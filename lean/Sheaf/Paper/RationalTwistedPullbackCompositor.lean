module

public import Sheaf.Paper.OrientationIntegralCoefficientTwists
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.PuritySourceTransports

import Sheaf.Paper.IntegralSystemReductionFullyFaithful

/-! # The canonical rational twisted pullback compositor

Source: current blueprint, sec-smooth-purity/sk-thm-purity-transport,
composition transport; the ordered Tate splitting of sk-prop-sp-composition
(blueprint: def-pur-rational-twisted-pullback-compositor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option Elab.async false
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField HasDerivedCategory.standard
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
namespace WeilConjectures.RationalTwistedPullback


open scoped TensorProduct

private theorem map_heq {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B A' B' : C} (hA : A = A') (hB : B = B')
    {a : A ⟶ B} {b : A' ⟶ B'} (h : HEq a b) : HEq (F.map a) (F.map b) := by
  subst A'
  subst B'
  exact heq_of_eq (congrArg F.map (eq_of_heq h))

private def tensorLeft {C : Type*} [Category* C] (T : C × C ⥤ C) (M : C) : C ⥤ C :=
  ((Functor.const C).obj M).prod' (𝟭 C) ⋙ T

private theorem map_pair_comp {C D S : Type*} [Category* C] [Category* D] [Category* S]
    (T : C × D ⥤ S) {A B C' : C} {X Y Z : D}
    (a : A ⟶ B) (b : X ⟶ Y) (a' : B ⟶ C') (b' : Y ⟶ Z) :
    T.map (Prod.mkHom a b) ≫ T.map (Prod.mkHom a' b') =
      T.map (Prod.mkHom (a ≫ a') (b ≫ b')) := by
  rw [← T.map_comp]
  rfl

private theorem naturality_of_map {C D S : Type*}
    [Category* C] [Category* D] [Category* S]
    (F G : C ⥤ D) (R : D ⥤ S) [R.Faithful] (H J : C ⥤ S)
    (a : F ⋙ R ≅ H) (b : G ⋙ R ≅ J) (c : H ≅ J)
    (e : ∀ K, F.obj K ≅ G.obj K)
    (he : ∀ K, R.map (e K).hom ≫ b.hom.app K = a.hom.app K ≫ c.hom.app K)
    {K N : C} (v : K ⟶ N) : F.map v ≫ (e N).hom = (e K).hom ≫ G.map v := by
  apply R.map_injective
  apply (cancel_mono (b.hom.app N)).1
  simp only [Functor.map_comp, Category.assoc]
  have ha := a.hom.naturality v
  have hb := b.hom.naturality v
  change R.map (F.map v) ≫ a.hom.app N = a.hom.app K ≫ H.map v at ha
  change R.map (G.map v) ≫ b.hom.app N = b.hom.app K ≫ J.map v at hb
  rw [he, ← Category.assoc, ha, Category.assoc, c.hom.naturality]
  rw [← Category.assoc, ← he, Category.assoc, ← hb]

private theorem counit_model_naturality
    {C D S : Type*} [Category* C] [Category* D] [Category* S]
    (R : D ⥤ S) (L : S ⥤ D) (adj : R ⊣ L) (F : C ⥤ D) (H : C ⥤ S)
    (a : F ≅ H ⋙ L) {M N : C} (v : M ⟶ N) :
    R.map (F.map v) ≫ R.map (a.hom.app N) ≫ adj.counit.app (H.obj N) =
      R.map (a.hom.app M) ≫ adj.counit.app (H.obj M) ≫ H.map v := by
  rw [← R.map_comp_assoc, a.hom.naturality, R.map_comp]
  simp only [Functor.comp_map, Category.assoc]
  exact congrArg (fun k ↦ R.map (a.hom.app M) ≫ k)
    (adj.counit.naturality (H.map v))

private theorem raw_naturality {R : Type*} [CommRing R]
    {C D : Type*} [Category* C] [Preadditive C] [Linear R C]
    [Category* D] [Preadditive D] [Linear R D] (t : R)
    (U V : C ⥤ D) (a : ∀ K, U.obj K ≅ V.obj K)
    (ha : ∀ {K N} (v : K ⟶ N), U.map v ≫ (a N).hom = (a K).hom ≫ V.map v)
    (F G : ScalarLocalization R C t ⥤ ScalarLocalization R D t)
    [F.Additive] [G.Additive]
    (hF : ∀ K, F.obj K = ⟨U.obj K.obj⟩)
    (hG : ∀ K, G.obj K = ⟨V.obj K.obj⟩)
    (mF : ∀ (K N : C) (v : K ⟶ N) (c : Localization.Away t),
      HEq (F.map (c ⊗ₜ[R] v : ScalarLocalization.mk K ⟶ ScalarLocalization.mk N))
        (c ⊗ₜ[R] U.map v))
    (mG : ∀ (K N : C) (v : K ⟶ N) (c : Localization.Away t),
      HEq (G.map (c ⊗ₜ[R] v : ScalarLocalization.mk K ⟶ ScalarLocalization.mk N))
        (c ⊗ₜ[R] V.map v))
    (e : ∀ K, F.obj K ≅ G.obj K)
    (he : ∀ K, HEq (e K).hom
      ((ScalarLocalization.localization R D t).map (a K.obj).hom))
    (K N : ScalarLocalization R C t) (v : K ⟶ N) :
    F.map v ≫ (e N).hom = (e K).hom ≫ G.map v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [F.map_add, G.map_add, Preadditive.add_comp, Preadditive.comp_add, hx, hy]
  | tmul c v =>
    apply eq_of_heq
    refine (heq_comp (hF K) (hF N) (hG N) (mF K.obj N.obj v c) (he N)).trans ?_
    apply HEq.trans _
      (heq_comp (hF K) (hG K) (hG N) (he K) (mG K.obj N.obj v c)).symm
    apply heq_of_eq
    change ScalarLocalization.composition R D t _ _ _ (1 ⊗ₜ[R] (a N.obj).hom)
        (c ⊗ₜ[R] U.map v) =
      ScalarLocalization.composition R D t _ _ _ (c ⊗ₜ[R] V.map v)
        (1 ⊗ₜ[R] (a K.obj).hom)
    simp only [ScalarLocalization.composition_tmul, one_mul, mul_one, ha v]

private def tensorLeftIso {C : Type*} [Category* C] (T : C × C ⥤ C)
    {M N : C} (e : M ≅ N) : tensorLeft T M ≅ tensorLeft T N :=
  NatIso.ofComponents (fun P ↦ T.mapIso (Iso.prod e (Iso.refl P))) (by
    intro P Q a
    change T.map (Prod.mkHom (𝟙 M) a) ≫ T.map (Prod.mkHom e.hom (𝟙 Q)) =
      T.map (Prod.mkHom e.hom (𝟙 P)) ≫ T.map (Prod.mkHom (𝟙 N) a)
    simp only [map_pair_comp, Category.id_comp, Category.comp_id])

private def tensorLeftComparison {C D : Type*} [Category* C] [Category* D]
    (T : C × C ⥤ C) (I : D × D ⥤ D) (R : C ⥤ D)
    (b : T ⋙ R ≅ R.prod R ⋙ I) (M : C) :
    tensorLeft T M ⋙ R ≅ R ⋙ tensorLeft I (R.obj M) :=
  NatIso.ofComponents (fun P ↦ b.app (M, P)) (by
    intro P Q a
    have hn := b.hom.naturality (Prod.mkHom (𝟙 M) a)
    change R.map (T.map (Prod.mkHom (𝟙 M) a)) ≫ b.hom.app (M, Q) =
      b.hom.app (M, P) ≫ I.map (Prod.mkHom (R.map (𝟙 M)) (R.map a)) at hn
    rw [R.map_id] at hn
    exact hn)

private theorem associator_naturality_of_reduction {C D : Type*}
    [Category* C] [Category* D] (T : C × C ⥤ C) (I : D × D ⥤ D)
    (R : C ⥤ D) [R.Faithful] (b : T ⋙ R ≅ R.prod R ⋙ I)
    (a : ∀ M N P, T.obj (T.obj (M, N), P) ≅ T.obj (M, T.obj (N, P)))
    (c : ∀ M N P, I.obj (I.obj (M, N), P) ≅ I.obj (M, I.obj (N, P)))
    (hc : ∀ M N {P Q} (v : P ⟶ Q),
      I.map (Prod.mkHom (𝟙 _) v) ≫ (c M N Q).hom =
        (c M N P).hom ≫ I.map (Prod.mkHom (𝟙 _) (I.map (Prod.mkHom (𝟙 _) v))))
    (ha : ∀ M N P, R.map (a M N P).hom ≫ b.hom.app (M, T.obj (N, P)) ≫
        I.map (Prod.mkHom (𝟙 _) (b.hom.app (N, P))) =
      b.hom.app (T.obj (M, N), P) ≫
        I.map (Prod.mkHom (b.hom.app (M, N)) (𝟙 _)) ≫
        (c (R.obj M) (R.obj N) (R.obj P)).hom)
    (M N P Q : C) (v : P ⟶ Q) :
    T.map (Prod.mkHom (𝟙 _) v) ≫ (a M N Q).hom =
      (a M N P).hom ≫ T.map (Prod.mkHom (𝟙 _) (T.map (Prod.mkHom (𝟙 _) v))) := by
  let F := tensorLeft T (T.obj (M, N))
  let G := tensorLeft T N ⋙ tensorLeft T M
  let H := R ⋙ tensorLeft I (I.obj (R.obj M, R.obj N))
  let J := R ⋙ (tensorLeft I (R.obj N) ⋙ tensorLeft I (R.obj M))
  let s : F ⋙ R ≅ H := tensorLeftComparison T I R b (T.obj (M, N)) ≪≫
    isoWhiskerLeft R (tensorLeftIso I (b.app (M, N)))
  let t : G ⋙ R ≅ J :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (tensorLeft T N) (tensorLeftComparison T I R b M) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (tensorLeftComparison T I R b N) (tensorLeft I (R.obj M)) ≪≫
      Functor.associator _ _ _
  let z : H ≅ J := isoWhiskerLeft R
    (NatIso.ofComponents (c (R.obj M) (R.obj N))
      (fun v ↦ hc (R.obj M) (R.obj N) v))
  apply naturality_of_map F G R H J s t z (a M N) ?_ v
  intro K
  simp only [s, t, z, tensorLeftComparison, tensorLeftIso,
    NatIso.ofComponents_hom_app, NatTrans.comp_app, Iso.app_hom, Iso.trans_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Iso.symm_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom,
    tensorLeft, Functor.comp_map, Functor.prod'_map, Functor.const_obj_map,
    Functor.id_map, Category.id_comp, Category.comp_id, Category.assoc]
  change R.map (a M N K).hom ≫ 𝟙 (R.obj (T.obj (M, T.obj (N, K)))) ≫
      b.hom.app (M, T.obj (N, K)) ≫ I.map (Prod.mkHom (𝟙 _) (b.hom.app (N, K))) =
    b.hom.app (T.obj (M, N), K) ≫
      I.map (Prod.mkHom (b.hom.app (M, N)) (𝟙 _)) ≫
        (c (R.obj M) (R.obj N) (R.obj K)).hom
  simpa only [Category.id_comp] using ha M N K

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The shifted line in the already specified rational source coordinates.
Source: purity transport, H_h (blueprint: def-pur-rational-twisted-pullback-compositor). -/
abbrev line (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] (d : ℕ) :=
  (sfRationalTwistingCoefficient l E X (d : ℤ))⟦2 * (d : ℤ)⟧

/-- Identify the intrinsic shifted line with its one-term integral complex.
Source: purity transport, canonical shift identification
(blueprint: def-pur-rational-twisted-pullback-compositor). -/
def integralModelIso (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (d : ℕ) :
    ((sfIntegralTwistingCoefficient l E X (d : ℤ))⟦2 * (d : ℤ)⟧).obj ≅
      DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d) :=
  ((sfIntegralConstructible l E X).ι.commShiftIso (2 * (d : ℤ))).app _ ≪≫
    ((DerivedCategory.singleFunctors _).shiftIso (2 * (d : ℤ))
      (-2 * (d : ℤ)) 0 (by omega)).app
        (FrobeniusCoefficientTwists.positiveLine l E X d)

/-- The actual one-term line, as an object of the existing integral category.
Source: purity transport, integral line model
(blueprint: def-pur-rational-twisted-pullback-compositor). -/
def model (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] (d : ℕ) :
    sfIntegralConstructibleCategory l E X :=
  ⟨DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d),
    (sfIntegralConstructible l E X).prop_of_iso (integralModelIso l E X d)
      ((sfIntegralTwistingCoefficient l E X (d : ℤ))⟦2 * (d : ℤ)⟧).property⟩

/-- Localize the specified single-complex shift identification.
Source: purity transport, rational line model
(blueprint: def-pur-rational-twisted-pullback-compositor). -/
def modelIso (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] (d : ℕ) :
    line l E X d ≅ (sfRationalConstructibleLocalization l E X).obj (model l E X d) :=
  ((sfRationalConstructibleLocalization l E X).commShiftIso
    (2 * (d : ℤ))).symm.app _ ≪≫
    (sfRationalConstructibleLocalization l E X).mapIso
      (ObjectProperty.isoMk _ (integralModelIso l E X d))

/-- Shifted Tate multiplication is the localization of the root-normalized product.
The single complexes have even degrees, so this includes the specified Koszul sign.
Source: purity transport, twist addition
(blueprint: def-pur-rational-twisted-pullback-compositor). -/
def product (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] (d e : ℕ) :
    (rationalDerivedTensor l E X).obj (line l E X d, line l E X e) ≅
      line l E X (d + e) :=
  (rationalDerivedTensor l E X).mapIso (Iso.prod (modelIso l E X d) (modelIso l E X e)) ≪≫
    eqToIso ((rationalDerivedTensor_existsUnique l E X).exists.choose_spec.1 _) ≪≫
    (sfRationalConstructibleLocalization l E X).mapIso
      (ObjectProperty.isoMk _ (by
        change (integralCompletedTensor l E X).obj
          (DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d),
            DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X e)) ≅ _
        exact sfOrientationIntegralDerivedProduct l E X d e)) ≪≫
    (modelIso l E X (d + e)).symm

/-- Pull back the actual shifted line by its root-normalized integral comparison.
Source: purity transport, twist pullback
(blueprint: def-pur-rational-twisted-pullback-compositor). -/
def pull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (e : ℕ) :
    (rationalDerivedPullback l E f).obj (line l E Y e) ≅ line l E X e :=
  (rationalDerivedPullback l E f).mapIso (modelIso l E Y e) ≪≫
    eqToIso ((rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 _) ≪≫
    (sfRationalConstructibleLocalization l E X).mapIso
      (ObjectProperty.isoMk _ (by
        change (integralDerivedPullback l E f).obj
          (DerivedCategory.Q.obj (sfOrientationIntegralComplex l E Y e)) ≅ _
        exact sfOrientationIntegralDerivedPull l E f e)) ≪≫
    (modelIso l E X e).symm

private theorem chosenUnique_spec {A : Sort*} {p : A → Prop} (h : ∃! a, p a)
    (a : A) (ha : a = h.exists.choose) : p a :=
  ha.symm ▸ h.exists.choose_spec

private abbrev tensor_spec (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :=
  chosenUnique_spec (rationalDerivedTensor_existsUnique l E W)
    (rationalDerivedTensor l E W) rfl

attribute [local irreducible] rationalDerivedTensor sfIntegralConstructible

private def coherentReduction (W : Scheme.{u}) :
    sfIntegralConstructibleCategory l E W ⥤ coefficientSequenceDerived l E W :=
  (sfIntegralConstructible l E W).ι ⋙ (pullbackTensorCalculus l E W).reduction

private def reductionTensor (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    constructibleIntegralTensor l E W ⋙ coherentReduction l E W ≅
      (coherentReduction l E W).prod (coherentReduction l E W) ⋙
        (pullbackTensorCalculus l E W).systemClosed.tensor :=
  NatIso.ofComponents (fun MN ↦ pullbackTensorIntegralReductionTensor l E W MN.1 MN.2) (by
    intro MN PQ k
    dsimp only [pullbackTensorIntegralReductionTensor, Iso.trans_hom,
      Functor.mapIso_hom, asIso_hom]
    simpa only [Category.assoc, Iso.app_hom, coherentReduction,
      constructibleIntegralTensor, ObjectProperty.lift, Functor.comp_map,
      Functor.comp_obj, Functor.id_obj, ObjectProperty.ι_obj, ObjectProperty.ι_map,
      ObjectProperty.homMk, Functor.prod_map, Functor.prod_obj, pullbackTensorCalculus] using
      counit_model_naturality
        (pullbackTensorCalculus l E W).reduction (coefficientSequenceLimit l E W)
        (pullbackTensorCalculus l E W).adjunction (integralCompletedTensor l E W)
        (((pullbackTensorCalculus l E W).reduction.prod
          (pullbackTensorCalculus l E W).reduction) ⋙
          (pullbackTensorCalculus l E W).systemClosed.tensor)
        (pullbackTensorIntegralTensorModel l E W) (Prod.mkHom k.1.hom k.2.hom))

private theorem integral_associator_naturality (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N P Q : sfIntegralConstructibleCategory l E W) (v : P ⟶ Q) :
    (constructibleIntegralTensor l E W).map (Prod.mkHom (𝟙 _) v) ≫
        (pullbackTensorIntegralAssociator l E W M N Q).hom =
      (pullbackTensorIntegralAssociator l E W M N P).hom ≫
        (constructibleIntegralTensor l E W).map
          (Prod.mkHom (𝟙 _) ((constructibleIntegralTensor l E W).map
            (Prod.mkHom (𝟙 _) v))) := by
  have : (coherentReduction l E W).Faithful := by
    simpa only [coherentReduction, integralSystemReduction, pullbackTensorCalculus] using
      (integralSystemReduction_fullyFaithful l E W).2
  apply associator_naturality_of_reduction
    (constructibleIntegralTensor l E W) (pullbackTensorCalculus l E W).systemClosed.tensor
    (coherentReduction l E W) (reductionTensor l E W)
    (pullbackTensorIntegralAssociator l E W)
    (pullbackTensorCalculus l E W).systemClosed.monoidal.associator
    (fun M N P Q v ↦ ?_) (fun M N P ↦ ?_) M N P Q v
  · exact @MonoidalCategory.id_tensor_associator_naturality _ _
      (pullbackTensorCalculus l E W).systemClosed.monoidal M N P Q v
  · exact (pullbackTensorIntegralAssociator_existsUnique l E W M N P).exists.choose_spec

private theorem pullback_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedPullback l E f).obj K =
      (sfRationalConstructibleLocalization l E X).obj
        ((constructibleIntegralPullback l E f).obj K.obj) :=
  (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K

private theorem pullback_tmul {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K N : sfIntegralConstructibleCategory l E Y) (a : K ⟶ N)
    (b : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
    HEq ((rationalDerivedPullback l E f).map
      (b ⊗ₜ[Padic.coefficientExtensionIntegers l E] a))
      (b ⊗ₜ[Padic.coefficientExtensionIntegers l E]
        (constructibleIntegralPullback l E f).map a) :=
  (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.2 K N a b

private theorem composition_naturality {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K N : sfRationalConstructibleCategory l E Z) (v : K ⟶ N) :
    (rationalDerivedPullback l E (f ≫ g)).map v ≫
        (pullbackTensorRationalComposition l E g f N).hom =
      (pullbackTensorRationalComposition l E g f K).hom ≫
        (rationalDerivedPullback l E f).map ((rationalDerivedPullback l E g).map v) := by
  have : (rationalDerivedPullback l E f).Additive :=
    (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.1
  have : (rationalDerivedPullback l E g).Additive :=
    (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.1
  have : (rationalDerivedPullback l E (f ≫ g)).Additive :=
    (rationalDerivedPullback_existsUnique l E (f ≫ g)).exists.choose_spec.1
  have hc (P : sfRationalConstructibleCategory l E Z) :=
    (pullbackTensorRationalComposition_existsUnique l E g f P).exists.choose_spec
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    change (rationalDerivedPullback l E (f ≫ g)).map (a + b : K ⟶ N) ≫ _ = _
    rw [Functor.map_add, Preadditive.add_comp, ha, hb, ← Preadditive.comp_add,
      ← Functor.map_add, ← Functor.map_add]
  | tmul b a =>
    have hh : HEq ((rationalDerivedPullback l E f).map
        ((rationalDerivedPullback l E g).map (b ⊗ₜ[_] a)))
        (b ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          (constructibleIntegralPullback l E f).map
            ((constructibleIntegralPullback l E g).map a)) :=
      (map_heq _ (pullback_obj l E g K) (pullback_obj l E g N)
        (pullback_tmul l E g K.obj N.obj a b)).trans
          (pullback_tmul l E f _ _ ((constructibleIntegralPullback l E g).map a) b)
    apply eq_of_heq
    apply (heq_comp (pullback_obj l E (f ≫ g) K)
      (pullback_obj l E (f ≫ g) N) (by rw [pullback_obj, pullback_obj]; rfl)
      (pullback_tmul l E (f ≫ g) K.obj N.obj a b) (hc N)).trans
    apply HEq.trans _ (heq_comp (pullback_obj l E (f ≫ g) K)
      (by rw [pullback_obj, pullback_obj]; rfl)
      (by rw [pullback_obj, pullback_obj]; rfl) (hc K) hh).symm
    change HEq (ScalarLocalization.composition _ _ _ _ _ _ (1 ⊗ₜ[_] _) (b ⊗ₜ[_] _))
      (ScalarLocalization.composition _ _ _ _ _ _ (b ⊗ₜ[_] _) (1 ⊗ₜ[_] _))
    rw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul,
      mul_one, one_mul]
    exact heq_of_eq (congrArg (fun a ↦ b ⊗ₜ[Padic.coefficientExtensionIntegers l E] a)
      ((pullbackTensorIntegralComposition l E g f).hom.naturality a))

private theorem tensor_obj (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (MN : sfRationalConstructibleCategory l E W × sfRationalConstructibleCategory l E W) :
    (rationalDerivedTensor l E W).obj MN =
      (sfRationalConstructibleLocalization l E W).obj
        ((constructibleIntegralTensor l E W).obj (MN.1.obj, MN.2.obj)) :=
  (tensor_spec l E W).1 MN

private theorem tensor_left_additive (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :
    (tensorLeft (rationalDerivedTensor l E W) M).Additive := by
  constructor
  intro P Q a b
  obtain ⟨B, hB, _⟩ :=
    (tensor_spec l E W).2 M M P Q
  change ∀ a b, (rationalDerivedTensor l E W).map (Prod.mkHom a b) = B a b at hB
  change (rationalDerivedTensor l E W).map (Prod.mkHom (𝟙 M) (a + b)) =
    (rationalDerivedTensor l E W).map (Prod.mkHom (𝟙 M) a) +
      (rationalDerivedTensor l E W).map (Prod.mkHom (𝟙 M) b)
  rw [hB, hB, hB, LinearMap.map_add]

private theorem tensor_left_tmul (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M P Q : sfRationalConstructibleCategory l E W) (a : P.obj ⟶ Q.obj)
    (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
    HEq ((tensorLeft (rationalDerivedTensor l E W) M).map
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] a))
      (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
        (constructibleIntegralTensor l E W).map (Prod.mkHom (𝟙 M.obj) a)) := by
  obtain ⟨B, hB, h⟩ :=
    (tensor_spec l E W).2 M M P Q
  change ∀ a b, (rationalDerivedTensor l E W).map (Prod.mkHom a b) = B a b at hB
  change HEq ((rationalDerivedTensor l E W).map
    (Prod.mkHom (1 ⊗ₜ[Padic.coefficientExtensionIntegers l E] (𝟙 M.obj))
      (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] a))) _
  rw [hB]
  simpa only [one_mul] using h (𝟙 M.obj) a 1 c

private theorem associator_naturality (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N P Q : sfRationalConstructibleCategory l E W) (v : P ⟶ Q) :
    (rationalDerivedTensor l E W).map (Prod.mkHom (𝟙 _) v) ≫
        (pullbackTensorRationalAssociator l E W M N Q).hom =
      (pullbackTensorRationalAssociator l E W M N P).hom ≫
        (rationalDerivedTensor l E W).map
          (Prod.mkHom (𝟙 _) ((rationalDerivedTensor l E W).map
            (Prod.mkHom (𝟙 _) v))) := by
  let T := rationalDerivedTensor l E W
  let I := constructibleIntegralTensor l E W
  let U := tensorLeft I (I.obj (M.obj, N.obj))
  let V := tensorLeft I N.obj ⋙ tensorLeft I M.obj
  let F := tensorLeft T (T.obj (M, N))
  let G := tensorLeft T N ⋙ tensorLeft T M
  have : (tensorLeft T M).Additive := tensor_left_additive l E W M
  have : (tensorLeft T N).Additive := tensor_left_additive l E W N
  have : F.Additive := tensor_left_additive l E W (T.obj (M, N))
  apply raw_naturality (Padic.coefficientExtensionUniformizer l E) U V
    (pullbackTensorIntegralAssociator l E W M.obj N.obj)
    (fun v ↦ integral_associator_naturality l E W M.obj N.obj _ _ v) F G
    (fun K ↦ ?_) (fun K ↦ ?_) (fun K J a c ↦ ?_) (fun K J a c ↦ ?_)
    (pullbackTensorRationalAssociator l E W M N)
    (fun K ↦ (pullbackTensorRationalAssociator_existsUnique l E W M N K).exists.choose_spec)
    P Q v
  · change T.obj (T.obj (M, N), K) = _
    rw [tensor_obj, tensor_obj]
    rfl
  · change T.obj (M, T.obj (N, K)) = _
    rw [tensor_obj, tensor_obj]
    rfl
  · have hMN : (T.obj (M, N)).obj = I.obj (M.obj, N.obj) :=
      congrArg (fun K : sfRationalConstructibleCategory l E W ↦ K.obj)
        (tensor_obj l E W (M, N))
    have ht := tensor_left_tmul l E W (T.obj (M, N)) ⟨K⟩ ⟨J⟩ a c
    rw [hMN] at ht
    simpa only [F, U, T, I, tensorLeft, Functor.comp_map, Functor.prod'_map,
      Functor.const_obj_map, Functor.id_map] using ht
  · exact (map_heq (tensorLeft T M) (tensor_obj l E W (N, ⟨K⟩))
      (tensor_obj l E W (N, ⟨J⟩)) (tensor_left_tmul l E W N ⟨K⟩ ⟨J⟩ a c)).trans
        (tensor_left_tmul l E W M _ _
          ((constructibleIntegralTensor l E W).map (Prod.mkHom (𝟙 N.obj) a)) c)

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ z : Z, Invertible (l : Z.residueField z)] (d e : ℕ)

/-- The canonical compositor, assembled from ordered line splitting, pullback
composition, associativity, inverse line pullback and inverse tensor pullback.
Source: purity transport, canonical u; composition proof, ordered splitting
(blueprint: def-pur-rational-twisted-pullback-compositor). -/
def component (K : sfRationalConstructibleCategory l E Z) :
    (RationalSmoothPurityCanonical.rationalSource l E (f ≫ g) (d + e)).obj K ≅
      (RationalSmoothPurityCanonical.rationalSource l E f d).obj
        ((RationalSmoothPurityCanonical.rationalSource l E g e).obj K) :=
  (rationalDerivedTensor l E X).mapIso
      (Iso.prod (product l E X d e).symm
        (pullbackTensorRationalComposition l E g f K)) ≪≫
    pullbackTensorRationalAssociator l E X (line l E X d) (line l E X e)
      ((rationalDerivedPullback l E f).obj ((rationalDerivedPullback l E g).obj K)) ≪≫
    (rationalDerivedTensor l E X).mapIso (Iso.prod (Iso.refl _)
      ((rationalDerivedTensor l E X).mapIso (Iso.prod (pull l E f e).symm (Iso.refl _)) ≪≫
        (canonicalRationalPullbackTensor l E f (line l E Y e)
          ((rationalDerivedPullback l E g).obj K)).symm))

attribute [local irreducible] product pull rationalDerivedPullback
  pullbackTensorRationalComposition pullbackTensorRationalAssociator
  canonicalRationalPullbackTensor

/-- The five canonical factors are natural on all rational arrows.
Source: purity transport, naturality of u
(blueprint: def-pur-rational-twisted-pullback-compositor).
Proof: line splitting is constant in K. Pullback composition is natural by its
whole-system construction. Tensor associativity is natural by its coherent
reduction normalization. The line pullback is constant in K, and the monoidal
pullback comparison is natural in both arguments. Apply functoriality of tensor
to each square and paste them; cancel each intermediate comparison with its inverse.
The resulting outside square is the equation below, including rational fractions. -/
theorem component_naturality (K N : sfRationalConstructibleCategory l E Z) (v : K ⟶ N) :
    (RationalSmoothPurityCanonical.rationalSource l E (f ≫ g) (d + e)).map v ≫
        (component l E f g d e N).hom =
      (component l E f g d e K).hom ≫
        (RationalSmoothPurityCanonical.rationalSource l E f d).map
          ((RationalSmoothPurityCanonical.rationalSource l E g e).map v) := by
  let T := rationalDerivedTensor l E X
  let P := rationalDerivedPullback l E f
  let Q := rationalDerivedPullback l E g
  let R := rationalDerivedPullback l E (f ≫ g)
  let A := line l E X d
  let B := line l E X e
  let C := line l E Y e
  let F₁ := (Q ⋙ P) ⋙ tensorLeft T (T.obj (A, B))
  let F₂ := (Q ⋙ P) ⋙ (tensorLeft T B ⋙ tensorLeft T A)
  let a : RationalSmoothPurityCanonical.rationalSource l E (f ≫ g) (d + e) ≅ F₁ :=
    NatIso.ofComponents (fun K ↦ T.mapIso
      (Iso.prod (product l E X d e).symm (pullbackTensorRationalComposition l E g f K)))
      (by
        intro K N v
        change T.map (Prod.mkHom (𝟙 _) (R.map v)) ≫
            T.map (Prod.mkHom (product l E X d e).inv
              (pullbackTensorRationalComposition l E g f N).hom) =
          T.map (Prod.mkHom (product l E X d e).inv
              (pullbackTensorRationalComposition l E g f K).hom) ≫
            T.map (Prod.mkHom (𝟙 _) (P.map (Q.map v)))
        rw [map_pair_comp, map_pair_comp]
        congr 1
        ext
        · simp
        · simpa only [Category.id_comp, Category.comp_id] using
            composition_naturality l E f g K N v)
  let b : F₁ ≅ F₂ :=
    NatIso.ofComponents
      (fun K ↦ pullbackTensorRationalAssociator l E X A B (P.obj (Q.obj K)))
      (fun v ↦ associator_naturality l E X A B _ _ (P.map (Q.map v)))
  obtain ⟨β, hβ⟩ := (derivedPullbackTensorIso l E f 0
    (AlgebraicClosure (Padic l))).2.2.2.2.2.2.1
  let h : P ⋙ tensorLeft T B ≅ tensorLeft (rationalDerivedTensor l E Y) C ⋙ P :=
    NatIso.ofComponents (fun K ↦
      T.mapIso (Iso.prod (pull l E f e).symm (Iso.refl _)) ≪≫
        (canonicalRationalPullbackTensor l E f C K).symm) (by
      intro K N v
      have h₁ := (tensorLeftIso T (pull l E f e).symm).hom.naturality (P.map v)
      have h₂ := β.inv.naturality (Prod.mkHom (𝟙 C) v)
      have hβi := fun M N ↦ congrArg Iso.inv (hβ M N)
      change ∀ M N, β.inv.app (M, N) = _ at hβi
      simp only [Functor.comp_map, Functor.prod_map] at h₂
      rw [hβi, hβi, (rationalDerivedPullback l E f).map_id] at h₂
      change T.map (Prod.mkHom (𝟙 B) (P.map v)) ≫
          T.map (Prod.mkHom (pull l E f e).inv (𝟙 _)) =
        T.map (Prod.mkHom (pull l E f e).inv (𝟙 _)) ≫
          T.map (Prod.mkHom (𝟙 (P.obj C)) (P.map v)) at h₁
      change T.map (Prod.mkHom (𝟙 B) (P.map v)) ≫
          (T.map (Prod.mkHom (pull l E f e).inv (𝟙 _)) ≫
            (canonicalRationalPullbackTensor l E f C N).inv) =
        (T.map (Prod.mkHom (pull l E f e).inv (𝟙 _)) ≫
          (canonicalRationalPullbackTensor l E f C K).inv) ≫
            P.map ((rationalDerivedTensor l E Y).map (Prod.mkHom (𝟙 C) v))
      rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc])
  let c : F₂ ≅ RationalSmoothPurityCanonical.rationalSource l E g e ⋙
      RationalSmoothPurityCanonical.rationalSource l E f d :=
    NatIso.ofComponents
      (fun K ↦ T.mapIso (Iso.prod (Iso.refl A) (h.app (Q.obj K)))) (by
        intro K N v
        change T.map (Prod.mkHom (𝟙 A) _) ≫
            T.map (Prod.mkHom (𝟙 A) (h.hom.app (Q.obj N))) =
          T.map (Prod.mkHom (𝟙 A) (h.hom.app (Q.obj K))) ≫
            T.map (Prod.mkHom (𝟙 A) _)
        rw [map_pair_comp, map_pair_comp]
        congr 1
        ext
        · simp
        · change (P ⋙ tensorLeft T B).map (Q.map v) ≫ h.hom.app (Q.obj N) =
            h.hom.app (Q.obj K) ≫
              (tensorLeft (rationalDerivedTensor l E Y) C ⋙ P).map (Q.map v)
          exact h.hom.naturality (Q.map v))
  exact (a ≪≫ b ≪≫ c).hom.naturality v

/-- The specified natural twisted pullback compositor.
Source: purity transport, u (blueprint: def-pur-rational-twisted-pullback-compositor). -/
def compositor :
    RationalSmoothPurityCanonical.rationalSource l E (f ≫ g) (d + e) ≅
      RationalSmoothPurityCanonical.rationalSource l E g e ⋙
        RationalSmoothPurityCanonical.rationalSource l E f d :=
  NatIso.ofComponents (component l E f g d e) (fun {K N} v ↦ component_naturality l E f g d e K N v)

end WeilConjectures.RationalTwistedPullback
