module

public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.LocalFrobeniusTrace

/-! # Constructible and rational forms of the normalized pullback comparisons

Source: Stacks 099N, 0D6D and 06YY; blueprint main-20261015,
sec-trace-formula/sk-thm-trace-transport/prop-trf-karoubi-independence.proof.md,
final common-stage Frobenius transport sentence
(blueprint: def-trf-realized-pullback-comparisons).

The constructible compositor restricts the specified integral compositor. The rational
compositor and scalar comparison are its raw localizations, with their prescribed
object identifications.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open TensorProduct

private theorem map_heq {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) {K J K' J' : A} (hK : K = K') (hJ : J = J')
    {f : K ⟶ J} {g : K' ⟶ J'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hK
  cases hJ
  cases h
  rfl

section ComparisonInterface

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (C : IntegralComparisonSystem.{u} l)

/-- The specified compositor in the fully faithful constructible subcategory.
Source: Stacks 099N, 0D6D; blueprint final common-stage transport paragraph
(blueprint: def-trf-realized-pullback-comparisons). -/
def integralComparisonConstructibleComposition {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    (constructibleIntegralPullback l E (h ≫ k)).obj K ≅
      (constructibleIntegralPullback l E h).obj
        ((constructibleIntegralPullback l E k).obj K) :=
  ObjectProperty.isoMk _ (integralComparisonComposition l E C h k K)

/-- Raw rationalization of exactly the counit-normalized integral compositor.
Source: Stacks 099N, 0D6D; blueprint final common-stage transport paragraph
(blueprint: def-trf-realized-pullback-comparisons). -/
def integralComparisonRationalComposition {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfRationalConstructibleCategory l E V) :
    (rationalDerivedPullback l E (h ≫ k)).obj K ≅
      (rationalDerivedPullback l E h).obj ((rationalDerivedPullback l E k).obj K) :=
  localPullbackObjectIso l E (h ≫ k) K ≪≫
    (sfRationalConstructibleLocalization l E Z).mapIso
      (integralComparisonConstructibleComposition l E C h k K.obj) ≪≫
    (localPullbackObjectIso l E h
      ((sfRationalConstructibleLocalization l E W).obj
        ((constructibleIntegralPullback l E k).obj K.obj))).symm ≪≫
    (rationalDerivedPullback l E h).mapIso (localPullbackObjectIso l E k K).symm

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (ι : E →ₐ[ℚ_[l]] M)

/-- The component of the rational scalar comparison at `K`: the raw localization of the
specified integral scalar comparison `a^C_{f,K.obj}`, between the prescribed object
formulas of rational pullback and rational scalar extension.
Source: Stacks 06YY, 099N; blueprint final common-stage transport paragraph
(blueprint: def-trf-realized-pullback-comparisons). -/
def integralComparisonRationalScalarComponent {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι).obj
        ((rationalDerivedPullback l E f).obj K) ≅
      (rationalDerivedPullback l M f).obj
        ((sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι).obj
          K) :=
  eqToIso ((congrArg
      (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι).obj
      ((rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K)).trans
      ((sfRationalScalarExtension_existsUnique l E X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι).exists.choose_spec.2.1
        ((sfRationalConstructibleLocalization l E X).obj
          ((constructibleIntegralPullback l E f).obj K.obj)))) ≪≫
    (sfRationalConstructibleLocalization l M X).mapIso
      (ObjectProperty.isoMk _
        (X := (integralComparisonConstructibleScalar l E M ι X).obj
          ((constructibleIntegralPullback l E f).obj K.obj))
        (Y := (constructibleIntegralPullback l M f).obj
          ((integralComparisonConstructibleScalar l E M ι Y).obj K.obj))
        (integralComparisonScalar l E M ι C f K.obj)) ≪≫
    eqToIso (((rationalDerivedPullback_existsUnique l M f).exists.choose_spec.2.1
      ((sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι).obj
        K)).trans (congrArg
          (fun J : sfRationalConstructibleCategory l M Y ↦
            (sfRationalConstructibleLocalization l M X).obj
              ((constructibleIntegralPullback l M f).obj J.obj))
          ((sfRationalScalarExtension_existsUnique l E Y 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι).exists.choose_spec.2.1 K))).symm

attribute [local irreducible] integralComparisonSequenceScalarModel
  integralComparisonPullbackCounit integralComparisonScalarCounit
  integralDerivedPullback integralComparisonDerivedSequencePullback
  integralComparisonDerivedSequenceScalar coefficientSequenceLimit

section IntegralNaturality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

private def thetaLambda
    (D : IntegralComparisonSystem.{u} l) :
    integralDerivedPullback l E f ⋙ integralScalarExtension l E M ι X ⟶
      ((D.coefficient E).system Y).reduction ⋙
        integralComparisonDerivedSequencePullback l E f ⋙
        integralComparisonDerivedSequenceScalar l E M ι X ⋙
        coefficientSequenceLimit l M X :=
  Functor.whiskerLeft (integralDerivedPullback l E f)
      ((D.scalar E M ι).model X).realization.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (integralComparisonPullbackCounit l E f
        ((D.coefficient E).system Y) ((D.coefficient E).system X)
        ((D.coefficient E).roos X) ((D.coefficient E).pullback f)) _ ≫
    (Functor.associator _ _ _).hom

private def thetaMu
    (D : IntegralComparisonSystem.{u} l) :
    integralScalarExtension l E M ι Y ⋙ integralDerivedPullback l M f ⟶
      ((D.coefficient E).system Y).reduction ⋙
        integralComparisonDerivedSequencePullback l E f ⋙
        integralComparisonDerivedSequenceScalar l E M ι X ⋙
        coefficientSequenceLimit l M X :=
  Functor.whiskerLeft (integralScalarExtension l E M ι Y)
      ((D.coefficient M).pullback f).realization.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (integralComparisonScalarCounit l E M ι Y
        ((D.coefficient E).system Y) ((D.coefficient M).system Y)
        ((D.coefficient M).roos Y) ((D.scalar E M ι).model Y)) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((D.coefficient E).system Y).reduction
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (integralComparisonSystemScalarPullback l E M ι f).inv _ ≫
        (Functor.associator _ _ _).hom)

private theorem thetaLambda_app
    (D : IntegralComparisonSystem.{u} l) (K : sfIntegralConstructibleCategory l E Y) :
    (thetaLambda l E M ι f D).app K.obj = (integralComparisonLambda l E M ι D f K).hom := by
  simp only [thetaLambda, integralComparisonLambda, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, asIso_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]

private theorem thetaMu_app
    (D : IntegralComparisonSystem.{u} l) (K : sfIntegralConstructibleCategory l E Y) :
    (thetaMu l E M ι f D).app K.obj = (integralComparisonMu l E M ι D f K).hom := by
  simp only [thetaMu, integralComparisonMu, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv, asIso_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

private theorem theta_comp_mu
    (D : IntegralComparisonSystem.{u} l) (K : sfIntegralConstructibleCategory l E Y) :
    (integralComparisonScalar l E M ι D f K).hom ≫ (thetaMu l E M ι f D).app K.obj =
      (thetaLambda l E M ι f D).app K.obj := by
  rw [thetaMu_app, thetaLambda_app]
  simp only [integralComparisonScalar, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem integralScalar_naturality
    (K J : sfIntegralConstructibleCategory l E Y) (r : K ⟶ J) :
    (integralScalarExtension l E M ι X).map ((integralDerivedPullback l E f).map r.hom) ≫
        (integralComparisonScalar l E M ι C f J).hom =
      (integralComparisonScalar l E M ι C f K).hom ≫
        (integralDerivedPullback l M f).map ((integralScalarExtension l E M ι Y).map r.hom) := by
  apply (cancel_mono (integralComparisonMu l E M ι C f J).hom).1
  simp only [Category.assoc, ← thetaMu_app l E M ι f C,
    theta_comp_mu l E M ι f C]
  have hmu := (thetaMu l E M ι f C).naturality r.hom
  dsimp only [Functor.comp_map] at hmu
  rw [hmu]
  simp only [← Category.assoc, theta_comp_mu l E M ι f C]
  exact (thetaLambda l E M ι f C).naturality r.hom

end IntegralNaturality

/-- The localized integral scalar components are natural for every rational morphism.
Source: Stacks 06YY, 099N; blueprint final common-stage transport paragraph
(blueprint: def-trf-realized-pullback-comparisons).
Proof: by the object formulas the outer arrows are identities, so the square is the
localization of the integral square for `a^C_f`. On a pure tensor `c ⊗ φ` both rational
pullback and rational scalar extension act by their prescribed tensor formulas, and the
integral naturality of `integralComparisonScalar`, recorded by
lem-trf-integral-pullback-comparison-realization, multiplied by the image of `c` gives
the rational square. Both sides are
additive in the morphism, and pure tensors generate every rational Hom group. -/
theorem integralComparisonRationalScalarComponent_naturality {X Y : Scheme.{u}}
    (f : X ⟶ Y) [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    {K K' : sfRationalConstructibleCategory l E Y} (φ : K ⟶ K') :
    (rationalDerivedPullback l E f ⋙
        sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι).map φ ≫
      (integralComparisonRationalScalarComponent l E C M ι f K').hom =
    (integralComparisonRationalScalarComponent l E C M ι f K).hom ≫
      (sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι ⋙
        rationalDerivedPullback l M f).map φ := by
  let A := rationalDerivedPullback l E f
  let B := rationalDerivedPullback l M f
  let TX := sfRationalScalarExtension l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι
  let TY := sfRationalScalarExtension l E Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι
  let S (W : Scheme.{u}) := integralComparisonConstructibleScalar l E M ι W
  let U := constructibleIntegralPullback l E f ⋙ S X
  let V := S Y ⋙ constructibleIntegralPullback l M f
  let Q := sfRationalConstructibleLocalization l M X
  let c (z : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :=
    (sfRationalCoefficientEquiv l M).symm (ι (sfRationalCoefficientEquiv l E z))
  have hA := (rationalDerivedPullback_existsUnique l E f).exists.choose_spec
  have hB := (rationalDerivedPullback_existsUnique l M f).exists.choose_spec
  have hS (W : Scheme.{u}) := (sfRationalScalarExtension_existsUnique l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι).exists.choose_spec
  have : A.Additive := hA.1
  have : B.Additive := hB.1
  have hoF (J : sfRationalConstructibleCategory l E Y) :
      (A ⋙ TX).obj J = Q.obj (U.obj J.obj) :=
    (congrArg TX.obj (hA.2.1 J)).trans (hS X |>.2.1 _)
  have hoG (J : sfRationalConstructibleCategory l E Y) :
      (TY ⋙ B).obj J = Q.obj (V.obj J.obj) :=
    (hB.2.1 _).trans (congrArg
      (fun Z : sfRationalConstructibleCategory l M Y ↦
        Q.obj ((constructibleIntegralPullback l M f).obj Z.obj)) (hS Y |>.2.1 J))
  let a (J : sfIntegralConstructibleCategory l E Y) : U.obj J ≅ V.obj J :=
    ObjectProperty.isoMk _ (integralComparisonScalar l E M ι C f J)
  have ha (J : sfRationalConstructibleCategory l E Y) :
      HEq (integralComparisonRationalScalarComponent l E C M ι f J).hom
        (Q.map (a J.obj).hom) := by
    apply (conj_eqToHom_iff_heq _ _ (hoF J) (hoG J)).1
    rfl
  have mF (J J' : sfIntegralConstructibleCategory l E Y) (r : J ⟶ J')
      (z : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
      HEq ((A ⋙ TX).map (z ⊗ₜ[Padic.coefficientExtensionIntegers l E] r))
        (c z ⊗ₜ[Padic.coefficientExtensionIntegers l M] U.map r) := by
    exact (map_heq TX (hA.2.1 _) (hA.2.1 _) (hA.2.2 J J' r z)).trans
      (hS X |>.2.2 _ _ ((constructibleIntegralPullback l E f).map r) z)
  have mG (J J' : sfIntegralConstructibleCategory l E Y) (r : J ⟶ J')
      (z : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
      HEq ((TY ⋙ B).map (z ⊗ₜ[Padic.coefficientExtensionIntegers l E] r))
        (c z ⊗ₜ[Padic.coefficientExtensionIntegers l M] V.map r) := by
    exact (map_heq B (hS Y |>.2.1 _) (hS Y |>.2.1 _)
      (hS Y |>.2.2 J J' r z)).trans
        (hB.2.2 _ _ ((S Y).map r) (c z))
  have hn (J J' : sfIntegralConstructibleCategory l E Y) (r : J ⟶ J') :
      U.map r ≫ (a J').hom = (a J).hom ≫ V.map r := by
    apply ObjectProperty.hom_ext
    exact integralScalar_naturality l E C M ι f J J' r
  change (A ⋙ TX).map φ ≫ _ = _ ≫ (TY ⋙ B).map φ
  induction φ using TensorProduct.induction_on with
  | zero => simp
  | tmul z r =>
    have h₁ := heq_comp (hoF K) (hoF K') (hoG K') (mF K.obj K'.obj r z) (ha K')
    have h₂ := heq_comp (hoF K) (hoG K) (hoG K') (ha K) (mG K.obj K'.obj r z)
    apply eq_of_heq
    refine h₁.trans (HEq.trans ?_ h₂.symm)
    apply heq_of_eq
    change ScalarLocalization.composition _ _ _ _ _ _
        (1 ⊗ₜ[Padic.coefficientExtensionIntegers l M] (a K'.obj).hom)
        (c z ⊗ₜ[Padic.coefficientExtensionIntegers l M] U.map r) =
      ScalarLocalization.composition _ _ _ _ _ _
        (c z ⊗ₜ[Padic.coefficientExtensionIntegers l M] V.map r)
        (1 ⊗ₜ[Padic.coefficientExtensionIntegers l M] (a K.obj).hom)
    simp only [ScalarLocalization.composition_tmul, one_mul, mul_one, hn]
  | add x y hx hy =>
    rw [(A ⋙ TX).map_add, (TY ⋙ B).map_add]
    rw [Preadditive.add_comp, Preadditive.comp_add, hx, hy]

/-- The rational scalar comparison: the natural isomorphism whose component at every `K`
is the localized specified integral comparison of `integralComparisonRationalScalarComponent`.
Source: Stacks 06YY, 099N; blueprint final common-stage transport paragraph
(blueprint: def-trf-realized-pullback-comparisons). -/
def integralComparisonRationalScalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    rationalDerivedPullback l E f ⋙
        sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι ≅
      sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι ⋙
        rationalDerivedPullback l M f :=
  NatIso.ofComponents (integralComparisonRationalScalarComponent l E C M ι f)
    (fun φ ↦ integralComparisonRationalScalarComponent_naturality l E C M ι f φ)

end ComparisonInterface

end WeilConjectures
