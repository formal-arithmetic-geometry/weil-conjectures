/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.IntegralDerivedOperations
public import Sheaf.Paper.IntegralOperationsPreserveConstructible
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields

/-! # Derived pullback, tensor product, and internal Hom

Source: blueprint sec-smooth-purity/sk-def-sf-operations, order 1467;
Stacks Project, Tags 06YL, 06YV, 08J7 and 099N
(blueprint: def-weil-derived-pullback-tensor-hom).

## Main definitions

- `finiteDerivedPullback`: exact intrinsic constant-coefficient inverse image.
- `finiteIntrinsicDerivedTensor`, `finiteIntrinsicDerivedInternalHom`: ambient operations.
- `finiteIntrinsicTensorModels`: K-flat tensor and ordinary evaluation normalization.
- `finiteIntrinsicReductionHom`: reduced evaluation's canonical closed transpose.
- `constructibleIntegralPullback`, `constructibleIntegralTensor`: actual restrictions.
- `constructibleIntegralHom`: ambient Hom restricted to permitted constructible pairs.
- `rationalDerivedPullback`, `rationalDerivedTensor`, `rationalDerivedInternalHom`:
  the uniquely specified linear and bilinear extensions with unchanged integral objects.
- `commonStageDerivedPullback`, `commonStageDerivedTensor`, `commonStageDerivedInternalHom`:
  operations on the recorded pair category, with normalized representative formulas.

Every common-stage comparison rationalizes the prescribed integral comparison.
No idempotent completion, arbitrary isomorphism, or extra coefficient flatness is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open Opposite TensorProduct

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The recorded quotient coefficient ring; every operation below uses exponent n+1.
Source: blueprint `def-weil-derived-pullback-tensor-hom`
(blueprint: def-weil-derived-pullback-tensor-hom).
-/
noncomputable abbrev finiteCoefficientRing (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) := Padic.coefficientExtensionRing l E n

/-- Finite-level derived pullback on the intrinsic constant-ring category.
Source: blueprint `def-weil-derived-pullback-tensor-hom`; uses the exact
pro-etale inverse image of `def-weil-pbc-proetale-operations`.
(blueprint: def-weil-derived-pullback-tensor-hom).
-/
noncomputable abbrev finiteDerivedPullback {X Y : Scheme.{u}}
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (f : X ⟶ Y) :
    proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1)) ⥤
      proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1)) :=
  letI : Finite (finiteCoefficientRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))
  sfIntrinsicDerivedPullback (finiteCoefficientRing l E (n + 1)) f

/-- Intrinsic finite closed structure for the recorded K-injective internal Hom.
The closed universal property and its K-flat evaluation normalization determine
this structure up to the unique compatible isomorphism used downstream.
Source: Stacks 07A4, 08J9; coefficient evaluation calculus
(blueprint: def-weil-derived-pullback-tensor-hom). -/
noncomputable def finiteIntrinsicClosed (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (n : ℕ) :
    CoefficientClosedStructure (coefficientFiniteInternalHom l E W n) :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose.finiteClosed n

/-- Tensor on the actual intrinsic positive-level coefficient category.
Source: Stacks 07A4 (blueprint: def-weil-derived-pullback-tensor-hom). -/
noncomputable def finiteIntrinsicDerivedTensor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (n : ℕ) :
    proEtaleDerivedCategory W (finiteCoefficientRing l E (n + 1)) ×
      proEtaleDerivedCategory W (finiteCoefficientRing l E (n + 1)) ⥤
        proEtaleDerivedCategory W (finiteCoefficientRing l E (n + 1)) :=
  (finiteIntrinsicClosed l E W n).tensor

/-- The recorded intrinsic ambient Hom, with its first input contravariant.
Source: Stacks 08J7 (blueprint: def-weil-derived-pullback-tensor-hom). -/
noncomputable abbrev finiteIntrinsicDerivedInternalHom (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (n : ℕ) := coefficientFiniteInternalHom l E W n

/-- The actual K-flat representative comparison, including the ordinary evaluation
formula on pure tensors. The site object and morphism universes remain u+1 and u.
Source: Stacks 07A4, 08J9 (blueprint: def-weil-derived-pullback-tensor-hom). -/
noncomputable def finiteIntrinsicTensorModels (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (n : ℕ) :
    CoefficientTensorModels.{u, u+1, u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n) (finiteIntrinsicClosed l E W n) :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose.finiteTensorModel n

/-- Intrinsic finite evaluation: the counit for the recorded internal Hom.
Source: Stacks 08J9 (blueprint: def-weil-derived-pullback-tensor-hom). -/
noncomputable abbrev finiteIntrinsicEvaluation (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (n : ℕ) := (finiteIntrinsicClosed l E W n).evaluation

/-- Intrinsic finite currying: the canonical closed Hom equivalence, whose
representative normalization is finiteIntrinsicTensorModels.uncurry_model.
Source: Stacks 08J9 (blueprint: def-weil-derived-pullback-tensor-hom). -/
noncomputable abbrev finiteIntrinsicTranspose (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (n : ℕ) := (finiteIntrinsicClosed l E W n).transpose

/-- The canonical quotient change-of-rings Hom comparison at n+1 ≤ m+1.
Its definition is the unique closed transpose of reduced evaluation, conjugated
by the comparison fixed on K-flat tensor generators. This supplies the requested
consumer on the existing intrinsic Hom with no flatness assumption on the quotient.
Source: Stacks 06YS, 0A95; coefficient calculus steps 10--11
(blueprint: def-weil-derived-pullback-tensor-hom). -/
noncomputable abbrev finiteIntrinsicReductionHom (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :=
  coefficientFiniteQuotientHomComparison l E W
    (coefficientDerivedSystemEvaluationCalculus l E W).choose.toCoefficientDerivedSystemTensors
    (coefficientDerivedSystemEvaluationCalculus l E W).choose.quotientCalculus h

/-- Restriction of the canonical integral pullback to the recorded constructible
subcategory. Its underlying object and arrow maps are the ambient ones.
Source: blueprint integral paragraph; Stacks Tag 099N(5)
(blueprint: def-weil-derived-pullback-tensor-hom). -/
noncomputable def constructibleIntegralPullback (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X :=
  (sfIntegralConstructible l E X).lift
    ((sfIntegralConstructible l E Y).ι ⋙ integralDerivedPullback l E f)
    (fun K ↦ ((integralOperations_preserve_constructible l E f).1 K.obj K.property).1)

/-- Constructible restriction of the completed integral tensor, for either scheme.
Source: blueprint integral paragraph; Bhatt--Scholze, Lemma 6.5.5
(blueprint: def-weil-derived-pullback-tensor-hom). -/
noncomputable def constructibleIntegralTensor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    sfIntegralConstructibleCategory l E W × sfIntegralConstructibleCategory l E W ⥤
      sfIntegralConstructibleCategory l E W :=
  (sfIntegralConstructible l E W).lift
    (((sfIntegralConstructible l E W).ι.prod (sfIntegralConstructible l E W).ι) ⋙
      integralCompletedTensor l E W)
    (fun MN ↦ ((integralOperations_preserve_constructible l E (𝟙 W)).2 W
      (Or.inl rfl) MN.1.obj MN.2.obj MN.1.property MN.2.property).1)

/-- The full subcategory of integral pairs for which the ambient derived internal
Hom is constructible. No closure assertion for all pairs is made.
Source: blueprint integral internal-Hom qualification; Stacks Tag 08J7
(blueprint: def-weil-derived-pullback-tensor-hom). -/
noncomputable def constructibleIntegralHomPairs (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) :
    ObjectProperty ((sfIntegralConstructibleCategory l E W)ᵒᵖ ×
      sfIntegralConstructibleCategory l E W) :=
  fun MN ↦ sfIntegralConstructible l E W
    ((integralDerivedInternalHom l E W).obj (op MN.1.unop.obj, MN.2.obj))

/-- Restrict ambient internal Hom exactly on the permitted pairs.
Source: blueprint integral paragraph; Stacks Tag 08J7
(blueprint: def-weil-derived-pullback-tensor-hom). -/
noncomputable def constructibleIntegralHom (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) :
    (constructibleIntegralHomPairs l E W).FullSubcategory ⥤
      sfIntegralConstructibleCategory l E W :=
  (sfIntegralConstructible l E W).lift
    ((constructibleIntegralHomPairs l E W).ι ⋙
      ((sfIntegralConstructible l E W).ι.op.prod (sfIntegralConstructible l E W).ι) ⋙
      integralDerivedInternalHom l E W)
    (fun MN ↦ MN.property)

/-- Rational Hom has exactly the same integral-pair restriction on its objects.
Source: blueprint rational paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
noncomputable def constructibleRationalHomPairs (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) :
    ObjectProperty ((sfRationalConstructibleCategory l E W)ᵒᵖ ×
      sfRationalConstructibleCategory l E W) :=
  fun MN ↦ constructibleIntegralHomPairs l E W (op MN.1.unop.obj, MN.2.obj)

/-- The rational pullback is uniquely prescribed on unchanged objects and every
pure tensor in the raw localized Hom groups. Additivity extends the displayed
formula to sums. Scalar-first coordinates are those of the recorded localization.
Source: blueprint rational paragraph
(blueprint: def-weil-derived-pullback-tensor-hom).
Proof: integral pullback is linear for the constant O_E action, since the strict
finite inverse images and their Roos construction commute with that action.
Base change its linear Hom maps. The tensor balancing relation gives well-defined
maps. On pure tensors the identity and composition equations follow from the
integral functor laws and multiplication of coefficients. Additivity gives them
on all morphisms. Objects and pure tensors determine the functor uniquely. -/
theorem rationalDerivedPullback_existsUnique (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! F : sfRationalConstructibleCategory l E Y ⥤
        sfRationalConstructibleCategory l E X,
      F.Additive ∧
      (∀ K, F.obj K = ⟨(constructibleIntegralPullback l E f).obj K.obj⟩) ∧
      (∀ (K L : sfIntegralConstructibleCategory l E Y) (a : K ⟶ L)
        (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
        HEq (F.map (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] a :
          (sfRationalConstructibleLocalization l E Y).obj K ⟶
            (sfRationalConstructibleLocalization l E Y).obj L))
          (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
            (constructibleIntegralPullback l E f).map a)) := by
  sorry

/-- The unique rational pullback with the prescribed integral object and tensor
Hom action. Source: blueprint rational paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
noncomputable def rationalDerivedPullback (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :=
  (rationalDerivedPullback_existsUnique l E f).exists.choose

/-- Rational tensor is the unique additive-in-each-variable extension with
coefficient multiplication c*d on pure tensors; no Karoubi envelope occurs.
Source: blueprint rational paragraph
(blueprint: def-weil-derived-pullback-tensor-hom).
Proof: integral tensor is O_E-linear in each variable by its strict finite tensor
formulas, preserved by Roos descent. Extend the bilinear Hom map in both scalar
factors. Balancing is precisely integral bilinearity. Integral functoriality and
commutativity of coefficients prove identities and composition on pure tensors,
then bilinearity proves them on all arrows. These generators prove uniqueness. -/
theorem rationalDerivedTensor_existsUnique (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    ∃! F : sfRationalConstructibleCategory l E W ×
        sfRationalConstructibleCategory l E W ⥤ sfRationalConstructibleCategory l E W,
      (∀ MN, F.obj MN = ⟨(constructibleIntegralTensor l E W).obj
        (MN.1.obj, MN.2.obj)⟩) ∧
      (∀ (M M' N N' : sfRationalConstructibleCategory l E W),
        ∃ b : (M ⟶ M') →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer l E)]
          (N ⟶ N') →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer l E)]
          (F.obj (M, N) ⟶ F.obj (M', N')),
        (∀ a b', F.map (Prod.mkHom a b') = b a b') ∧
        ∀ (a : M.obj ⟶ M'.obj) (b' : N.obj ⟶ N'.obj)
          (c d : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
          HEq (b (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] a)
            (d ⊗ₜ[Padic.coefficientExtensionIntegers l E] b'))
            ((c * d) ⊗ₜ[Padic.coefficientExtensionIntegers l E]
              (constructibleIntegralTensor l E W).map (Prod.mkHom a b'))) := by
  sorry

/-- Rational tensor with unchanged integral objects and bilinear scalar extension
on morphisms. Source: blueprint rational paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
noncomputable def rationalDerivedTensor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :=
  (rationalDerivedTensor_existsUnique l E W).exists.choose

/-- The underlying permitted integral pair of a permitted rational pair.
Source: blueprint rational internal-Hom paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
noncomputable def integralPairOfRationalHomPair (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (P : (constructibleRationalHomPairs l E W).FullSubcategory) :
    (constructibleIntegralHomPairs l E W).FullSubcategory :=
  ⟨(op P.obj.1.unop.obj, P.obj.2.obj), P.property⟩

/-- The unique rational internal Hom on the permitted full subcategory of pairs.
The multiplication c*d applies to the contravariant first map and covariant
second map, in exactly the source and target order of the blueprint.
Source: blueprint rational paragraph; Stacks Tag 08J7
(blueprint: def-weil-derived-pullback-tensor-hom).
Proof: the ambient integral Hom functor is O_E-linear separately in both
variables, with precomposition in the first variable and postcomposition in the
second. Restrict its maps to the permitted endpoints, then extend bilinearly
along O_E to E using the tensor universal property. Balancing gives the formula
on pure tensors. Identities and composition follow on pure tensors from the
integral functor laws; extend to sums by bilinearity. Objects and these formulas
uniquely determine the functor. The domain restriction concerns objects only,
so every pair of arrows between permitted endpoints is included. -/
theorem rationalDerivedInternalHom_existsUnique (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) :
    ∃! F : (constructibleRationalHomPairs l E W).FullSubcategory ⥤
        sfRationalConstructibleCategory l E W,
      (∀ P, F.obj P = ⟨(constructibleIntegralHom l E W).obj
        (integralPairOfRationalHomPair l E W P)⟩) ∧
      (∀ (P Q : (constructibleRationalHomPairs l E W).FullSubcategory),
        ∃ b : (Q.obj.1.unop ⟶ P.obj.1.unop)
          →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer l E)]
          (P.obj.2 ⟶ Q.obj.2)
          →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer l E)]
          (F.obj P ⟶ F.obj Q),
        (∀ a b', F.map (ObjectProperty.homMk (Prod.mkHom a.op b')) = b a b') ∧
        ∀ (a : Q.obj.1.unop.obj ⟶ P.obj.1.unop.obj)
          (b' : P.obj.2.obj ⟶ Q.obj.2.obj)
          (c d : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
          HEq (b (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] a)
            (d ⊗ₜ[Padic.coefficientExtensionIntegers l E] b'))
            ((c * d) ⊗ₜ[Padic.coefficientExtensionIntegers l E]
              (constructibleIntegralHom l E W).map
                (X := integralPairOfRationalHomPair l E W P)
                (Y := integralPairOfRationalHomPair l E W Q)
                (ObjectProperty.homMk (Prod.mkHom a.op b')))) := by
  sorry

/-- Rational internal Hom, with its contravariant/covariant pure-tensor action.
Source: blueprint rational paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
noncomputable def rationalDerivedInternalHom (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) :=
  (rationalDerivedInternalHom_existsUnique l E W).exists.choose


universe r s w x

private theorem scalarComparisonLift
    {R : Type r} [CommRing R] {S : Type s} [CommRing S]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
    {D : Type w} [Category.{x} D] [Preadditive D] [Linear S D]
    (t : R) (b : S) (ψ : Localization.Away t →+* Localization.Away b)
    (I J : C ⥤ D) (η : I ≅ J)
    (F G : ScalarLocalization R C t ⥤ ScalarLocalization S D b)
    [F.Additive] [G.Additive]
    (hF : ∀ K, F.obj K = ⟨I.obj K.obj⟩)
    (hG : ∀ K, G.obj K = ⟨J.obj K.obj⟩)
    (mF : ∀ (K L : C) (c : Localization.Away t) (a : K ⟶ L),
      HEq (F.map (c ⊗ₜ[R] a : (ScalarLocalization.localization R C t).obj K ⟶
        (ScalarLocalization.localization R C t).obj L)) (ψ c ⊗ₜ[S] I.map a))
    (mG : ∀ (K L : C) (c : Localization.Away t) (a : K ⟶ L),
      HEq (G.map (c ⊗ₜ[R] a : (ScalarLocalization.localization R C t).obj K ⟶
        (ScalarLocalization.localization R C t).obj L)) (ψ c ⊗ₜ[S] J.map a)) :
    ∃! α : F ≅ G, ∀ K, HEq (α.hom.app K)
      ((ScalarLocalization.localization S D b).map (η.hom.app K.obj)) := by
  let e (K : ScalarLocalization R C t) : F.obj K ≅ G.obj K :=
    eqToIso (hF K) ≪≫ (ScalarLocalization.localization S D b).mapIso (η.app K.obj) ≪≫
      (eqToIso (hG K)).symm
  have he (K : ScalarLocalization R C t) : HEq (e K).hom
      ((ScalarLocalization.localization S D b).map (η.hom.app K.obj)) :=
    (conj_eqToHom_iff_heq _ _ (hF K) (hG K)).1 rfl
  have hn (K L : ScalarLocalization R C t) (f : K ⟶ L) :
      F.map f ≫ (e L).hom = (e K).hom ≫ G.map f := by
    induction f using TensorProduct.induction_on with
    | zero => simp
    | add f g hf hg =>
      simpa only [F.map_add, G.map_add, Preadditive.add_comp, Preadditive.comp_add]
        using congrArg₂ (· + ·) hf hg
    | tmul c a =>
      have hf := (conj_eqToHom_iff_heq _ _ (hF K) (hF L)).2 (mF K.obj L.obj c a)
      have hg := (conj_eqToHom_iff_heq _ _ (hG K) (hG L)).2 (mG K.obj L.obj c a)
      rw [hf, hg]
      dsimp only [e, Iso.trans_hom, eqToIso.hom, Iso.symm_hom, eqToIso.inv,
        Functor.mapIso_hom, Iso.app_hom]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      have hi : (ψ c ⊗ₜ[S] I.map a :
          (ScalarLocalization.localization S D b).obj (I.obj K.obj) ⟶
            (ScalarLocalization.localization S D b).obj (I.obj L.obj)) ≫
          (ScalarLocalization.localization S D b).map (η.hom.app L.obj) =
        (ScalarLocalization.localization S D b).map (η.hom.app K.obj) ≫
          (ψ c ⊗ₜ[S] J.map a) := by
        change ScalarLocalization.composition S D b _ _ _ _ _ =
          ScalarLocalization.composition S D b _ _ _ _ _
        simp only [ScalarLocalization.localization, ScalarLocalization.composition_tmul,
          mul_one, one_mul, η.hom.naturality]
      simpa only [Category.assoc] using congrArg
        (fun z ↦ eqToHom (hF K) ≫ z ≫ eqToHom (hG L).symm) hi
  refine ⟨NatIso.ofComponents e (fun f ↦ hn _ _ f), he, ?_⟩
  intro α hα
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((hα K).trans (he K).symm)
private theorem operationInverseSquare
    {C : Type*} [Category C] {X Y X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y')
    (a : X ⟶ Y) (b : X' ⟶ Y') (h : a ≫ e'.hom = e.hom ≫ b) :
    b ≫ e'.inv = e.inv ≫ a := by
  apply (Iso.comp_inv_eq e').2
  rw [Category.assoc]
  exact (Iso.eq_inv_comp e).2 h.symm

private theorem scalarPairComparisonLift
    {R : Type r} [CommRing R] {S : Type s} [CommRing S]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
    {D : Type w} [Category.{x} D] [Preadditive D] [Linear S D]
    (t : R) (b : S) (ψ : Localization.Away t →+* Localization.Away b)
    (I J : C × C ⥤ D) (η : I ≅ J)
    (F G : ScalarLocalization R C t × ScalarLocalization R C t ⥤
      ScalarLocalization S D b)
    (hF : ∀ K, F.obj K = ⟨I.obj (K.1.obj, K.2.obj)⟩)
    (hG : ∀ K, G.obj K = ⟨J.obj (K.1.obj, K.2.obj)⟩)
    (bF : ∀ K L, ∃ β : (K.1 ⟶ L.1) →+ (K.2 ⟶ L.2) →+ (F.obj K ⟶ F.obj L),
      ∀ a b', F.map (Prod.mkHom a b') = β a b')
    (bG : ∀ K L, ∃ β : (K.1 ⟶ L.1) →+ (K.2 ⟶ L.2) →+ (G.obj K ⟶ G.obj L),
      ∀ a b', G.map (Prod.mkHom a b') = β a b')
    (mF : ∀ (K M N P : C) (c d : Localization.Away t) (a : K ⟶ M) (b' : N ⟶ P),
      HEq (F.map (X := (ScalarLocalization.mk K, ScalarLocalization.mk N))
        (Y := (ScalarLocalization.mk M, ScalarLocalization.mk P))
          (Prod.mkHom (c ⊗ₜ[R] a) (d ⊗ₜ[R] b')))
        (ψ (c * d) ⊗ₜ[S] I.map (Prod.mkHom a b')))
    (mG : ∀ (K M N P : C) (c d : Localization.Away t) (a : K ⟶ M) (b' : N ⟶ P),
      HEq (G.map (X := (ScalarLocalization.mk K, ScalarLocalization.mk N))
        (Y := (ScalarLocalization.mk M, ScalarLocalization.mk P))
          (Prod.mkHom (c ⊗ₜ[R] a) (d ⊗ₜ[R] b')))
        (ψ (c * d) ⊗ₜ[S] J.map (Prod.mkHom a b'))) :
    ∃! α : F ≅ G, ∀ K, HEq (α.hom.app K)
      ((ScalarLocalization.localization S D b).map (η.hom.app (K.1.obj, K.2.obj))) := by
  let e (K : ScalarLocalization R C t × ScalarLocalization R C t) : F.obj K ≅ G.obj K :=
    eqToIso (hF K) ≪≫
      (ScalarLocalization.localization S D b).mapIso (η.app (K.1.obj, K.2.obj)) ≪≫
        (eqToIso (hG K)).symm
  have he (K : ScalarLocalization R C t × ScalarLocalization R C t) : HEq (e K).hom
      ((ScalarLocalization.localization S D b).map (η.hom.app (K.1.obj, K.2.obj))) :=
    (conj_eqToHom_iff_heq _ _ (hF K) (hG K)).1 rfl
  have hn (K L : ScalarLocalization R C t × ScalarLocalization R C t) (f : K ⟶ L) :
      F.map f ≫ (e L).hom = (e K).hom ≫ G.map f := by
    rcases f with ⟨a, b'⟩
    obtain ⟨β, hβ⟩ := bF K L
    obtain ⟨γ, hγ⟩ := bG K L
    rw [hβ, hγ]
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add a a' ha ha' =>
      simpa only [map_add, AddMonoidHom.add_apply, Preadditive.add_comp,
        Preadditive.comp_add] using congrArg₂ (· + ·) ha ha'
    | tmul c a =>
      induction b' using TensorProduct.induction_on with
      | zero => simp
      | add b' b'' hb hb' =>
        simpa only [map_add, Preadditive.add_comp, Preadditive.comp_add]
          using congrArg₂ (· + ·) hb hb'
      | tmul d b' =>
        have hf := (conj_eqToHom_iff_heq _ _ (hF K) (hF L)).2
          (mF K.1.obj L.1.obj K.2.obj L.2.obj c d a b')
        have hg := (conj_eqToHom_iff_heq _ _ (hG K) (hG L)).2
          (mG K.1.obj L.1.obj K.2.obj L.2.obj c d a b')
        rw [hβ] at hf
        rw [hγ] at hg
        rw [hf, hg]
        dsimp only [e, Iso.trans_hom, eqToIso.hom, Iso.symm_hom, eqToIso.inv,
          Functor.mapIso_hom, Iso.app_hom]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        have hi : (ψ (c * d) ⊗ₜ[S] I.map (Prod.mkHom a b') :
            (ScalarLocalization.localization S D b).obj (I.obj (K.1.obj, K.2.obj)) ⟶
              (ScalarLocalization.localization S D b).obj (I.obj (L.1.obj, L.2.obj))) ≫
            (ScalarLocalization.localization S D b).map (η.hom.app (L.1.obj, L.2.obj)) =
          (ScalarLocalization.localization S D b).map (η.hom.app (K.1.obj, K.2.obj)) ≫
            (ψ (c * d) ⊗ₜ[S] J.map (Prod.mkHom a b')) := by
          change ScalarLocalization.composition S D b _ _ _ _ _ =
            ScalarLocalization.composition S D b _ _ _ _ _
          simp only [ScalarLocalization.localization, ScalarLocalization.composition_tmul,
            mul_one, one_mul, η.hom.naturality]
        simpa only [Category.assoc] using congrArg
          (fun z ↦ eqToHom (hF K) ≫ z ≫ eqToHom (hG L).symm) hi
  refine ⟨NatIso.ofComponents e (fun f ↦ hn _ _ f), he, ?_⟩
  intro α hα
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((hα K).trans (he K).symm)
private theorem operationProdHomHEq
    {A B : Type*} [Category A] [Category B]
    {X Y X' Y' : A} {K M K' M' : B}
    (hx : X = X') (hy : Y = Y') (hk : K = K') (hm : M = M')
    {f : X ⟶ Y} {g : X' ⟶ Y'} {a : K ⟶ M} {b : K' ⟶ M'}
    (hf : HEq f g) (ha : HEq a b) : HEq (Prod.mkHom f a) (Prod.mkHom g b) := by
  subst X'; subst Y'; subst K'; subst M'
  exact heq_of_eq (congrArg₂ Prod.mkHom (eq_of_heq hf) (eq_of_heq ha))
private def operationBilinearPost
    {k : Type*} [CommRing k] {V V' : Type*}
    [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
    {C D : Type*} [Category C] [Preadditive C] [Linear k C]
    [Category D] [Preadditive D] (A : C ⥤ D) [A.Additive] {K M : C}
    (β : V →ₗ[k] V' →ₗ[k] (K ⟶ M)) : V →+ V' →+ (A.obj K ⟶ A.obj M) where
  toFun a :=
    { toFun := fun b ↦ A.map (β a b)
      map_zero' := by rw [map_zero, A.map_zero]
      map_add' := by intros; rw [map_add, A.map_add] }
  map_zero' := by
    apply AddMonoidHom.ext
    intro b
    change A.map (β 0 b) = 0
    rw [map_zero, LinearMap.zero_apply, A.map_zero]
  map_add' := by
    intro a a'
    apply AddMonoidHom.ext
    intro b
    change A.map (β (a + a') b) = A.map (β a b) + A.map (β a' b)
    rw [map_add, LinearMap.add_apply, A.map_add]

private def operationBilinearPre
    {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]
    {C D : Type*} [Category C] [Preadditive C]
    [Category D] [Preadditive D] [Linear k D] (A : C ⥤ D) [A.Additive]
    {K M N P : C} (β : (A.obj K ⟶ A.obj M) →ₗ[k] (A.obj N ⟶ A.obj P) →ₗ[k] V) :
    (K ⟶ M) →+ (N ⟶ P) →+ V where
  toFun a :=
    { toFun := fun b ↦ β (A.map a) (A.map b)
      map_zero' := by rw [A.map_zero, map_zero]
      map_add' := by intros; rw [A.map_add, map_add] }
  map_zero' := by
    apply AddMonoidHom.ext
    intro b
    change β (A.map 0) (A.map b) = 0
    rw [A.map_zero, map_zero, LinearMap.zero_apply]
  map_add' := by
    intro a a'
    apply AddMonoidHom.ext
    intro b
    change β (A.map (a + a')) (A.map b) =
      β (A.map a) (A.map b) + β (A.map a') (A.map b)
    rw [A.map_add, map_add, LinearMap.add_apply]

private theorem operationRationalTensorSpec (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    let F := rationalDerivedTensor l E W
    (∀ MN, F.obj MN = ⟨(constructibleIntegralTensor l E W).obj
        (MN.1.obj, MN.2.obj)⟩) ∧
      (∀ (M M' N N' : sfRationalConstructibleCategory l E W),
        ∃ b : (M ⟶ M') →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer l E)]
          (N ⟶ N') →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer l E)]
          (F.obj (M, N) ⟶ F.obj (M', N')),
        (∀ a b', F.map (Prod.mkHom a b') = b a b') ∧
        ∀ (a : M.obj ⟶ M'.obj) (b' : N.obj ⟶ N'.obj)
          (c d : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
          HEq (b (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] a)
            (d ⊗ₜ[Padic.coefficientExtensionIntegers l E] b'))
            ((c * d) ⊗ₜ[Padic.coefficientExtensionIntegers l E]
              (constructibleIntegralTensor l E W).map (Prod.mkHom a b'))) :=
  (rationalDerivedTensor_existsUnique l E W).exists.choose_spec


private theorem operationRationalScalarSpec
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (Y : Scheme.{u}) :
    let F := sfRationalScalarExtension l E Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
    F.Additive ∧
      (∀ K : sfRationalConstructibleCategory l E Y,
        F.obj K = ⟨(sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj K.obj⟩) ∧
      (∀ (K K' : sfIntegralConstructibleCategory l E Y)
        (f : K ⟶ K') (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
        HEq (F.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
          (sfRationalConstructibleLocalization l E Y).obj K ⟶
            (sfRationalConstructibleLocalization l E Y).obj K'))
          ((sfRationalCoefficientEquiv l L).symm (ι (sfRationalCoefficientEquiv l E a))
            ⊗ₜ[Padic.coefficientExtensionIntegers l L]
              (sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).map f :
                (sfRationalConstructibleLocalization l L Y).obj
                  ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj K) ⟶
                (sfRationalConstructibleLocalization l L Y).obj
                  ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj K'))) :=
  (sfRationalScalarExtension_existsUnique l E Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec

private theorem operationHomMapHEq {A B : Type*} [Category A] [Category B]
    (J : A ⥤ B) {X Y X' Y' : A} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (hf : HEq f g) : HEq (J.map f) (J.map g) := by
  subst X'; subst Y'
  exact heq_of_eq (congrArg J.map (eq_of_heq hf))

section ScalarComparisons
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The restricted integral pullback comparison, with its canonical ambient component.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def integralPullbackScalarComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι X).obj ((constructibleIntegralPullback l E f).obj K) ≅
      (constructibleIntegralPullback l L f).obj
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj K) :=
  ObjectProperty.isoMk _ (scalarPullbackCompleted l E L ι f K.obj K.property.1
    ((constructibleIntegralPullback l E f).obj K).property.1)

/-- The restricted integral tensor comparison, with both input comparisons covariant.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def integralTensorScalarComparison (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι W).obj ((constructibleIntegralTensor l E W).obj (M, N)) ≅
      (constructibleIntegralTensor l L W).obj
        (((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M),
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj N)) :=
  ObjectProperty.isoMk _ (scalarTensorCompleted l E L ι W M.obj N.obj
    M.property.1 N.property.1 ((constructibleIntegralTensor l E W).obj (M, N)).property.1)

private theorem integralPullbackScalarComparison_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    {K M : sfIntegralConstructibleCategory l E Y} (a : K ⟶ M) :
    (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).map
        ((constructibleIntegralPullback l E f).map a) ≫
          (integralPullbackScalarComparison l E L ι f M).hom =
    (integralPullbackScalarComparison l E L ι f K).hom ≫
      (constructibleIntegralPullback l L f).map
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).map a) := by
  let P := integralDerivedPullback l E f
  let Q := integralDerivedPullback l L f
  let OX := integralOrdinaryDerivedScalar l E L ι X
  let OY := integralOrdinaryDerivedScalar l E L ι Y
  let SX := integralScalarExtension l E L ι X
  let SY := integralScalarExtension l E L ι Y
  let eK := scalarCompletionIso l E L ι Y K.obj K.property.1
  let eM := scalarCompletionIso l E L ι Y M.obj M.property.1
  let ePK := scalarCompletionIso l E L ι X (P.obj K.obj)
    ((constructibleIntegralPullback l E f).obj K).property.1
  let ePM := scalarCompletionIso l E L ι X (P.obj M.obj)
    ((constructibleIntegralPullback l E f).obj M).property.1
  let β := scalarPullbackOrdinary l E L ι f
  have hx : SX.map (P.map a.hom) ≫ ePM.inv = ePK.inv ≫ OX.map (P.map a.hom) :=
    operationInverseSquare ePK ePM _ _
      ((scalarCompletion l E L ι X).naturality (P.map a.hom))
  have hy := (scalarCompletion l E L ι Y).naturality a.hom
  have hb := β.hom.naturality a.hom
  change OX.map (P.map a.hom) ≫ β.hom.app M.obj =
    β.hom.app K.obj ≫ Q.map (OY.map a.hom) at hb
  apply ObjectProperty.hom_ext
  change SX.map (P.map a.hom) ≫ (ePM.inv ≫ β.hom.app M.obj ≫ Q.map eM.hom) =
    (ePK.inv ≫ β.hom.app K.obj ≫ Q.map eK.hom) ≫ Q.map (SY.map a.hom)
  calc
    _ = (SX.map (P.map a.hom) ≫ ePM.inv) ≫ β.hom.app M.obj ≫ Q.map eM.hom := by
      simp only [Category.assoc]
    _ = ePK.inv ≫ (OX.map (P.map a.hom) ≫ β.hom.app M.obj) ≫ Q.map eM.hom := by
      rw [hx]
      simp only [Category.assoc]
    _ = ePK.inv ≫ (β.hom.app K.obj ≫ Q.map (OY.map a.hom)) ≫ Q.map eM.hom := by
      rw [hb]
    _ = ePK.inv ≫ β.hom.app K.obj ≫ Q.map (OY.map a.hom ≫ eM.hom) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = ePK.inv ≫ β.hom.app K.obj ≫ Q.map (eK.hom ≫ SY.map a.hom) := by
      rw [show OY.map a.hom ≫ eM.hom = eK.hom ≫ SY.map a.hom from hy]
    _ = _ := by simp only [Functor.map_comp, Category.assoc]

/-- Rational pullback comparison: precisely the rationalized normalized integral map.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom).
Proof: apply localization to integralPullbackScalarComparison. The scalar and
pullback object formulas identify the endpoints. Naturality holds on integral
maps by the normalized chain construction, then on pure tensors by linearity,
and hence on every morphism by addition. The inverse localizes too. The displayed
component formula determines the natural isomorphism uniquely. -/
theorem rationalPullbackScalarComparison_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! α : rationalDerivedPullback l E f ⋙
        sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ≅
      sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙
        rationalDerivedPullback l L f,
      ∀ K : sfRationalConstructibleCategory l E Y,
        HEq (α.hom.app K) ((sfRationalConstructibleLocalization l L X).map
          (integralPullbackScalarComparison l E L ι f K.obj).hom) := by
  let R := Padic.coefficientExtensionIntegers l E
  let S := Padic.coefficientExtensionIntegers l L
  let t := Padic.coefficientExtensionUniformizer l E
  let b := Padic.coefficientExtensionUniformizer l L
  let P := rationalDerivedPullback l E f
  let Q := rationalDerivedPullback l L f
  let SX := sfRationalScalarExtension l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  let SY := sfRationalScalarExtension l E Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  let IX := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X
  let IY := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y
  let PI := constructibleIntegralPullback l E f
  let QI := constructibleIntegralPullback l L f
  have hP := (rationalDerivedPullback_existsUnique l E f).exists.choose_spec
  have hQ := (rationalDerivedPullback_existsUnique l L f).exists.choose_spec
  have hSX := (sfRationalScalarExtension_existsUnique l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec
  have hSY := (sfRationalScalarExtension_existsUnique l E Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec
  let : P.Additive := hP.1
  let : Q.Additive := hQ.1
  let : SX.Additive := hSX.1
  let : SY.Additive := hSY.1
  let ψ : Localization.Away t →+* Localization.Away b :=
    ((sfRationalCoefficientEquiv l L).symm.toRingHom.comp ι.toRingHom).comp
      (sfRationalCoefficientEquiv l E).toRingHom
  let η : PI ⋙ IX ≅ IY ⋙ QI := NatIso.ofComponents
    (integralPullbackScalarComparison l E L ι f)
    (fun a ↦ integralPullbackScalarComparison_naturality l E L ι f a)
  have hpo (K : sfRationalConstructibleCategory l E Y) :
      P.obj K = ⟨PI.obj K.obj⟩ := hP.2.1 K
  have hqo (K : sfRationalConstructibleCategory l L Y) :
      Q.obj K = ⟨QI.obj K.obj⟩ := hQ.2.1 K
  have hsxo (K : sfRationalConstructibleCategory l E X) :
      SX.obj K = ⟨IX.obj K.obj⟩ := hSX.2.1 K
  have hsyo (K : sfRationalConstructibleCategory l E Y) :
      SY.obj K = ⟨IY.obj K.obj⟩ := hSY.2.1 K
  have hF (K : sfRationalConstructibleCategory l E Y) :
      (P ⋙ SX).obj K = ⟨(PI ⋙ IX).obj K.obj⟩ := by
    change SX.obj (P.obj K) = _
    rw [hpo, hsxo]
    rfl
  have hG (K : sfRationalConstructibleCategory l E Y) :
      (SY ⋙ Q).obj K = ⟨(IY ⋙ QI).obj K.obj⟩ := by
    change Q.obj (SY.obj K) = _
    rw [hsyo, hqo]
    rfl
  have mF (K M : sfIntegralConstructibleCategory l E Y)
      (c : Localization.Away t) (a : K ⟶ M) :
      HEq ((P ⋙ SX).map (c ⊗ₜ[R] a :
        (sfRationalConstructibleLocalization l E Y).obj K ⟶
          (sfRationalConstructibleLocalization l E Y).obj M))
        (ψ c ⊗ₜ[S] (PI ⋙ IX).map a) := by
    exact (operationHomMapHEq SX (hP.2.1 ⟨K⟩) (hP.2.1 ⟨M⟩)
      (hP.2.2 K M a c)).trans (hSX.2.2 (PI.obj K) (PI.obj M) (PI.map a) c)
  have mG (K M : sfIntegralConstructibleCategory l E Y)
      (c : Localization.Away t) (a : K ⟶ M) :
      HEq ((SY ⋙ Q).map (c ⊗ₜ[R] a :
        (sfRationalConstructibleLocalization l E Y).obj K ⟶
          (sfRationalConstructibleLocalization l E Y).obj M))
        (ψ c ⊗ₜ[S] (IY ⋙ QI).map a) := by
    exact (operationHomMapHEq Q (hSY.2.1 ⟨K⟩) (hSY.2.1 ⟨M⟩)
      (hSY.2.2 K M a c)).trans (hQ.2.2 (IY.obj K) (IY.obj M) (IY.map a) (ψ c))
  exact scalarComparisonLift t b ψ (PI ⋙ IX) (IY ⋙ QI) η
    (P ⋙ SX) (SY ⋙ Q) hF hG mF mG

/-- The uniquely normalized rational pullback scalar comparison.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def rationalPullbackScalarComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :=
  (rationalPullbackScalarComparison_existsUnique l E L ι f).exists.choose

private theorem integralTensorScalarComparison_naturality (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    {M M' N N' : sfIntegralConstructibleCategory l E W} (a : M ⟶ M') (b : N ⟶ N') :
    (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map
        ((constructibleIntegralTensor l E W).map (Prod.mkHom a b)) ≫
          (integralTensorScalarComparison l E L ι W M' N').hom =
    (integralTensorScalarComparison l E L ι W M N).hom ≫
      (constructibleIntegralTensor l L W).map (Prod.mkHom
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map a)
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map b)) := by
  let P := integralCompletedTensor l E W
  let Q := integralCompletedTensor l L W
  let O := integralOrdinaryDerivedScalar l E L ι W
  let S := integralScalarExtension l E L ι W
  let eK := Iso.prod (scalarCompletionIso l E L ι W M.obj M.property.1)
    (scalarCompletionIso l E L ι W N.obj N.property.1)
  let eM := Iso.prod (scalarCompletionIso l E L ι W M'.obj M'.property.1)
    (scalarCompletionIso l E L ι W N'.obj N'.property.1)
  let ePK := scalarCompletionIso l E L ι W (P.obj (M.obj, N.obj))
    ((constructibleIntegralTensor l E W).obj (M, N)).property.1
  let ePM := scalarCompletionIso l E L ι W (P.obj (M'.obj, N'.obj))
    ((constructibleIntegralTensor l E W).obj (M', N')).property.1
  let β := scalarTensorOrdinary l E L ι W
  let c := Prod.mkHom a.hom b.hom
  have hx : S.map (P.map c) ≫ ePM.inv = ePK.inv ≫ O.map (P.map c) :=
    operationInverseSquare ePK ePM _ _
      ((scalarCompletion l E L ι W).naturality (P.map c))
  have hy : Prod.mkHom (O.map a.hom) (O.map b.hom) ≫ eM.hom =
      eK.hom ≫ Prod.mkHom (S.map a.hom) (S.map b.hom) := by
    apply Prod.ext
    · exact (scalarCompletion l E L ι W).naturality a.hom
    · exact (scalarCompletion l E L ι W).naturality b.hom
  have hb := β.hom.naturality c
  change O.map (P.map c) ≫ β.hom.app (M'.obj, N'.obj) =
    β.hom.app (M.obj, N.obj) ≫ Q.map (Prod.mkHom (O.map a.hom) (O.map b.hom)) at hb
  apply ObjectProperty.hom_ext
  change S.map (P.map c) ≫ (ePM.inv ≫ β.hom.app (M'.obj, N'.obj) ≫ Q.map eM.hom) =
    (ePK.inv ≫ β.hom.app (M.obj, N.obj) ≫ Q.map eK.hom) ≫
      Q.map (Prod.mkHom (S.map a.hom) (S.map b.hom))
  calc
    _ = (S.map (P.map c) ≫ ePM.inv) ≫ β.hom.app (M'.obj, N'.obj) ≫ Q.map eM.hom := by
      simp only [Category.assoc]
    _ = ePK.inv ≫ (O.map (P.map c) ≫ β.hom.app (M'.obj, N'.obj)) ≫ Q.map eM.hom := by
      rw [hx]
      simp only [Category.assoc]
    _ = ePK.inv ≫ (β.hom.app (M.obj, N.obj) ≫
        Q.map (Prod.mkHom (O.map a.hom) (O.map b.hom))) ≫ Q.map eM.hom := by
      rw [hb]
    _ = ePK.inv ≫ β.hom.app (M.obj, N.obj) ≫
        Q.map (Prod.mkHom (O.map a.hom) (O.map b.hom) ≫ eM.hom) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = ePK.inv ≫ β.hom.app (M.obj, N.obj) ≫
        Q.map (eK.hom ≫ Prod.mkHom (S.map a.hom) (S.map b.hom)) := by rw [hy]
    _ = _ := by simp only [Functor.map_comp, Category.assoc]

section
attribute [local irreducible] rationalDerivedTensor sfRationalScalarExtension

set_option maxHeartbeats 800000 in
-- The bilinear comparison's dependent object transports exceed the default heartbeat budget.
/-- Rational tensor comparison, fixed by rationalizing the specified integral comparison.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom).
Proof: localize integralTensorScalarComparison. Both sides have the prescribed
integral tensor objects. On pairs of pure tensors, integral naturality and the
product of the two coefficients give rational naturality. Bilinearity gives it
on arbitrary maps. The integral inverse localizes to the inverse; the component
formula makes this isomorphism unique. -/
theorem rationalTensorScalarComparison_existsUnique (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    ∃! α : rationalDerivedTensor l E W ⋙
        sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ≅
      (sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).prod
        (sfRationalScalarExtension l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι) ⋙ rationalDerivedTensor l L W,
      ∀ M N : sfRationalConstructibleCategory l E W,
        HEq (α.hom.app (M, N)) ((sfRationalConstructibleLocalization l L W).map
          (integralTensorScalarComparison l E L ι W M.obj N.obj).hom) := by
  let R := Padic.coefficientExtensionIntegers l E
  let S := Padic.coefficientExtensionIntegers l L
  let t := Padic.coefficientExtensionUniformizer l E
  let b := Padic.coefficientExtensionUniformizer l L
  let T := rationalDerivedTensor l E W
  let U := rationalDerivedTensor l L W
  let A := sfRationalScalarExtension l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  let I := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let TI := constructibleIntegralTensor l E W
  let UI := constructibleIntegralTensor l L W
  have hT := operationRationalTensorSpec l E W
  have hU := operationRationalTensorSpec l L W
  have hA := operationRationalScalarSpec l E L ι W
  let : A.Additive := hA.1
  let ψ : Localization.Away t →+* Localization.Away b :=
    ((sfRationalCoefficientEquiv l L).symm.toRingHom.comp ι.toRingHom).comp
      (sfRationalCoefficientEquiv l E).toRingHom
  let η : TI ⋙ I ≅ I.prod I ⋙ UI := NatIso.ofComponents
    (fun K ↦ integralTensorScalarComparison l E L ι W K.1 K.2)
    (fun a ↦ integralTensorScalarComparison_naturality l E L ι W a.1 a.2)
  have hto (K : sfRationalConstructibleCategory l E W ×
      sfRationalConstructibleCategory l E W) :
      T.obj K = ⟨TI.obj (K.1.obj, K.2.obj)⟩ := hT.1 K
  have huo (K : sfRationalConstructibleCategory l L W ×
      sfRationalConstructibleCategory l L W) :
      U.obj K = ⟨UI.obj (K.1.obj, K.2.obj)⟩ := hU.1 K
  have hao (K : sfRationalConstructibleCategory l E W) :
      A.obj K = ⟨I.obj K.obj⟩ := hA.2.1 K
  have hF (K : sfRationalConstructibleCategory l E W ×
      sfRationalConstructibleCategory l E W) :
      (T ⋙ A).obj K = ⟨(TI ⋙ I).obj (K.1.obj, K.2.obj)⟩ := by
    change A.obj (T.obj K) = _
    rw [hto, hao]
    rfl
  have hG (K : sfRationalConstructibleCategory l E W ×
      sfRationalConstructibleCategory l E W) :
      (A.prod A ⋙ U).obj K = ⟨(I.prod I ⋙ UI).obj (K.1.obj, K.2.obj)⟩ := by
    change U.obj (A.obj K.1, A.obj K.2) = _
    rw [hao, hao, huo]
    rfl
  have bF (K M : sfRationalConstructibleCategory l E W ×
      sfRationalConstructibleCategory l E W) :
      ∃ β : (K.1 ⟶ M.1) →+ (K.2 ⟶ M.2) →+
        ((T ⋙ A).obj K ⟶ (T ⋙ A).obj M),
        ∀ a b', (T ⋙ A).map (Prod.mkHom a b') = β a b' := by
    obtain ⟨β, hβ, _⟩ := hT.2 K.1 M.1 K.2 M.2
    refine ⟨operationBilinearPost (k := Localization.Away t)
      (K := T.obj K) (M := T.obj M) A β, ?_⟩
    intro a b'
    change A.map (T.map (Prod.mkHom a b')) = A.map (β a b')
    rw [hβ]
  have bG (K M : sfRationalConstructibleCategory l E W ×
      sfRationalConstructibleCategory l E W) :
      ∃ β : (K.1 ⟶ M.1) →+ (K.2 ⟶ M.2) →+
        ((A.prod A ⋙ U).obj K ⟶ (A.prod A ⋙ U).obj M),
        ∀ a b', (A.prod A ⋙ U).map (Prod.mkHom a b') = β a b' := by
    obtain ⟨β, hβ, _⟩ := hU.2 (A.obj K.1) (A.obj M.1) (A.obj K.2) (A.obj M.2)
    refine ⟨operationBilinearPre (k := Localization.Away b)
      (K := K.1) (M := M.1) (N := K.2) (P := M.2) A β, ?_⟩
    intro a b'
    exact hβ (A.map a) (A.map b')
  have mF (K M N P : sfIntegralConstructibleCategory l E W)
      (c d : Localization.Away t) (a : K ⟶ M) (b' : N ⟶ P) :
      HEq ((T ⋙ A).map (X := (⟨K⟩, ⟨N⟩)) (Y := (⟨M⟩, ⟨P⟩))
        (Prod.mkHom (c ⊗ₜ[R] a) (d ⊗ₜ[R] b')))
        (ψ (c * d) ⊗ₜ[S] (TI ⋙ I).map (Prod.mkHom a b')) := by
    obtain ⟨β, hβ, hβpure⟩ := hT.2 ⟨K⟩ ⟨M⟩ ⟨N⟩ ⟨P⟩
    have ht := (heq_of_eq (hβ (c ⊗ₜ[R] a) (d ⊗ₜ[R] b'))).trans (hβpure a b' c d)
    exact (operationHomMapHEq A (hT.1 (⟨K⟩, ⟨N⟩)) (hT.1 (⟨M⟩, ⟨P⟩)) ht).trans
      (hA.2.2 (TI.obj (K, N)) (TI.obj (M, P)) (TI.map (Prod.mkHom a b')) (c * d))
  have mG (K M N P : sfIntegralConstructibleCategory l E W)
      (c d : Localization.Away t) (a : K ⟶ M) (b' : N ⟶ P) :
      HEq ((A.prod A ⋙ U).map (X := (⟨K⟩, ⟨N⟩)) (Y := (⟨M⟩, ⟨P⟩))
        (Prod.mkHom (c ⊗ₜ[R] a) (d ⊗ₜ[R] b')))
        (ψ (c * d) ⊗ₜ[S] (I.prod I ⋙ UI).map (Prod.mkHom a b')) := by
    have ha := hA.2.2 K M a c
    have hb := hA.2.2 N P b' d
    have hpair := operationProdHomHEq (hA.2.1 ⟨K⟩) (hA.2.1 ⟨M⟩)
      (hA.2.1 ⟨N⟩) (hA.2.1 ⟨P⟩) ha hb
    have hh := operationHomMapHEq U
      (Prod.ext (hA.2.1 ⟨K⟩) (hA.2.1 ⟨N⟩))
      (Prod.ext (hA.2.1 ⟨M⟩) (hA.2.1 ⟨P⟩)) hpair
    obtain ⟨β, hβ, hβpure⟩ := hU.2 ⟨I.obj K⟩ ⟨I.obj M⟩ ⟨I.obj N⟩ ⟨I.obj P⟩
    have ht := (heq_of_eq (hβ (ψ c ⊗ₜ[S] I.map a) (ψ d ⊗ₜ[S] I.map b'))).trans
      (hβpure (I.map a) (I.map b') (ψ c) (ψ d))
    change HEq _ (U.map (Prod.mkHom (ψ c ⊗ₜ[S] I.map a)
      (ψ d ⊗ₜ[S] I.map b'))) at hh
    change HEq (U.map (Prod.mkHom (ψ c ⊗ₜ[S] I.map a) (ψ d ⊗ₜ[S] I.map b')))
      ((ψ c * ψ d) ⊗ₜ[S] (I.prod I ⋙ UI).map (Prod.mkHom a b')) at ht
    rw [← ψ.map_mul c d] at ht
    exact hh.trans ht
  obtain ⟨α, hα, huniq⟩ := scalarPairComparisonLift t b ψ (TI ⋙ I) (I.prod I ⋙ UI)
    η (T ⋙ A) (A.prod A ⋙ U) hF hG bF bG mF mG
  refine ⟨α, fun M N ↦ hα (M, N), ?_⟩
  intro α' hα'
  exact huniq α' (fun K ↦ hα' K.1 K.2)


end

/-- The uniquely normalized rational tensor scalar comparison.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def rationalTensorScalarComparison (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :=
  (rationalTensorScalarComparison_existsUnique l E L ι W).exists.choose


/-- Scalar extension preserves the permitted integral-Hom pairs.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom).
Proof: the source Hom is constructible by the permitted-pair predicate. Completed
scalar extension preserves that predicate. scalarHomCompleted identifies its
extension with the target Hom using the evaluation-defined ordinary comparison
and the three normalized completion maps. Constructibility is invariant under
this actual integral isomorphism, proving precisely the target predicate. -/
theorem integralHomScalarPair_permitted (W : Scheme.{u})
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory) :
    sfIntegralConstructible l L W ((integralDerivedInternalHom l L W).obj
      (op ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj P.obj.1.unop).obj,
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj P.obj.2).obj)) := by
  let e := scalarHomCompleted l E L ι W P.obj.1.unop.obj P.obj.2.obj
    P.obj.1.unop.property.1 P.obj.2.property.1 P.property.1
  exact (sfIntegralConstructible l L W).prop_of_iso e
    (sfIntegralScalarExtension_constructible 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W _ P.property)

/-- The scalar-extended permitted integral pair.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def integralHomScalarPair (W : Scheme.{u})
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory) :
    (constructibleIntegralHomPairs l L W).FullSubcategory :=
  ⟨(op ((sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj P.obj.1.unop),
    (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj P.obj.2),
    integralHomScalarPair_permitted l E L ι W P⟩

/-- The restricted integral Hom comparison is the specified completed ambient comparison.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def integralHomScalarComparison (W : Scheme.{u})
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι W).obj ((constructibleIntegralHom l E W).obj P) ≅
      (constructibleIntegralHom l L W).obj (integralHomScalarPair l E L ι W P) :=
  ObjectProperty.isoMk _ (scalarHomCompleted l E L ι W P.obj.1.unop.obj P.obj.2.obj
    P.obj.1.unop.property.1 P.obj.2.property.1 P.property.1)

/-- Rational scalar extension preserves exactly the permitted Hom-pair domain.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom).
Proof: the rational scalar object formula gives the scalar extension of the
underlying integral objects. Substitute those formulas in the domain predicate;
it becomes integralHomScalarPair_permitted, with only proof-irrelevant subtype
fields to identify. No rational isomorphism is used to infer integral constructibility. -/
theorem rationalHomScalarPair_permitted (W : Scheme.{u})
    (P : (constructibleRationalHomPairs l E W).FullSubcategory) :
    constructibleRationalHomPairs l L W
      (op ((sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.1.unop),
        (sfRationalScalarExtension l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.2) := by
  have h₁ := (sfRationalScalarExtension_existsUnique l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1 P.obj.1.unop
  have h₂ := (sfRationalScalarExtension_existsUnique l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1 P.obj.2
  change (sfRationalScalarExtension l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.1.unop = _ at h₁
  change (sfRationalScalarExtension l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.2 = _ at h₂
  change constructibleIntegralHomPairs l L W
    (op (((sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.1.unop).obj),
      ((sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.2).obj)
  rw [h₁, h₂]
  exact integralHomScalarPair_permitted l E L ι W
    (integralPairOfRationalHomPair l E W P)

/-- The permitted rational pair after scalar extension.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def rationalHomScalarPair (W : Scheme.{u})
    (P : (constructibleRationalHomPairs l E W).FullSubcategory) :
    (constructibleRationalHomPairs l L W).FullSubcategory :=
  ⟨(op ((sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.1.unop),
    (sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P.obj.2),
    rationalHomScalarPair_permitted l E L ι W P⟩

/-- Rational Hom scalar comparison is precisely the rationalized canonical integral map.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom).
Proof: use the scalar and Hom object formulas to identify the endpoints with the
localizations of the integral endpoints. Localize integralHomScalarComparison
and its inverse. Its hom is the displayed component, which also proves uniqueness.
Naturality extends from the integral comparison by the separate linearity of Hom,
with precomposition in the first variable. -/
theorem rationalHomScalarComparison_existsUnique (W : Scheme.{u})
    (P : (constructibleRationalHomPairs l E W).FullSubcategory) :
    ∃! α : (sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
          ((rationalDerivedInternalHom l E W).obj P) ≅
      (rationalDerivedInternalHom l L W).obj (rationalHomScalarPair l E L ι W P),
      HEq α.hom ((sfRationalConstructibleLocalization l L W).map
        (integralHomScalarComparison l E L ι W (integralPairOfRationalHomPair l E W P)).hom) := by
  let S := sfRationalScalarExtension l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  let I := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  have hs (K : sfRationalConstructibleCategory l E W) : S.obj K = ⟨I.obj K.obj⟩ :=
    (sfRationalScalarExtension_existsUnique l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1 K
  have he (Q : (constructibleRationalHomPairs l E W).FullSubcategory) :
      (rationalDerivedInternalHom l E W).obj Q =
        ⟨(constructibleIntegralHom l E W).obj (integralPairOfRationalHomPair l E W Q)⟩ :=
    (rationalDerivedInternalHom_existsUnique l E W).exists.choose_spec.1 Q
  have hl (Q : (constructibleRationalHomPairs l L W).FullSubcategory) :
      (rationalDerivedInternalHom l L W).obj Q =
        ⟨(constructibleIntegralHom l L W).obj (integralPairOfRationalHomPair l L W Q)⟩ :=
    (rationalDerivedInternalHom_existsUnique l L W).exists.choose_spec.1 Q
  have hp : integralPairOfRationalHomPair l L W (rationalHomScalarPair l E L ι W P) =
      integralHomScalarPair l E L ι W (integralPairOfRationalHomPair l E W P) := by
    apply ObjectProperty.FullSubcategory.ext
    change (op (S.obj P.obj.1.unop).obj, (S.obj P.obj.2).obj) = _
    rw [hs, hs]
    rfl
  have hsource : S.obj ((rationalDerivedInternalHom l E W).obj P) =
      (sfRationalConstructibleLocalization l L W).obj
        (I.obj ((constructibleIntegralHom l E W).obj
          (integralPairOfRationalHomPair l E W P))) := by
    rw [he, hs]
    rfl
  have htarget : (rationalDerivedInternalHom l L W).obj
      (rationalHomScalarPair l E L ι W P) =
      (sfRationalConstructibleLocalization l L W).obj
        ((constructibleIntegralHom l L W).obj
          (integralHomScalarPair l E L ι W (integralPairOfRationalHomPair l E W P))) := by
    rw [hl, hp]
    rfl
  let e := (sfRationalConstructibleLocalization l L W).mapIso
    (integralHomScalarComparison l E L ι W (integralPairOfRationalHomPair l E W P))
  refine ⟨eqToIso hsource ≪≫ e ≪≫ (eqToIso htarget).symm, ?_, ?_⟩
  · dsimp only [Iso.trans_hom, eqToIso.hom, Iso.symm_hom, eqToIso.inv]
    exact (conj_eqToHom_iff_heq _ _ hsource htarget).1 rfl
  · intro e' he'
    apply Iso.ext
    exact eq_of_heq (he'.trans
      ((conj_eqToHom_iff_heq _ _ hsource htarget).1 rfl).symm)

/-- The uniquely normalized rational internal-Hom scalar comparison.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def rationalHomScalarComparison (W : Scheme.{u})
    (P : (constructibleRationalHomPairs l E W).FullSubcategory) :=
  (rationalHomScalarComparison_existsUnique l E L ι W P).exists.choose

end ScalarComparisons

section CommonStage

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The recorded stage transition is the specified rational scalar functor.
The equality is part of the existing stage-system uniqueness specification.
Source: blueprint common-stage coefficient construction
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def operationStageTransitionIso (W : Scheme.{u})
    (E L : Index l Ω) (h : E ≤ L) :
    (stageSystem l Ω W).T h ≅ transition l Ω W E L h :=
  eqToIso ((stageSystem_existsUnique l Ω W).exists.choose_spec.1 E L h)

private def operationStageIntegralAssociator (W : Scheme.{u})
    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (K : Stage l Ω W E) :
    (((stageSystem l Ω W).T k).obj (((stageSystem l Ω W).T h).obj K)).obj ≅
      (((stageSystem l Ω W).T (h.trans k)).obj K).obj := by
  have ht := (stageSystem_existsUnique l Ω W).exists.choose_spec.1
  rw [ht E L h, ht L M k, ht E M (h.trans k)]
  let CE := Coefficient.{u} l Ω E
  let CL := Coefficient.{u} l Ω L
  let CM := Coefficient.{u} l Ω M
  have hs (A B : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      [Field B] [Algebra ℚ_[l] B] [FiniteDimensional ℚ_[l] B]
      (j : A →ₐ[ℚ_[l]] B) (V : sfRationalConstructibleCategory l A W) :
      (sfRationalScalarExtension l A W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) B j).obj V =
          ⟨(sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) A B j W).obj V.obj⟩ :=
    (sfRationalScalarExtension_existsUnique l A W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) B j).exists.choose_spec.2.1 V
  change ((sfRationalScalarExtension l CL W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) CM (coefficientInclusion l Ω L M k)).obj
      ((sfRationalScalarExtension l CE W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) CL
          (coefficientInclusion l Ω E L h)).obj K)).obj ≅
    ((sfRationalScalarExtension l CE W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) CM
        (coefficientInclusion l Ω E M (h.trans k))).obj K).obj
  rw [hs, hs, hs]
  exact (sfIntegralScalarComp l CE CL (coefficientInclusion l Ω E L h) W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) CM
      (coefficientInclusion l Ω L M k)).app K.obj ≪≫
    (eqToIso (congrArg (fun j ↦
      (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) CE CM j W).obj K.obj)
          ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k)))

/-- Common-stage pullback retains the literal coefficient stage.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStagePullbackObject {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  ⟨P.stage, (rationalDerivedPullback l (Coefficient.{u} l Ω P.stage) f).obj P.obj⟩

/-- The canonical pullback comparison includes the recorded transition identifications.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStagePullbackComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : Index l Ω) (h : P.stage ≤ L) :
    (commonStagePullbackObject l Ω f P).toStage h ≅
      (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).obj (P.toStage h) :=
  (operationStageTransitionIso l Ω X P.stage L h).app
      (commonStagePullbackObject l Ω f P).obj ≪≫
    (rationalPullbackScalarComparison l (Coefficient.{u} l Ω P.stage)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω P.stage L h) f).app P.obj ≪≫
    (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).mapIso
      ((operationStageTransitionIso l Ω Y P.stage L h).app P.obj).symm

/-- Pullback on the actual pair-category quotient has the prescribed representative action.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom).
Proof: use the normalized rationalPullbackScalarComparison for every coefficient
inclusion. The strict generator formulas commute with a tower of coefficient
maps; multiplication and associativity of tensors give the scalar associators.
Both Roos coordinates preserve these equalities. Thus the comparisons satisfy
the coherent pair-functor descent equation. Conjugating a representative by the
source comparison and inverse target comparison is independent of enlargement
and eventual equality. Composition cancels the middle comparisons; identity
representatives give identities. Every arrow has a representative, so the object
and representative formulas uniquely determine the functor. -/
theorem commonStageDerivedPullback_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! F : generalAlgebraicallyClosedConstructibleCategory l Ω Y ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω X,
      (∀ P, F.obj P = commonStagePullbackObject l Ω f P) ∧
      (∀ (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
        (L : Index l Ω) (hP : P.stage ≤ L) (hQ : Q.stage ≤ L)
        (a : P.toStage hP ⟶ Q.toStage hQ),
        HEq (F.map (X := P) (Y := Q) (ofHom P Q L hP hQ a))
          (ofHom (commonStagePullbackObject l Ω f P)
            (commonStagePullbackObject l Ω f Q) L hP hQ
            ((commonStagePullbackComparison l Ω f P L hP).hom ≫
              (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).map a ≫
              (commonStagePullbackComparison l Ω f Q L hQ).inv))) := by
  sorry

/-- Canonical common-stage pullback, with no new coefficient objects or retracts.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageDerivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :=
  (commonStageDerivedPullback_existsUnique l Ω f).exists.choose

/-- The literal tensor object is formed at the finite coefficient compositum.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageTensorObject (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    generalAlgebraicallyClosedConstructibleCategory l Ω W :=
  ⟨Padic.finiteCoefficientCompositum l Ω P.stage Q.stage,
    (rationalDerivedTensor l (Coefficient.{u} l Ω
      (Padic.finiteCoefficientCompositum l Ω P.stage Q.stage)) W).obj
      (P.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1,
        Q.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2)⟩

/-- The tensor comparison at a common stage includes the scalar associators of both inputs.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageTensorComparison (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : Index l Ω) (h : (commonStageTensorObject l Ω W P Q).stage ≤ L) :
    (commonStageTensorObject l Ω W P Q).toStage h ≅
      (rationalDerivedTensor l (Coefficient.{u} l Ω L) W).obj
        (P.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1.trans h),
          Q.toStage
            (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2.trans h)) :=
  (operationStageTransitionIso l Ω W _ L h).app
      (commonStageTensorObject l Ω W P Q).obj ≪≫
    (rationalTensorScalarComparison l
      (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω P.stage Q.stage))
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω _ L h) W).app
      (P.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1,
        Q.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2) ≪≫
    (rationalDerivedTensor l (Coefficient.{u} l Ω L) W).mapIso
      (Iso.prod
        (((operationStageTransitionIso l Ω W _ L h).app
          (P.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
            P.stage Q.stage).1)).symm ≪≫
          ((stageSystem l Ω W).assoc
            ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1 h).app P.obj)
        (((operationStageTransitionIso l Ω W _ L h).app
          (Q.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
            P.stage Q.stage).2)).symm ≪≫
          ((stageSystem l Ω W).assoc
            ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2 h).app Q.obj))

/-- Common-stage tensor has the bilinear representative formula of the blueprint.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom).
Proof: extend both endpoints to their finite coefficient composita and use the
literal object formula. At a common larger stage, use commonStageTensorComparison
to identify their scalar extensions with the tensor of the extended inputs. The
normalized scalar tensor comparisons are natural, compatible with coefficient
towers and units: test their strict finite generator formulas and both Roos
coordinates. Thus the displayed conjugation respects eventual equality. At a
common stage, composition and identities follow from the rational tensor functor;
intermediate comparisons cancel. Directedness puts every pair of morphisms at
such a common stage, so the formula also gives uniqueness. -/
theorem commonStageDerivedTensor_existsUnique (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    ∃! F : generalAlgebraicallyClosedConstructibleCategory l Ω W ×
        generalAlgebraicallyClosedConstructibleCategory l Ω W ⥤
          generalAlgebraicallyClosedConstructibleCategory l Ω W,
      (∀ P Q, F.obj (P, Q) = commonStageTensorObject l Ω W P Q) ∧
      (∀ (P Q P' Q' : generalAlgebraicallyClosedConstructibleCategory l Ω W)
        (L : Index l Ω)
        (h : (commonStageTensorObject l Ω W P Q).stage ≤ L)
        (h' : (commonStageTensorObject l Ω W P' Q').stage ≤ L)
        (a : P.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1.trans h) ⟶
          P'.toStage
            (((Padic.finiteCoefficientFields_properties l Ω).1 P'.stage Q'.stage).1.trans h'))
        (b : Q.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2.trans h) ⟶
          Q'.toStage
            (((Padic.finiteCoefficientFields_properties l Ω).1 P'.stage Q'.stage).2.trans h')),
        HEq (F.map (X := (P, Q)) (Y := (P', Q')) (Prod.mkHom
          (ofHom P P' L
            (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1.trans h)
            (((Padic.finiteCoefficientFields_properties l Ω).1 P'.stage Q'.stage).1.trans h') a)
          (ofHom Q Q' L
            (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2.trans h)
            (((Padic.finiteCoefficientFields_properties l Ω).1 P'.stage Q'.stage).2.trans h') b)))
          (ofHom (commonStageTensorObject l Ω W P Q)
            (commonStageTensorObject l Ω W P' Q') L h h'
            ((commonStageTensorComparison l Ω W P Q L h).hom ≫
              (rationalDerivedTensor l (Coefficient.{u} l Ω L) W).map (Prod.mkHom a b) ≫
              (commonStageTensorComparison l Ω W P' Q' L h').inv))) := by
  sorry

/-- The canonical common-stage tensor functor on the existing pair category.
Source: blueprint common-stage paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageDerivedTensor (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :=
  (commonStageDerivedTensor_existsUnique l Ω W).exists.choose


/-- The permitted common-stage Hom pairs: extend both entries to their compositum,
then require exactly the integral-Hom constructibility predicate there.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageHomPairs (W : Scheme.{u}) :
    ObjectProperty ((generalAlgebraicallyClosedConstructibleCategory l Ω W)ᵒᵖ ×
      generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  fun P ↦ constructibleRationalHomPairs l
    (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω P.1.unop.stage P.2.stage)) W
    (op (P.1.unop.toStage
      ((Padic.finiteCoefficientFields_properties l Ω).1 P.1.unop.stage P.2.stage).1),
      P.2.toStage
        ((Padic.finiteCoefficientFields_properties l Ω).1 P.1.unop.stage P.2.stage).2)

/-- The literal permitted rational pair at the compositum, with no choice of lift.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageHomRationalPair (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory) :
    (constructibleRationalHomPairs l
      (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω
        P.obj.1.unop.stage P.obj.2.stage)) W).FullSubcategory :=
  ⟨(op (P.obj.1.unop.toStage
      ((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1),
    P.obj.2.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
      P.obj.1.unop.stage P.obj.2.stage).2), P.property⟩

/-- Common-stage internal Hom is the literal pair at the coefficient compositum.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageHomObject (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory) :
    generalAlgebraicallyClosedConstructibleCategory l Ω W :=
  ⟨Padic.finiteCoefficientCompositum l Ω P.obj.1.unop.stage P.obj.2.stage,
    (rationalDerivedInternalHom l (Coefficient.{u} l Ω
      (Padic.finiteCoefficientCompositum l Ω P.obj.1.unop.stage P.obj.2.stage)) W).obj
        (commonStageHomRationalPair l Ω W P)⟩

/-- A permitted compositum pair remains permitted at every larger finite stage.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: def-weil-derived-pullback-tensor-hom).
Proof: rationalHomScalarPair_permitted first extends the permitted integral pair.
The two integral scalar associators identify its entries with the entries extended
directly from their original stages. Internal Hom uses the inverse first
associator and the second associator. Its underlying integral isomorphism preserves
constructibility. Thus the displayed predicate holds before rationalization,
including identity inclusions and every further stage. -/
theorem commonStageHomPairAtStage_permitted (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L) :
    constructibleRationalHomPairs l (Coefficient.{u} l Ω L) W
      (op (P.obj.1.unop.toStage
        (((Padic.finiteCoefficientFields_properties l Ω).1
          P.obj.1.unop.stage P.obj.2.stage).1.trans h)),
        P.obj.2.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
          P.obj.1.unop.stage P.obj.2.stage).2.trans h)) := by
  let C := Padic.finiteCoefficientCompositum l Ω P.obj.1.unop.stage P.obj.2.stage
  have h₁ := ((Padic.finiteCoefficientFields_properties l Ω).1
    P.obj.1.unop.stage P.obj.2.stage).1
  have h₂ := ((Padic.finiteCoefficientFields_properties l Ω).1
    P.obj.1.unop.stage P.obj.2.stage).2
  let Q := commonStageHomRationalPair l Ω W P
  have hp := rationalHomScalarPair_permitted l (Coefficient.{u} l Ω C)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω C L h) W Q
  have ht := (stageSystem_existsUnique l Ω W).exists.choose_spec.1 C L h
  change constructibleRationalHomPairs l (Coefficient.{u} l Ω L) W
    (op ((transition l Ω W C L h).obj Q.obj.1.unop),
      (transition l Ω W C L h).obj Q.obj.2) at hp
  rw [← ht] at hp
  let e₁ := operationStageIntegralAssociator l Ω W _ C L h₁ h P.obj.1.unop.obj
  let e₂ := operationStageIntegralAssociator l Ω W _ C L h₂ h P.obj.2.obj
  exact (sfIntegralConstructible l (Coefficient.{u} l Ω L) W).prop_of_iso
    ((integralDerivedInternalHom l (Coefficient.{u} l Ω L) W).mapIso
        (Iso.prod ((sfIntegralConstructible l (Coefficient.{u} l Ω L) W).ι.mapIso
          e₁.symm).op ((sfIntegralConstructible l (Coefficient.{u} l Ω L) W).ι.mapIso
            e₂))) hp

/-- The permitted pair at a larger stage, using the actual scalar extensions.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageHomPairAtStage (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L) :
    (constructibleRationalHomPairs l (Coefficient.{u} l Ω L) W).FullSubcategory :=
  ⟨(op (P.obj.1.unop.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1.trans h)),
    P.obj.2.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
      P.obj.1.unop.stage P.obj.2.stage).2.trans h)),
    commonStageHomPairAtStage_permitted l Ω W P L h⟩

/-- The Hom comparison includes the inverse first-variable scalar associator.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageHomComparison (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L) :
    (commonStageHomObject l Ω W P).toStage h ≅
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).obj
        (commonStageHomPairAtStage l Ω W P L h) :=
  (operationStageTransitionIso l Ω W _ L h).app
      (commonStageHomObject l Ω W P).obj ≪≫
    rationalHomScalarComparison l
      (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω
        P.obj.1.unop.stage P.obj.2.stage))
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω _ L h) W
        (commonStageHomRationalPair l Ω W P) ≪≫
    (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).mapIso
      (ObjectProperty.isoMk _ (Iso.prod
        (((operationStageTransitionIso l Ω W _ L h).app
            (P.obj.1.unop.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
              P.obj.1.unop.stage P.obj.2.stage).1)).symm ≪≫
          ((stageSystem l Ω W).assoc ((Padic.finiteCoefficientFields_properties l Ω).1
            P.obj.1.unop.stage P.obj.2.stage).1 h).app P.obj.1.unop.obj).symm.op
        (((operationStageTransitionIso l Ω W _ L h).app
            (P.obj.2.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
              P.obj.1.unop.stage P.obj.2.stage).2)).symm ≪≫
          ((stageSystem l Ω W).assoc ((Padic.finiteCoefficientFields_properties l Ω).1
            P.obj.1.unop.stage P.obj.2.stage).2 h).app P.obj.2.obj)))

/-- Common-stage internal Hom has precisely the contravariant representative formula.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: def-weil-derived-pullback-tensor-hom).
Proof: form the permitted rational Hom at each literal compositum. The permitted
pair remains permitted at every common stage by commonStageHomPairAtStage_permitted.
Use commonStageHomComparison to compare the scalar extension of each output with
the Hom of the extended inputs. Its ordinary comparison transposes extended
evaluation; the inverse comparison in its first argument gives exactly u.op in
the formula. Naturality and the normalized coefficient tower equations show that
conjugation respects further transport and eventual equality. At a common stage,
the rational Hom functor gives identity and composition; the middle comparisons
cancel. Directedness puts any two representatives at such a stage. Every arrow
has a representative, so these formulas determine the functor uniquely. -/
theorem commonStageDerivedInternalHom_existsUnique (W : Scheme.{u}) :
    ∃! F : (commonStageHomPairs l Ω W).FullSubcategory ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω W,
      (∀ P, F.obj P = commonStageHomObject l Ω W P) ∧
      (∀ (P Q : (commonStageHomPairs l Ω W).FullSubcategory)
        (L : Index l Ω)
        (h : (commonStageHomObject l Ω W P).stage ≤ L)
        (h' : (commonStageHomObject l Ω W Q).stage ≤ L)
        (a : (commonStageHomPairAtStage l Ω W Q L h').obj.1.unop ⟶
          (commonStageHomPairAtStage l Ω W P L h).obj.1.unop)
        (b : (commonStageHomPairAtStage l Ω W P L h).obj.2 ⟶
          (commonStageHomPairAtStage l Ω W Q L h').obj.2),
        HEq (F.map (X := P) (Y := Q)
          (ObjectProperty.homMk (X := P) (Y := Q) (Prod.mkHom
            (ofHom Q.obj.1.unop P.obj.1.unop L
              (((Padic.finiteCoefficientFields_properties l Ω).1
                Q.obj.1.unop.stage Q.obj.2.stage).1.trans h')
              (((Padic.finiteCoefficientFields_properties l Ω).1
                P.obj.1.unop.stage P.obj.2.stage).1.trans h) a).op
            (ofHom P.obj.2 Q.obj.2 L
              (((Padic.finiteCoefficientFields_properties l Ω).1
                P.obj.1.unop.stage P.obj.2.stage).2.trans h)
              (((Padic.finiteCoefficientFields_properties l Ω).1
                Q.obj.1.unop.stage Q.obj.2.stage).2.trans h') b))))
          (ofHom (commonStageHomObject l Ω W P)
            (commonStageHomObject l Ω W Q) L h h'
            ((commonStageHomComparison l Ω W P L h).hom ≫
              (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).map
                (X := commonStageHomPairAtStage l Ω W P L h)
                (Y := commonStageHomPairAtStage l Ω W Q L h')
                (ObjectProperty.homMk
                  (X := commonStageHomPairAtStage l Ω W P L h)
                  (Y := commonStageHomPairAtStage l Ω W Q L h')
                  (Prod.mkHom a.op b)) ≫
              (commonStageHomComparison l Ω W Q L h').inv))) := by
  sorry

/-- The canonical common-stage internal Hom on precisely the permitted full subcategory.
Source: blueprint common-stage internal-Hom paragraph
(blueprint: def-weil-derived-pullback-tensor-hom). -/
def commonStageDerivedInternalHom (W : Scheme.{u}) :=
  (commonStageDerivedInternalHom_existsUnique l Ω W).exists.choose

end CommonStage
end WeilConjectures
