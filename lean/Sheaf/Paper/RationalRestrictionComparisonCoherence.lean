/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ConstantCoefficientScalarNormalization
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import all Sheaf.Paper.DerivedPullbackTensorHom

/-! # Rational restriction and comparison coherence

Source: blueprint main-20261015, def-pur-section-invariant, final invertibility assertion;
agent raw-Hom subargument in the DAG, and def-weil-derived-pullback-tensor-hom,
rational paragraph (blueprint: lem-pur-rational-restriction-comparison-coherence).

All abbreviations below specialize the published intrinsic operations. They introduce
no alternative coefficient category, scalar map, tensor product or comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.defeqAttrib.useBackward false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry TensorProduct
open WeilConjectures.AlgebraicallyClosedCoefficients (Index)

namespace WeilConjectures.RationalRestrictionComparison

attribute [local irreducible] Linear.homModule Preadditive.homGroup
  ScalarLocalization.linear ScalarLocalization.preadditive sfIntegralConstructible
  sfRationalScalarComp sfRationalScalarUnit
  integralDerivedPullback integralCompletedTensor
  integralDerivedInternalHom completedIntegralCoefficientSheafUnrestricted
  integralScalarExtension integralOrdinaryScalar HasDerivedCategory.standard
  constructibleIntegralPullback constructibleIntegralTensor rationalDerivedPullback
  rationalDerivedTensor sfRationalScalarExtension rationalPullbackScalarComparison
  rationalTensorScalarComparison constantCoefficientRationalScalarIso

variable (P : PurityFiniteSetting.{u})

/-- The finite coefficient indices in the fixed closure, with their existing order.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
abbrev Fields := Index P.coefficients.l P.coefficients.Qbar

/-- The actual intermediate coefficient field in the fixed closure.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
abbrev FieldAt (E : Fields P) :=
  E.val

/-- Schemes over the fixed geometric base field.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
abbrev Schemes := Over (Spec (CommRingCat.of P.field.k))

/-- The coefficient prime is invertible in every residue field, by the published stalk unit.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
@[instance_reducible]
def residueInvertible (W : Schemes P) (w : W.left) :
    Invertible (P.coefficients.l : W.left.residueField w) :=
  letI := (P.coefficientPrime_isUnit_stalk W.left W.hom w).invertible
  (Invertible.map (IsLocalRing.residue (W.left.presheaf.stalk w))
    (P.coefficients.l : W.left.presheaf.stalk w)).copy _ (map_natCast _ _).symm

attribute [instance] residueInvertible

/-- The recorded integralCategory at the small model of the finite coefficient field.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
abbrev integralCategory (E : Fields P) (W : Schemes P) :=
  sfIntegralConstructibleCategory P.coefficients.l (FieldAt P E) W.left

/-- The recorded rationalCategory at the small model of the finite coefficient field.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
abbrev rationalCategory (E : Fields P) (W : Schemes P) :=
  sfRationalConstructibleCategory P.coefficients.l (FieldAt P E) W.left

/-- The unchanged-object raw localization functor.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
abbrev localization (E : Fields P) (W : Schemes P) :=
  sfRationalConstructibleLocalization P.coefficients.l (FieldAt P E) W.left

/-- The published integralTensor operation, without a new choice.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
def integralTensor (E : Fields P) (W : Schemes P) :
    integralCategory P E W × integralCategory P E W ⥤ integralCategory P E W :=
  constructibleIntegralTensor P.coefficients.l (FieldAt P E) W.left

/-- The published rationalTensor operation, without a new choice.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
def rationalTensor (E : Fields P) (W : Schemes P) :
    rationalCategory P E W × rationalCategory P E W ⥤ rationalCategory P E W :=
  rationalDerivedTensor P.coefficients.l (FieldAt P E) W.left

/-- The published integralPullback for the given scheme morphism.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
def integralPullback (E : Fields P) {Y X : Schemes P} (f : Y ⟶ X) :
    integralCategory P E X ⥤ integralCategory P E Y :=
  constructibleIntegralPullback P.coefficients.l (FieldAt P E) f.left

/-- The published rationalPullback for the given scheme morphism.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
def rationalPullback (E : Fields P) {Y X : Schemes P} (f : Y ⟶ X) :
    rationalCategory P E X ⥤ rationalCategory P E Y :=
  rationalDerivedPullback P.coefficients.l (FieldAt P E) f.left

/-- The specified integral coefficient extension.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
def integralScalar (E L : Fields P) (h : E ≤ L) (W : Schemes P) :
    integralCategory P E W ⥤ integralCategory P L W :=
  sfConstructibleIntegralScalarExtension 0 P.coefficients.l
    (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime))
    (FieldAt P E) (FieldAt P L)
    (IntermediateField.inclusion h) W.left

/-- The specified rational coefficient extension.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
def rationalScalar (E L : Fields P) (h : E ≤ L) (W : Schemes P) :
    rationalCategory P E W ⥤ rationalCategory P L W :=
  sfRationalScalarExtension P.coefficients.l (FieldAt P E) W.left 0
    (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) (FieldAt P L)
    (IntermediateField.inclusion h)

/-- The regular completed coefficient module in the integral constructible category.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
abbrev integralUnit (E : Fields P) (W : Schemes P) :=
  constantWeilIntegralObject P.coefficients.l (FieldAt P E)
    P.field P.coefficients.different W.left

/-- The canonical integralB comparison, with its existing normalization.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
def integralB (E L : Fields P) (h : E ≤ L) {Y X : Schemes P} (f : Y ⟶ X)
    (K : integralCategory P E X) :
    (integralScalar P E L h Y).obj ((integralPullback P E f).obj K) ≅
      (integralPullback P L f).obj ((integralScalar P E L h X).obj K) :=
  integralPullbackScalarComparison P.coefficients.l (FieldAt P E) (FieldAt P L)
    (IntermediateField.inclusion h) f.left K

/-- The canonical rationalB comparison, with its existing normalization.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
def rationalB (E L : Fields P) (h : E ≤ L) {Y X : Schemes P} (f : Y ⟶ X) :
    rationalPullback P E f ⋙ rationalScalar P E L h Y ≅
      rationalScalar P E L h X ⋙ rationalPullback P L f :=
  rationalPullbackScalarComparison P.coefficients.l (FieldAt P E) (FieldAt P L)
    (IntermediateField.inclusion h) f.left

/-- The canonical integralTheta comparison, with both tensor variables covariant.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
def integralTheta (E L : Fields P) (h : E ≤ L) (W : Schemes P)
    (M N : integralCategory P E W) :
    (integralScalar P E L h W).obj ((integralTensor P E W).obj (M, N)) ≅
      (integralTensor P L W).obj
        ((integralScalar P E L h W).obj M, (integralScalar P E L h W).obj N) :=
  integralTensorScalarComparison P.coefficients.l (FieldAt P E) (FieldAt P L)
    (IntermediateField.inclusion h) W.left M N

/-- The canonical rationalTheta comparison, with both tensor variables covariant.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
def rationalTheta (E L : Fields P) (h : E ≤ L) (W : Schemes P) :
    rationalTensor P E W ⋙ rationalScalar P E L h W ≅
      (rationalScalar P E L h W).prod (rationalScalar P E L h W) ⋙
        rationalTensor P L W :=
  rationalTensorScalarComparison P.coefficients.l (FieldAt P E) (FieldAt P L)
    (IntermediateField.inclusion h) W.left

/-- The canonical integralUpsilon comparison, normalized on the regular coefficient object.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
abbrev integralUpsilon (E L : Fields P) (h : E ≤ L) (W : Schemes P) :=
  constantCoefficientConstructibleScalarIso P.coefficients.l (FieldAt P E) (FieldAt P L)
    (IntermediateField.inclusion h) W.left
    P.field P.coefficients.different

/-- The canonical rationalUpsilon comparison, normalized on the regular coefficient object.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
abbrev rationalUpsilon (E L : Fields P) (h : E ≤ L) (W : Schemes P) :=
  constantCoefficientRationalScalarIso P.coefficients.l (FieldAt P E) (FieldAt P L)
    (IntermediateField.inclusion h) W.left
    P.field P.coefficients.different

/-- The localized integral coefficient associator, including the inclusion transport.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
def rationalAssociator (E L M : Fields P) (h : E ≤ L) (j : L ≤ M)
    (W : Schemes P) :
    rationalScalar P E L h W ⋙ rationalScalar P L M j W ≅
      rationalScalar P E M (h.trans j) W :=
  sfRationalScalarComp P.coefficients.l (FieldAt P E) (FieldAt P L)
    (IntermediateField.inclusion h) W.left 0
    (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) (FieldAt P M)
    (IntermediateField.inclusion j)

/-- The localized integral identity-coefficient comparison.
Source: the rational raw-Hom subargument of def-pur-section-invariant
(blueprint: lem-pur-rational-restriction-comparison-coherence). -/
def rationalUnitor (E : Fields P) (W : Schemes P) :
    rationalScalar P E E le_rfl W ≅ 𝟭 (rationalCategory P E W) :=
  sfRationalScalarUnit P.coefficients.l (FieldAt P E) W.left 0
    (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime))

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem iso_inv_heq {C : Type*} [Category C] {A B A' B' : C}
    (ha : A = A') (hb : B = B') (e : A ≅ B) (e' : A' ≅ B')
    (he : HEq e.hom e'.hom) : HEq e.inv e'.inv := by
  subst A'; subst B'
  have : e = e' := Iso.ext (eq_of_heq he)
  cases this
  rfl

private theorem raw_pullback_obj (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ x : X, Invertible (l : X.residueField x)]
    (K : sfRationalConstructibleCategory l E X) :
    (rationalDerivedPullback l E f).obj K = ⟨(constructibleIntegralPullback l E f).obj K.obj⟩ :=
  by
    unfold rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique l E
      f).exists.choose_spec.2.1 K

set_option backward.defeqAttrib.useBackward false in
private theorem raw_tensor_obj (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfRationalConstructibleCategory l E W) :
    (rationalDerivedTensor l E W).obj (M, N) =
      ⟨(constructibleIntegralTensor l E W).obj (M.obj, N.obj)⟩ := by
  unfold rationalDerivedTensor
  exact (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 (M, N)

set_option backward.defeqAttrib.useBackward false in
private theorem tensor_obj (E : Fields P) (W : Schemes P)
    (M N : rationalCategory P E W) :
    (rationalTensor P E W).obj (M, N) = ⟨(integralTensor P E W).obj (M.obj, N.obj)⟩ :=
  by
    exact raw_tensor_obj P.coefficients.l (FieldAt P E) W.left M N

private theorem scalar_obj (E L : Fields P) (h : E ≤ L) (W : Schemes P)
    (K : rationalCategory P E W) :
    (rationalScalar P E L h W).obj K = ⟨(integralScalar P E L h W).obj K.obj⟩ :=
  by
    unfold rationalScalar sfRationalScalarExtension integralScalar
    exact
    (sfRationalScalarExtension_existsUnique P.coefficients.l (FieldAt P E) W.left 0
    (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) (FieldAt P L)
    (IntermediateField.inclusion h)).exists.choose_spec.2.1 K

private theorem iso_existsUnique {C : Type*} [Category C] {A A' B : C}
    (h : A = A') (e : A' ≅ B) :
    ∃! e' : A ≅ B, HEq e'.hom e.hom ∧ HEq e'.inv e.inv := by
  subst A'
  refine ⟨e, ⟨HEq.rfl, HEq.rfl⟩, ?_⟩
  intro e' he'
  exact Iso.ext (eq_of_heq he'.1)

private theorem pullback_obj {Y X : Schemes P} (f : Y ⟶ X) (E : Fields P)
    (K : rationalCategory P E X) :
    (rationalPullback P E f).obj K = ⟨(integralPullback P E f).obj K.obj⟩ := by
  exact raw_pullback_obj P.coefficients.l (FieldAt P E) f.left K

private theorem raw_pullback_map (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ x : X, Invertible (l : X.residueField x)]
    (K K' : sfIntegralConstructibleCategory l E X) (a : K ⟶ K')
    (c : Localization.Away (Padic.coefficientExtensionUniformizer
      l E)) :
    HEq ((rationalDerivedPullback l E f).map
      (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] a :
        (sfRationalConstructibleLocalization l E X).obj K ⟶
          (sfRationalConstructibleLocalization l E X).obj K'))
      (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
        (constructibleIntegralPullback l E f).map a) :=
  by
    unfold rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique l E
      f).exists.choose_spec.2.2 K K' a c


private theorem raw_pullback_additive (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ x : X, Invertible (l : X.residueField x)] :
    (rationalDerivedPullback l E f).Additive := by
  unfold rationalDerivedPullback
  exact (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.1

private theorem tensor_bilinear (E : Fields P) (W : Schemes P)
    (M M' N N' : rationalCategory P E W) :
    ∃ B : (M ⟶ M') →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer
          P.coefficients.l (FieldAt P E))]
        (N ⟶ N') →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer
          P.coefficients.l (FieldAt P E))]
        ((rationalTensor P E W).obj (M, N) ⟶ (rationalTensor P E W).obj (M', N')),
      (∀ a b, (rationalTensor P E W).map (Prod.mkHom a b) = B a b) ∧
      ∀ (a : M.obj ⟶ M'.obj) (b : N.obj ⟶ N'.obj)
        (c d : Localization.Away (Padic.coefficientExtensionUniformizer
          P.coefficients.l (FieldAt P E))),
        HEq (B
          (c ⊗ₜ[Padic.coefficientExtensionIntegers P.coefficients.l (FieldAt P E)] a)
          (d ⊗ₜ[Padic.coefficientExtensionIntegers P.coefficients.l (FieldAt P E)] b))
          ((c * d) ⊗ₜ[Padic.coefficientExtensionIntegers P.coefficients.l (FieldAt P E)]
            (integralTensor P E W).map (Prod.mkHom a b)) := by
  unfold rationalTensor integralTensor
  obtain ⟨B, hB, hm⟩ := (rationalTensor_spec P.coefficients.l (FieldAt P E) W.left).2
    M M' N N'
  refine ⟨B, ?_, ?_⟩
  · exact hB
  · exact hm


private theorem tensorIso_localize
    {R : Type*} [CommRing R] {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D] (t : R)
    (U : C × C ⥤ C) (V : D × D ⥤ D) (r : C ⥤ D)
    (A : ScalarLocalization R C t × ScalarLocalization R C t ⥤ ScalarLocalization R C t)
    (B : ScalarLocalization R D t × ScalarLocalization R D t ⥤ ScalarLocalization R D t)
    (T : ScalarLocalization R C t ⥤ ScalarLocalization R D t) [T.Additive]
    (hA : ∀ K, A.obj K = ⟨U.obj (K.1.obj, K.2.obj)⟩)
    (hB : ∀ K, B.obj K = ⟨V.obj (K.1.obj, K.2.obj)⟩)
    (hT : ∀ K, T.obj K = ⟨r.obj K.obj⟩)
    (mT : ∀ (K K' : C) (a : K ⟶ K') (x : Localization.Away t),
      HEq (T.map (x ⊗ₜ[R] a : ScalarLocalization.mk K ⟶ ScalarLocalization.mk K'))
        (x ⊗ₜ[R] r.map a))
    (mA : ∀ (K K' N N' : ScalarLocalization R C t),
      ∃ β : (K ⟶ K') →ₗ[Localization.Away t] (N ⟶ N') →ₗ[Localization.Away t]
          (A.obj (K, N) ⟶ A.obj (K', N')),
        (∀ a b, A.map (Prod.mkHom a b) = β a b) ∧
        ∀ (a : K.obj ⟶ K'.obj) (b : N.obj ⟶ N'.obj) (x y : Localization.Away t),
          HEq (β (x ⊗ₜ[R] a) (y ⊗ₜ[R] b)) ((x * y) ⊗ₜ[R] U.map (Prod.mkHom a b)))
    (mB : ∀ (K K' N N' : ScalarLocalization R D t),
      ∃ β : (K ⟶ K') →ₗ[Localization.Away t] (N ⟶ N') →ₗ[Localization.Away t]
          (B.obj (K, N) ⟶ B.obj (K', N')),
        (∀ a b, B.map (Prod.mkHom a b) = β a b) ∧
        ∀ (a : K.obj ⟶ K'.obj) (b : N.obj ⟶ N'.obj) (x y : Localization.Away t),
          HEq (β (x ⊗ₜ[R] a) (y ⊗ₜ[R] b)) ((x * y) ⊗ₜ[R] V.map (Prod.mkHom a b)))
    (μ : U ⋙ r ≅ r.prod r ⋙ V) :
    ∃! α : A ⋙ T ≅ T.prod T ⋙ B,
      ∀ K, HEq (α.hom.app K)
        ((ScalarLocalization.localization R D t).map (μ.hom.app (K.1.obj, K.2.obj))) := by
  apply rawBilinearIso_existsUnique t t id (U ⋙ r) (r.prod r ⋙ V) μ
    (A ⋙ T) (T.prod T ⋙ B)
  · intro K
    exact (congrArg T.obj (hA K)).trans (hT _)
  · intro K
    exact (hB _).trans (congrArg
      (fun Z : ScalarLocalization R D t × ScalarLocalization R D t ↦
        ScalarLocalization.mk (V.obj (Z.1.obj, Z.2.obj)))
      (congrArg₂ Prod.mk (hT K.1) (hT K.2)))
  · intro K K' N N'
    obtain ⟨β, hβ, pβ⟩ := mA K K' N N'
    let γ := bilinearPost (bilinearAdd (R := Localization.Away t) β) T.mapAddHom
    refine ⟨γ, ?_, ?_⟩
    · intro a b
      change T.map (A.map (Prod.mkHom a b)) = T.map (β a b)
      rw [hβ]
    · intro a b x y
      exact (map_heq T (hA _) (hA _) (pβ a b x y)).trans
        (mT _ _ (U.map (Prod.mkHom a b)) (x * y))
  · intro K K' N N'
    obtain ⟨β, hβ, pβ⟩ := mB (T.obj K) (T.obj K') (T.obj N) (T.obj N')
    let γ := bilinearPre (bilinearAdd (R := Localization.Away t) β) T.mapAddHom T.mapAddHom
    refine ⟨γ, ?_, ?_⟩
    · intro a b
      exact hβ (T.map a) (T.map b)
    · intro a b x y
      change HEq (β (T.map _) (T.map _)) _
      rw [← hβ]
      have hp := prod_hom_heq (hT K) (hT K') (hT N) (hT N')
        (mT K.obj K'.obj a x) (mT N.obj N'.obj b y)
      have hm := map_heq B (congrArg₂ Prod.mk (hT K) (hT N))
        (congrArg₂ Prod.mk (hT K') (hT N')) hp
      obtain ⟨δ, hδ, pδ⟩ := mB ⟨r.obj K.obj⟩ ⟨r.obj K'.obj⟩
        ⟨r.obj N.obj⟩ ⟨r.obj N'.obj⟩
      have hd := pδ (r.map a) (r.map b) x y
      rw [← hδ] at hd
      exact hm.trans hd

/-- The supplied integral tensor comparison extends uniquely to the recorded rational
operations, with the specified localized inverse.
Proof (steps 1, 3, 5): objects are unchanged. Integral naturality on two arrows
multiplied by the product of their coefficients is rational naturality on pure
tensors. Balancing follows from integral bilinearity; extend by addition in both
variables. Localize the inverse equations. Components determine a natural isomorphism.
Source: blueprint def-pur-section-invariant, final invertibility assertion,
DAG raw-Hom subargument (blueprint: lem-pur-rational-restriction-comparison-coherence). -/
theorem tensorComparison_existsUnique {Y X : Schemes P} (f : Y ⟶ X) (E : Fields P)
    (μ : integralTensor P E X ⋙ integralPullback P E f ≅
      (integralPullback P E f).prod (integralPullback P E f) ⋙ integralTensor P E Y) :
    ∃! a : rationalTensor P E X ⋙ rationalPullback P E f ≅
        (rationalPullback P E f).prod (rationalPullback P E f) ⋙ rationalTensor P E Y,
      ∀ M N : rationalCategory P E X,
        HEq (a.hom.app (M, N)) ((localization P E Y).map (μ.hom.app (M.obj, N.obj))) ∧
        HEq (a.inv.app (M, N)) ((localization P E Y).map (μ.inv.app (M.obj, N.obj))) := by
  let A := rationalTensor P E X
  let B := rationalTensor P E Y
  let T := rationalPullback P E f
  let t := Padic.coefficientExtensionUniformizer P.coefficients.l (FieldAt P E)
  have : T.Additive := raw_pullback_additive P.coefficients.l (FieldAt P E) f.left
  have H := tensorIso_localize t (integralTensor P E X) (integralTensor P E Y)
    (integralPullback P E f) A B T
    (fun K ↦ tensor_obj P E X K.1 K.2)
    (fun K ↦ tensor_obj P E Y K.1 K.2)
    (pullback_obj P f E)
    (raw_pullback_map P.coefficients.l (FieldAt P E) f.left)
    (tensor_bilinear P E X) (tensor_bilinear P E Y) μ
  obtain ⟨a, ha, hu⟩ := H
  have hi (M N : rationalCategory P E X) :
      HEq (a.inv.app (M, N)) ((localization P E Y).map (μ.inv.app (M.obj, N.obj))) := by
    apply iso_inv_heq _ _ (a.app (M, N))
      ((localization P E Y).mapIso (μ.app (M.obj, N.obj))) (ha (M, N))
    · exact (congrArg T.obj (tensor_obj P E X M N)).trans (pullback_obj P f E _)
    · exact (tensor_obj P E Y _ _).trans (congrArg
        (fun z : rationalCategory P E Y × rationalCategory P E Y ↦
        ScalarLocalization.mk ((integralTensor P E Y).obj (z.1.obj, z.2.obj)))
        (congrArg₂ Prod.mk (pullback_obj P f E M) (pullback_obj P f E N)))
  refine ⟨a, fun M N ↦ ⟨ha (M, N), hi M N⟩, ?_⟩
  intro a' h'
  exact hu a' (fun K ↦ (h' K.1 K.2).1)

/-- The rational tensor comparison fixed by the supplied integral comparison.
Source: blueprint def-pur-section-invariant, final invertibility assertion,
DAG raw-Hom subargument (blueprint: lem-pur-rational-restriction-comparison-coherence). -/
def tensorComparison {Y X : Schemes P} (f : Y ⟶ X) (E : Fields P)
    (μ : integralTensor P E X ⋙ integralPullback P E f ≅
      (integralPullback P E f).prod (integralPullback P E f) ⋙ integralTensor P E Y) :
    rationalTensor P E X ⋙ rationalPullback P E f ≅
      (rationalPullback P E f).prod (rationalPullback P E f) ⋙ rationalTensor P E Y :=
  (tensorComparison_existsUnique P f E μ).exists.choose

/-- The unit comparison and its inverse are precisely the localized integral arrows.
Proof (steps 1, 4): localize the supplied isomorphism. The rational pullback object
formula gives the endpoints. Functoriality localizes both inverse equations; its
hom component determines the isomorphism uniquely. Constant-diagram naturality
is the identity equation.
Source: blueprint def-pur-section-invariant, final invertibility assertion,
DAG raw-Hom subargument (blueprint: lem-pur-rational-restriction-comparison-coherence). -/
theorem unitComparison_existsUnique {Y X : Schemes P} (f : Y ⟶ X) (E : Fields P)
    (ε : (integralPullback P E f).obj (integralUnit P E X) ≅ integralUnit P E Y) :
    ∃! a : (rationalPullback P E f).obj ((localization P E X).obj (integralUnit P E X)) ≅
        (localization P E Y).obj (integralUnit P E Y),
      HEq a.hom ((localization P E Y).map ε.hom) ∧
      HEq a.inv ((localization P E Y).map ε.inv) := by
  exact iso_existsUnique (pullback_obj P f E _)
    ((localization P E Y).mapIso ε)


/-- The rational unit comparison, fixed before localization.
Source: blueprint def-pur-section-invariant, final invertibility assertion,
DAG raw-Hom subargument (blueprint: lem-pur-rational-restriction-comparison-coherence). -/
def unitComparison {Y X : Schemes P} (f : Y ⟶ X) (E : Fields P)
    (ε : (integralPullback P E f).obj (integralUnit P E X) ≅ integralUnit P E Y) :
    (rationalPullback P E f).obj ((localization P E X).obj (integralUnit P E X)) ≅
      (localization P E Y).obj (integralUnit P E Y) :=
  (unitComparison_existsUnique P f E ε).exists.choose

/-- The canonical pullback, tensor and coefficient-unit scalar comparisons have
exactly their integral hom and inverse components.
Proof (steps 2, 4, 5): apply semilinear localization to the two functors compared
by b. For theta multiply the two-variable integral naturality equation by the
product of the scalars. The coefficient inclusion carries the nonzero source
uniformizer to a unit in the target field, including ramified extensions.
All inverse equations follow by applying Q; use the recorded component
normalizations to identify the resulting isomorphisms with b, theta and upsilon.
Source: blueprint def-pur-section-invariant, final invertibility assertion,
DAG raw-Hom subargument (blueprint: lem-pur-rational-restriction-comparison-coherence). -/
theorem scalarComparisons_localized {Y X : Schemes P} (f : Y ⟶ X)
    (E L : Fields P) (h : E ≤ L) :
    (∀ K : rationalCategory P E X,
      HEq ((rationalB P E L h f).hom.app K)
        ((localization P L Y).map (integralB P E L h f K.obj).hom) ∧
      HEq ((rationalB P E L h f).inv.app K)
        ((localization P L Y).map (integralB P E L h f K.obj).inv)) ∧
    (∀ (W : Schemes P) (M N : rationalCategory P E W),
      HEq ((rationalTheta P E L h W).hom.app (M, N))
        ((localization P L W).map (integralTheta P E L h W M.obj N.obj).hom) ∧
      HEq ((rationalTheta P E L h W).inv.app (M, N))
        ((localization P L W).map (integralTheta P E L h W M.obj N.obj).inv)) ∧
    (∀ W : Schemes P,
      HEq (rationalUpsilon P E L h W).hom
        ((localization P L W).map (integralUpsilon P E L h W).hom) ∧
      HEq (rationalUpsilon P E L h W).inv
        ((localization P L W).map (integralUpsilon P E L h W).inv)) := by
  constructor
  · intro K
    have hb : HEq ((rationalB P E L h f).hom.app K)
        ((localization P L Y).map (integralB P E L h f K.obj).hom) :=
      by
        unfold rationalB rationalPullbackScalarComparison integralB rationalPullback
          rationalScalar integralPullback integralScalar
        exact
        (rationalPullbackScalarComparison_existsUnique P.coefficients.l (FieldAt P E)
        (FieldAt P L) (IntermediateField.inclusion h) f.left).exists.choose_spec K
    refine ⟨hb, iso_inv_heq ?_ ?_ ((rationalB P E L h f).app K)
      ((localization P L Y).mapIso (integralB P E L h f K.obj)) hb⟩
    · exact (scalar_obj P E L h Y _).trans
        (congrArg (fun Z : rationalCategory P E Y ↦
          (localization P L Y).obj ((integralScalar P E L h Y).obj Z.obj))
            (pullback_obj P f E K))
    · exact (pullback_obj P f L _).trans
        (congrArg (fun Z : rationalCategory P L X ↦
          (localization P L Y).obj ((integralPullback P L f).obj Z.obj))
            (scalar_obj P E L h X K))
  constructor
  · intro W M N
    have ht : HEq ((rationalTheta P E L h W).hom.app (M, N))
        ((localization P L W).map (integralTheta P E L h W M.obj N.obj).hom) :=
      by
        unfold rationalTheta rationalTensorScalarComparison integralTheta rationalTensor
          rationalScalar integralTensor integralScalar
        exact
        (rationalTensorScalarComparison_existsUnique P.coefficients.l (FieldAt P E)
        (FieldAt P L) (IntermediateField.inclusion h) W.left).exists.choose_spec M N
    refine ⟨ht, iso_inv_heq ?_ ?_ ((rationalTheta P E L h W).app (M, N))
      ((localization P L W).mapIso (integralTheta P E L h W M.obj N.obj)) ht⟩
    · exact (scalar_obj P E L h W _).trans
        (congrArg (fun Z : rationalCategory P E W ↦
          (localization P L W).obj ((integralScalar P E L h W).obj Z.obj))
            (tensor_obj P E W M N))
    · rw [show ((rationalScalar P E L h W).prod
          (rationalScalar P E L h W) ⋙ rationalTensor P L W).obj (M, N) =
          (rationalTensor P L W).obj ((rationalScalar P E L h W).obj M,
            (rationalScalar P E L h W).obj N) from rfl,
        tensor_obj, scalar_obj, scalar_obj]
      rfl
  · intro W
    have hu : HEq (rationalUpsilon P E L h W).hom
        ((localization P L W).map (integralUpsilon P E L h W).hom) :=
      by
        unfold rationalUpsilon constantCoefficientRationalScalarIso
        exact
        (constantCoefficientRationalScalarIso_existsUnique P.coefficients.l (FieldAt P E)
        (FieldAt P L) (IntermediateField.inclusion h) W.left P.field
        P.coefficients.different).exists.choose_spec
    exact ⟨hu, iso_inv_heq (scalar_obj P E L h W _) rfl
      (rationalUpsilon P E L h W)
      ((localization P L W).mapIso (integralUpsilon P E L h W)) hu⟩


variable {Y X : Schemes P} (f : Y ⟶ X)
  [hXft : LocallyOfFiniteType X.hom] [hXqc : QuasiCompact X.hom]
  [hYft : LocallyOfFiniteType Y.hom] [hYqc : QuasiCompact Y.hom]
  (linear : ∀ E : Fields P,
    (integralPullback P E f).Linear (Padic.coefficientExtensionIntegers
      P.coefficients.l (FieldAt P E)))
  (μ : ∀ E : Fields P, integralTensor P E X ⋙ integralPullback P E f ≅
    (integralPullback P E f).prod (integralPullback P E f) ⋙ integralTensor P E Y)
  (ε : ∀ E : Fields P,
    (integralPullback P E f).obj (integralUnit P E X) ≅ integralUnit P E Y)

include hXft hXqc hYft hYqc linear in
/-- Both specified mixed squares survive raw rationalization, for the given natural
integral comparisons and the canonical scalar comparisons.
Proof (steps 1--6): construct tensorComparison and unitComparison as above.
Apply Q at L,Y to each assumed integral equality. Unary operations commute with
Q by semilinear localization, tensor does so by the bilinear pure-arrow formula,
and Q preserves composition. The component prescriptions identify every factor
with the displayed rational one. Thus both equalities hold. There is no
injectivity or cancellation of integral Homs in this argument.
Source: blueprint def-pur-section-invariant, final invertibility assertion,
DAG raw-Hom subargument (blueprint: lem-pur-rational-restriction-comparison-coherence). -/
theorem mixedSquares
    (hTensor : ∀ (E L : Fields P) (h : E ≤ L) (M N : integralCategory P E X),
      (integralScalar P E L h Y).map ((μ E).hom.app (M, N)) ≫
        (integralTheta P E L h Y
          ((integralPullback P E f).obj M) ((integralPullback P E f).obj N)).hom ≫
        (integralTensor P L Y).map
          (Prod.mkHom (integralB P E L h f M).hom (integralB P E L h f N).hom) =
      (integralB P E L h f ((integralTensor P E X).obj (M, N))).hom ≫
        (integralPullback P L f).map (integralTheta P E L h X M N).hom ≫
        (μ L).hom.app ((integralScalar P E L h X).obj M,
          (integralScalar P E L h X).obj N))
    (hUnit : ∀ (E L : Fields P) (h : E ≤ L),
      (integralScalar P E L h Y).map (ε E).hom ≫ (integralUpsilon P E L h Y).hom =
      (integralB P E L h f (integralUnit P E X)).hom ≫
        (integralPullback P L f).map (integralUpsilon P E L h X).hom ≫ (ε L).hom) :
    (∀ (E L : Fields P) (h : E ≤ L) (M N : rationalCategory P E X),
      (rationalScalar P E L h Y).map ((tensorComparison P f E (μ E)).hom.app (M, N)) ≫
        (rationalTheta P E L h Y).hom.app
          ((rationalPullback P E f).obj M, (rationalPullback P E f).obj N) ≫
        (rationalTensor P L Y).map
          (Prod.mkHom ((rationalB P E L h f).hom.app M)
            ((rationalB P E L h f).hom.app N)) =
      (rationalB P E L h f).hom.app ((rationalTensor P E X).obj (M, N)) ≫
        (rationalPullback P L f).map ((rationalTheta P E L h X).hom.app (M, N)) ≫
        (tensorComparison P f L (μ L)).hom.app
          ((rationalScalar P E L h X).obj M, (rationalScalar P E L h X).obj N)) ∧
    (∀ (E L : Fields P) (h : E ≤ L),
      (rationalScalar P E L h Y).map (unitComparison P f E (ε E)).hom ≫
        (rationalUpsilon P E L h Y).hom =
      (rationalB P E L h f).hom.app ((localization P E X).obj (integralUnit P E X)) ≫
        (rationalPullback P L f).map (rationalUpsilon P E L h X).hom ≫
        (unitComparison P f L (ε L)).hom) := by
  sorry


/-- The canonical b and theta obey their identity-coefficient compatibility.
Proof (steps 1, 2, 3, 7): apply Q to the integral identity equations. The
semilinear unary and bilinear tensor formulas identify the images of all
whiskerings, and Q preserves composition. The coefficient unit is the
published localized integral unit, including the coefficient-inclusion transport.
Source: blueprint def-pur-section-invariant, final invertibility assertion,
DAG raw-Hom subargument (blueprint: lem-pur-rational-restriction-comparison-coherence). -/
theorem identityCoherence {Y X : Schemes P} (f : Y ⟶ X) (E : Fields P) :
    (∀ K : rationalCategory P E X,
      (rationalB P E E le_rfl f).hom.app K ≫
        (rationalPullback P E f).map ((rationalUnitor P E X).hom.app K) =
      (rationalUnitor P E Y).hom.app ((rationalPullback P E f).obj K)) ∧
    (∀ (W : Schemes P) (M N : rationalCategory P E W),
      (rationalTheta P E E le_rfl W).hom.app (M, N) ≫
        (rationalTensor P E W).map
          (Prod.mkHom ((rationalUnitor P E W).hom.app M)
            ((rationalUnitor P E W).hom.app N)) =
      (rationalUnitor P E W).hom.app ((rationalTensor P E W).obj (M, N))) := by
  sorry

/-- The canonical b and theta obey their coefficient-tower compatibility.
Proof (steps 1, 2, 3, 7): apply Q in the final field to the specified integral
tower equations of the normalized scalar comparisons. The published associator
is the localized integral associator with the actual coefficient-inclusion
composition transport. Unary and binary whiskerings commute with Q, and
composition does too, giving exactly both displayed paths. Repeated fields
use the same associator and identity comparisons.
Source: blueprint def-pur-section-invariant, final invertibility assertion,
DAG raw-Hom subargument (blueprint: lem-pur-rational-restriction-comparison-coherence). -/
theorem towerCoherence {Y X : Schemes P} (f : Y ⟶ X)
    (E L F : Fields P) (h : E ≤ L) (j : L ≤ F) :
    (∀ K : rationalCategory P E X,
      (rationalScalar P L F j Y).map ((rationalB P E L h f).hom.app K) ≫
        (rationalB P L F j f).hom.app ((rationalScalar P E L h X).obj K) ≫
        (rationalPullback P F f).map ((rationalAssociator P E L F h j X).hom.app K) =
      (rationalAssociator P E L F h j Y).hom.app ((rationalPullback P E f).obj K) ≫
        (rationalB P E F (h.trans j) f).hom.app K) ∧
    (∀ (W : Schemes P) (M N : rationalCategory P E W),
      (rationalScalar P L F j W).map ((rationalTheta P E L h W).hom.app (M, N)) ≫
        (rationalTheta P L F j W).hom.app
          ((rationalScalar P E L h W).obj M, (rationalScalar P E L h W).obj N) ≫
        (rationalTensor P F W).map
          (Prod.mkHom ((rationalAssociator P E L F h j W).hom.app M)
            ((rationalAssociator P E L F h j W).hom.app N)) =
      (rationalAssociator P E L F h j W).hom.app ((rationalTensor P E W).obj (M, N)) ≫
        (rationalTheta P E F (h.trans j) W).hom.app (M, N)) := by
  sorry

/-- Pullback and tensor have exactly the source pure-arrow formulas. The bilinear
map is on the actual localized Hom groups, so balancing and additive extension
in both slots are part of the assertion. The canonical localized-coefficient
equivalence identifies these scalar-first coordinates with Hom tensor E.
Proof (steps 2, 3): use the recorded rational operation normalizations.
Integral pullback is O_E-linear. Tensor is O_E-linear separately in each slot,
so the two balancing relations give the same product of scalars. Extend
additively. The integral bifunctor law and commutativity of scalar products
give composition, and the coefficient one gives identities.
Source: blueprint def-pur-section-invariant, final invertibility assertion,
DAG raw-Hom subargument (blueprint: lem-pur-rational-restriction-comparison-coherence). -/
theorem pureArrowActions {Y X : Schemes P} (f : Y ⟶ X) (E : Fields P) :
    (rationalPullback P E f).Additive ∧
    (∀ (K K' : integralCategory P E X) (a : K ⟶ K')
      (c : Localization.Away (Padic.coefficientExtensionUniformizer
        P.coefficients.l (FieldAt P E))),
      HEq ((rationalPullback P E f).map
        (c ⊗ₜ[Padic.coefficientExtensionIntegers P.coefficients.l (FieldAt P E)] a :
          (localization P E X).obj K ⟶ (localization P E X).obj K'))
        (c ⊗ₜ[Padic.coefficientExtensionIntegers P.coefficients.l (FieldAt P E)]
          (integralPullback P E f).map a)) ∧
    (∀ (W : Schemes P) (M M' N N' : rationalCategory P E W),
      ∃ B : (M ⟶ M') →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer
            P.coefficients.l (FieldAt P E))]
          (N ⟶ N') →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer
            P.coefficients.l (FieldAt P E))]
          ((rationalTensor P E W).obj (M, N) ⟶ (rationalTensor P E W).obj (M', N')),
        (∀ a b, (rationalTensor P E W).map (Prod.mkHom a b) = B a b) ∧
        ∀ (a : M.obj ⟶ M'.obj) (b : N.obj ⟶ N'.obj)
          (c d : Localization.Away (Padic.coefficientExtensionUniformizer
            P.coefficients.l (FieldAt P E))),
          HEq (B
            (c ⊗ₜ[Padic.coefficientExtensionIntegers P.coefficients.l (FieldAt P E)] a)
            (d ⊗ₜ[Padic.coefficientExtensionIntegers P.coefficients.l (FieldAt P E)] b))
            ((c * d) ⊗ₜ[Padic.coefficientExtensionIntegers P.coefficients.l (FieldAt P E)]
              (integralTensor P E W).map (Prod.mkHom a b))) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold rationalPullback
    exact raw_pullback_additive P.coefficients.l (FieldAt P E) f.left
  · unfold rationalPullback integralPullback localization
    exact raw_pullback_map P.coefficients.l (FieldAt P E) f.left
  · intro W M M' N N'
    obtain ⟨B, hB, hm⟩ := tensor_bilinear P E W M M' N N'
    exact ⟨B, hB, hm⟩

/-- Localization preserves integral equations and their identity, composite,
pullback, scalar and tensor operations. Along with the comparison and inverse
component normalizations these are the recursive evaluation laws for every
specified integral comparison expression.
Proof (steps 1--3, 8): Q is a functor, so it preserves equality, identities
and composition. The unary pure-arrow formulas with coefficient one show
that pullback and scalar application commute with Q. The bilinear formula
with both coefficients one proves the tensor case. Induction on a finite
well-typed expression using these laws and scalarComparisons_localized
identifies its rational evaluation with Q of its integral evaluation.
Apply Q to the supplied equality. No integral Hom injectivity is required.
Source: blueprint def-pur-section-invariant, final invertibility assertion,
DAG raw-Hom subargument (blueprint: lem-pur-rational-restriction-comparison-coherence). -/
theorem equationCalculus {Y X : Schemes P} (f : Y ⟶ X)
    (E L : Fields P) (h : E ≤ L) :
    (∀ (W : Schemes P) (K K' : integralCategory P E W) (a b : K ⟶ K'),
      a = b → (localization P E W).map a = (localization P E W).map b) ∧
    (∀ (W : Schemes P) (K : integralCategory P E W),
      (localization P E W).map (𝟙 K) = 𝟙 ((localization P E W).obj K)) ∧
    (∀ (W : Schemes P) (K K' K'' : integralCategory P E W)
      (a : K ⟶ K') (b : K' ⟶ K''),
      (localization P E W).map (a ≫ b) =
        (localization P E W).map a ≫ (localization P E W).map b) ∧
    (∀ (K K' : integralCategory P E X) (a : K ⟶ K'),
      HEq ((rationalPullback P E f).map ((localization P E X).map a))
        ((localization P E Y).map ((integralPullback P E f).map a))) ∧
    (∀ (W : Schemes P) (K K' : integralCategory P E W) (a : K ⟶ K'),
      HEq ((rationalScalar P E L h W).map ((localization P E W).map a))
        ((localization P L W).map ((integralScalar P E L h W).map a))) ∧
    (∀ (W : Schemes P) (M M' N N' : integralCategory P E W)
      (a : M ⟶ M') (b : N ⟶ N'),
      HEq ((rationalTensor P E W).map
        (Prod.mkHom ((localization P E W).map a) ((localization P E W).map b)))
        ((localization P E W).map ((integralTensor P E W).map (Prod.mkHom a b)))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W K K' a b hab
    exact congrArg (localization P E W).map hab
  · intro W K
    exact (localization P E W).map_id K
  · intro W K K' K'' a b
    exact (localization P E W).map_comp a b
  · intro K K' a
    exact (pureArrowActions P f E).2.1 K K' a 1
  · intro W K K' a
    unfold rationalScalar sfRationalScalarExtension integralScalar
    have hs := (sfRationalScalarExtension_existsUnique P.coefficients.l (FieldAt P E)
      W.left 0 (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime)) (FieldAt P L)
      (IntermediateField.inclusion h)).exists.choose_spec.2.2 K K' a 1
    simp only [map_one] at hs
    have hr : HEq
        ((1 : Localization.Away (Padic.coefficientExtensionUniformizer
          P.coefficients.l (FieldAt P L)))
          ⊗ₜ[Padic.coefficientExtensionIntegers P.coefficients.l (FieldAt P L)]
            (integralScalar P E L h W).map a)
        ((localization P L W).map ((integralScalar P E L h W).map a)) := by rfl
    exact hs.trans hr
  · intro W M M' N N' a b
    obtain ⟨B, hB, hm⟩ := (pureArrowActions P f E).2.2 W
      ((localization P E W).obj M) ((localization P E W).obj M')
      ((localization P E W).obj N) ((localization P E W).obj N')
    have ht := hm a b 1 1
    rw [← hB] at ht
    simp only [one_mul] at ht
    have hr : HEq
        ((1 : Localization.Away (Padic.coefficientExtensionUniformizer
          P.coefficients.l (FieldAt P E)))
          ⊗ₜ[Padic.coefficientExtensionIntegers P.coefficients.l (FieldAt P E)]
            (integralTensor P E W).map (Prod.mkHom a b))
        ((localization P E W).map ((integralTensor P E W).map (Prod.mkHom a b))) := by rfl
    exact ht.trans hr

end WeilConjectures.RationalRestrictionComparison
