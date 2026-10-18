/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplex
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass

/-! # Tate and contragredient data for strict Weil complexes

Source: main-20261015 blueprint, sec-smooth-purity/sk-def-sf-weil-complexes,
complement (normalization, scope and duals) (blueprint: sk-def-sf-weil-complexes).

The pair category is the existing `AlgebraicGeometry.Etale.WeilComplex`.
The internal-Hom comparison below is the transpose of pullback of evaluation,
so the contragredient datum uses the canonical comparison, with no chosen map.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {T : Scheme.{u}} (g : T ≅ T)

/-- Canonical pullback comparison for internal Hom: transpose pullback of evaluation.
Source: the contragredient composite, first arrow
(blueprint: sk-def-sf-weil-complexes). -/
def strictWeilHomComparison (K M : DerivedCategoryModule Λ T) :
    (L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj
        ((RHom(T)[ModuleCat.{u + 1} Λ].obj (op K)).obj M) ⟶
      (RHom(T)[ModuleCat.{u + 1} Λ].obj
        (op ((L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj K))).obj
          ((L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj M) :=
  ((derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ)
    ((L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj K)).homEquiv _ _)
      ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g.hom K
        ((RHom(T)[ModuleCat.{u + 1} Λ].obj (op K)).obj M)).inv ≫
          (L((g.hom)^*[ModuleCat.{u + 1} Λ])).map
            ((derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) K).counit.app M))

/-- Pullback by the automorphism preserves internal Hom, including for nonperfect K.
Source: the first isomorphism in the contragredient composite
(blueprint: sk-def-sf-weil-complexes).
Proof: pullback by g and its inverse are inverse exact monoidal equivalences.
The comparison is the tensor-Hom adjoint mate of its tensorator. Mates along
an equivalence preserve isomorphisms, so its components are isomorphisms. -/
theorem strictWeilHomComparison_isIso (K M : DerivedCategoryModule Λ T) :
    IsIso (strictWeilHomComparison Λ g K M) := by
  sorry

/-- The canonical first isomorphism in the displayed contragredient composite.
Source: complement, duals (blueprint: sk-def-sf-weil-complexes). -/
def strictWeilHomIso (K M : DerivedCategoryModule Λ T) :
    (L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj
        ((RHom(T)[ModuleCat.{u + 1} Λ].obj (op K)).obj M) ≅
      (RHom(T)[ModuleCat.{u + 1} Λ].obj
        (op ((L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj K))).obj
          ((L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj M) :=
  @asIso _ _ _ _ _ (strictWeilHomComparison_isIso Λ g K M)

/-- The contragredient map is the three-arrow composite in the source: pull back
internal Hom, apply the coefficient datum in the second variable, and precompose
with the inverse Weil datum in the first variable.
Source: complement, displayed contragredient formula
(blueprint: sk-def-sf-weil-complexes). -/
def strictWeilContragredientMap {K : DerivedCategoryModule Λ T}
    (φ : (L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj K ≅ K) :
    (L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) T).obj (op K)) ⟶
      (DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) T).obj (op K) :=
  (strictWeilHomIso Λ g K (𝟙_ _)).hom ≫
    (RHom(T)[ModuleCat.{u + 1} Λ].obj
      (op ((L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj K))).map
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g.hom).hom ≫
    ((RHom(T)[ModuleCat.{u + 1} Λ]).map φ.inv.op).app (𝟙_ _)

/-- The composite defining the contragredient datum is invertible.
Source: complement, contragredient datum (blueprint: sk-def-sf-weil-complexes).
Proof: the first arrow is the canonical pullback isomorphism just constructed.
The second and third arrows are functorial images of the coefficient isomorphism
and of the inverse of φ, respectively. Compose these three isomorphisms. -/
theorem strictWeilContragredientMap_isIso {K : DerivedCategoryModule Λ T}
    (φ : (L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj K ≅ K) :
    IsIso (strictWeilContragredientMap Λ g φ) := by
  sorry

/-- The contragredient Weil isomorphism, without an added perfectness assumption.
Source: complement, duals (blueprint: sk-def-sf-weil-complexes). -/
def strictWeilContragredientIso {K : DerivedCategoryModule Λ T}
    (φ : (L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj K ≅ K) :
    (L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) T).obj (op K)) ≅
      (DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) T).obj (op K) :=
  @asIso _ _ _ _ _ (strictWeilContragredientMap_isIso Λ g φ)

/-- Apply the displayed contragredient composite to the existing category of pairs.
The forgetful inclusion supplies exactly the underlying Frobenius isomorphism.
Source: complement, duals (blueprint: sk-def-sf-weil-complexes). -/
def WeilComplex.contragredientDatum (K : WeilComplex (ModuleCat.{u + 1} Λ) g) :
    (L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) T).obj
          (op ((DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) T).obj K.obj))) ≅
      (DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) T).obj
        (op ((DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) T).obj K.obj)) :=
  strictWeilContragredientIso Λ g
    ((DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) T).mapIso K.frobenius)

variable [HasTateTwist Λ] [HasInvertibleExponent Λ T]

/-- The canonical Tate Weil datum τ_r, using the existing Tate pullback comparison.
Source: complement, Tate normalization (blueprint: sk-def-sf-weil-complexes). -/
def strictWeilTateIso (r : ℤ) :
    (L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ T r) ≅ tateObject Λ T r :=
  leftDerivedUpperStarTateObjectIso g.hom r

/-- The Tate line as an object of the existing strict Weil pair category.
Source: complement, canonical Tate Weil structure
(blueprint: sk-def-sf-weil-complexes). -/
def WeilComplex.tateLine (r : ℤ) : WeilComplex (ModuleCat.{u + 1} Λ) g where
  obj := ⟨tateObject Λ T r, boundedConstructibleFiniteTor_tateObject Λ T r⟩
  frobenius := ObjectProperty.isoMk _ (strictWeilTateIso Λ g r)

/-- The zero Tate datum is the canonical coefficient datum, transported through
Λ(0) ≅ Λ. Source: complement, τ₀ = φ_Λ
(blueprint: sk-def-sf-weil-complexes).
Proof: the zero-twist unit law identifies multiplication by Λ(0) with the
unitor. Compatibility of the Tate pullback with this multiplication and the
unit coherence of monoidal pullback identify its zero-twist comparison with
the coefficient comparison. Cancel the invertible twisting line. -/
theorem strictWeilTateIso_zero :
    (L((g.hom)^*[ModuleCat.{u + 1} Λ])).map
        (HasTateTwist.twistObjectZeroIso (Λ := Λ) T).hom ≫
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g.hom).hom =
      (strictWeilTateIso Λ g 0).hom ≫
        (HasTateTwist.twistObjectZeroIso (Λ := Λ) T).hom := by
  sorry

/-- The twisted contragredient is an isomorphism, obtained by tensoring the two
isomorphisms after the canonical pullback-tensor comparison.
Source: complement, last sentence (blueprint: sk-def-sf-weil-complexes). -/
def strictWeilTwistedContragredientIso {K : DerivedCategoryModule Λ T}
    (φ : (L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj K ≅ K) (r : ℤ) :
    (L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) T).obj
          ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) T).obj (op K))).obj
            (tateObject Λ T r)) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) T).obj
        ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) T).obj (op K))).obj
          (tateObject Λ T r) :=
  leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g.hom _ _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) T).mapIso
      (strictWeilContragredientIso Λ g φ)).app _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) T).obj _).mapIso (strictWeilTateIso Λ g r)

/-- The datum on the twisted dual is φ_{K^∨} tensor τ_r, with the canonical
pullback-tensor comparison inserted to give the specified source.
Source: complement, last sentence (blueprint: sk-def-sf-weil-complexes). -/
def strictWeilTwistedContragredientMap {K : DerivedCategoryModule Λ T}
    (φ : (L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj K ≅ K) (r : ℤ) :
    (L((g.hom)^*[ModuleCat.{u + 1} Λ])).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) T).obj
          ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) T).obj (op K))).obj
            (tateObject Λ T r)) ⟶
      ((derivedTensor (ModuleCat.{u + 1} Λ) T).obj
        ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) T).obj (op K))).obj
          (tateObject Λ T r) :=
  tensorWeilDatum g.hom (strictWeilContragredientIso Λ g φ).hom
    (strictWeilTateIso Λ g r).hom

/-- The scalar q^{-r}, including negative twists over rings without a division operation.
Source: complement, normalization (blueprint: sk-def-sf-weil-complexes). -/
def strictWeilTateScalar (q : ℕ) : ℤ → Λ
  | Int.ofNat n => Ring.inverse (q : Λ) ^ n
  | Int.negSucc n => (q : Λ) ^ (n + 1)

section CyclotomicNormalization

variable (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] Λ]
  (k₀ : Type u) [Field k₀] [Finite k₀]

/-- The canonical scalar on the r-th Tate line at any coefficient stage: extend
its geometric cyclotomic character from ℤ_l, and take the integer power.
This includes finite, integral, rational and algebraically closed coefficients.
Source: complement, Tate normalization (blueprint: sk-def-sf-weil-complexes). -/
def strictWeilTateCyclotomicScalar (r : ℤ) : Λ :=
  letI := Fintype.ofFinite k₀
  ((Units.map (algebraMap ℤ_[l] Λ).toMonoidHom
    (cyclotomicCharacter (AlgebraicClosure k₀) l
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀
        (AlgebraicClosure k₀)).toRingEquiv)) ^ r : Λˣ)

/-- The cyclotomic normalization is q^{-r} after every coefficient realization.
No finiteness or field assumption is imposed on Λ.
Source: complement, Tate normalization (blueprint: sk-def-sf-weil-complexes).
Proof: arithmetic Frobenius raises each l-power root of unity to its q-th
power. Its cyclotomic character is therefore q in ℤ_l. The geometric character
is its inverse. Apply the coefficient algebra map, then integer powers; a
nonnegative power gives inverse(q)^r and a negative power gives q^{-r}.
The prime inequality ensures q is a unit in ℤ_l and in Λ. -/
theorem strictWeilTateCyclotomicScalar_normalization
    (hl : l ≠ ringChar k₀) (r : ℤ) :
    strictWeilTateCyclotomicScalar Λ l k₀ r =
      strictWeilTateScalar Λ (Nat.card k₀) r := by
  sorry

end CyclotomicNormalization

variable [Finite Λ] [HasTateTwist.IsNormalized Λ]
  (k₀ : Type u) [Field k₀] [Finite k₀]
  [HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k₀)))]

/-- Geometric Frobenius acts on the normalized Tate line by q^{-r}, and hence
by q^{r} on the negative twist. The line is read as H⁰ over the geometric point;
this asserts equality of operators, independently of a chosen generator.
Source: complement, normalization (blueprint: sk-def-sf-weil-complexes).
Proof: for r=1, arithmetic Frobenius raises every prime-to-characteristic root
of unity to the q-th power. Geometric Frobenius is its inverse, so it acts by
q^{-1}. Tensor powers multiply these scalars, and duals invert them. At r=0
use the coefficient comparison, which fixes scalars. -/
theorem strictWeilTateIso_normalization (r : ℤ)
    (x : 𝟙_ (DerivedCategoryModule Λ (Spec (.of (AlgebraicClosure k₀)))) ⟶
      tateObject Λ (Spec (.of (AlgebraicClosure k₀))) r) :
    frobeniusOperator (specGeometricFrobenius k₀).hom
        (strictWeilTateIso Λ (specGeometricFrobenius k₀) r).hom x =
      strictWeilTateScalar Λ (Nat.card k₀) r • x := by
  sorry

end AlgebraicGeometry.Etale
