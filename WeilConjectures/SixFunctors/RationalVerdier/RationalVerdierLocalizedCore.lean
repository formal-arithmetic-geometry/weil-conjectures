/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierModels
public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations

/-! # The rational dual functor from the existing rational internal Hom

Source: blueprint thm-coef-rational-verdier, paragraphs 1--2
(blueprint: lem-coef-rational-verdier-localized-core). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Fix the second internal-Hom argument to the supplied integral dualizing object.
Source: blueprint thm-coef-rational-verdier, paragraphs 1--2
(blueprint: lem-coef-rational-verdier-localized-core). -/
def dualInput (w : sfIntegralConstructibleCategory l E X)
    (hp : ∀ K : sfIntegralConstructibleCategory l E X,
      sfIntegralConstructible l E X ((IntegralVerdier.dual l E X w.obj).obj (op K.obj))) :
    (sfRationalConstructibleCategory l E X)ᵒᵖ ⥤
      (constructibleRationalHomPairs l E X).FullSubcategory where
  obj K := ⟨(K, (sfRationalConstructibleLocalization l E X).obj w), hp K.unop.obj⟩
  map f := ObjectProperty.homMk (Prod.mkHom f (𝟙 _))

/-- The actual rational internal Hom into the localized integral object.
Source: blueprint thm-coef-rational-verdier, paragraphs 1--2
(blueprint: lem-coef-rational-verdier-localized-core). -/
@[irreducible] def localizedDual (w : sfIntegralConstructibleCategory l E X)
    (hp : ∀ K : sfIntegralConstructibleCategory l E X,
      sfIntegralConstructible l E X ((IntegralVerdier.dual l E X w.obj).obj (op K.obj))) :
    (sfRationalConstructibleCategory l E X)ᵒᵖ ⥤ sfRationalConstructibleCategory l E X :=
  dualInput l E X w hp ⋙ rationalDerivedInternalHom l E X

attribute [local irreducible] rationalDerivedInternalHom
  sfIntegralConstructibleLinear ScalarLocalization.linear ScalarLocalization.preadditive
  Preadditive.fullSubcategory Linear.fullSubcategory

private theorem chosen_spec {A : Sort*} {P : A → Prop}
    (h : ∃ a, P a) (a : A) (ha : a = h.choose) : P a :=
  ha.symm ▸ h.choose_spec

private theorem fixed_linear {S : Type*} [CommRing S]
    {C : Type*} [Category* C] [Preadditive C] [Linear S C]
    {D : Type*} [Category* D] [Preadditive D] [Linear S D]
    (F : Cᵒᵖ ⥤ D)
    (b : ∀ K M : C, (K ⟶ M) →ₗ[S] (F.obj (op M) ⟶ F.obj (op K)))
    (hb : ∀ (K M : C) (f : K ⟶ M), F.map f.op = b K M f) :
    F.Additive ∧ ∀ (K M : C) (f : K ⟶ M) (c : S),
      F.map (c • f).op = c • F.map f.op := by
  constructor
  · constructor
    intro K M f g
    change F.map (f.unop + g.unop).op = F.map f.unop.op + F.map g.unop.op
    rw [hb, hb, hb, map_add]
  · intro K M f c
    rw [hb, hb, map_smul]

/-- The rational dual has the prescribed integral objects and pure-tensor maps,
and is additive and linear over the localized coefficient field.
Source: blueprint thm-coef-rational-verdier, paragraphs 1--2
(blueprint: lem-coef-rational-verdier-localized-core).
Proof: restrict the existing permitted-pair rational internal Hom to the fixed
second object. Its object and bilinear arrow specifications specialize to the
asserted formulas by putting the identity in the second variable. The first
linear map is additive and homogeneous for all localized scalars, hence for
the field coordinates as well. -/
theorem localizedDual_spec (w : sfIntegralConstructibleCategory l E X)
    (hp : ∀ K : sfIntegralConstructibleCategory l E X,
      sfIntegralConstructible l E X ((IntegralVerdier.dual l E X w.obj).obj (op K.obj))) :
    (∀ K : sfRationalConstructibleCategory l E X,
      (localizedDual l E X w hp).obj (op K) =
        (sfRationalConstructibleLocalization l E X).obj
          ((IntegralVerdier.restrictedDual l E X w.obj hp).obj (op K.obj))) ∧
    (localizedDual l E X w hp).Additive ∧
    (∀ (K M : sfRationalConstructibleCategory l E X) (f : K ⟶ M)
      (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
      (localizedDual l E X w hp).map (c • f).op =
        c • (localizedDual l E X w hp).map f.op) ∧
    (∀ (K M : sfIntegralConstructibleCategory l E X) (f : K ⟶ M)
      (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
      HEq ((localizedDual l E X w hp).map (Quiver.Hom.op
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
          (sfRationalConstructibleLocalization l E X).obj K ⟶
            (sfRationalConstructibleLocalization l E X).obj M)))
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          (IntegralVerdier.restrictedDual l E X w.obj hp).map f.op)) := by
  unfold localizedDual
  have hs := chosen_spec (rationalDerivedInternalHom_existsUnique l E X).exists
    (rationalDerivedInternalHom l E X) (by unfold rationalDerivedInternalHom; rfl)
  have hm (K M : sfRationalConstructibleCategory l E X) :=
    hs.2 ((dualInput l E X w hp).obj (op M)) ((dualInput l E X w hp).obj (op K))
  let F := dualInput l E X w hp ⋙ rationalDerivedInternalHom l E X
  let b (K M : sfRationalConstructibleCategory l E X) :=
    (hm K M).choose.flip (𝟙 ((sfRationalConstructibleLocalization l E X).obj w))
  have hmap (K M : sfRationalConstructibleCategory l E X) (f : K ⟶ M) :
      F.map f.op = b K M f := (hm K M).choose_spec.1 f (𝟙 _)
  have hlin := fixed_linear F b hmap
  refine ⟨?_, hlin.1, hlin.2, ?_⟩
  · intro K
    exact hs.1 ((dualInput l E X w hp).obj (op K))
  · intro K M f c
    have h := (hm ((sfRationalConstructibleLocalization l E X).obj K)
      ((sfRationalConstructibleLocalization l E X).obj M)).choose_spec.2 f (𝟙 w) c 1
    rw [hmap]
    have hi : (constructibleIntegralHom l E X).map
        (X := integralPairOfRationalHomPair l E X
          ((dualInput l E X w hp).obj (op ((sfRationalConstructibleLocalization l E X).obj M))))
        (Y := integralPairOfRationalHomPair l E X
          ((dualInput l E X w hp).obj (op ((sfRationalConstructibleLocalization l E X).obj K))))
        (ObjectProperty.homMk (Prod.mkHom f.op (𝟙 w))) =
          (IntegralVerdier.restrictedDual l E X w.obj hp).map f.op := by
      apply ObjectProperty.hom_ext
      rfl
    simp only [mul_one] at h
    have hh := congrArg (fun k ↦ c ⊗ₜ[Padic.coefficientExtensionIntegers l E] k) hi
    exact h.trans (heq_of_eq hh)

end WeilConjectures.RationalVerdier
