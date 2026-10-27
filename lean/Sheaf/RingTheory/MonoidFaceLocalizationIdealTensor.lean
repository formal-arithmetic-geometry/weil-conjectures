/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.TraceFormula.LogChartFaceTorComparison
public import Sheaf.RingTheory.AffineToricEquivariantIdeals
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Face localization of monomial ideal tensors

Source: ILO, Exposé VIII 3.1.2, p. 98, and proof of Lemma 3.4.3, p. 110
(blueprint: lem-trf-monoid-face-localization-ideal-tensor).

Monoids are written multiplicatively, as in the existing face localization: `p * f⁻¹`
means `p - f`. The ideal and integer monoid algebra are the existing constructions.
The coefficient action on an ideal tensor is transported along the canonical tensor swap,
so the tensor order remains `Z[H] ⊗ A`. The monoid and coefficient universes are independent.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open Algebra AlgebraicGeometry
open scoped TensorProduct

namespace MonoidAlgebra.FaceIdealTensor

/-- The fraction `p-f` in the existing localization inside the group completion.
Source: ILO VIII 3.1.2 (blueprint: lem-trf-monoid-face-localization-ideal-tensor). -/
def fraction {P : Type u} [CommMonoid P] (F : Submonoid P) (p : P) (f : F) :
    faceLocalization P F :=
  ⟨GrothendieckGroup.of p * (GrothendieckGroup.of f.1)⁻¹, p, f, rfl⟩

/-- The localized exponent ideal, with the empty subset permitted.
Source: ILO VIII 3.1.2 and proof of 3.4.3
(blueprint: lem-trf-monoid-face-localization-ideal-tensor). -/
def localizedIdeal {P : Type u} [CommMonoid P] (F : Submonoid P) (H : Set P) :
    Set (faceLocalization P F) :=
  {x | ∃ h ∈ H, ∃ f : F, x = fraction F h f}

/-- The module tensor with exactly the chart-induced scalar action, in the stated order.
The algebra is restriction along `z^p ↦ α(p)`, the same action as the recorded coefficient
module, here allowing independent universes for `P` and `A`.
Source: ILO VIII, proof of 3.4.3; Stacks 00CX
(blueprint: lem-trf-monoid-face-localization-ideal-tensor). -/
noncomputable abbrev tensor {P : Type u} {A : Type v} [CommMonoid P] [CommRing A]
    (α : P →* A) (H : Set P) : Type (max u v) := by
  letI : Algebra (MonoidAlgebra ℤ P) A := (MonoidAlgebra.lift ℤ A P α).toRingHom.toAlgebra
  exact LogChartFaceTor.ideal H ⊗[MonoidAlgebra ℤ P] A

/-- The coefficient-ring module structure acts on the right factor of the stated tensor.
It is transported from `A ⊗ Z[H]` by Mathlib's canonical tensor swap.
Source: ILO VIII, proof of 3.4.3; Stacks 00CX
(blueprint: lem-trf-monoid-face-localization-ideal-tensor). -/
noncomputable instance tensorModule {P : Type u} {A : Type v}
    [CommMonoid P] [CommRing A] (α : P →* A) (H : Set P) : Module A (tensor α H) := by
  letI : Algebra (MonoidAlgebra ℤ P) A := (MonoidAlgebra.lift ℤ A P α).toRingHom.toAlgebra
  exact (TensorProduct.comm (MonoidAlgebra ℤ P) (LogChartFaceTor.ideal H) A).toAddEquiv.module A

/-- The pure tensor `z ⊗ a`, with the chart-induced action made explicit.
Source: ILO VIII, proof of 3.4.3; Stacks 00CX
(blueprint: lem-trf-monoid-face-localization-ideal-tensor). -/
noncomputable def pure {P : Type u} {A : Type v} [CommMonoid P] [CommRing A]
    (α : P →* A) (H : Set P) (z : LogChartFaceTor.ideal H) (a : A) : tensor α H := by
  letI : Algebra (MonoidAlgebra ℤ P) A := (MonoidAlgebra.lift ℤ A P α).toRingHom.toAlgebra
  exact z ⊗ₜ[MonoidAlgebra ℤ P] a

/-- The canonical multiplication map evaluates the ideal element at the chart and
multiplies by its coefficient. The construction uses tensor swap and base-change lift.
Source: ILO VIII, proof of 3.4.3; Stacks 00CX
(blueprint: lem-trf-monoid-face-localization-ideal-tensor). -/
noncomputable def multiplication {P : Type u} {A : Type v} [CommMonoid P] [CommRing A]
    (α : P →* A) (H : Set P) : tensor α H →ₗ[A] A := by
  letI : Algebra (MonoidAlgebra ℤ P) A := (MonoidAlgebra.lift ℤ A P α).toRingHom.toAlgebra
  exact (LinearMap.liftBaseChange A
    ((Algebra.linearMap (MonoidAlgebra ℤ P) A).comp (LogChartFaceTor.ideal H).subtype)).comp
    ((TensorProduct.comm (MonoidAlgebra ℤ P) (LogChartFaceTor.ideal H) A).toAddEquiv.linearEquiv
      A).toLinearMap

/-- The generator formulas and multiplication square specifying the comparison.
Quantifying over ideal elements whose values are the given monomials avoids choosing
membership proofs; every such monomial exists by the ideal span construction.
The inverse formula is required for every fraction representative.
Source: ILO VIII 3.1.2 and proof of 3.4.3
(blueprint: lem-trf-monoid-face-localization-ideal-tensor). -/
def IsComparison {P : Type u} {A : Type v} [CommMonoid P] [CommRing A]
    (F : Submonoid P) (α : P →* A) (hα : ∀ f : F, IsUnit (α f.1))
    (αF : faceLocalization P F →* A) (H : Set P)
    (e : tensor α H ≃ₗ[A] tensor αF (localizedIdeal F H)) : Prop :=
  (∀ (h : P), h ∈ H → ∀ (z : LogChartFaceTor.ideal H)
    (zF : LogChartFaceTor.ideal (localizedIdeal F H)) (a : A),
    (z : MonoidAlgebra ℤ P) = MonoidAlgebra.single h 1 →
    (zF : MonoidAlgebra ℤ (faceLocalization P F)) =
      MonoidAlgebra.single (MonoidAlgebra.toricLocalizationInclusion F h) 1 →
    e (pure α H z a) = pure αF (localizedIdeal F H) zF a) ∧
  (∀ (h : P), h ∈ H → ∀ (f : F) (z : LogChartFaceTor.ideal H)
    (zF : LogChartFaceTor.ideal (localizedIdeal F H)) (a : A),
    (z : MonoidAlgebra ℤ P) = MonoidAlgebra.single h 1 →
    (zF : MonoidAlgebra ℤ (faceLocalization P F)) = MonoidAlgebra.single (fraction F h f) 1 →
    e.symm (pure αF (localizedIdeal F H) zF a) =
      pure α H z ((↑((hα f).unit⁻¹) : A) * a)) ∧
  (∀ x : tensor α H, multiplication αF (localizedIdeal F H) (e x) = multiplication α H x)

/-- Face localization preserves monomial ideal tensors when the face acts by units,
with the displayed fraction inverse, multiplication square, and both coefficient squares.

Source: ILO, Exposé VIII 3.1.2, printed p. 98, and proof of Lemma 3.4.3, printed p. 110
(blueprint: lem-trf-monoid-face-localization-ideal-tensor).

Proof:
1. Integrality identifies P with its image in its group completion. If p/f=p'/f',
   cross multiplication gives pf'=p'f in P. Apply α and invert the unit denominators
   to construct the well-defined monoid homomorphism αF with the stated formula.
   Multiplying h/f by p/g gives hp/(fg), so the localized exponent set is an ideal.
2. Every extended monomial has exponent hp/f in H_F, and each z^(h/f)=z^h z^(-f)
   is in the extension. Finite integer linear combinations give equality of ideals.
3. The inclusion of ideals gives the balanced pairing (i,a) ↦ i ⊗ a in the localized
   tensor. The universal property of def-weil-pbc-module-tensor-product gives λ.
   It is A-linear since the A-action is on the coefficient factor.
4. For h/f=h'/f', use hf'=h'f and the common coefficient
   α(f)^(-1)α(f')^(-1)a. Tensor balancing identifies the two proposed inverse values.
   Extend by finite integer linear combinations using the monomial basis of the ideal.
5. For a monomial z^(p/g), balancing follows from
   z^(hp) ⊗ α(fg)^(-1)a = z^h ⊗ α(p)α(f)^(-1)α(g)^(-1)a.
   Expanding finite sums gives balancing over the localized monoid ring; the tensor
   universal property supplies the A-linear inverse map.
6. With denominator 1 the inverse after λ fixes each generator. In the other order,
   move z^f across the tensor sign and cancel α(f)α(f)^(-1). Monomial pure tensors
   generate both tensors, proving that the maps are inverse.
7. The multiplication maps evaluate to α(h)a and αF(h/f)a. The generator formulas
   show that λ, its inverse, and multiplication commute; extend by additivity.
8. A coefficient homomorphism φ induces additive maps i ⊗ a ↦ i ⊗ φ(a) by balancing.
   They commute with λ on generators and with its inverse because φ preserves unit
   inverses. Additivity proves both naturality squares. All arguments include H empty.
-/
theorem face_localization_ideal_tensor
    {P : Type u} [CommMonoid P]
    (hP : Function.Injective (GrothendieckGroup.of : P →* GrothendieckGroup P))
    (F : Submonoid P) (hF : ∀ p q : P, p * q ∈ F → p ∈ F ∧ q ∈ F)
    {A : Type v} [CommRing A] (α : P →* A) (hα : ∀ f : F, IsUnit (α f.1)) :
    ∃ αF : faceLocalization P F →* A,
      αF.comp (MonoidAlgebra.toricLocalizationInclusion F) = α ∧
      (∀ (p : P) (f : F), αF (fraction F p f) = α p * (↑((hα f).unit⁻¹) : A)) ∧
      ∀ (H : Set P), (∀ h ∈ H, ∀ p : P, h * p ∈ H) →
        (∀ x ∈ localizedIdeal F H, ∀ p : faceLocalization P F,
          x * p ∈ localizedIdeal F H) ∧
        (LogChartFaceTor.ideal H).map
          (MonoidAlgebra.mapDomainRingHom ℤ (MonoidAlgebra.toricLocalizationInclusion F)) =
          LogChartFaceTor.ideal (localizedIdeal F H) ∧
        ∃ e : tensor α H ≃ₗ[A] tensor αF (localizedIdeal F H),
          IsComparison F α hα αF H e ∧
          ∀ (A' : Type w) [CommRing A'] (φ : A →+* A'),
            ∃ (e' : tensor (φ.toMonoidHom.comp α) H ≃ₗ[A']
                tensor (φ.toMonoidHom.comp αF) (localizedIdeal F H))
              (c : tensor α H →+ tensor (φ.toMonoidHom.comp α) H)
              (cF : tensor αF (localizedIdeal F H) →+
                tensor (φ.toMonoidHom.comp αF) (localizedIdeal F H)),
              IsComparison F (φ.toMonoidHom.comp α) (fun f ↦ (hα f).map φ)
                (φ.toMonoidHom.comp αF) H e' ∧
              (∀ (z : LogChartFaceTor.ideal H) (a : A),
                c (pure α H z a) = pure (φ.toMonoidHom.comp α) H z (φ a)) ∧
              (∀ (z : LogChartFaceTor.ideal (localizedIdeal F H)) (a : A),
                cF (pure αF (localizedIdeal F H) z a) =
                  pure (φ.toMonoidHom.comp αF) (localizedIdeal F H) z (φ a)) ∧
              (∀ x : tensor α H, cF (e x) = e' (c x)) ∧
              (∀ y : tensor αF (localizedIdeal F H), c (e.symm y) = e'.symm (cF y)) := by
  sorry

end MonoidAlgebra.FaceIdealTensor
