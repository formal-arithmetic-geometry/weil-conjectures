/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q92
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Scalar extension of an augmented smooth algebra's tangent module

Source: Stacks Project, algebra.tex, Tags 00T2 (`definition-smooth`),
00RO (`lemma-universal-omega`) and 00RV (`lemma-differentials-base-change`)
(blueprint: lem-sfb-smooth-augmented-tangent-scalar-extension).

The tangent module is Mathlib's `Derivation`, with scalars acting through the
specified augmentation. The comparison is determined uniquely by its tensor formula.
The final statements express identity, tower and augmented-algebra naturality on
all tensor elements, using the usual tensor identifications.
-/

@[expose] public section

universe u v w z

open scoped TensorProduct

set_option autoImplicit false

namespace Algebra

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Derivations into the base ring, with the algebra acting through `ε`.
This is an abbreviation for Mathlib's `Derivation`, with its specified module action.

Source: Stacks Project, algebra.tex, Tag 00RO (`lemma-universal-omega`)
(blueprint: lem-sfb-smooth-augmented-tangent-scalar-extension). -/
abbrev augmentedTangent (ε : B →ₐ[A] A) :=
  @Derivation A B A _ _ _ _ (Module.compHom A ε.toRingHom) _

/-- The usual base-ring module structure on derivations through the augmentation.
The instance is Mathlib's derivation module instance, specialized to `ε`.

Source: Stacks Project, algebra.tex, Tag 00RO (`lemma-universal-omega`)
(blueprint: lem-sfb-smooth-augmented-tangent-scalar-extension). -/
instance augmentedTangentModule (ε : B →ₐ[A] A) : Module A (augmentedTangent ε) :=
  letI : Algebra B A := ε.toRingHom.toAlgebra
  inferInstanceAs (Module A (Derivation A B A))

variable {C : Type w} [CommRing C] [Algebra A C]

/-- The tensor augmentation, sending `c ⊗ b` to `c * algebraMap A C (ε b)`.
It is the algebra tensor universal property's actual lift of the two structure maps.

Source: Stacks Project, algebra.tex, Tags 00RO and 00RV; the tensor universal property
(blueprint: lem-sfb-smooth-augmented-tangent-scalar-extension). -/
def augmentedBaseChange (ε : B →ₐ[A] A) : C ⊗[A] B →ₐ[C] C :=
  Algebra.TensorProduct.lift (AlgHom.id C C)
    ((IsScalarTower.toAlgHom A A C).comp ε) (fun _ _ ↦ Commute.all _ _)

/-- The augmented tangent module is a retract of a finite free module, and its
scalar comparison is the unique linear equivalence with the specified tensor formula.

Source: Stacks Project, algebra.tex, Tags 00T2, 00RO and 00RV, assembled by finite
projective duality (blueprint: lem-sfb-smooth-augmented-tangent-scalar-extension).

Proof plan, following the node's six steps:
1. Smoothness makes Ω[B/A] finite projective. Tensor its split inclusion and retraction
   with A through ε, obtaining a retract P of A^n. The tensor algebra universal property
   gives the augmentation after scalar extension.
2. Universal differentials identify Der_A(B,A) with Hom_B(Ω[B/A],A), and tensor-Hom
   adjunction identifies this with the ordinary A-dual of P.
3. Differential base change, `lem-weil-pbc-kahler-differentials-base-change`, and tensor
   cancellation identify C ⊗ P with the corresponding pulled-back cotangent module.
4. Apply `lem-sf-finite-projective-dual`. For a finite free module the scalar comparison
   on duals is an isomorphism by dual bases. For a retract, naturality transports its
   inverse through the split maps. Compose with steps 2 and 3. Evaluation gives the
   displayed formula. Tensor generators determine the equivalence uniquely.
5. Evaluate the successive comparisons on pure tensors to obtain the tower equation;
   multiplication gives the identity comparison.
6. Precompose with an augmentation-preserving algebra map. Both routes evaluate to
   c*c'*f(d(q(b))); tensor generation proves naturality. No flatness or nonzero-ring
   assumption occurs in these arguments. -/
theorem smooth_augmentedTangent_scalarExtension [Smooth A B] (ε : B →ₐ[A] A) :
    (∃ n : ℕ, ∃ i : augmentedTangent ε →ₗ[A] (Fin n → A),
      ∃ p : (Fin n → A) →ₗ[A] augmentedTangent ε, p.comp i = LinearMap.id) ∧
    ∃! θ : (C ⊗[A] augmentedTangent ε) ≃ₗ[C]
        augmentedTangent (augmentedBaseChange (C := C) ε),
      ∀ (c c' : C) (d : augmentedTangent ε) (b : B),
        θ (c ⊗ₜ[A] d) (c' ⊗ₜ[A] b) = c * c' * algebraMap A C (d b) := by
  sorry

/-- The canonical tangent comparison, chosen from its uniquely determining formula.
Only the proof of existence is postponed: the preceding theorem determines the
linear equivalence uniquely, so this definition does not choose unspecified data.

Source: Stacks Project, algebra.tex, Tags 00RO and 00RV; finite projective duality
(blueprint: lem-sfb-smooth-augmented-tangent-scalar-extension). -/
noncomputable def augmentedTangentBaseChangeEquiv [Smooth A B] (ε : B →ₐ[A] A) :
    (C ⊗[A] augmentedTangent ε) ≃ₗ[C]
      augmentedTangent (augmentedBaseChange (C := C) ε) :=
  Classical.choose (smooth_augmentedTangent_scalarExtension (C := C) ε).2

/-- The identity comparison is the identity under the tensor multiplication maps.

Source: Stacks Project, algebra.tex, tensor universal property, node proof step 5
(blueprint: lem-sfb-smooth-augmented-tangent-scalar-extension).

Proof: For t = a ⊗ d and x = a' ⊗ b both sides are a*a'*d(b).
Additivity and generation by pure tensors extend the equality to all t and x. -/
theorem augmentedTangentBaseChangeEquiv_id [Smooth A B] (ε : B →ₐ[A] A)
    (t : A ⊗[A] augmentedTangent ε) (x : A ⊗[A] B) :
    augmentedTangentBaseChangeEquiv ε t x =
      (_root_.TensorProduct.lid A (augmentedTangent ε) t) (Algebra.TensorProduct.lid A B x) := by
  sorry

variable {D : Type z} [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower A C D]

/-- Successive coefficient changes agree with direct change after tensor cancellation.
Both arguments are arbitrary tensor elements, so this states equality of the whole
comparison maps after transporting the augmented algebra by the usual associator.

Source: Stacks Project, algebra.tex, tensor universal property, node proof step 5
(blueprint: lem-sfb-smooth-augmented-tangent-scalar-extension).

Proof: On t = d₀ ⊗ (c ⊗ v), x = d₁ ⊗ (c' ⊗ b), both sides evaluate to
 d₀*d₁*h(c)*h(c')*(h ∘ f)(v(b)). Tensor balancing identifies the two augmentations;
additivity and tensor generation extend this calculation to arbitrary arguments. -/
theorem augmentedTangentBaseChangeEquiv_comp [Smooth A B] (ε : B →ₐ[A] A)
    (t : D ⊗[C] (C ⊗[A] augmentedTangent ε)) (x : D ⊗[C] (C ⊗[A] B)) :
    augmentedTangentBaseChangeEquiv (augmentedBaseChange (C := C) ε)
        ((augmentedTangentBaseChangeEquiv (C := C) ε).toLinearMap.baseChange D t) x =
      augmentedTangentBaseChangeEquiv (C := D) ε
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A C D D
          (augmentedTangent ε) t)
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A C D D B x) := by
  sorry

variable {B' : Type z} [CommRing B'] [Algebra A B']

/-- Precomposition with an augmentation-preserving algebra map commutes with
scalar comparison. The map p is specified on every derivation and every algebra
element, and the naturality equality holds for all tensor elements.

Source: Stacks Project, algebra.tex, Tag 00RO and tensor universal property, node step 6
(blueprint: lem-sfb-smooth-augmented-tangent-scalar-extension).

Proof: Set p(d) = d ∘ q. The equality ε' ∘ q = ε verifies its Leibniz rule;
composition is A-linear in d. The algebra tensor map sends c' ⊗ b to c' ⊗ q(b).
On t = c ⊗ d and x = c' ⊗ b, both routes therefore give c*c'*f(d(q(b))).
Tensor generation and additivity prove the equality for all t and x. -/
theorem augmentedTangentBaseChangeEquiv_natural [Smooth A B] [Smooth A B']
    (ε : B →ₐ[A] A) (ε' : B' →ₐ[A] A) (q : B →ₐ[A] B') (hq : ε'.comp q = ε) :
    ∃ p : augmentedTangent ε' →ₗ[A] augmentedTangent ε,
      (∀ (d : augmentedTangent ε') (b : B), p d b = d (q b)) ∧
      ∀ (t : C ⊗[A] augmentedTangent ε') (x : C ⊗[A] B),
        augmentedTangentBaseChangeEquiv (C := C) ε (p.baseChange C t) x =
          augmentedTangentBaseChangeEquiv (C := C) ε' t
            (Algebra.TensorProduct.map (AlgHom.id C C) q x) := by
  sorry

end Algebra
