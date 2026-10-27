module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.RingTheory.IntegralClosureFiniteNormalProduct
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Sheaf.RingTheory.FaithfullyFlatNormalRingDescent
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal

/-!
# A finite normalization model over a finite algebraic stage

Source: Stacks Project, Algebra, Tags 05N9 and 033G; More on Algebra, Tag 09II,
final normalization-colimit argument, with the explicit finite-module hypothesis
(blueprint: lem-sfb-finite-normalization-algebraic-model).

The algebra structures are specified by their maps into the actual ambient rings.
The pure-tensor formula specifies the canonical isomorphism, including its
B tensor R_P algebra compatibility. Quotient representatives avoid choosing lifts
or introducing a second definition of the reduced generic tensor algebra.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y

open scoped TensorProduct

namespace IsDiscreteValuationRing

/-- The canonical coefficient algebra structure and its finite-module property.
Source: Stacks Project, Tag 09II, normalization colimit; the finite-module hypothesis
of the extracted model lemma (blueprint: lem-sfb-finite-normalization-algebraic-model).
Every algebra structure is fixed by its values on pure tensors. -/
structure FiniteNormalizationCoefficientModel
    (A : Type u) (B : Type v) (K : Type w) (L : Type x) (P : Type y)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field P]
    [Algebra A B] [Algebra B L] [Algebra K L] [Algebra K P] [Algebra A P] where
  /-- The coefficient action, constrained by `canonical`. -/
  [coeffAlgebra : Algebra (B ⊗[A] integralClosure A P)
    (integralClosure B ((L ⊗[K] P) ⧸ nilradical (L ⊗[K] P)))]
  /-- Multiplication of the two canonical images in the reduced tensor algebra. -/
  canonical : ∀ (b : B) (r : integralClosure A P),
    ((algebraMap (B ⊗[A] integralClosure A P)
      (integralClosure B ((L ⊗[K] P) ⧸ nilradical (L ⊗[K] P)))
      (b ⊗ₜ[A] r)) : (L ⊗[K] P) ⧸ nilradical (L ⊗[K] P)) =
    Ideal.Quotient.mk _ ((algebraMap B L b) ⊗ₜ[K] (r : P))
  /-- Finite generation for that canonical coefficient action. -/
  finite : Module.Finite (B ⊗[A] integralClosure A P)
    (integralClosure B ((L ⊗[K] P) ⧸ nilradical (L ⊗[K] P)))

set_option synthInstance.maxHeartbeats 100000 in
/- Nested integral-closure scalar instances need additional typeclass search. -/
/-- An isomorphism at a field stage, fixed to be the canonical multiplication map.
Source: Stacks Project, Tags 05N9 and 033G, applied to the normalization system of
Tag 09II (blueprint: lem-sfb-finite-normalization-algebraic-model).
The quotient-representative formula covers every element of the upper normalization
and forces compatibility with both B and R_P, hence with B tensor over A with R_P. -/
structure FiniteNormalizationStageModel
    (A : Type u) (B : Type v) (K : Type w) (L : Type x) (P : Type y)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field P]
    [Algebra B L] [Algebra K L] [Algebra K P] [Algebra A K] [Algebra A P]
    [IsScalarTower A K P] (F : IntermediateField K P) where
  /-- The lower transition algebra, fixed by `lower_canonical`. -/
  [lowerAlgebra : Algebra (integralClosure A F) (integralClosure A P)]
  /-- The lower-to-upper algebra, fixed by `upper_canonical`. -/
  [upperAlgebra : Algebra (integralClosure A F)
    (integralClosure B ((L ⊗[K] F) ⧸ nilradical (L ⊗[K] F)))]
  /-- The lower transition is the restriction of the field inclusion. -/
  lower_canonical : ∀ r : integralClosure A F,
    ((algebraMap (integralClosure A F) (integralClosure A P) r) : P) = F.val (r : F)
  /-- The lower-to-upper map is the restriction of r ↦ 1 tensor r. -/
  upper_canonical : ∀ r : integralClosure A F,
    ((algebraMap (integralClosure A F)
      (integralClosure B ((L ⊗[K] F) ⧸ nilradical (L ⊗[K] F))) r) :
        (L ⊗[K] F) ⧸ nilradical (L ⊗[K] F)) =
      Ideal.Quotient.mk _ ((1 : L) ⊗ₜ[K] (r : F))
  /-- The isomorphism whose forward map is constrained by `multiplication`. -/
  equiv : ((integralClosure B ((L ⊗[K] F) ⧸ nilradical (L ⊗[K] F)))
    ⊗[integralClosure A F] (integralClosure A P)) ≃+*
      (integralClosure B ((L ⊗[K] P) ⧸ nilradical (L ⊗[K] P)))
  /-- The forward map is exactly c tensor r ↦ cr in the ambient reduced tensor. -/
  multiplication : ∀ (z : L ⊗[K] F) (hz : IsIntegral B (Ideal.Quotient.mk
      (nilradical (L ⊗[K] F)) z)) (r : integralClosure A P),
    ((equiv (⟨Ideal.Quotient.mk _ z, hz⟩ ⊗ₜ[integralClosure A F] r)) :
        (L ⊗[K] P) ⧸ nilradical (L ⊗[K] P)) =
      Ideal.Quotient.mk _ (Algebra.TensorProduct.map (AlgHom.id K L) F.val z) *
        Ideal.Quotient.mk _ ((1 : L) ⊗ₜ[K] (r : P))

/-- Finite normalization stabilizes at a finite intermediate field.

Source: Stacks Project, Algebra, Tags 05N9 and 033G; More on Algebra, Tag 09II,
last three paragraphs, repaired by the explicit finite-module assumption
(blueprint: lem-sfb-finite-normalization-algebraic-model).

Proof:
1. Apply lem-sfb-normalization-algebraic-transition-system to obtain the normalization
   colimits, injective transitions, faithfully flat lower transitions, and the generic
   localization surjections. Case (b) of lem-sfb-dvr-algebraic-normalization-structure
   makes E_P a nonempty finite product of fields. Then
   lem-sbc-integral-closure-finite-normal-product makes C_P normal.
2. Write B as U localized at p. The algebra U tensor R_P is finite type over the
   Noetherian ring R_P, hence Noetherian by lem-weil-pbc-finite-type-algebra-noetherian.
   The localization-tensor-over-base and localization-noetherian lemmas give that
   T_P = B tensor R_P is Noetherian.
3. Apply lem-sfb-noetherian-integral-colimit-image-model to T_F -> C_F. This gives a
   finite T_* subalgebra H of C_* with H tensor T_P = C_P. Tensor cancellation gives
   H tensor over R_* with R_P = C_P, by h tensor (b tensor r) -> bh tensor r.
4. For every later F put N_F = H tensor over R_* with R_F. Its multiplication map
   into C_F becomes the isomorphism to C_P after tensoring with R_P. Faithfully flat
   base change and ideal contraction make N_F -> C_P injective and faithfully flat.
   By lem-sfb-faithfully-flat-normal-ring-descent, N_F is normal.
5. The image of N_F contains T_F, whose localization at an upper uniformizer b
   surjects onto E_F. Since N_F embeds in E_F and b is a unit there, E_F = N_F[1/b].
   This embeds E_F in the total fraction ring of N_F.
6. Every element of C_F is integral over B and hence over N_F. Apply
   lem-weil-pbc-normal-ring-integrally-closed-total to get C_F = N_F. Tensoring with
   R_P identifies C_F tensor R_P with C_P. All maps multiply their factors, yielding
   precisely the displayed formula and compatibility with B tensor R_P.
-/
theorem exists_finite_normalization_algebraic_model
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (B : Type v) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hinj : Function.Injective (algebraMap A B))
    (K : Type w) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type x) [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L] [IsScalarTower A K L]
    (hfiniteType : ∃ (U : Type (max u v)) (_ : CommRing U) (_ : Algebra A U)
      (p : Ideal U) (_ : p.IsPrime),
      RingHom.FiniteType (algebraMap A U) ∧ Nonempty (B ≃ₐ[A] Localization.AtPrime p))
    (P : Type y) [Field P] [Algebra K P] [Algebra A P] [IsScalarTower A K P]
    [Algebra.IsAlgebraic K P] [IsNoetherianRing (integralClosure A P)]
    (hfinite : Nonempty (FiniteNormalizationCoefficientModel A B K L P)) :
    ∃ F₀ : IntermediateField K P, Module.Finite K F₀ ∧
      ∀ (F : IntermediateField K P), F₀ ≤ F → Module.Finite K F →
        Nonempty (FiniteNormalizationStageModel A B K L P F) := by
  sorry

end IsDiscreteValuationRing
