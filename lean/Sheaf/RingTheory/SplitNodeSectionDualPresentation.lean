/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# The dual of the section ideal in a split node

Source: Knudsen, A Closer Look at the Stacks of Stable Pointed Curves,
arXiv:1106.1588, Section 3, Proposition 3.1 and Corollary 3.2; split-coordinate
polynomial calculation over arbitrary coefficient rings
(blueprint: lem-sfb-split-node-section-dual-presentation).

The augmentation and the two distinguished dual maps in the statement are specified
by their values. All ring and ideal carriers below are actual quotients and spans.
The equivalences in the conclusion are characterized on pure tensors, including the
evaluation formula for the dual comparison; they are therefore the canonical maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open scoped TensorProduct

namespace RingTheory.SplitNodeSection

variable {A : Type u} [CommRing A]

/-- The split nodal ring, using variables 0 and 1 for x and y.
Source: Knudsen §3, split coordinates (blueprint: lem-sfb-split-node-section-dual-presentation).
-/
def Ring (a b : A) :=
  MvPolynomial (Fin 2) A ⧸
    Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (a * b)}

/-- The commutative ring structure on the polynomial quotient.
Source: Knudsen §3 (blueprint: lem-sfb-split-node-section-dual-presentation). -/
instance ringCommRing (a b : A) : CommRing (Ring a b) := inferInstanceAs (CommRing (_ ⧸ _))

/-- The coefficient algebra structure on the polynomial quotient.
Source: Knudsen §3 (blueprint: lem-sfb-split-node-section-dual-presentation). -/
instance ringAlgebra (a b : A) : Algebra A (Ring a b) := inferInstanceAs (Algebra A (_ ⧸ _))

/-- Restriction of the coefficient algebra structure to a ground ring.
Source: Knudsen §3, coefficient change
(blueprint: lem-sfb-split-node-section-dual-presentation). -/
instance groundAlgebra {B : Type v} [CommRing B] [Algebra B A] (a b : A) : Algebra B (Ring a b) :=
  inferInstanceAs (Algebra B (MvPolynomial (Fin 2) A ⧸ _))

/-- The residue class of x.
Source: Knudsen §3, split coordinates (blueprint: lem-sfb-split-node-section-dual-presentation).
-/
def x (a b : A) : Ring a b := Ideal.Quotient.mk _ (MvPolynomial.X 0)

/-- The residue class of y.
Source: Knudsen §3, split coordinates (blueprint: lem-sfb-split-node-section-dual-presentation).
-/
def y (a b : A) : Ring a b := Ideal.Quotient.mk _ (MvPolynomial.X 1)

/-- The section ideal, constructed from its two displayed generators.
Source: Knudsen §3, split coordinates (blueprint: lem-sfb-split-node-section-dual-presentation).
-/
def sectionIdeal (a b : A) : Ideal (Ring a b) :=
  Ideal.span {x a b - algebraMap A (Ring a b) a, y a b - algebraMap A (Ring a b) b}

/-- The generator x-a as an element of the actual section ideal.
Source: Knudsen §3 (blueprint: lem-sfb-split-node-section-dual-presentation). -/
def u (a b : A) : sectionIdeal a b :=
  ⟨x a b - algebraMap A (Ring a b) a, Ideal.subset_span (Set.mem_insert _ _)⟩

/-- The generator y-b as an element of the actual section ideal.
Source: Knudsen §3 (blueprint: lem-sfb-split-node-section-dual-presentation). -/
def v (a b : A) : sectionIdeal a b :=
  ⟨y a b - algebraMap A (Ring a b) b,
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

/-- The dual module Hom_R(I,R), without a replacement presentation as its carrier.
Source: Knudsen Proposition 3.1 (blueprint: lem-sfb-split-node-section-dual-presentation).
-/
abbrev Dual (a b : A) := Module.Dual (Ring a b) (sectionIdeal a b)

/-- The distinguished inclusion functional.
Source: Knudsen Proposition 3.1 (blueprint: lem-sfb-split-node-section-dual-presentation).
-/
def inclusion (a b : A) : Dual a b := (sectionIdeal a b).subtype

/-- The multiplication map r ↦ r times the inclusion functional.
Source: Knudsen Proposition 3.1 (blueprint: lem-sfb-split-node-section-dual-presentation).
-/
def multiplier (a b : A) : Ring a b →ₗ[Ring a b] Dual a b :=
  (LinearMap.id : Ring a b →ₗ[Ring a b] Ring a b).smulRight (inclusion a b)

/-- The displayed two-generator map (r,s) ↦ r times inclusion + s times e.
Source: Knudsen Proposition 3.1 (blueprint: lem-sfb-split-node-section-dual-presentation).
-/
def presentation (a b : A) (e : Dual a b) :
    (Ring a b × Ring a b) →ₗ[Ring a b] Dual a b :=
  (multiplier a b).comp (LinearMap.fst _ _ _) +
    ((LinearMap.id : Ring a b →ₗ[Ring a b] Ring a b).smulRight e).comp
      (LinearMap.snd _ _ _)

/-- The clauses of the displayed presentation and short exact sequence. Linearity of
π over R is expressed using the specified augmentation, avoiding any chosen R-action on A.
Source: Knudsen Proposition 3.1 (blueprint: lem-sfb-split-node-section-dual-presentation).
-/
def Presentation (a b : A) (ε : Ring a b →ₐ[A] A) (e : Dual a b)
    (π : Dual a b →ₗ[A] A) : Prop :=
  ε (x a b) = a ∧ ε (y a b) = b ∧ RingHom.ker ε.toRingHom = sectionIdeal a b ∧
  Module.FinitePresentation (Ring a b) (sectionIdeal a b) ∧
  Module.FinitePresentation (Ring a b) (Dual a b) ∧
  e (u a b) = -algebraMap A (Ring a b) a ∧ e (v a b) = y a b ∧
  (∀ e' : Dual a b, e' (u a b) = -algebraMap A (Ring a b) a →
    e' (v a b) = y a b → e' = e) ∧
  Function.Surjective (presentation a b e) ∧
  LinearMap.ker (presentation a b e) =
    Submodule.span (Ring a b)
      {(algebraMap A (Ring a b) a, (u a b).val), (-y a b, (v a b).val)} ∧
  Function.Injective (multiplier a b) ∧
  (∀ r s : Ring a b, π (r • inclusion a b + s • e) = ε s) ∧
  (∀ (r : Ring a b) (m : Dual a b), π (r • m) = ε r * π m) ∧
  Function.Exact (multiplier a b) π ∧ Function.Surjective π

/-- For an arbitrary coefficient ring, the dual section ideal has the stated two-generator
presentation and universal coefficient base change, and its flat extensions have the
same dual presentation and short exact sequence.

Source: Knudsen §3, Proposition 3.1 and Corollary 3.2, and §4 Main Lemma;
the arbitrary-ring split-coordinate argument is the node's polynomial proof
(blueprint: lem-sfb-split-node-section-dual-presentation).

Proof plan (the twelve steps of the node):
1. Translate X,Y to u=X-a,v=Y-b. Evaluation has kernel (u,v), and f=Yu+av.
2. Multiplication by u and v in the respective polynomial rings is injective.
   The leading monomial XY makes f a nonzerodivisor over any coefficient ring.
3. Polynomial relations of (u,v) are multiples of (-v,u). Lifting through f gives
   the two relations (Y,a),(-v,u), hence the finite presentation matrix K of I.
4. With Q=K transpose and T having columns (u,v),(-a,Y), QT=TQ=f times identity.
   Lift a kernel vector to the polynomial ring and cancel f to get ker Q=im T
   and ker T=im Q after quotienting.
5. Evaluate Hom(I,R) on u,v. It is ker Q=im T, giving inclusion and the unique e;
   its relation module is generated by (a,u),(-Y,v).
6. The two finite matrix presentations give finite presentation of I and its dual,
   using def-sc-finitely-presented-module.
7. If r times inclusion vanishes, write (r,0)=Q(c,d); the relations in step 3
   imply r=-(Yu+av)k=0, proving the first arrow injective.
8. The rule (r,s) ↦ ε(s) kills the relations and gives a surjective π. If ε(s)=0,
   write s=uh+vk; ue=-a times inclusion and ve=Y times inclusion give exactness.
9. Tensor the finite presentations by A' using lem-weil-pbc-tensor-right-exact.
   The polynomial tensor comparison gives the primed matrices and therefore the
   canonical ideal and dual equivalences, with the stated pure-tensor formulas.
10. The formulas identify both arrows with their primed counterparts, even for
    nonflat coefficient change; apply steps 7 and 8 over A' for exactness.
11. For flat C, flip tensor factors to use def-weil-pbc-flat-ring-map. Factoring
    exact pairs through images shows tensoring preserves both matrix kernels.
    The tensor of I injects into C with image IC.
12. Evaluation on the two generators identifies the dual over C with ker Q_C,
    and the tensored dual with coker Q_C=im T_C. Their comparison is evaluation
    c⊗φ on d i ↦ cdφ(i). Flatness preserves the short exact sequence, whose
    last term is C⊗_R A=C/IC. The scalar unit C⊗_R R=C identifies its first map.
Tensor constructions throughout use def-weil-pbc-module-tensor-product. -/
theorem split_node_section_dual_presentation (a b : A) :
    ∃ (ε : Ring a b →ₐ[A] A) (e : Dual a b) (π : Dual a b →ₗ[A] A),
      Presentation a b ε e π ∧
      (∀ (A' : Type v) [CommRing A'] [Algebra A A'],
        ∃ (ρ : Ring a b →ₐ[A] Ring (algebraMap A A' a) (algebraMap A A' b))
          (ε' : Ring (algebraMap A A' a) (algebraMap A A' b) →ₐ[A'] A')
          (e' : Dual (algebraMap A A' a) (algebraMap A A' b))
          (π' : Dual (algebraMap A A' a) (algebraMap A A' b) →ₗ[A'] A')
          (i : A' ⊗[A] sectionIdeal a b ≃ₗ[A']
            sectionIdeal (algebraMap A A' a) (algebraMap A A' b))
          (m : A' ⊗[A] Dual a b ≃ₗ[A']
            Dual (algebraMap A A' a) (algebraMap A A' b)),
          ρ (x a b) = x (algebraMap A A' a) (algebraMap A A' b) ∧
          ρ (y a b) = y (algebraMap A A' a) (algebraMap A A' b) ∧
          Presentation (algebraMap A A' a) (algebraMap A A' b) ε' e' π' ∧
          (∀ (c : A') (z : sectionIdeal a b),
            (i (c ⊗ₜ[A] z)).val = c • ρ z.val) ∧
          (∀ (c d : A') (φ : Dual a b) (z : sectionIdeal a b),
            m (c ⊗ₜ[A] φ) (i (d ⊗ₜ[A] z)) = (c * d) • ρ (φ z)) ∧
          (∀ c : A', m (c ⊗ₜ[A] inclusion a b) =
            c • inclusion (algebraMap A A' a) (algebraMap A A' b)) ∧
          (∀ c : A', m (c ⊗ₜ[A] e) = c • e') ∧
          (∀ (c : A') (φ : Dual a b),
            π' (m (c ⊗ₜ[A] φ)) = c * algebraMap A A' (π φ))) ∧
      (∀ (C : Type w) [CommRing C] [Algebra (Ring a b) C] [Module.Flat (Ring a b) C],
        ∃ (i : C ⊗[Ring a b] sectionIdeal a b ≃ₗ[C]
            (sectionIdeal a b).map (algebraMap (Ring a b) C))
          (m : C ⊗[Ring a b] Dual a b ≃ₗ[C]
            Module.Dual C ((sectionIdeal a b).map (algebraMap (Ring a b) C)))
          (q : C ⊗[Ring a b] Dual a b →ₗ[C]
            C ⧸ (sectionIdeal a b).map (algebraMap (Ring a b) C)),
          (∀ (c : C) (z : sectionIdeal a b),
            (i (c ⊗ₜ[Ring a b] z)).val = c * algebraMap (Ring a b) C z.val) ∧
          (∀ (c d : C) (φ : Dual a b) (z : sectionIdeal a b),
            m (c ⊗ₜ[Ring a b] φ) (i (d ⊗ₜ[Ring a b] z)) =
              c * d * algebraMap (Ring a b) C (φ z)) ∧
          (∀ c : C, m (c ⊗ₜ[Ring a b] inclusion a b) =
            c • ((sectionIdeal a b).map (algebraMap (Ring a b) C)).subtype) ∧
          (∀ (c : C) (r s : Ring a b),
            q (c ⊗ₜ[Ring a b] (r • inclusion a b + s • e)) =
              Ideal.Quotient.mk _ (c * algebraMap (Ring a b) C s)) ∧
          Function.Injective (fun c : C ↦ c • ((1 : C) ⊗ₜ[Ring a b] inclusion a b)) ∧
          Function.Exact (fun c : C ↦ c • ((1 : C) ⊗ₜ[Ring a b] inclusion a b)) q ∧
          Function.Surjective q) := by
  sorry

end RingTheory.SplitNodeSection
