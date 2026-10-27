module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.LinearAlgebra.Dual.Defs

/-! # Finite-order distributions and tangent functionals

Source: Milne, Algebraic Groups (2017), Sections 10e and 10l,
Propositions 10.28--10.29, printed pp.195--196 and 208.
(blueprint: def-sfb-bialgebra-distribution-algebra)

The carriers are actual functionals in Mathlib's convolution dual. The algebra
and Lie operations are restrictions of those on that dual; only their closure
proofs are postponed. No antipode, finiteness, or characteristic assumption is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open scoped TensorProduct

namespace Bialgebra
variable (k : Type u) (C : Type v) [Field k] [CommRing C] [Bialgebra k C]

/-- The augmentation ideal. Source: Milne, 10l, p.208.
(blueprint: def-sfb-bialgebra-distribution-algebra) -/
def augmentationIdeal : Ideal C := RingHom.ker (counitAlgHom k C)

/-- An order bound on a convolution functional. Source: Milne, 10l, p.208.
(blueprint: def-sfb-bialgebra-distribution-algebra) -/
def HasDistributionOrder (n : ℕ) (a : WithConv (C →ₗ[k] k)) : Prop :=
  ∀ c : C, c ∈ augmentationIdeal k C ^ (n + 1) → a c = 0

/-- The order subspaces, with F_(-1)=0 (and zero in every negative degree).
Source: Milne, 10l, p.208.
(blueprint: def-sfb-bialgebra-distribution-algebra) -/
def distributionFiltration (n : ℤ) : Submodule k (WithConv (C →ₗ[k] k)) :=
  if n < 0 then ⊥ else
    (((augmentationIdeal k C ^ (n.toNat + 1)).restrictScalars k).dualAnnihilator).comap
      (WithConv.linearEquiv k (C →ₗ[k] k)).toLinearMap

/-- The finite-order carrier. Source: Milne, 10l, p.208.
(blueprint: def-sfb-bialgebra-distribution-algebra) -/
def IsDistribution (a : WithConv (C →ₗ[k] k)) : Prop :=
  ∃ n : ℕ, HasDistributionOrder k C n a

/-- Closure needed to restrict the convolution algebra to finite-order functionals.
Source: Milne, 10l, p.208.
(blueprint: def-sfb-bialgebra-distribution-algebra)

Proof: the counit kills I. Powers of I decrease, so the order spaces are nested
vector subspaces. For orders r,s expand Delta of a product of r+s+1 elements of I.
The augmentation splitting C=k+I puts at least one augmentation factor in each
summand of each Delta(x). Every resulting tensor has at least r+1 factors on
one side or s+1 on the other, hence is killed. Such products span the ideal
power, proving closure; the unit and scalar maps are the counit and its multiples.
This uses the tensor-product and full-dual convolution constructions. -/
theorem distribution_closed :
    IsDistribution k C 0 ∧
      (∀ a b : WithConv (C →ₗ[k] k), IsDistribution k C a → IsDistribution k C b →
        IsDistribution k C (a + b)) ∧
      IsDistribution k C 1 ∧
      (∀ a b : WithConv (C →ₗ[k] k), IsDistribution k C a → IsDistribution k C b →
        IsDistribution k C (a * b)) ∧
      (∀ t : k, IsDistribution k C (algebraMap k (WithConv (C →ₗ[k] k)) t)) := by
  sorry

/-- The union of the order spaces, with the actual convolution operations.
Source: Milne, 10l, p.208.
(blueprint: def-sfb-bialgebra-distribution-algebra) -/
def distributionAlgebra : Subalgebra k (WithConv (C →ₗ[k] k)) where
  carrier := {a | IsDistribution k C a}
  zero_mem' := (distribution_closed k C).1
  add_mem' := fun {a b} ↦ (distribution_closed k C).2.1 a b
  one_mem' := (distribution_closed k C).2.2.1
  mul_mem' := fun {a b} ↦ (distribution_closed k C).2.2.2.1 a b
  algebraMap_mem' := (distribution_closed k C).2.2.2.2

/-- Tangent functionals are derivations at the counit. Source: Milne, 10e, p.195.
(blueprint: def-sfb-bialgebra-distribution-algebra) -/
def IsTangentFunctional (a : WithConv (C →ₗ[k] k)) : Prop :=
  ∀ x y : C, a (x * y) = counitAlgHom k C x * a y + a x * counitAlgHom k C y

/-- The commutator Lie ring of the full convolution dual, using Mathlib's construction.
Source: Milne, 10e and 10l, pp.195--196 and 208.
(blueprint: def-sfb-bialgebra-distribution-algebra) -/
instance convolutionLieRing : LieRing (WithConv (C →ₗ[k] k)) :=
  LieRing.ofAssociativeRing

/-- Closure of tangent functionals under linear operations and convolution commutator.
Source: Milne, 10e, Proposition 10.29, and 10l.
(blueprint: def-sfb-bialgebra-distribution-algebra)

Proof: linear closure follows by adding and scaling the counit Leibniz identities.
For v define D_v=(id tensor v)Delta. Multiplicativity of Delta and the counit
identities give its Leibniz rule. Coassociativity gives invariance. Invariant
derivations are closed under commutators, and epsilon(D_v D_w)=v*w, so the
commutator of functionals is again tangent. This is the counit contraction
calculation of Milne, Proposition 10.29. -/
theorem tangent_closed :
    IsTangentFunctional k C 0 ∧
      (∀ a b : WithConv (C →ₗ[k] k),
        IsTangentFunctional k C a → IsTangentFunctional k C b →
          IsTangentFunctional k C (a + b)) ∧
      (∀ (t : k) (a : WithConv (C →ₗ[k] k)),
        IsTangentFunctional k C a → IsTangentFunctional k C (t • a)) ∧
      (∀ a b : WithConv (C →ₗ[k] k),
        IsTangentFunctional k C a → IsTangentFunctional k C b →
          IsTangentFunctional k C ⁅a, b⁆) := by
  sorry

/-- The tangent Lie algebra with convolution commutator bracket.
Source: Milne, 10e and 10l, pp.195--196 and 208.
(blueprint: def-sfb-bialgebra-distribution-algebra) -/
def tangentLieAlgebra : LieSubalgebra k (WithConv (C →ₗ[k] k)) where
  carrier := {a | IsTangentFunctional k C a}
  zero_mem' := (tangent_closed k C).1
  add_mem' := fun {a b} ↦ (tangent_closed k C).2.1 a b
  smul_mem' := (tangent_closed k C).2.2.1
  lie_mem' := fun {a b} ↦ (tangent_closed k C).2.2.2 a b

end Bialgebra
