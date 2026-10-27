module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Ideal.Cotangent

/-! # Regular cochains for a square-zero affine group deformation

Source: Conrad, Reductive group schemes, Appendix B.2, pp.283--287
(blueprint: def-sfb-infinitesimal-regular-cochains).

All constructions are formulas. Base change uses A/J tensor R, canonically R/JR.
The coefficient ideal is J/J², canonically J when J² = 0. This uses Mathlib's existing
quotient module rather than choosing an extra module structure on J.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Coalgebra Bialgebra WithConv
open scoped TensorProduct

namespace AlgebraicGeometry.InfinitesimalRegular

variable (A : Type u) [CommRing A] (J : Ideal A)

/-- Reduction of an algebra. Source: Conrad B.2.6
(blueprint: def-sfb-infinitesimal-regular-cochains). -/
abbrev Reduced (R : Type u) [CommRing R] [Algebra A R] := (A ⧸ J) ⊗[A] R

/-- The quotient map in the tensor presentation. Source: Conrad B.2.6
(blueprint: def-sfb-infinitesimal-regular-cochains). -/
def reduce (R : Type u) [CommRing R] [Algebra A R] : R →ₐ[A] Reduced A J R :=
  Algebra.TensorProduct.includeRight

/-- Base change of an algebra map. Source: Conrad B.2.6
(blueprint: def-sfb-infinitesimal-regular-cochains). -/
def reduceMap {R T : Type u} [CommRing R] [CommRing T] [Algebra A R] [Algebra A T]
    (f : R →ₐ[A] T) : Reduced A J R →ₐ[A ⧸ J] Reduced A J T :=
  AlgHom.liftEquiv A (A ⧸ J) R (Reduced A J T) ((reduce A J T).comp f)

/-- Cotangent module at the identity of an affine group. Source: Conrad B.2.6
(blueprint: def-sfb-infinitesimal-regular-cochains). -/
def identityCotangent (K D : Type u) [CommRing K] [CommRing D] [HopfAlgebra K D] :
    ModuleCat K := by
  letI : Algebra D K := (counitAlgHom K D).toRingHom.toAlgebra
  exact ModuleCat.of K (K ⊗[D] KaehlerDifferential K D)

/-- Universal identity differential. Source: Conrad B.2.6
(blueprint: def-sfb-infinitesimal-regular-cochains). -/
def identityDifferential (K D : Type u) [CommRing K] [CommRing D] [HopfAlgebra K D]
    (d : D) : identityCotangent K D := by
  letI : Algebra D K := (counitAlgHom K D).toRingHom.toAlgebra
  exact (1 : K) ⊗ₜ[D] KaehlerDifferential.D K D d

/-- Lie dual tensor the square-zero ideal. Source: Conrad B.2.6
(blueprint: def-sfb-infinitesimal-regular-cochains). -/
abbrev Coeff (D : Type u) [CommRing D] [HopfAlgebra A D] :=
  Module.Dual (A ⧸ J) (identityCotangent (A ⧸ J) (Reduced A J D)) ⊗[A ⧸ J] J.Cotangent

/-- Tensor powers, including degree zero. Source: Conrad B.2, regular cochains
(blueprint: def-sfb-infinitesimal-regular-cochains). -/
def power (K C : Type u) [CommRing K] [CommRing C] [Algebra K C] : ℕ → CommAlgCat K
  | 0 => CommAlgCat.of K K
  | 1 => CommAlgCat.of K C
  | n + 2 => CommAlgCat.of K (power K C (n + 1) ⊗[K] C)

/-- Evaluation on a tuple of algebra-valued points. Source: Conrad B.2
(blueprint: def-sfb-infinitesimal-regular-cochains). -/
def powerEval {K C T : Type u} [CommRing K] [CommRing C] [CommRing T]
    [Algebra K C] [Algebra K T] :
    (n : ℕ) → (Fin n → C →ₐ[K] T) → (power K C n →ₐ[K] T)
  | 0, _ => Algebra.ofId K T
  | 1, h => h 0
  | n + 2, h => Algebra.TensorProduct.lift
      (powerEval (n + 1) (fun i ↦ h i.castSucc))
      (h (Fin.last (n + 1))) (fun _ _ ↦ Commute.all _ _)

/-- Regular cochains are tensors, not arbitrary functions on points. Source: Conrad B.2
(blueprint: def-sfb-infinitesimal-regular-cochains). -/
abbrev Cochain {K : Type u} [CommRing K] (C E : Type u) [CommRing C] [Algebra K C]
    [AddCommGroup E] [Module K E] (n : ℕ) := E ⊗[K] power K C n

/-- Cochain evaluation with coefficients retained. Source: Conrad B.2
(blueprint: def-sfb-infinitesimal-regular-cochains). -/
def eval {K C E T : Type u} [CommRing K] [CommRing C] [CommRing T]
    [Algebra K C] [Algebra K T] [AddCommGroup E] [Module K E]
    {n : ℕ} (h : Fin n → C →ₐ[K] T) : Cochain (K := K) C E n →ₗ[K] E ⊗[K] T :=
  TensorProduct.map LinearMap.id (powerEval n h).toLinearMap

/-- Evaluation of a linear coaction on coefficient-valued points. Source: Conrad B.2.5
(blueprint: def-sfb-infinitesimal-regular-cochains). -/
def action {K C E T : Type u} [CommRing K] [CommRing C] [CommRing T]
    [Algebra K C] [Algebra K T] [AddCommGroup E] [Module K E]
    (ρ : E →ₗ[K] E ⊗[K] C) (h : C →ₐ[K] T) : E ⊗[K] T →ₗ[K] E ⊗[K] T :=
  (TensorProduct.map LinearMap.id
      (Algebra.TensorProduct.lift h (AlgHom.id K T) (fun _ _ ↦ Commute.all _ _)).toLinearMap).comp
    ((TensorProduct.assoc K E C T).toLinearMap.comp (TensorProduct.map ρ LinearMap.id))

/-- Coassociativity and counitality. Source: Conrad B.2, quasi-coherent group modules
(blueprint: def-sfb-infinitesimal-regular-cochains). -/
def IsCoaction {K C E : Type u} [CommRing K] [CommRing C] [HopfAlgebra K C]
    [AddCommGroup E] [Module K E] (ρ : E →ₗ[K] E ⊗[K] C) : Prop :=
  (TensorProduct.assoc K E C C).toLinearMap.comp ((TensorProduct.map ρ LinearMap.id).comp ρ) =
      (TensorProduct.map LinearMap.id (comul : C →ₗ[K] C ⊗[K] C)).comp ρ ∧
    (TensorProduct.rid K E).toLinearMap.comp
      ((TensorProduct.map LinearMap.id (counit : C →ₗ[K] K)).comp ρ) = LinearMap.id

/-- The infinitesimal kernel, as a subtype; its multiplication is that of group points.
Source: Conrad B.2.6 (blueprint: def-sfb-infinitesimal-regular-cochains). -/
abbrev Kernel (D R : Type u) [CommRing D] [HopfAlgebra A D] [CommRing R] [Algebra A R] :=
  {g : WithConv (D →ₐ[A] R) //
    (reduce A J R).comp g.ofConv =
      (reduce A J R).comp (1 : WithConv (D →ₐ[A] R)).ofConv}

/-- The family of kernel bijections. Additivity, normalization and naturality are assertions
of the theorem, not assumptions in this type. Source: Conrad B.2.6
(blueprint: def-sfb-infinitesimal-regular-cochains). -/
abbrev Comparison (D : Type u) [CommRing D] [HopfAlgebra A D] :=
  (R : Type u) → [CommRing R] → [Algebra A R] → [Module.Flat A R] →
    (Coeff A J D ⊗[A ⧸ J] Reduced A J R) ≃ Kernel A J D R

/-- Inversion of a group-valued point by the antipode. Unlike Mathlib's convolution
`Inv` instance this requires no bialgebra structure on the test algebra.
Source: Conrad B.2.5 (blueprint: def-sfb-infinitesimal-regular-cochains). -/
def inverse {K D R : Type u} [CommRing K] [CommRing D] [CommRing R]
    [HopfAlgebra K D] [Algebra K R] (g : WithConv (D →ₐ[K] R)) :
    WithConv (D →ₐ[K] R) :=
  toConv (g.ofConv.comp (HopfAlgebra.antipodeAlgHom K D))

/-- The regular defect equation on all flat test algebras. The universal pair algebra
is flat, so this specifies the unique regular tensor, not just its field-valued values.
Source: Conrad B.2.5 (blueprint: def-sfb-infinitesimal-regular-cochains). -/
def HasDefect {D C : Type u} [CommRing D] [CommRing C]
    [HopfAlgebra A D] [HopfAlgebra A C]
    (κ : Comparison A J D) (f : D →ₐ[A] C)
    (c : Cochain (K := A ⧸ J) (Reduced A J C) (Coeff A J D) 2) : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra A R] [Module.Flat A R]
    (h k : WithConv (C →ₐ[A] R)),
    (κ R (eval ![reduceMap A J h.ofConv, reduceMap A J k.ofConv] c)).val =
      toConv ((h * k).ofConv.comp f) *
        inverse (toConv (k.ofConv.comp f)) * inverse (toConv (h.ofConv.comp f))

/-- The correction is an actual coordinate map of schemes. Source: Conrad B.2.5
(blueprint: def-sfb-infinitesimal-regular-cochains). -/
def correct {D C : Type u} [CommRing D] [CommRing C]
    [HopfAlgebra A D] [HopfAlgebra A C] [Module.Flat A C]
    (κ : Comparison A J D) (f : D →ₐ[A] C)
    (b : Coeff A J D ⊗[A ⧸ J] Reduced A J C) : D →ₐ[A] C :=
  ((κ C b).val * toConv f).ofConv

end AlgebraicGeometry.InfinitesimalRegular
