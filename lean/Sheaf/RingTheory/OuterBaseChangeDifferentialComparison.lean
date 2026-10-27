module

public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Differentials under simultaneous outer scalar extension

Source: Stacks Project, Algebra, Tags 0C4F and 00RV
(blueprint: lem-trf-outer-base-change-differential-comparison).

The module structure on `T ⊗[A] Ω[C⁄B]` is existentially packaged together with its
pure-tensor action formula, which determines it uniquely. The explicit module
arguments of the two linear equivalences refer to that same structure.

The scoped structures use Mathlib's tensor algebra, its right algebra structure,
and its differential modules. Open `KaehlerDifferential.OuterBaseChange`
to use the statement. The generator formula uniquely characterizes the transported
canonical differential map, because differential generators span the source.

## Main statements

- `KaehlerDifferential.OuterBaseChange.comparison`: the simultaneous outer comparison,
  including the forward and inverse tensor formulas.
-/

@[expose] public section

universe uA uB uC uT

open scoped TensorProduct

namespace KaehlerDifferential.OuterBaseChange

/-- The right algebra structure on an outer tensor product, from Mathlib.
Source: Stacks, Tag 00CX
(blueprint: lem-trf-outer-base-change-differential-comparison). -/
abbrev rightAlgebra (A : Type uA) (T : Type uT) (C : Type uC)
    [CommRing A] [CommRing T] [CommRing C] [Algebra A T] [Algebra A C] :
    Algebra C (T ⊗[A] C) := Algebra.TensorProduct.rightAlgebra

/-- The scalar-extended algebra map sends `t ⊗ b` to `t ⊗ φ(b)`.
Here the compatible `B`-algebra structure on `C` encodes the `A`-algebra map `φ`.
Source: Stacks, Tag 0C4F
(blueprint: lem-trf-outer-base-change-differential-comparison). -/
abbrev tensorAlgebra (A : Type uA) (B : Type uB) (C : Type uC) (T : Type uT)
    [CommRing A] [CommRing B] [CommRing C] [CommRing T]
    [Algebra A B] [Algebra A C] [Algebra A T] [Algebra B C] [IsScalarTower A B C] :
    Algebra (T ⊗[A] B) (T ⊗[A] C) :=
  (Algebra.TensorProduct.map (AlgHom.id A T) (IsScalarTower.toAlgHom A B C)).toAlgebra

attribute [scoped instance] rightAlgebra tensorAlgebra

open scoped KaehlerDifferential.OuterBaseChange

/-- Simultaneous outer scalar extension commutes with relative differentials,
with the explicit ring and module identifications in both directions.
Source: Stacks, Tag 0C4F, scalar-extended rings; Tag 00RV, differential base change
(blueprint: lem-trf-outer-base-change-differential-comparison).

Proof: (1) Use the tensor universal property (def-weil-pbc-module-tensor-product)
to balance `(t ⊗ b) ⊗ c ↦ t ⊗ φ(b)c` over both `A` and `B`. The inverse sends
`t ⊗ c` to `(t ⊗ 1) ⊗ c`. The pure-tensor multiplication rule from
lem-weil-pbc-algebra-tensor-pushout-universal-property proves multiplicativity,
unit preservation and compatibility with the specified tensor algebra map.
The composites fix pure tensors, hence all elements by additivity.
(2) Balance `(t ⊗ c) ⊗ ω ↦ t ⊗ c • ω` and its proposed inverse over `A` and `C`.
Both composites fix pure tensors. On pure tensors linearity is the identity
`ut ⊗ (c'c) • ω = ut ⊗ c' • (c • ω)`. This also checks the stated action.
(3) Apply lem-weil-pbc-kahler-differentials-base-change with base `B`, scalar
extension `T ⊗[A] B` and algebra `C`. Transport its ring tensor product through
`q`; the differential transport is induced by the universal derivation, and its
inverse by `q.symm`. Reassociate its module domain by the tensor universal
property and then use `h.symm`. All maps are linear for `T ⊗[A] C`.
(4) The resulting map sends `t ⊗ d c` to `(t ⊗ 1) • d (1 ⊗ c)`.
This formula determines the map uniquely, since `d c` generate the differential
module over `C`. No step needs flatness, finite generation or nonzero rings. -/
theorem comparison
    (A : Type uA) (B : Type uB) (C : Type uC) (T : Type uT)
    [CommRing A] [CommRing B] [CommRing C] [CommRing T]
    [Algebra A B] [Algebra A C] [Algebra A T] [Algebra B C] [IsScalarTower A B C] :
    ∃ (m : Module (T ⊗[A] C) (T ⊗[A] KaehlerDifferential B C))
      (q : (T ⊗[A] B) ⊗[B] C ≃ₐ[T ⊗[A] B] T ⊗[A] C)
      (h : @LinearEquiv (T ⊗[A] C) (T ⊗[A] C) _ _
        (RingHom.id (T ⊗[A] C)) (RingHom.id (T ⊗[A] C)) _ _
        ((T ⊗[A] C) ⊗[C] KaehlerDifferential B C)
        (T ⊗[A] KaehlerDifferential B C) _ _ _ m)
      (F : @LinearEquiv (T ⊗[A] C) (T ⊗[A] C) _ _
        (RingHom.id (T ⊗[A] C)) (RingHom.id (T ⊗[A] C)) _ _
        (T ⊗[A] KaehlerDifferential B C)
        (KaehlerDifferential (T ⊗[A] B) (T ⊗[A] C)) _ _ m _),
      (∀ (t : T) (b : B),
        algebraMap (T ⊗[A] B) (T ⊗[A] C) (t ⊗ₜ[A] b) =
          t ⊗ₜ[A] algebraMap B C b) ∧
      (∀ (t : T) (b : B) (c : C),
        q ((t ⊗ₜ[A] b) ⊗ₜ[B] c) = t ⊗ₜ[A] (algebraMap B C b * c)) ∧
      (∀ (t : T) (c : C), q.symm (t ⊗ₜ[A] c) = (t ⊗ₜ[A] (1 : B)) ⊗ₜ[B] c) ∧
      (∀ (t u : T) (c : C) (ω : KaehlerDifferential B C),
        @SMul.smul _ _ m.toSMul (t ⊗ₜ[A] c) (u ⊗ₜ[A] ω) =
          (t * u) ⊗ₜ[A] (c • ω)) ∧
      (∀ (t : T) (c : C) (ω : KaehlerDifferential B C),
        h ((t ⊗ₜ[A] c) ⊗ₜ[C] ω) = t ⊗ₜ[A] (c • ω)) ∧
      (∀ (t : T) (ω : KaehlerDifferential B C),
        h.symm (t ⊗ₜ[A] ω) = (t ⊗ₜ[A] (1 : C)) ⊗ₜ[C] ω) ∧
      (∀ (t : T) (c : C),
        F (t ⊗ₜ[A] KaehlerDifferential.D B C c) =
          (t ⊗ₜ[A] (1 : C)) •
            KaehlerDifferential.D (T ⊗[A] B) (T ⊗[A] C) ((1 : T) ⊗ₜ[A] c)) := by
  sorry

end KaehlerDifferential.OuterBaseChange
