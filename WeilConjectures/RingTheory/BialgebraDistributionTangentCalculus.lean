/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Derivation.Lie
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.LinearAlgebra.Dual.Defs

/-! # Finite-order convolution and tangent derivations for a commutative bialgebra

Source: Milne, *Algebraic Groups*, Sections 10e and 10l, Propositions 10.28--10.29,
printed pp.195--196, 208 (blueprint: lem-sfb-bialgebra-distribution-tangent-calculus).
-/

@[expose] public section

set_option autoImplicit false

open scoped TensorProduct
open Coalgebra

universe u v

namespace BialgebraDistribution

/-- The augmentation ideal of a bialgebra.

Source: Milne, *Algebraic Groups*, Sections 10e and 10l, printed pp.195--196, 208
(blueprint: lem-sfb-bialgebra-distribution-tangent-calculus). -/
def augmentationIdeal (k : Type u) (C : Type v) [Field k] [CommRing C]
    [Bialgebra k C] : Ideal C := RingHom.ker (Bialgebra.counitAlgHom k C).toRingHom

/-- Functionals of order at most `n` supported at the bialgebra counit.

Source: Milne, *Algebraic Groups*, Sections 10e and 10l, printed pp.195--196, 208
(blueprint: lem-sfb-bialgebra-distribution-tangent-calculus). -/
def finiteOrder (k : Type u) (C : Type v) [Field k] [CommRing C]
    [Bialgebra k C] (n : ℕ) : Submodule k (C →ₗ[k] k) :=
  (((augmentationIdeal k C) ^ (n + 1)).restrictScalars k).dualAnnihilator

/-- The order filtration, extended by zero to negative indices.

Source: Milne, *Algebraic Groups*, Sections 10e and 10l, printed pp.195--196, 208
(blueprint: lem-sfb-bialgebra-distribution-tangent-calculus). -/
def orderFiltration (k : Type u) (C : Type v) [Field k] [CommRing C]
    [Bialgebra k C] (n : ℤ) : Submodule k (C →ₗ[k] k) :=
  if n < 0 then ⊥ else finiteOrder k C n.toNat

/-- The union of the finite-order distribution spaces.

Source: Milne, *Algebraic Groups*, Sections 10e and 10l, printed pp.195--196, 208
(blueprint: lem-sfb-bialgebra-distribution-tangent-calculus). -/
def distributions (k : Type u) (C : Type v) [Field k] [CommRing C]
    [Bialgebra k C] : Set (C →ₗ[k] k) :=
  {a | ∃ n : ℕ, a ∈ finiteOrder k C n}

/-- Convolution of two linear functionals on a bialgebra.

Source: Milne, *Algebraic Groups*, Sections 10e and 10l, printed pp.195--196, 208
(blueprint: lem-sfb-bialgebra-distribution-tangent-calculus). -/
noncomputable def convolution (k : Type u) (C : Type v) [Field k] [CommRing C]
    [Bialgebra k C] (a b : C →ₗ[k] k) : C →ₗ[k] k :=
  (WithConv.toConv a * WithConv.toConv b).ofConv

/-- The tangent functionals at the counit, presented as a canonical submodule.

Source: Milne, *Algebraic Groups*, Sections 10e and 10l, printed pp.195--196, 208
(blueprint: lem-sfb-bialgebra-distribution-tangent-calculus). -/
def tangentFunctionals (k : Type u) (C : Type v) [Field k] [CommRing C]
    [Bialgebra k C] : Submodule k (C →ₗ[k] k) :=
  ⨅ a : C, ⨅ b : C, LinearMap.ker
    (Module.Dual.eval k C (a * b) - Coalgebra.counit (R := k) a • Module.Dual.eval k C b -
      Coalgebra.counit (R := k) b • Module.Dual.eval k C a)

/-- The contraction `(1 ⊗ v) Δ` used to produce an invariant derivation.

Source: Milne, *Algebraic Groups*, Sections 10e and 10l, printed pp.195--196, 208
(blueprint: lem-sfb-bialgebra-distribution-tangent-calculus). -/
def tangentContraction (k : Type u) (C : Type v) [Field k] [CommRing C]
    [Bialgebra k C] (v : C →ₗ[k] k) : C →ₗ[k] C :=
  (TensorProduct.rid k C).comp
    ((TensorProduct.map (LinearMap.id : C →ₗ[k] C) v).comp
      (Coalgebra.comul (R := k) (A := C)))

/-- The invariance equation for a derivation.

Source: Milne, *Algebraic Groups*, Sections 10e and 10l, printed pp.195--196, 208
(blueprint: lem-sfb-bialgebra-distribution-tangent-calculus). -/
def invariantDerivation (k : Type u) (C : Type v) [Field k] [CommRing C]
    [Bialgebra k C] (D : Derivation k C C) : Prop :=
  (Coalgebra.comul (R := k) (A := C)).comp D.toLinearMap =
    (TensorProduct.map (LinearMap.id : C →ₗ[k] C) D.toLinearMap).comp
      (Coalgebra.comul (R := k) (A := C))

/--
For a commutative augmented bialgebra, finite-order distributions form the filtered
convolution algebra and tangent functionals identify with invariant derivations.

Source: Milne, *Algebraic Groups*, Sections 10e and 10l, Propositions 10.28--10.29,
printed pp.195--196, 208 (blueprint: lem-sfb-bialgebra-distribution-tangent-calculus).

Proof:
1. Write η for the scalar map and p(c) = c - ε(c)1. Since εη = 1, we have
   C = k1 ⊕ I. Tensor bilinearity [def-weil-pbc-module-tensor-product] expands each
   tensor into its four scalar and augmentation slots, projected by ηε and p.
2. For x ∈ I the scalar-scalar slot of Δx vanishes by the counit identity. Every
   remaining slot has a factor in I. Thus Δ(I) lies in the sum of the images of
   I ⊗ C and C ⊗ I, using [def-weil-pbc-module-tensor-product].
3. If a ∈ F_r and b ∈ F_s, expand Δ(x₁⋯x_N), N = r+s+1, using step 2 and the
   multiplicative tensor structure [lem-weil-pbc-algebra-tensor-pushout-universal-property].
   Every term has either r+1 augmentation factors on the left or s+1 on the right,
   so a ⊗ b kills it. These products span I^N, giving the order bound.
4. Apply [lem-sfb-convolution-linear-map-algebra] with R = B = k. Each F_n is a
   subspace and F_n ⊆ F_(n+1). Their union is a subspace, step 3 closes it under
   convolution, and ε ∈ F_0. Restrict the full-dual algebra to this union.
5. For v ∈ L, the identity at 1 gives v(1) = 2v(1), hence v(1) = 0 even in
   characteristic two. Leibniz kills I², so v restricts to a form on I/I² and
   belongs to F_1. The splitting in step 1 shows that this form determines v.
6. Given λ on I/I², set v(c) = λ([p(c)]). The identity
   p(ab) = ε(a)p(b) + ε(b)p(a) + p(a)p(b) proves Leibniz. Since p(x) = x on I,
   this is the linear inverse of restriction, giving the asserted equivalence.
7. For Δa = Σ a₁ ⊗ a₂, multiplicativity and Leibniz give
   D_v(ab) = Σ a₁b₁(ε(a₂)v(b₂) + v(a₂)ε(b₂)) = aD_v(b) + D_v(a)b.
   This uses [def-weil-pbc-module-tensor-product] and
   [lem-weil-pbc-algebra-tensor-pushout-universal-property].
8. Apply 1 ⊗ 1 ⊗ v to coassociativity to get ΔD_v = (1 ⊗ D_v)Δ.
   The other counit contraction gives εD_v = v. The formula is linear in v.
9. For invariant D, εD satisfies Leibniz since ε is multiplicative. Apply 1 ⊗ ε
   to the invariance equation to get D = D_(εD). This proves the linear bijection
   and its asserted inverse, together with step 8.
10. Expand DE-ED by Leibniz: the cross terms cancel, giving a derivation. The
    equations ΔDE = (1 ⊗ DE)Δ and ΔED = (1 ⊗ ED)Δ show invariance of DE-ED.
11. The commutator Lie algebra on End_k(C) and its closed subspace of invariant
    derivations are supplied by [def-wf-lie-algebra]. Transport through steps 8--9.
    This preserves the given vector space structure and gives D_[v,w] = [D_v,D_w].
12. Finally ε(D_vD_w(c)) = Σ ε(D_v(c₁))w(c₂) = Σ v(c₁)w(c₂) = (v*w)(c).
    Subtract the reversed identity and apply the inverse εD to get [v,w] = v*w-w*v.
-/
theorem finiteOrderConvolutionAndTangentDerivations
    (k : Type u) [Field k] (C : Type v) [CommRing C] [Bialgebra k C] :
    (∃ S : Subalgebra k (WithConv (C →ₗ[k] k)),
      (∀ a : WithConv (C →ₗ[k] k), a ∈ S ↔ a.ofConv ∈ distributions k C) ∧
      (∀ r s : ℕ, ∀ a b : C →ₗ[k] k,
        a ∈ finiteOrder k C r → b ∈ finiteOrder k C s →
          convolution k C a b ∈ finiteOrder k C (r + s)) ∧
      ((1 : WithConv (C →ₗ[k] k)).ofConv = Coalgebra.counit (R := k) (A := C))) ∧
    (∃ e : tangentFunctionals k C ≃ₗ[k] Module.Dual k (augmentationIdeal k C).Cotangent,
      (∀ v : tangentFunctionals k C, ∀ x : augmentationIdeal k C,
        e v ((augmentationIdeal k C).toCotangent x) = v.1 x.1)) ∧
    (∃ M : Submodule k (Derivation k C C),
      (∀ D : Derivation k C C, D ∈ M ↔ invariantDerivation k C D) ∧
      (∃ eD : tangentFunctionals k C ≃ₗ[k] M,
        (∀ v : tangentFunctionals k C,
          (eD v).1.toLinearMap = tangentContraction k C v.1) ∧
        (∀ D : M,
          (eD.symm D).1 = Coalgebra.counit.comp D.1.toLinearMap))) ∧
    (∀ v : tangentFunctionals k C, v.1 ∈ finiteOrder k C 1 ∧ v.1 1 = 0) ∧
    (∀ D E : Derivation k C C,
      invariantDerivation k C D → invariantDerivation k C E →
        invariantDerivation k C ⁅D, E⁆) ∧
    (∃ LR : LieRing (tangentFunctionals k C),
      LR.toAddCommGroup = (inferInstance : AddCommGroup (tangentFunctionals k C)) ∧
      ∃ LA : @LieAlgebra k (tangentFunctionals k C) _ LR,
        HEq LA.toModule (inferInstance : Module k (tangentFunctionals k C)) ∧
        ∀ v w : tangentFunctionals k C,
          (@Bracket.bracket _ _ LR.toBracket v w).1 =
            convolution k C v.1 w.1 - convolution k C w.1 v.1 ∧
          tangentContraction k C (@Bracket.bracket _ _ LR.toBracket v w).1 =
            (tangentContraction k C v.1).comp (tangentContraction k C w.1) -
              (tangentContraction k C w.1).comp (tangentContraction k C v.1)) := by
  sorry

end BialgebraDistribution
