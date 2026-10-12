/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Exact.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace WeilConjectures.DerivedTotalResolution

variable {R : Type u} [Ring R]

/-- The total augmentation is injective on homology in every degree.
Source: Stacks Project, Homology, Tag 09IZ, proof.
(blueprint: lem-pc-derived-total-resolution-homology-injective)

Proof. Write A_i = K.X (-i). The short exact sequences of cycles, terms and
images, together with exactness of the term and cycle rows, give exact image
rows. Applying the same argument to boundaries, cycles and homology gives
exact homology rows. Represent a class in the kernel by a total cocycle x,
whose components x_i in A_i^(n+i) have finite support. If its largest index
r is positive, the cocycle equation says x_r is a vertical cycle and its
horizontal image is a vertical boundary. Exactness of the homology row
lifts its class to a vertical cycle y in A_(r+1)^(n+r). Subtract the total
boundary of y, which has degree n-1, to make x_r a vertical boundary.
Subtract the appropriately signed total boundary of a primitive in
A_r^(n+r-1). Its other component has index r-1, so this kills x_r without
creating any component at a larger index. Induction on the finite support
reduces x to a cycle x_0 in A_0^n. Its augmentation is a boundary d_M m.
Lift m through the surjective term map A_0^(n-1) to M^(n-1), obtaining t.
Then x_0-d t is a cycle with augmentation zero. Exactness of the augmented
cycle row lifts it to a cycle b in A_1^n. The total boundary of b is its
horizontal image, and that of t is d t since the positive columns vanish.
Thus x is a total boundary. A linear map with zero kernel is injective. -/
theorem total_resolution_homology_injective
    (M : CochainComplex (ModuleCat R) ℤ)
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (ε : K.total (ComplexShape.up ℤ) ⟶ M)
    (a : K.X 0 ⟶ M)
    [∀ i, (K.total (ComplexShape.up ℤ)).HasHomology i]
    [∀ i, M.HasHomology i]
    [∀ p q, (K.X p).HasHomology q]
    (n : ℤ)
    (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))
    (h_augmentation_zero : ∀ q : ℤ,
      K.ιTotal (ComplexShape.up ℤ) 0 q q (by simp) ≫ ε.f q = a.f q)
    (h_augmentation : ∀ (p q n : ℤ) (hp : p < 0)
      (h : ComplexShape.π (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      K.ιTotal (ComplexShape.up ℤ) p q n h ≫ ε.f n = 0)
    (h_exact : ∀ (p q : ℤ), p < -1 →
      Function.Exact
        ((K.d p (p + 1)).f q).hom
        ((K.d (p + 1) (p + 2)).f q).hom)
    (h_exact_zero : ∀ q : ℤ, Function.Exact
      ((K.d (-1) 0).f q).hom (a.f q).hom)
    (h_surjective : ∀ q : ℤ, Function.Surjective
      (a.f q).hom)
    (h_cycles : ∀ (p q : ℤ), p < -1 →
      Function.Exact
        (HomologicalComplex.cyclesMap (K.d p (p + 1)) q).hom
        (HomologicalComplex.cyclesMap (K.d (p + 1) (p + 2)) q).hom)
    (h_cycles_zero : ∀ q : ℤ, Function.Exact
      (HomologicalComplex.cyclesMap (K.d (-1) 0) q).hom
      (HomologicalComplex.cyclesMap a q).hom)
    (h_cycles_surjective : ∀ q : ℤ, Function.Surjective
      (HomologicalComplex.cyclesMap a q).hom) :
    Function.Injective (HomologicalComplex.homologyMap ε n).hom := by
  sorry

end WeilConjectures.DerivedTotalResolution
