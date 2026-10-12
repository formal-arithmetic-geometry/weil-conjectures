/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Sheaf.RingTheory.FormallySmoothAdic
import Sheaf.RingTheory.CompleteLocalQuotient
import Sheaf.RingTheory.FiniteOverCompleteRing
import Sheaf.RingTheory.FormallySmoothAdicLift
import Sheaf.RingTheory.FormallySmoothAdicLiftIntoComplete

/-!
# Lifting over a finite coefficient map

Source: Stacks Project, More on Algebra, Remark 07NS (parts (3), (4)),
Lemmas 07NR and 07NJ, and Proposition 07PM.
(blueprint: lem-weil-pbc-fs-adic-lift-over-finite-coefficient-map)
-/

@[expose] public section

universe u v w

namespace RingHom

/-- Lifting a formally smooth complete local algebra along a finite coefficient map.

Source: Stacks Project, More on Algebra, Remark 07NS (parts (3), (4)),
Lemmas 07NR and 07NJ, and Proposition 07PM.
(blueprint: lem-weil-pbc-fs-adic-lift-over-finite-coefficient-map)

Proof (the eight steps of the node):
1. The closed fibre E = B/m_A B is complete Noetherian local by
   `lem-weil-pbc-complete-local-quotient`. Its maximal ideal is the image of m_B.
   The induced residue-field isomorphism transports its formal smoothness over
   k = A/m_A to k₀ = A₀/m₀ (`def-weil-pbc-formally-smooth-adic`).
2. Apply `lem-weil-pbc-fs-adic-lift-from-residue-field` to A₀ and E. Obtain a
   complete Noetherian local C, a local formally smooth γ : A₀ → C, and an
   A₀-algebra isomorphism C/m₀C ≅ E. The resulting θ : C → E is surjective,
   has kernel m₀C, and maps m_C onto the maximal ideal of E.
3. Apply `lem-weil-pbc-fs-adic-lift-into-complete` to lift θ through B → E.
   The ideal m_A B lies in m_B and is m_B-adically closed by
   `lem-weil-pbc-krull-intersection-jacobson`. The lift ψ is an A₀-algebra map,
   hence ψγ = φα, and is local because θ maps m_C into the maximal ideal of E.
4. The finite k₀-algebra A/m₀A is Artinian local. By
   `lem-weil-pbc-artinian-local-noetherian-nilpotent`, some positive power
   of m_A is contained in m₀A (`def-weil-finitely-generated-module`).
5. Form D = C ⊗[A₀] A and Φ(c ⊗ a) = ψ(c)φ(a), using
   `lem-weil-pbc-algebra-tensor-pushout-universal-property` and
   `def-weil-module-base-change`. Finite module generators of A give finite
   C-module generators of D. By `lem-weil-pbc-finite-algebra-noetherian` and
   `lem-weil-pbc-finite-algebra-local-radical`, D is Noetherian and m_C D is
   in every maximal ideal. Step 4 then puts m_A D in the Jacobson radical.
6. Since θ is onto, B = ψ(C) + m_A B. Iterating and using Step 4 gives
   B = Φ(D) + m_C B. The images of the chosen finite generators generate
   B/m_C B. Locality of ψ and `lem-weil-pbc-krull-intersection-jacobson`
   make B m_C-adically separated. By `lem-weil-pbc-finite-over-complete-ring`,
   those images generate B over C; thus Φ is surjective.
7. Put K = ker Φ. Flatness of B over A (`def-weil-pbc-flat-ring-map`) and
   `lem-weil-pbc-flat-quotient-tensor-injective` make K/m_A K inject into
   D/m_A D. The latter maps isomorphically to E: residue surjectivity reduces
   every tensor to c ⊗ 1, and θ(c) = 0 means c ∈ m₀C, hence c ⊗ 1 ∈ m_A D.
   Therefore K/m_A K = 0. Since D is Noetherian and m_A D lies in its
   Jacobson radical, `lem-weil-pbc-nakayama-jacobson` gives K = 0.
8. Thus Φ is bijective, yielding the required ring isomorphism, with C, γ,
   and ψ having all the properties from Steps 2 and 3.
-/
theorem exists_fs_adic_lift_over_finite_coefficient_map
    {A₀ : Type u} {A : Type v} {B : Type w}
    [CommRing A₀] [CommRing A] [CommRing B]
    [Algebra A₀ A] [Algebra A B]
    [IsNoetherianRing A₀] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A₀] [IsLocalRing A] [IsLocalRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A₀) A₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (α : A₀ →+* A) (hα : algebraMap A₀ A = α) [IsLocalHom α]
    [Module.Finite A₀ A]
    (hres : Function.Bijective (IsLocalRing.ResidueField.map α))
    (φ : A →+* B) (hφ : algebraMap A B = φ) [IsLocalHom φ] (hflat : RingHom.Flat φ) :
    letI : Algebra (IsLocalRing.ResidueField A)
        (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)) :=
      Ideal.Quotient.algebraQuotientOfLEComap
        (Eq.mpr (congrArg (fun f : A →+* B => IsLocalRing.maximalIdeal A ≤
          (Ideal.map φ (IsLocalRing.maximalIdeal A)).comap f) hφ)
          Ideal.le_comap_map)
    Algebra.FormallySmoothAdic (IsLocalRing.ResidueField A)
      (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A))
      (Ideal.map (Ideal.Quotient.mk (Ideal.map φ (IsLocalRing.maximalIdeal A)))
        (IsLocalRing.maximalIdeal B)) →
    ∃ (C : Type (max u v w)) (_ : CommRing C) (_ : IsLocalRing C)
      (_ : Algebra A₀ C),
      IsNoetherianRing C ∧
      IsAdicComplete (IsLocalRing.maximalIdeal C) C ∧
      ∃ (γ : A₀ →+* C),
        algebraMap A₀ C = γ ∧ IsLocalHom γ ∧
        Algebra.FormallySmoothAdic A₀ C (IsLocalRing.maximalIdeal C) ∧
        ∃ (ψ : C →+* B),
          IsLocalHom ψ ∧ ψ.comp γ = φ.comp α ∧
          ∃ F : RingHom (TensorProduct A₀ C A) B,
            Function.Bijective F ∧
            ∀ c a, F (TensorProduct.tmul A₀ c a) = ψ c * φ a := by
  sorry

end RingHom
