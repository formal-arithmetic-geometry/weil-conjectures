/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.RingTheory.LocalizedApproximationColimits
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.Localization.BaseChange

/-! # Transition base changes after localization at compatible primes

Source: Stacks Project, Algebra, Tag 02JO, first paragraph, and Tag 00QX.
(blueprint: lem-pc-localized-approximation-base-change)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

/-- Localization of transition tensor isomorphisms gives a localization of ring
base change and an isomorphism of module base change. It uses no colimit or flatness.

Source: Stacks Project, Algebra, Tag 02JO, first paragraph; Tag 00QX.
(blueprint: lem-pc-localized-approximation-base-change)

Proof:
1. For i to j, write p_i and q_i for the contracted primes of A_i and B_i.
   The local map A_i,p_i to B_i,q_i and both transition maps are the canonical
   fraction maps. The original tensor formula shows that their square commutes.
2. Apply tensor-localization compatibility to the original isomorphism
   B_i tensor over A_i with A_j to B_j. First invert the images of the complements
   of p_i and q_i, and then those of p_j in A_j. The result identifies
   B_i,q_i tensor over A_i,p_i with A_j,p_j with the localization of B_j at the
   corresponding multiplicative set. These elements avoid q_j by naturality.
3. Further invert every element of B_j outside q_j. The composite localization
   is B_j,q_j. Its preimage multiplicative set in the preceding tensor product
   gives W, and the composite comparison gives the displayed ring homomorphism.
   The original pure-tensor formula, followed by localization, gives its formula.
4. Localize B_j tensor over B_i with D_i to D_j at the complement of q_j.
   Since each element outside q_i maps outside q_j, the localized tensor factors
   through D_i,q_i. Tensor-localization compatibility and cancellation identify
   its domain with B_j,q_j tensor over B_i,q_i with D_i,q_i. This gives the
   displayed linear equivalence, with its pure-tensor formula inherited from the
   original equivalence. This holds also for zero modules and identity transitions.
-/
theorem localized_approximation_baseChange
    {S : Type u} [CommRing S]
    {Λ : Type u} [Preorder Λ]
    (A B : Λ ⥤ CommRingCat.{u}) (η : A ⟶ B)
    (κ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S))
    (D : Λ ⥤ AddCommGrpCat.{v}) [∀ i : Λ, Module (B.obj i) (D.obj i)]
    (hs : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : D.obj i),
      (D.map f).hom (b • x) = (B.map f).hom b • (D.map f).hom x)
    (hring : ∀ (i j : Λ) (f : i ⟶ j),
      letI := (η.app i).hom.toAlgebra
      letI := (A.map f).hom.toAlgebra
      ∃ e : B.obj i ⊗[A.obj i] A.obj j ≃+* B.obj j,
        ∀ (x : B.obj i) (y : A.obj j),
          e (x ⊗ₜ[A.obj i] y) = (B.map f).hom x * (η.app j).hom y)
    (hmodule : ∀ (i j : Λ) (f : i ⟶ j),
      letI := (B.map f).hom.toAlgebra
      ∃ e : B.obj j ⊗[B.obj i] D.obj i ≃ₗ[B.obj j] D.obj j,
        ∀ (y : B.obj j) (x : D.obj i),
          e (y ⊗ₜ[B.obj i] x) = y • (D.map f).hom x)
    (q : PrimeSpectrum S) :
    let Aq := primeRingDiagram A (η ≫ κ) q
    let Bq := primeRingDiagram B κ q
    let Nq := primeModuleDiagram B κ q D hs
    (∀ (i j : Λ) (f : i ⟶ j),
      letI := (primeDiagramHom A B η κ q i).toAlgebra
      letI := (Aq.map f).hom.toAlgebra
      ∃ (t : Bq.obj i ⊗[Aq.obj i] Aq.obj j →+* Bq.obj j)
        (W : Submonoid (Bq.obj i ⊗[Aq.obj i] Aq.obj j)),
        (∀ (b : Bq.obj i) (a : Aq.obj j),
          t (b ⊗ₜ[Aq.obj i] a) =
            (Bq.map f).hom b * primeDiagramHom A B η κ q j a) ∧
        (letI := t.toAlgebra; IsLocalization W (Bq.obj j))) ∧
    (∀ (i j : Λ) (f : i ⟶ j),
      letI := (Bq.map f).hom.toAlgebra
      ∃ e : Bq.obj j ⊗[Bq.obj i] Nq.obj i ≃ₗ[Bq.obj j] Nq.obj j,
        ∀ (b : Bq.obj j) (x : Nq.obj i),
          e (b ⊗ₜ[Bq.obj i] x) = b • (Nq.map f).hom x) := by sorry

end Algebra
