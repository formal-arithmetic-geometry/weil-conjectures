/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.RingTheory.NoetherianLocalModelTowerExistence
import WeilConjectures.RingTheory.NoetherianLocalModelTowerBaseFlat
import WeilConjectures.RingTheory.NoetherianLocalModelTowerFiberFlat

/-!
# A common Noetherian stage for base and closed-fibre flatness

A flat module over a local homomorphism of essentially finitely presented local algebras has a
Noetherian model at which both the base module and the closed-fibre module are flat.

## Implementation details

The model comes from the limit tower for essentially finite presentation, after lifting rings
to a common universe. Flatness at one stage is obtained from eventual flatness of colimits,
first for the given system and then for the system of closed fibres, and persists at later stages
by base change and localization. No nonzero hypothesis is needed.

## References

* [Stacks, Tag 00R7] (first two paragraphs of the proof)
-/

@[expose] public section

universe u v w t p q

open scoped TensorProduct

namespace Module

/-- A Noetherian model `R₀ → S₀ → T₀` with finite module `N₀` at which the base module and the
closed-fibre module are flat, together with identifications of `S` and `M` with localizations of
the appropriate base changes.

This asserts the inputs to the Noetherian fibre criterion, not its conclusions: it does not
assert flatness of `S₀` over `R₀` or of `N₀` over `S₀`. -/
theorem exists_noetherian_flat_closedFiber_model
    (R : Type u) (S : Type v) (S' : Type w) (M : Type t)
    [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [AddCommGroup M] [Module S' M] [Module S M] [Module R M]
    [IsScalarTower S S' M] [IsScalarTower R S M]
    (P : Type p) (Q : Type q) [CommRing P] [CommRing Q]
    [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Algebra R Q] [Algebra Q S'] [IsScalarTower R Q S']
    [Algebra.FinitePresentation R P] [Algebra.FinitePresentation R Q]
    (W : Submonoid P) (V : Submonoid Q) [IsLocalization W S] [IsLocalization V S']
    [Module.FinitePresentation S' M]
    (h_fibre : Module.Flat
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      ((S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) ⊗[S] M))
    [Module.Flat R M] :
    ∃ (R₀ S₀ T₀ : Type (max u v w)) (N₀ : Type t)
      (_ : CommRing R₀) (_ : CommRing S₀) (_ : CommRing T₀)
      (_ : IsLocalRing R₀) (_ : IsLocalRing S₀) (_ : IsLocalRing T₀)
      (_ : IsNoetherianRing R₀) (_ : IsNoetherianRing S₀)
      (_ : IsNoetherianRing T₀)
      (_ : Algebra R₀ S₀) (_ : Algebra S₀ T₀) (_ : Algebra R₀ T₀)
      (_ : IsScalarTower R₀ S₀ T₀)
      (_ : IsLocalHom (algebraMap R₀ S₀)) (_ : IsLocalHom (algebraMap S₀ T₀))
      (_ : AddCommGroup N₀) (_ : Module T₀ N₀) (_ : Module S₀ N₀)
      (_ : Module R₀ N₀) (_ : IsScalarTower S₀ T₀ N₀)
      (_ : IsScalarTower R₀ S₀ N₀)
      (_ : Algebra R₀ R) (_ : Algebra S₀ S),
      Module.Finite T₀ N₀ ∧ Module.Flat R₀ N₀ ∧
      Module.Flat
        (S₀ ⧸ Ideal.map (algebraMap R₀ S₀) (IsLocalRing.maximalIdeal R₀))
        ((S₀ ⧸ Ideal.map (algebraMap R₀ S₀) (IsLocalRing.maximalIdeal R₀)) ⊗[S₀] N₀) ∧
      (∃ U : Submonoid (R ⊗[R₀] S₀),
        Nonempty (LocalizedModule U (R ⊗[R₀] S₀) ≃ₗ[R] S)) ∧
      (∃ (_ : Module (S ⊗[S₀] T₀) (S ⊗[S₀] N₀))
        (_ : IsScalarTower S (S ⊗[S₀] T₀) (S ⊗[S₀] N₀))
        (U : Submonoid (S ⊗[S₀] T₀)),
        Nonempty (LocalizedModule U (S ⊗[S₀] N₀) ≃ₗ[S] M)) := by
  obtain ⟨X⟩ := exists_noetherian_localModelTower R S S' M P Q W V
  let := X.preorder
  let := X.directed
  let := X.commR
  let := X.commS
  let := X.commT
  let := X.localR
  let := X.localS
  let := X.localT
  let := X.noethR
  let := X.noethS
  let := X.noethT
  let := X.algRS
  let := X.algST
  let := X.algRT
  let := X.towerRST
  let := X.localRS
  let := X.localST
  let := X.addN
  let := X.moduleT
  let := X.moduleS
  let := X.moduleR
  let := X.towerSTN
  let := X.towerRSN
  let := X.algRLimit
  let := X.algSLimit
  obtain ⟨i, hi⟩ := X.eventually_baseFlat
  obtain ⟨j, hj⟩ := X.eventually_fiberFlat h_fibre
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  exact ⟨X.R₀ k, X.S₀ k, X.T₀ k, X.N₀ k,
    X.commR k, X.commS k, X.commT k, X.localR k, X.localS k, X.localT k,
    X.noethR k, X.noethS k, X.noethT k, X.algRS k, X.algST k, X.algRT k,
    X.towerRST k, X.localRS k, X.localST k, X.addN k, X.moduleT k, X.moduleS k,
    X.moduleR k, X.towerSTN k, X.towerRSN k, X.algRLimit k, X.algSLimit k,
    X.finite k, hi k hik, hj k hjk, X.baseLocalization k, X.moduleLocalization k⟩

end Module
