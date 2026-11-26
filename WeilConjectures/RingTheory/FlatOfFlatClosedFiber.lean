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
import WeilConjectures.RingTheory.NoetherianFlatClosedFiberModel
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import WeilConjectures.RingTheory.FlatAndFlatOfFlatFibreNoetherian

/-!
# Flatness from flatness over the base and on the closed fibre

Let `R → S → S'` be local homomorphisms of local rings, with `S` and `S'` essentially of finite
presentation over `R`, and let `M` be a nonzero finitely presented `S'`-module, flat over `R`,
whose closed fibre `M / m_R M` is flat over `S / m_R S`. Then `S` is flat over `R` and `M` is
flat over `S`.

## Implementation details

The proof writes the data as a filtered limit of Noetherian local models `R_λ → S_λ → S'_λ`
with finite modules `M_λ`. Flatness of `M` over `R` and of the closed fibre descend to some
stage, where the Noetherian fibre criterion applies; flatness then passes back to `R → S` and
to `M` because each step is a base change followed by a localization. All scalar towers
express restriction along the given local homomorphisms.

## References

* [Stacks, Tag 00R7]
* [Stacks, Tag 00MP]
-/

@[expose] public section

universe u v w t p q

open scoped TensorProduct

namespace Module

/-- The fibre criterion for flatness: let `R → S → S'` be local homomorphisms of local rings
with `S` and `S'` essentially of finite presentation over `R`, and let `M` be a nonzero finitely
presented `S'`-module that is flat over `R`. If the closed fibre `M / m_R M` is flat over
`S / m_R S`, then `S` is flat over `R` and `M` is flat over `S`.

Here `S` is a localization of the finitely presented `R`-algebra `P` at `W`, and `S'` of `Q` at
`V`; the closed fibre module is written as `(S / m_R S) ⊗[S] M`. -/
theorem flat_of_flat_closedFiber
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
    [Module.FinitePresentation S' M] [Nontrivial M]
    (h_fibre : Module.Flat
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      ((S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) ⊗[S] M))
    [Module.Flat R M] : Module.Flat R S ∧ Module.Flat S M := by
  obtain ⟨R₀, S₀, T₀, N₀,
    instR₀, instS₀, instT₀, locR₀, locS₀, locT₀, noethR₀, noethS₀, noethT₀,
    algRS₀, algST₀, algRT₀, towerRST₀, localRS₀, localST₀,
    groupN₀, modTN₀, modSN₀, modRN₀, towerSTN₀, towerRSN₀, algR₀R, algS₀S,
    hfinite, hbase, hfibre, ⟨U, ⟨eS⟩⟩, hM⟩ :=
    exists_noetherian_flat_closedFiber_model R S S' M P Q W V h_fibre
  have : Module.Finite T₀ N₀ := hfinite
  obtain ⟨modCN₀, towerSCN₀, V₀, ⟨eM⟩⟩ := hM
  have : Nontrivial N₀ := by
    by_contra h
    have : Subsingleton N₀ := not_nontrivial_iff_subsingleton.mp h
    have : Subsingleton (LocalizedModule V₀ (S ⊗[S₀] N₀)) := inferInstance
    exact not_subsingleton M (eM.symm.injective.subsingleton)
  have : Module.Flat R₀ N₀ := hbase
  obtain ⟨hS₀, hN₀⟩ := flat_and_flat_of_flat_fibre_noetherian R₀ S₀ T₀ N₀ hfibre
  have : Module.Flat R₀ S₀ := hS₀
  have : Module.Flat S₀ N₀ := hN₀
  have hRS : Module.Flat R (R ⊗[R₀] S₀) := inferInstance
  have hlocS : Module.Flat R (LocalizedModule U (R ⊗[R₀] S₀)) :=
    Flat.localizedModule_of_algebra U hRS
  have hS : Module.Flat R S := (Flat.equiv_iff eS).mp hlocS
  have hSN : Module.Flat S (S ⊗[S₀] N₀) := inferInstance
  have hlocM : Module.Flat S (LocalizedModule V₀ (S ⊗[S₀] N₀)) :=
    Flat.localizedModule_of_algebra V₀ hSN
  exact ⟨hS, (Flat.equiv_iff eM).mp hlocM⟩

end Module
