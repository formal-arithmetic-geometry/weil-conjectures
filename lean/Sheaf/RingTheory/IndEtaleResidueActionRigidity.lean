/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q90
-/
module

public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.RingTheory.MapIntoHenselianColimit

/-! # Residue action rigidity for a local ind-etale algebra

Source: Stacks Project, Fundamental Groups, Tag 0BSW; Algebra, Tag 08HR;
Fields, Tag 030K (blueprint: lem-dl-a1-ind-etale-residue-action-rigidity).

The fields κ, κs and E are the canonical residue fields of H, R and T.
The embedding j is the residue map induced by i. The displayed compatibility
characterizes the restriction homomorphism r, since j is injective.
-/

@[expose] public section

set_option autoImplicit false

universe u v w g

namespace Algebra

open IsLocalRing

/-- Residue restriction detects exactly the automorphisms fixing the embedded local
ind-etale algebra. Pure inseparability is expressed by the p-power condition in
positive characteristic and surjectivity of j in characteristic zero.

Source: Stacks Project, Fundamental Groups, Tag 0BSW (uniqueness with prescribed
residue action), Algebra, Tag 08HR, and Fields, Tag 030K.
(blueprint: lem-dl-a1-ind-etale-residue-action-rigidity).

Proof:
1. Each H-algebra automorphism preserves the maximal ideal, since it preserves
   units and nonunits. Reduction therefore gives its canonical κ-automorphism of E;
   reduction respects composition and identity.
2. By lem-weil-pbc-separable-first-purely-inseparable, E is purely inseparable
   over its separable subfield Es. Identify Es with j(κs): one inclusion uses
   def-pd-separable-closure. For the other, a separable element's minimal polynomial
   remains separable over κs by Bezout, and splits there by def-kun-separably-closed.
   A root in E must equal the image of one of its roots in κs. This yields the
   p-power condition, or E = j(κs) in characteristic zero.
3. Each reduced automorphism fixes κ and thus preserves separable elements and Es.
   Its inverse gives the reverse inclusion. Hence it restricts, via j, to a
   κ-automorphism of κs. Composition and identity give the homomorphism r.
4. If r(γ) = 1, reduction fixes j(κs). In characteristic p, choose n from step 2:
   (γbar(x) - x)^(p^n) = γbar(x^(p^n)) - x^(p^n) = 0, so γbar(x) = x in the field E.
   In characteristic zero step 2 gives this directly. The converse is restriction.
5. If r(γ) = 1, apply lem-weil-pbc-map-into-henselian-colimit to i and γ ∘ i.
   The ind-etale presentation supplies the filtered etale stages; T is henselian;
   locality gives the same maximal-ideal preimage; their residue maps both equal j.
   The uniqueness clause gives γ ∘ i = i.
6. Conversely, if γ ∘ i = i, represent each element of κs by an element of R.
   Reducing the equality shows γbar ∘ j = j, hence r(γ) = 1. Together with steps
   4 and 5 this proves the two equivalences.
-/
theorem indEtale_residue_action_rigidity
    (H : Type u) [CommRing H] [IsLocalRing H]
    (R : Type v) [CommRing R] [IsLocalRing R] [Algebra H R]
    [IsLocalHom (algebraMap H R)]
    (hR : RingHom.IndEtaleAcrossUniverses (algebraMap H R))
    [IsSepClosure (ResidueField H) (ResidueField R)]
    (T : Type w) [CommRing T] [HenselianLocalRing T] [Algebra H T]
    [IsLocalHom (algebraMap H T)]
    [Algebra.IsAlgebraic (ResidueField H) (ResidueField T)]
    (i : R →ₐ[H] T) [IsLocalHom i] (hi : Function.Injective i)
    (Γ : Type g) [Group Γ] (ρ : Γ →* (T ≃ₐ[H] T)) :
    IsPurelyInseparable (ResidueField.mapAlgHom' i).fieldRange (ResidueField T) ∧
    (∀ (p : ℕ), p.Prime → ringChar (ResidueField H) = p →
      ∀ x : ResidueField T, ∃ n : ℕ,
        x ^ (p ^ n) ∈ Set.range (ResidueField.mapAlgHom' i)) ∧
    (ringChar (ResidueField H) = 0 →
      Function.Surjective (ResidueField.mapAlgHom' i)) ∧
    (∀ γ : Γ, Set.MapsTo (ResidueField.mapAlgEquiv' (ρ γ))
      (Set.range (ResidueField.mapAlgHom' i))
      (Set.range (ResidueField.mapAlgHom' i))) ∧
    ∃ r : Γ →* (ResidueField R ≃ₐ[ResidueField H] ResidueField R),
      (∀ (γ : Γ) (x : ResidueField R),
        ResidueField.mapAlgHom' i (r γ x) =
          ResidueField.mapAlgEquiv' (ρ γ) (ResidueField.mapAlgHom' i x)) ∧
      ∀ γ : Γ,
        (r γ = 1 ↔ ResidueField.mapAlgEquiv' (ρ γ) = 1) ∧
        (ResidueField.mapAlgEquiv' (ρ γ) = 1 ↔ ∀ x : R, ρ γ (i x) = i x) := by
  sorry

end Algebra
