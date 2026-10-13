/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.RingTheory.Depth

import Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatTargetLocus
import Sheaf.AlgebraicGeometry.Morphisms.PuncturedLocalPurityFiniteFlatFiber

/-!
# Flatness of a supplied depth-two extension under local purity

Source: Stacks Project, Tags 0EY7 and 0EY6(2).
(blueprint: lem-sbc-local-purity-depth-two-finite-flat-stalk)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem exists_minimal_boundary (S : Scheme.{u}) (U : S.Opens) (hU : U ≠ ⊤) :
    ∃ s : S, s ∉ U ∧ ∀ t : S, t ⤳ s → t ∉ U → t = s := by
  classical
  have hne : (U : Set S)ᶜ.Nonempty := by
    by_contra h
    apply hU
    apply top_unique
    intro x _
    by_contra hx
    exact h ⟨x, hx⟩
  let B := (U : Set S)ᶜ
  let : Nonempty B := hne.to_subtype
  have hB : IsClosed B := U.isOpen.isClosed_compl
  let : QuasiSober B := hB.isClosedEmbedding_subtypeVal.quasiSober
  let x : B := Classical.choice inferInstance
  let s := genericPoints.ofComponent
    (⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩)
  refine ⟨s.1.1, s.1.2, ?_⟩
  intro t hts ht
  let t' : B := ⟨t, ht⟩
  have hts' : t' ⤳ s.1 := (Topology.IsInducing.subtypeVal.specializes_iff).mp hts
  have hcl : closure ({s.1} : Set B) ⊆ closure ({t'} : Set B) :=
    hts'.closure_subset
  have heq : closure ({s.1} : Set B) = closure ({t'} : Set B) :=
    le_antisymm hcl (s.2.2 isIrreducible_singleton.closure hcl)
  exact congrArg Subtype.val ((isGenericPoint_closure (x := t')).eq
    (heq ▸ isGenericPoint_closure (x := s.1)))

/-- Local purity makes a supplied finite depth-two extension flat.

Source: Stacks Project, Tag 0EY7, `pione-lemma-purity-essentially-surjective`,
and Tag 0EY6(2),(3), `pione-lemma-extend-S2`.
(blueprint: lem-sbc-local-purity-depth-two-finite-flat-stalk)

Proof: The finite flat target locus W is open and contains V, by the stalk
isomorphisms for open restriction. If W is not all of L, take a generic
point s of an irreducible component of its closed complement. Every proper
generalization t of s belongs to W, by maximality of that component and
sobriety. Thus every stalk over t is flat. Since s is outside V, hdepth gives
target depth at least two at s and hpurity gives punctured-spectrum purity.
Apply the local pure-fibre theorem to deduce flatness at every point above
s. This says s belongs to W, a contradiction. Hence W is all of L and all
source stalks are flat, so the stalk criterion gives Flat p. This closed-complement
argument does not need global quasi-compactness or quasi-separatedness. Empty sources give
W = L, and V = L is likewise immediate. -/
theorem flat_of_local_purity_depth_two_finite_extension
    {L E : Scheme.{u}} [IsLocallyNoetherian L] (V : L.Opens)
    (hdepth : ∀ y : L, y ∉ V →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y) (L.presheaf.stalk y))
    (hpurity : ∀ y : L, y ∉ V →
      ∀ (U : (Spec (L.presheaf.stalk y)).Opens),
        (∀ x : Spec (L.presheaf.stalk y),
          x ∈ U ↔ x ≠ IsLocalRing.closedPoint (L.presheaf.stalk y)) →
        ∀ (Z : Scheme.{u}) (q : Z ⟶ U.toScheme), IsFinite q → Etale q →
          ∃ (F : Scheme.{u}) (r : F ⟶ Spec (L.presheaf.stalk y)),
            IsFinite r ∧ Etale r ∧
              ∃ e : Z ≅ (r ⁻¹ᵁ U).toScheme, e.hom ≫ r ∣_ U = q)
    (p : E ⟶ L) [IsFinite p] [Etale (p ∣_ V)]
    (hsource : ∀ z : E, p z ∉ V →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z)) :
    Flat p := by
  classical
  let W : L.Opens := ⟨{y | ∀ x : E, p x = y → (p.stalkMap x).hom.Flat},
    isOpen_setOf_finite_flat_stalks p⟩
  have hVW : V ≤ W := by
    intro y hy x hx
    let xV : (p ⁻¹ᵁ V).toScheme := ⟨x, by change p x ∈ V; rwa [hx]⟩
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap p V xV)).mp (Flat.stalkMap (p ∣_ V) xV)
  have hW : W = ⊤ := by
    by_contra hne
    obtain ⟨s, hs, hmin⟩ := exists_minimal_boundary L W hne
    have hsV : s ∉ V := fun hsV ↦ hs (hVW hsV)
    have hsflat : ∀ x : E, p x = s → (p.stalkMap x).hom.Flat := by
      apply flat_fibre_of_punctured_local_purity V p hsource s hsV
        (hdepth s hsV) (hpurity s hsV)
      intro t hts hne x hx
      have ht : t ∈ W := by
        by_contra ht
        exact hne (hmin t hts ht)
      exact ht x hx
    exact hs hsflat
  apply Flat.of_stalkMap
  intro z
  have hpz : p z ∈ W := by rw [hW]; trivial
  exact hpz z rfl

end AlgebraicGeometry.Scheme
