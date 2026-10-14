/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatTargetLocus
import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Flatness near a point from a flat test

Source: Stacks Project, Tag 0EYJ, flatness descent and openness.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TensorProduct
namespace AlgebraicGeometry.Scheme

/-- A finite morphism is flat over a neighbourhood of x if a flat test through x
makes its pullback flat. This isolates descent and openness from the formal
splitting calculation.

Source: Stacks Project, Tag 0EYJ, final flatness descent and neighbourhood argument.
(blueprint: lem-sbc-stalk-normalization-depth-two-section-flat-core)

Proof: Lift every source point over x to the pullback using the specified test
point. The local map of the projection is flat and local, hence faithfully flat.
The composite stalk map is flat. Faithful flatness reflects tensor injectivity,
so the original stalk map is flat. The finite flat target locus is open and
contains x; restrict the morphism to that open and apply the stalk criterion. -/
theorem stalk_normalization_depth_two_section_flat_core
    {L E T : Scheme.{u}} [IsLocallyNoetherian L]
    (p : E ⟶ L) [IsFinite p] (t : T ⟶ L)
    [Flat t] [Flat (pullback.snd p t)] (x : L) (b : T) (hb : t b = x) :
    ∃ W : L.Opens, x ∈ W ∧ Flat (p ∣_ W) := by
  -- Point lifting follows from hb; no rational-section hypothesis is needed for descent.
  -- The argument proceeds by stalkwise faithful-flat descent.
  classical
  let F : Set L := {y | ∀ z, p z = y → (p.stalkMap z).hom.Flat}
  let W : L.Opens := ⟨F, isOpen_setOf_finite_flat_stalks p⟩
  refine ⟨W, ?_, ?_⟩
  · intro z hz
    obtain ⟨w, hw, _⟩ :=
      Pullback.exists_preimage_pullback (f := p) (g := t) z b (hz.trans hb.symm)
    let g := Limits.pullback.fst p t
    have hcomp : ((g ≫ p).stalkMap w).hom.Flat := by
      rw [Limits.pullback.condition, Hom.stalkMap_comp, CommRingCat.hom_comp]
      exact (Flat.stalkMap t _).comp (Flat.stalkMap (Limits.pullback.snd p t) w)
    rw [Hom.stalkMap_comp, CommRingCat.hom_comp] at hcomp
    have hg : (g.stalkMap w).hom.FaithfullyFlat := by
      algebraize [(g.stalkMap w).hom]
      have : Module.Flat _ _ := Flat.stalkMap g w
      have : IsLocalHom (algebraMap (E.presheaf.stalk (g w))
          ((Limits.pullback p t).presheaf.stalk w)) :=
        inferInstanceAs (IsLocalHom (g.stalkMap w).hom)
      exact Module.FaithfullyFlat.of_flat_of_isLocalHom
    have hp : (p.stalkMap (g w)).hom.Flat := by
      let R := L.presheaf.stalk (p (g w))
      let A := E.presheaf.stalk (g w)
      let B := (pullback p t).presheaf.stalk w
      let f : R →+* A := (p.stalkMap (g w)).hom
      let g : A →+* B := (g.stalkMap w).hom
      have hfg : (g.comp f).Flat := hcomp
      have hg : g.FaithfullyFlat := hg
      algebraize [f, g, g.comp f]
      have : Module.Flat R B := hfg
      have : Module.FaithfullyFlat A B := hg
      exact Module.Flat.of_flat_of_faithfullyFlat (A := R) (B := A) (C := B)
    change g w = z at hw
    rw [hw] at hp
    exact hp
  · apply Flat.of_stalkMap
    intro z
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap p W z)).mpr (z.2 z.1 rfl)

end AlgebraicGeometry.Scheme
