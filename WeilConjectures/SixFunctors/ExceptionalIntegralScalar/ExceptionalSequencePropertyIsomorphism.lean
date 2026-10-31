/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralScalarMatesData
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated

/-! # Isomorphism invariance of normalized finite-Tor sequence systems

Source: Zheng, Construction 4.1 and Proposition 5.24. The normalization condition
and all four common bounds are invariant under an isomorphism of whole systems.
(blueprint: lem-sf-exceptional-sequence-property-isomorphism)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

private theorem normalized_of_iso (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l)
    (W : Scheme.{u})
    {X Y : coefficientSequenceDerived l E.carrier W} (e : X ≅ Y)
    (hX : IsNormalizedCoefficientSequence l E.carrier W X) :
    IsNormalizedCoefficientSequence l E.carrier W Y := by
  intro m n h P
  let en := (coefficientSequenceDerivedEvaluation l E.carrier W n).mapIso e
  let em := (coefficientSequenceDerivedEvaluation l E.carrier W m).mapIso e
  let G := normalizedDVRRes l E.carrier W h
  have hn := (coefficientSequenceDerivedTransition l E.carrier W h).naturality e.hom
  change em.hom ≫ (coefficientSequenceDerivedTransition l E.carrier W h).app Y =
    (coefficientSequenceDerivedTransition l E.carrier W h).app X ≫ G.map en.hom at hn
  constructor
  · intro x y hxy
    apply (cancel_epi en.hom).1
    apply (hX h P).injective
    change (coefficientSequenceDerivedTransition l E.carrier W h).app X ≫ G.map (en.hom ≫ x) =
      (coefficientSequenceDerivedTransition l E.carrier W h).app X ≫ G.map (en.hom ≫ y)
    change (coefficientSequenceDerivedTransition l E.carrier W h).app Y ≫ G.map x =
      (coefficientSequenceDerivedTransition l E.carrier W h).app Y ≫ G.map y at hxy
    simp only [G.map_comp, ← Category.assoc, ← hn]
    simpa only [Category.assoc] using congrArg (fun k ↦ em.hom ≫ k) hxy
  · intro t
    obtain ⟨s, hs⟩ := (hX h P).surjective (em.hom ≫ t)
    refine ⟨en.inv ≫ s, ?_⟩
    apply (cancel_epi em.hom).1
    change em.hom ≫ (coefficientSequenceDerivedTransition l E.carrier W h).app Y ≫
      G.map (en.inv ≫ s) = em.hom ≫ t
    rw [G.map_comp, ← Category.assoc, hn]
    simp only [Category.assoc, ← G.map_comp, Iso.hom_inv_id_assoc]
    exact hs


/-- The normalized sequence property is invariant under whole-system isomorphisms.
Proof: conjugate the transition Hom bijections by the evaluated isomorphisms.
At every positive finite level, transport constructibility, cohomological bounds
and the same Tor interval along the evaluated isomorphism. The bounds remain
uniform in the level; zero systems and equal-index transitions use the same proof.
Source: Zheng, Construction 4.1 and Proposition 5.24; Stacks Tag 08FZ for Tor amplitude.
(blueprint: lem-sf-exceptional-sequence-property-isomorphism) -/
theorem sequenceProperty_transport_of_iso
    (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l) (T : Scheme.{u})
    {M N : coefficientSequenceDerived l E.carrier T} (e : M ≅ N)
    (hM : sequenceProperty l E T M) : sequenceProperty l E T N := by
  obtain ⟨a, b, c, d, hab, hcd, h⟩ := hM.2
  refine ⟨normalized_of_iso l E T e hM.1, a, b, c, d, hab, hcd, ?_⟩
  intro n
  let en := (coefficientSequenceDerivedEvaluation l E.carrier T n).mapIso e
  obtain ⟨hf, hge, hle, htor⟩ := h n
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) T) :=
    (finite_ctf_isTriangulated l E.carrier (n + 1) (Nat.succ_pos n) T).1
  have := hge
  have := hle
  refine ⟨ObjectProperty.prop_of_iso _ en hf,
    DerivedCategory.TStructure.t.isGE_of_iso en a,
    DerivedCategory.TStructure.t.isLE_of_iso en b, htor.1, ?_⟩
  intro A P hA f hf hP Q i hi
  exact htor.2 A P (hA.map (fun q ↦ q ≪≫ en.symm)) f hf hP Q i hi

end WeilConjectures.ExceptionalIntegralScalar
