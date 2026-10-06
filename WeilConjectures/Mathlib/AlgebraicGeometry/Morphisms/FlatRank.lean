/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Fibres of finite flat morphisms

A fibre of a finite flat morphism `f : X ⟶ Y` over a point `y` has at most
`Scheme.Hom.finrank f y` points.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A scheme which is finite and flat over the spectrum of a field `K` is finite, with at most
as many points as the rank. -/
lemma Scheme.Hom.finite_and_card_le_finrank_of_field {K : Type u} [Field K]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K)) [IsFinite g] [Flat g] (z : Spec (.of K)) :
    Finite Z ∧ Nat.card Z ≤ g.finrank z := by
  have : IsAffine Z := isAffine_of_isAffineHom g
  let e := Scheme.homeoOfIso Z.isoSpec
  rw [← finrank_comp_left_of_isIso Z.isoSpec.inv, Nat.card_congr e.toEquiv,
    e.toEquiv.finite_iff]
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ g)
  have h₁ : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  have h₂ : φ.hom.Flat := by
    rw [← Flat.SpecMap_iff, hφ]
    infer_instance
  rw [← hφ, finrank_SpecMap_eq_finrank h₁ h₂]
  algebraize [φ.hom]
  have : IsArtinianRing Γ(Z, ⊤) := .of_finite K Γ(Z, ⊤)
  rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap,
    Module.rankAtStalk_eq_finrank_of_free]
  exact ⟨inferInstanceAs (Finite (PrimeSpectrum Γ(Z, ⊤))),
    IsArtinianRing.card_primeSpectrum_le_finrank K Γ(Z, ⊤)⟩

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (y : Y) :
    IsFinite (f.fiberToSpecResidueField y) :=
  inferInstanceAs (IsFinite (pullback.snd f (Y.fromSpecResidueField y)))

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (y : Y) :
    Flat (f.fiberToSpecResidueField y) :=
  inferInstanceAs (Flat (pullback.snd f (Y.fromSpecResidueField y)))

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]

/-- A fibre of a finite flat morphism `f` over `y` has at most `f.finrank y` points: it is the
spectrum of an algebra of dimension `f.finrank y` over the residue field of `y`. -/
lemma Scheme.Hom.ncard_preimage_singleton_le_finrank (y : Y) :
    (f ⁻¹' {y}).ncard ≤ f.finrank y := by
  have h := (finite_and_card_le_finrank_of_field (K := Y.residueField y)
    (f.fiberToSpecResidueField y) (IsLocalRing.closedPoint _)).2
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr (f.fiberHomeo y).toEquiv]
  exact h.trans_eq ((finrank_pullback_snd f (Y.fromSpecResidueField y) _).trans
    (congrArg f.finrank (Y.fromSpecResidueField_apply y _)))

end AlgebraicGeometry
