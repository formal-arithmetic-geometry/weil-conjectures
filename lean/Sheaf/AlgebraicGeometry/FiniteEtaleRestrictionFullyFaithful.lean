/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-! # Full faithfulness of finite étale restriction
Source: corrected blueprint thm-weil-pbc-finite-etale-lifting, proof steps 1–6;
Stacks Project, Tags 0GS2 (the result) and 0A0B (clopen restriction).
(blueprint: lem-weil-pbc-finite-etale-restriction-fully-faithful)
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Finite étale restriction is fully faithful over a proper henselian pair.
Source: corrected blueprint thm-weil-pbc-finite-etale-lifting, proof steps 1–6;
Stacks Project, Tags 0GS2 (the result) and 0A0B (clopen restriction).
(blueprint: lem-weil-pbc-finite-etale-restriction-fully-faithful)

Proof: For finite étale U,V over Y, morphisms U → V over Y correspond to sections of
P = V ×[Y] U → U. A section of this finite étale separated morphism is an open and
closed immersion; conversely a clopen W in P whose projection to U is an isomorphism
recovers a unique section. These correspondences commute with base change. The schemes
U and P are proper over A. Clopen restriction for proper henselian schemes lifts a
clopen W₀ in P₀ uniquely to W in P. Its projection is finite étale. Its rank-one locus
is clopen in U and contains U₀ because W₀ → U₀ is an isomorphism; the complementary
clopen misses U₀, hence is empty by injectivity of clopen restriction. The projection
therefore has rank one everywhere, so is an isomorphism. Thus restriction induces a
bijection on sections, hence on every Hom set. This is full faithfulness. Empty U or V
cause no exception: the same clopen and rank argument applies to empty schemes. -/
theorem Scheme.fullyFaithful_pullback_finiteEtale_of_henselianRing
    (hstable : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange)
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f] (i : Y₀ ⟶ Y)
    (f₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :
    letI := hstable
    Nonempty (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).FullyFaithful := by sorry

end AlgebraicGeometry
