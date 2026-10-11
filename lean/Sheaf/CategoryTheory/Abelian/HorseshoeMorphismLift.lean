/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Lifting a morphism between horseshoe resolutions

Source: the classical horseshoe naturality argument of Weibel, Theorem 2.4.6,
using Stacks Project, Tags 0136, 013R, 013P and 013T
(blueprint: lem-weil-pbc-horseshoe-morphism-lift).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InjectiveResolution

/-- Any prescribed lifts on the outer resolutions extend to a compatible middle lift
between two horseshoe resolutions of a morphism of short exact sequences.
Natural-number indexing encodes vanishing in negative degrees. The zero-composite witnesses
and the degreewise short-exactness hypotheses express the two short exact rows of complexes;
the four augmentation equations, stated as equations of chain maps out of `single₀` as in
`exists_horseshoe_prescribed_resolutions` and Mathlib's `desc_commutes` (equivalent to the
degree-zero equations of the node, `single₀` being concentrated in degree zero), express
their compatibility with the augmentations.

Source: Weibel, Theorem 2.4.6, classical horseshoe naturality calculation, using Stacks
Project, Tags 0136, 013R, 013P and 013T
(blueprint: lem-weil-pbc-horseshoe-morphism-lift).

Proof, Step 1 (lem-weil-pbc-ses-injective-kernel-splits): split both rows degreewise, since
 their first terms are injective. With retraction r of alpha and section sigma' of beta',
set chi = alpha' phiA r + sigma' phiC beta, in ordinary composition order. Then
chi alpha = alpha' phiA and beta' chi = phiC beta.
Step 2 (def-sp-abelian): the differential defect D = d' chi - chi d annihilates alpha and
is annihilated by beta'. Row exactness factors it uniquely as D = alpha' E beta.
Cancelling the monic alpha' and epic beta gives d' E + E d = 0. The augmentation defect
chi^0 sB - sB' b similarly factors uniquely as alpha'^0 e g, and E^0 sC = d' e.
Step 3 (lem-weil-pbc-acyclic-map-to-injective-nullhomotopy): augment IC by C in degree -1.
This augmented complex is acyclic. The maps u^{-1} = e and u^n = (-1)^n E^n define a map
into the bounded-below injective complex with degree m term JA^{m+1}. Tag 013R makes
it null-homotopic. With h^{-1} = 0 and k^n = (-1)^n h^n, the homotopy identities give
e = k^0 sC and E^n = d' k^n - k^{n+1} d.
Step 4: set phiB = chi - alpha' k beta. The last identities kill its differential and
augmentation defects. The zero composites beta' alpha' and beta alpha preserve both outer
squares, so phiB has all three required properties. Existence of the prescribed outer
lifts is supplied separately by lem-weil-pbc-injective-resolution-lift-exists, namely
Mathlib's desc and desc_commutes_zero; this theorem allows any such outer lifts. -/
theorem exists_horseshoe_morphism_lift
    {C : Type u} [Category.{v} C] [Abelian C]
    (S T : ShortComplex C) (hS : S.ShortExact) (hT : T.ShortExact) (F : S ⟶ T)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (JA : InjectiveResolution T.X₁) (JB : InjectiveResolution T.X₂)
    (JC : InjectiveResolution T.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (α' : JA.cocomplex ⟶ JB.cocomplex) (β' : JB.cocomplex ⟶ JC.cocomplex)
    (hαβ : α ≫ β = 0) (hαβ' : α' ≫ β' = 0)
    (hα : IA.ι ≫ α = (CochainComplex.single₀ C).map S.f ≫ IB.ι)
    (hβ : IB.ι ≫ β = (CochainComplex.single₀ C).map S.g ≫ IC.ι)
    (hα' : JA.ι ≫ α' = (CochainComplex.single₀ C).map T.f ≫ JB.ι)
    (hβ' : JB.ι ≫ β' = (CochainComplex.single₀ C).map T.g ≫ JC.ι)
    (hexact : ∀ n : ℕ,
      ((ShortComplex.mk α β hαβ).map
        (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (hexact' : ∀ n : ℕ,
      ((ShortComplex.mk α' β' hαβ').map
        (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (φA : IA.cocomplex ⟶ JA.cocomplex) (φC : IC.cocomplex ⟶ JC.cocomplex)
    (hφA : IA.ι ≫ φA = (CochainComplex.single₀ C).map F.τ₁ ≫ JA.ι)
    (hφC : IC.ι ≫ φC = (CochainComplex.single₀ C).map F.τ₃ ≫ JC.ι) :
    ∃ φB : IB.cocomplex ⟶ JB.cocomplex,
      IB.ι ≫ φB = (CochainComplex.single₀ C).map F.τ₂ ≫ JB.ι ∧
      α ≫ φB = φA ≫ α' ∧ φB ≫ β' = β ≫ φC := by
  sorry

end CategoryTheory.InjectiveResolution
