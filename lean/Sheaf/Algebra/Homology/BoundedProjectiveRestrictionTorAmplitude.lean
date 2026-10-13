/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor

/-! # Tor amplitude after restricting a bounded projective complex

Source: Stacks Project, Tag 0B6G, lemma-perfect-proper-perfect-direct-image,
condition (3); More on Algebra, Tags 066H, 066K and 0655.
(blueprint: lem-pc-bounded-projective-restriction-tor-amplitude).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A bounded complex of projective B-modules acquires amplitude [r-d,s] over A
when the regular B-module has Tor dimension at most d over A.

Source: Stacks Project, Tag 0B6G, lemma-perfect-proper-perfect-direct-image,
condition (3); More on Algebra, Tags 066H, 066K and 0655.
(blueprint: lem-pc-bounded-projective-restriction-tor-amplitude).

Proof: fix an A-module M and take a free resolution F in nonpositive cochain
degrees. Being bounded above and flat, F is K-flat, so the derived tensor is
computed by Tot(C tensor_A F). Tensor balancing identifies the double complex
with C tensor_B (B tensor_A F). Tensoring with the projective B-module C^p is
exact; its column homology is C^p tensor_B Tor^A_{-q}(B,M). This vanishes for
q>0 or q<-d. Filter the total complex by C-degree. This filtration is finite
because C is bounded, and its spectral sequence has the computed column
homology on its first page. For total degree n<r-d or s<n every first-page
term is zero: either p is outside [r,s], or q=n-p is outside [-d,0]. All later
pages and the finite filtration's associated graded pieces are zero, hence
its total homology is zero. If r>s every term of C is zero, since for any t
either t<r or s<t. The total complex is then zero in every degree. No finite
generation condition on the projective terms or on the ring map is needed. -/
theorem boundedProjective_restriction_torAmplitude
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (C : CochainComplex (ModuleCat.{u} B) ℤ)
    (r s : ℤ) (hdegrees : ∀ t : ℤ, t < r ∨ s < t → IsZero (C.X t))
    (hprojective : ∀ t : ℤ, Projective (C.X t)) (d : ℕ)
    (hTor : ∀ M : ModuleCat.{u} A, ∀ j : ℕ, d < j →
      IsZero (((Tor' (ModuleCat.{u} A) j).obj
        ((ModuleCat.restrictScalars ρ).obj (ModuleCat.of B B))).obj M)) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u} A) (r - (d : ℤ)) s
      (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).obj C)) := by sorry

end CochainComplex
