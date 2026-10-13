/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectMorphism
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Affine coordinate Tor bounds from stalkwise bounds

Source: Stacks Project, Tag 069C.
(blueprint: lem-pc-affine-sections-finite-tor-of-stalkwise).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finite stalk Tor dimensions give a finite Tor bound for an affine coordinate ring.
Source: Stacks Project, Tag 069C, `lemma-check-perfect-stalks`, (3) implies (1),
and the first sentence of the proof of (1) implies (2).

Proof: put A = Γ(Y,U), B = Γ(X,V). The map A to B induced by f is of finite
type because U and V are affine. A is Noetherian, so a finite polynomial
presentation P = A[t₁,...,tₙ] surjecting onto B makes B a pseudo-coherent
P-module, concentrated in degree zero. For a prime q of P outside the support
of B, B_q is zero. Otherwise q corresponds to a source point y in V and
B_q identifies with the source local ring. The hypothesis gives finite Tor
dimension over the localization of A at the image prime. The localized
polynomial algebra is flat over that localization and its fibres have finite
global dimension, bounded by n. Tag 068X therefore makes B_q perfect over P_q.
Tag 068W, applied to the bounded-below pseudo-coherent complex B[0], makes B
perfect over P. A bounded resolution by finite projective P-modules is a bounded
flat A-resolution, since P is flat over A. Choose d so that this resolution is
zero below degree -d. Tensoring with any A-module gives Tor vanishing above d;
compute Tor' with a projective resolution and compare it to this flat resolution.
The empty affine source has B = 0 and permits d = 0; no bound on dim A is used.
(blueprint: lem-pc-affine-sections-finite-tor-of-stalkwise). -/
theorem affineSections_finiteTorDimension_of_stalkwise
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hperfect : HasStalkwiseFiniteTorDimension f)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) :
    ∃ d : ℕ, ∀ M : ModuleCat.{u} Γ(Y, U), ∀ j : ℕ, d < j →
      IsZero (((Tor' (ModuleCat.{u} Γ(Y, U)) j).obj
        ((ModuleCat.restrictScalars (f.appLE U V e).hom).obj
          (ModuleCat.of Γ(X, V) Γ(X, V)))).obj M) := by sorry

end AlgebraicGeometry
