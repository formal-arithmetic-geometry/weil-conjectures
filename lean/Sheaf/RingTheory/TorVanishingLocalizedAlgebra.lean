/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Localization.Basic

/-! # Tor vanishing after localizing the coefficient algebra

Source: Stacks Project, Tag 0B67, the source-algebra localization part of (1) to (2).
(blueprint: lem-pc-tor-vanishing-localized-algebra).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Localization of the coefficient algebra preserves vanishing of a fixed Tor group.
Source: Stacks Project, Tag 0B67, `lemma-tor-amplitude-localization`, the
source-algebra localization step in (1) to (2), expanded here for modules.

Proof: choose a free A-resolution Q of N. Balancedness identifies the Tor' object
in the hypothesis with the j-th homology of B tensor_A Q. This complex carries its
termwise B-action. Tensoring it over B with C is exact because C is a localization
of B, so its j-th homology is C tensor_B H_j(B tensor_A Q), hence zero. The tensor
associativity maps identify its terms and differentials with C tensor_A Q.
Balancedness again identifies this homology with the asserted Tor' object.
All scalar actions are induced by the displayed composite ring homomorphism.
The proof works also in degree zero, for the trivial localization S = {1},
and for localizations at a submonoid containing zero (then C is the zero ring).
(blueprint: lem-pc-tor-vanishing-localized-algebra). -/
theorem isZero_tor_localized_algebra
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) [Algebra B C] (S : Submonoid B) [IsLocalization S C]
    (N : ModuleCat.{u} A) (j : ℕ)
    (h : IsZero (((Tor' (ModuleCat.{u} A) j).obj
      ((restrictScalars φ).obj (of B B))).obj N)) :
    IsZero (((Tor' (ModuleCat.{u} A) j).obj
      ((restrictScalars ((algebraMap B C).comp φ)).obj (of C C))).obj N) := by sorry

end ModuleCat
