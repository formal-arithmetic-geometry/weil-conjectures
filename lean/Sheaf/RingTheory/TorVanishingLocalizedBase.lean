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

/-! # Tor vanishing over a localized base ring

Source: Stacks Project, Tag 0B67, the base-ring localization part of (1) to (2).
(blueprint: lem-pc-tor-vanishing-localized-base).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Tor vanishing after scalar restriction implies Tor vanishing over the localization.
Source: Stacks Project, Tag 0B67, `lemma-tor-amplitude-localization`, the
base-ring localization step in (1) to (2), expanded here for modules.

Proof: let P be an A-projective resolution of the restriction of L. Extend scalars
along A to A'. Localization is flat, so A' tensor_A P remains an exact resolution
by projective A'-modules. The augmentation targets A' tensor_A L, canonically
isomorphic to L: every element of the localization submonoid already acts invertibly
on an A'-module, so the counit is invertible. Tensor associativity identifies
(A' tensor_A P) tensor_A' M with P tensor_A M. This is an identification of chain
complexes after restriction to A and therefore of their homology. The latter
homology is the Tor' object in the hypothesis and is zero. Restriction of scalars
reflects zero objects, giving the required zero Tor' object over A'.
This includes j = 0, S = {1}, and the zero localization; no finite generation
hypothesis is used, and both L and M have their original A'-module structures.
(blueprint: lem-pc-tor-vanishing-localized-base). -/
theorem isZero_tor_of_restrictScalars_localization
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    (S : Submonoid A) [IsLocalization S A']
    (L M : ModuleCat.{u} A') (j : ℕ)
    (h : IsZero (((Tor' (ModuleCat.{u} A) j).obj
      ((restrictScalars (algebraMap A A')).obj L)).obj
        ((restrictScalars (algebraMap A A')).obj M))) :
    IsZero (((Tor' (ModuleCat.{u} A') j).obj L).obj M) := by sorry

end ModuleCat
