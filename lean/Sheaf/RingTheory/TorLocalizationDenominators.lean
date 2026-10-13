/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Localization.Basic

/-! # Clearing denominators in Tor classes

(blueprint: lem-pc-tor-localization-denominators)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Every localized Tor class has a unit multiple in the image of the coefficient map.
The multiplier is induced by multiplication on the coefficient algebra, rather than
an arbitrary action on Tor. The map `f` is specified on elements, so it is exactly
restriction of the localization map with the displayed scalar structures.

Source: Stacks Project, Tag 0B67, the localized derived-tensor homology identity in
its proof, specialized to B in degree zero; expanded here to individual classes.
Proof: choose a free A-resolution Q of N. Balancedness identifies the two Tor'
objects, naturally in the coefficient, with H_j(B tensor_A Q) and H_j(C tensor_A Q).
Tensor associativity identifies the latter complex with the localization at S of
the former B-complex. Localization is exact, hence its homology is the localization
of H_j(B tensor_A Q). More explicitly, represent a localized homology class by a
cycle. Clear its denominator to obtain a chain over B. Its differential becomes
zero after localization, so a second denominator annihilates that differential.
Multiplying by this second denominator gives a cycle over B. The product s of the
two denominators belongs to S, and its image in C is a unit u. The original class
multiplied by u is the image of the class y of this cycle. Naturality of balancedness
identifies multiplication by u with the displayed Tor' map, and the coefficient
map with Tor'(f,N). This also works in degree zero, for S = {1}, for N = 0, and
when S contains zero (then C and its Tor objects are zero).
(blueprint: lem-pc-tor-localization-denominators)
-/
theorem tor_localization_denominators
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) [Algebra B C] (S : Submonoid B) [IsLocalization S C]
    (N : ModuleCat.{u} A) (j : ℕ)
    (f : (restrictScalars φ).obj (of B B) ⟶
      (restrictScalars ((algebraMap B C).comp φ)).obj (of C C))
    (hf : ∀ b : B, f b = algebraMap B C b)
    (x : (((Tor' (ModuleCat.{u} A) j).obj
      ((restrictScalars ((algebraMap B C).comp φ)).obj (of C C))).obj N)) :
    ∃ u : Cˣ, ∃ y : (((Tor' (ModuleCat.{u} A) j).obj
      ((restrictScalars φ).obj (of B B))).obj N),
      (((Tor' (ModuleCat.{u} A) j).map
        ((restrictScalars ((algebraMap B C).comp φ)).map
          (u.mulLeftLinearEquiv C C).toModuleIso.hom)).app N) x =
        (((Tor' (ModuleCat.{u} A) j).map f).app N) y := by sorry

end ModuleCat
