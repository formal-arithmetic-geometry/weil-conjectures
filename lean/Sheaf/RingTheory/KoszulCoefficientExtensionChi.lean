/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.RingTheory.KoszulDualComplex
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Sheaf.RingTheory.KoszulRegularSequence
public import Mathlib.RingTheory.Localization.Defs

/-! # KoszulCoefficientExtensionChi

Source: Stacks Project, Tag 0BQZ, coefficient formulas in the finite free
Koszul calculation (blueprint: new-lem-sc-koszul-coefficient-extension-chi).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

/-- The coefficient extension cochain map with its evaluation formula.
Source: Stacks Project, Tag 0BQZ, finite free Koszul computation.
(blueprint: new-lem-sc-koszul-coefficient-extension-chi)

Proof: Write e_J for the increasing standard basis wedges of degree n. For a
functional x, define its extension by sending e_J over S to the image of x(e_J).
The exterior basis makes this a unique S-linear functional, and the assignment
is A-linear in x. Expanding any wedge in that basis expresses its coefficients
as minors of the vector-coordinate matrix. Ring maps preserve these minors,
which proves the evaluation formula. On a basis wedge the contraction is the
alternating sum of f(i) times the wedge omitting i. Applying A -> S to this
formula gives contraction for the image sequence. The signed dual differential
is precomposition with this contraction times (-1)^(n+1); the ring map preserves
that sign. Thus the degreewise extensions commute with every differential and
form chi. For n > r both exterior terms are zero; for n = 0 the single empty
basis wedge gives scalar extension A -> S. No regularity assumption is needed
for this component, though the common hypotheses are retained. -/
theorem exists_koszul_coefficient_extension_chi
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I)
    (T : Submonoid A) (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization T S]
    (hs : Ideal.span (Set.range (algebraMap A S ∘ f)) = I.map (algebraMap A S)) :
  ∃ (χ : koszulDualComplex A r f ⟶
    ((ModuleCat.restrictScalars (algebraMap A S)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (koszulDualComplex S r (algebraMap A S ∘ f))),
  ∀ (n : ℕ) (x : (koszulComplex A r f).X n ⟶ ModuleCat.of A A)
    (v : Fin n → (Fin r →₀ A)),
    (χ.f n x).hom (exteriorPower.ιMulti S n
      (fun i ↦ (v i).mapRange (algebraMap A S) (map_zero _))) =
    algebraMap A S (x.hom (exteriorPower.ιMulti A n v)) := by sorry

end ExteriorAlgebra
