/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.RingTheory.ConePseudoCoherent
import Sheaf.RingTheory.FiniteHomologyOfMPseudoCoherent

/-! # Finite-free models at finitely many localizations

Source: Stacks Project, Tag 08EE, descending construction in the proof of
lemma-lift-pseudo-coherent (blueprint: lem-sc-finite-localization-free-model).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace DerivedCategory

/-- A finite family of pseudo-coherent localizations admits a single bounded-above
finite-free complex mapping to the original complex by a quasi-isomorphism at each
of those localizations. The elements need not generate the unit ideal.

Source: Stacks Project, Tag 08EE, proof of lemma-lift-pseudo-coherent, descending
construction and denominator clearing (blueprint: lem-sc-finite-localization-free-model).

Proof:
Choose a common upper cohomology bound b for the finitely many localized models.
Start at cutoff n = b+1 with F = 0 and its zero map to M. At degree n
maintain that F is zero below n, finite free and bounded above, and that its map
induces localized cohomology isomorphisms above n and surjections in degree n.
The cone has localized cohomology zero in degrees at least n. Its localizations
are (n-1)-pseudo-coherent by Tag 064R: localized F is n-pseudo-coherent
because it is bounded finite free, and truncation of each local finite-free
model of M gives (n-1)-pseudo-coherence. Tag 064S then
makes their degree-(n-1) cohomology finite. Choose finitely many generators at
all localizations. Clear denominators of representatives in the cone and multiply
by further powers of the corresponding element to make their differentials zero
globally. These powers are units at that localization, so the representatives
still generate there. Their direct sum defines a finite-free module F in degree
n-1 mapping to cone cycles. The two cone components define the new component
of the map to M and the negative of the new differential. The cycle equation
proves the chain-map and square-zero equations. The cone cohomology sequence
proves the induction invariant one degree lower. Iterate downward, keeping all
previously constructed degrees fixed. The resulting complex retains the initial
upper bound, has finite-free terms, and its localized map is an isomorphism on
cohomology in every degree. For an empty family take the zero complex; zero
localizations impose no conditions, and the same construction applies to a zero ring.
-/
theorem exists_finite_localization_free_model (A : Type u) [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (r : ℕ) (f : Fin r → A)
    [∀ i : Fin r, HasDerivedCategory.{w} (ModuleCat.{u} (Localization.Away (f i)))]
    (hlocal : ∀ i : Fin r, IsPseudoCoherent
      (Q.obj ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
        (ComplexShape.up ℤ)).obj M))) :
    ∃ (F : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ), F.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free A (F.X i) ∧ Module.Finite A (F.X i)) ∧
      ∃ α : F ⟶ M, ∀ j : Fin r, QuasiIso
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
          (ComplexShape.up ℤ)).map α) := by sorry

end DerivedCategory
