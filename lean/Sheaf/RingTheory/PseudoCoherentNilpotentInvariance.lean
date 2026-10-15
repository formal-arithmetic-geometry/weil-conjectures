/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.RingTheory.Ideal.Maps
import Sheaf.Algebra.Homology.DerivedChangeOfRings
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import Sheaf.RingTheory.NakayamaNilpotent
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Flat.Basic

/-!
# Pseudo-coherence across a nilpotent quotient

Source: Stacks Project, More on Algebra, Tag 0H76,
lemma-check-pseudo-coherent-modulo-nilpotent
(blueprint: lem-weil-pbc-pseudo-coherent-nilpotent-invariance).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace DerivedCategory

/-- Pseudo-coherence is detected after derived scalar extension along a surjective ring map
with nilpotent kernel. The functor `L`, with its universal counit `ε`, is the total left
derived functor of termwise extension of scalars; thus `L.obj K'` is precisely the derived
reduction, with no flatness assumption on the quotient.

Source: Stacks Project, More on Algebra, Tag 0H76
(blueprint: lem-weil-pbc-pseudo-coherent-nilpotent-invariance).

Proof: Put I = ker φ and identify the target ring with the quotient by surjectivity.
If K' is pseudo-coherent, choose a bounded-above finite-free representative. Free modules
are projective and flat (lem-weil-pbc-projective-module-flat), so this representative is
K-flat (lem-pc-module-bounded-flat-kflat). The K-flat computation of derived change of rings
(lem-pur-derived-change-of-rings, on the one-object site) reduces it termwise to a
bounded-above finite-free representative of L(K').
Conversely, choose a bounded-above finite-free representative E of L(K'). Its terms are
projective (lem-weil-pbc-free-module-projective). Lift it through the nilpotent quotient to
a bounded-above projective representative P of K', with P/IP isomorphic to E
(lem-weil-pbc-nilpotent-projective-complex-lift). In each degree lift the finite basis of
the reduction. Nilpotent Nakayama (lem-weil-pbc-nakayama-nilpotent), without any finiteness
assumption upstairs, shows the resulting map from a finite free module onto P is surjective.
Projectivity (def-weil-pbc-projective-module) splits this surjection. Its kernel has zero
reduction because the reduced map is an isomorphism; nilpotent Nakayama kills that kernel.
Thus every term of P is finite free, including degrees of rank zero. Its bound and derived
identification are unchanged, proving pseudo-coherence of K'. -/
theorem isPseudoCoherent_iff_of_surjective_nilpotent_kernel
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} B)]
    (φ : A →+* B) (hφ : Function.Surjective φ) (hnil : IsNilpotent (RingHom.ker φ))
    (L : DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} B))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _ (ModuleCat.extendScalars φ)
        (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive (.up ℤ) ⋙
          DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (.up ℤ))]
    (K' : DerivedCategory (ModuleCat.{max u v} A)) :
    IsPseudoCoherent (L.obj K') ↔ IsPseudoCoherent K' := by
  sorry

end DerivedCategory
