/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Sheaf.Algebra.Homology.DerivedChangeOfRings
import Sheaf.AlgebraicGeometry.ComplexLiftClassProjective

/-!
# Lifting a prescribed projective complex through a nilpotent quotient

Source: Stacks Project, More on Algebra, Tag 09AR, lemma-lift-complex-projectives
(blueprint: lem-weil-pbc-nilpotent-projective-complex-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

open CategoryTheory

namespace CochainComplex

/-- A bounded-above projective model of derived reduction lifts as a complex, not merely
as a derived object. Source: Stacks Project, More on Algebra, Tag 09AR
(blueprint: lem-weil-pbc-nilpotent-projective-complex-lift).

The functor `L`, with its universal counit `ε`, is the total left derived functor of
termwise extension of scalars, as in `lem-pur-derived-change-of-rings` on the one-object
site. Thus `L.obj C` is `C ⊗ᴸ A/I`; no boundedness of `C` is assumed.
Extension of scalars along the quotient map is canonically the termwise quotient by `I`.

Proof:
1. Take the class of all projective A-modules. The lifting property of
   `def-weil-pbc-projective-module` gives closure under sums and summands. If T/IT = 0,
   then T = IT = ... = I^N T = 0. Apply this to a cokernel to see that a map which is
   surjective modulo I is surjective. These verify conditions (1), (2), (3) of Tag 0BCA.
2. By `lem-weil-pbc-nilpotent-projective-module-lift`, lift every E^i to a projective
   A-module. Together with the upper bound on E, this verifies condition (4).
3. Choose an upper bound b on E. Its cohomology vanishes above b, hence so does that
   of the derived reduction of C. By `lem-weil-pbc-nilpotent-derived-upper-bound`, the
   cohomology of C vanishes above b as well.
4. Apply `lem-weil-pbc-bounded-above-projective-model` to obtain a bounded-above
   projective representative of C, verifying condition (5), without assuming
   pseudo-coherence or finite Tor amplitude.
5. Apply `lem-sc-complex-lift-class-projective`. It supplies P representing C and a
   complex isomorphism between its termwise reduction and the prescribed E. -/
theorem exists_projective_lift_of_nilpotent
    (A : Type u) [CommRing A] (I : Ideal A)
    (hI : ∃ N : ℕ, 1 ≤ N ∧ I ^ N = ⊥)
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (A ⧸ I))]
    (L : DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} (A ⧸ I)))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _
        (ModuleCat.extendScalars (Ideal.Quotient.mk I))
        (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))]
    (C : DerivedCategory (ModuleCat.{max u v} A))
    (E : CochainComplex (ModuleCat.{max u v} (A ⧸ I)) ℤ)
    (hEbound : ∃ b : ℤ, E.IsStrictlyLE b)
    (hEproj : ∀ i : ℤ, Module.Projective (A ⧸ I) (E.X i))
    (hReduction : Nonempty (L.obj C ≅ DerivedCategory.Q.obj E)) :
    ∃ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      (∃ b : ℤ, P.IsStrictlyLE b) ∧
      (∀ i : ℤ, Module.Projective A (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ C) ∧
      Nonempty (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P ≅ E) := by
  sorry

end CochainComplex
