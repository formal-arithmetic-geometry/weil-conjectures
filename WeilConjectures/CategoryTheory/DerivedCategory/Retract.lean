/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-!
# Retracts in the derived category

The homology objects of a retract of an object `N` of `D(C)` are retracts of those of `N`. Hence
the bounded objects of `D(C)` are stable under retracts, and so are the objects all of whose
homology objects satisfy a property `P` of objects of `C` stable under retracts.
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The bounded objects of `D(C)` are stable under retracts. -/
instance : (TStructure.t : CategoryTheory.Triangulated.TStructure (DerivedCategory C)).bounded
    |>.IsStableUnderRetracts where
  of_retract {M N} e hN := by
    obtain ⟨a, b, hab⟩ := (exists_homologyConcentratedIn_iff_bounded N).2 hN
    exact (exists_homologyConcentratedIn_iff_bounded M).1
      ⟨a, b, (homologyConcentratedIn a b).prop_of_retract e hab⟩

/-- If `P` is stable under retracts, then so are the objects of `D(C)` all of whose homology
objects satisfy `P`. -/
instance (P : ObjectProperty C) [P.IsStableUnderRetracts] :
    (homologyProperty P).IsStableUnderRetracts where
  of_retract e h n := P.prop_of_retract (e.map (homologyFunctor C n)) (h n)

end DerivedCategory
