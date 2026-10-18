/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Perfect ring complexes are closed under triangle extensions

Source: Stacks Project, More on Algebra, Tag 066R, lemma-two-out-of-three-perfect,
the first-and-third-imply-second case (blueprint: lem-sf-perfect-ring-triangle-closure).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- In a distinguished triangle over a commutative ring, perfect first and third objects
imply a perfect second object, in any chosen localization universe.
Source: Stacks Project, More on Algebra, Tag 066R, lemma-two-out-of-three-perfect
(blueprint: lem-sf-perfect-ring-triangle-closure).

Proof plan (the node's direct bounded-projective cone argument):
1. By def-pc-perfect-ring-complex choose bounded finite-projective models P₁ and P₃,
   with bounds [a₁,b₁] and [a₃,b₃], and isomorphisms e₁ : Q(P₁) ≅ T.obj₁ and
   e₃ : Q(P₃) ≅ T.obj₃. The shift P₁[1] has bounds [a₁-1,b₁-1]. The commutation
   of Q with shifts in def-weil-abstract-derived-category gives s : Q(P₁[1]) ≅ T.obj₁[1].
2. Conjugate T.mor₃ by e₃ and s to obtain g : Q(P₃) ⟶ Q(P₁[1]). By
   lem-pc-ring-derived-map-representative, the bounded-above projective source P₃ makes
   the homotopy-to-derived Hom map bijective. Choose a chain map f representing g;
   then Q(f) followed by s equals e₃ followed by T.mor₃. No condition is needed on
   the target of the representative lemma or on the localization universe.
3. Form the actual cone F of f. Its degree i term is P₁^(i+1) ⊕ P₃^(i+1), with
   differential (y,x) ↦ (-d₁ y + f x,-d₃ x). It vanishes outside [L,U], where
   L = min(a₁-1,a₃-1) and U = max(b₁-1,b₃-1). Finite generators of the two
   summands generate their sum; projectivity follows by lifting the two restrictions
   along a surjection and adding the lifts (def-weil-pbc-projective-module).
   The cone triangle Q(P₃) ⟶ Q(P₁[1]) ⟶ Q(F) ⟶ Q(P₃)[1] is distinguished by
   def-weil-abstract-derived-category.
4. Twice rotate T using TR2 of def-weil-triangulated-category. Its vertices become
   T.obj₃, T.obj₁[1], T.obj₂[1], with arrows T.mor₃, -T.mor₁[1], -T.mor₂[1].
   The equality from step 2 gives the first commuting square from the cone triangle.
   TR3 extends (e₃,s) to a triangle morphism; lem-sf-triangle-morphism-iso shows its
   third component Q(F) ⟶ T.obj₂[1] is an isomorphism.
5. Shift this isomorphism by [-1], commute Q with shifts, and cancel [1][-1] to
   obtain Q(F[-1]) ≅ T.obj₂. The shifted complex has bounds [L+1,U+1] and the same
   finite-projective terms reindexed. It is the model required by
   def-pc-perfect-ring-complex. Zero complexes and the zero ring require no exception. -/
theorem isPerfectRingComplex_obj₂_of_distTriang {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (T : Triangle (DerivedCategory (ModuleCat.{u} A)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{u} A)))
    (h₁ : IsPerfectRingComplex T.obj₁) (h₃ : IsPerfectRingComplex T.obj₃) :
    IsPerfectRingComplex T.obj₂ := by
  sorry

end DerivedCategory
