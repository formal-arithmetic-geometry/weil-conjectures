/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# The cohomology of a cochain complex of abelian groups

The cohomology `Hⁿ⁺¹(C)` of an `ℕ`-indexed cochain complex `C` of abelian groups is the explicit
quotient of the cocycles `ker(Cⁿ⁺¹ ⟶ Cⁿ⁺²)` by the coboundaries, the class of a cycle being the
class of its underlying element (`CochainComplex.abHomologySuccAddEquiv_homologyπ`).

A short complex (or a homological complex) in an abelian category is exact as soon as its images
under all the functors `Hom(a, -)` are exact
(`CategoryTheory.ShortComplex.exact_of_forall_exact_map_preadditiveCoyoneda`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CochainComplex

end CochainComplex

namespace CategoryTheory.ShortComplex

variable {A : Type*} [Category* A] [Abelian A]

/-- A short complex in an abelian category is exact if its images under all the functors
`Hom(a, -)` are exact. -/
lemma exact_of_forall_exact_map_preadditiveCoyoneda (S : ShortComplex A)
    (h : ∀ a : A, (S.map (preadditiveCoyoneda.obj (Opposite.op a))).Exact) : S.Exact := by
  obtain ⟨x, hx⟩ := (ShortComplex.ab_exact_iff _).1 (h S.cycles) S.iCycles S.iCycles_g
  rw [S.exact_iff_epi_toCycles]
  have hx' : x ≫ S.toCycles = 𝟙 _ := by
    rw [← cancel_mono S.iCycles, Category.assoc, toCycles_i, Category.id_comp]
    exact hx
  have : IsSplitEpi S.toCycles := IsSplitEpi.mk' ⟨x, hx'⟩
  infer_instance

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {A : Type*} [Category* A] [Abelian A] {ι : Type*} {c : ComplexShape ι}

/-- A complex in an abelian category is exact at `i` if its images under all the functors
`Hom(a, -)` are exact at `i`. -/
lemma exactAt_of_forall_exactAt_map_preadditiveCoyoneda (K : HomologicalComplex A c) (i : ι)
    (h : ∀ a : A,
      (((preadditiveCoyoneda.obj (Opposite.op a)).mapHomologicalComplex c).obj K).ExactAt i) :
    K.ExactAt i :=
  (K.sc i).exact_of_forall_exact_map_preadditiveCoyoneda h

end HomologicalComplex
