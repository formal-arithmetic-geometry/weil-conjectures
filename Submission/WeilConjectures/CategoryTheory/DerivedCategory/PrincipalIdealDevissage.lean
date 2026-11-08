/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.PointFiber

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Dévissage of `Dᵇ_fg(R)` over a principal ideal domain

Let `R` be a principal ideal domain (for instance a discrete valuation ring or a field). A
triangulated subcategory of `D(R)`, closed under isomorphisms, which contains `R` placed in
degree `0` contains every bounded complex with finitely generated cohomology modules
(`DerivedCategory.prop_of_boundedFiniteCohomology`): it contains the free modules of finite
rank (direct sums of copies of `R`), hence every finitely generated module `M`, which is the
cokernel of an injective map of free modules of finite rank (submodules of free modules of
finite rank are free of finite rank), and one concludes by the dévissage of bounded complexes
along their truncations (`DerivedCategory.prop_of_bounded`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated ZeroObject

namespace DerivedCategory

variable {R : Type (u + 1)} [CommRing R]
  (P : ObjectProperty (DerivedCategory (ModuleCat.{u + 1} R))) [P.IsTriangulated]
  [P.IsClosedUnderIsomorphisms]


variable [IsDomain R] [IsPrincipalIdealRing R]


section Triangulated

variable {R : Type (u + 1)} [CommRing R] [IsNoetherianRing R]

private lemma moduleFinite_of_exact {M N P : Type (u + 1)} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) [Module.Finite R M] [Module.Finite R P] : Module.Finite R N :=
  Module.Finite.of_exact (f := f) (g := g.rangeRestrict)
    (fun y ↦ by rw [← h y]; simp [Subtype.ext_iff]) g.surjective_rangeRestrict

instance : (boundedFiniteCohomology R).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, ⟨TStructure.t.bounded.prop_of_isZero (isZero_zero _),
    fun n ↦ by
      have := (ModuleCat.isZero_iff_subsingleton.1
        ((homologyFunctor (ModuleCat.{u + 1} R) n).map_isZero (isZero_zero _)))
      infer_instance⟩⟩
  isStableUnderShiftBy a := ⟨fun X hX ↦ ⟨TStructure.t.bounded.le_shift a X hX.1, fun n ↦ by
    have := hX.2 (a + n)
    exact Module.Finite.equiv (M := (homologyFunctor (ModuleCat.{u + 1} R) (a + n)).obj X)
      (((homologyFunctor (ModuleCat.{u + 1} R) 0).shiftIso a n (a + n) rfl).app
        X).symm.toLinearEquiv⟩⟩
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ ↦
    ⟨TStructure.t.bounded.ext_of_isTriangulatedClosed₂ T hT h₁.1 h₃.1, fun n ↦ by
      have := h₁.2 n
      have := h₃.2 n
      exact moduleFinite_of_exact (f := ((homologyFunctor (ModuleCat.{u + 1} R) n).map T.mor₁).hom)
        (g := ((homologyFunctor (ModuleCat.{u + 1} R) n).map T.mor₂).hom)
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
          (HomologySequence.exact₂ T hT n))⟩

end Triangulated

/-- A finitely generated module placed in degree `0` lies in `Dᵇ_fg`. -/
lemma boundedFiniteCohomology_singleFunctor {R : Type (u + 1)} [CommRing R]
    (M : ModuleCat.{u + 1} R) [Module.Finite R M] :
    boundedFiniteCohomology R ((singleFunctor (ModuleCat.{u + 1} R) 0).obj M) := by
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst hn
    exact Module.Finite.equiv (M := M)
      ((singleFunctorCompHomologyFunctorIso (ModuleCat.{u + 1} R) 0).app M).symm.toLinearEquiv
  · have : Subsingleton ((homologyFunctor (ModuleCat.{u + 1} R) n).obj
        ((singleFunctor (ModuleCat.{u + 1} R) 0).obj M)) := by
      rw [← ModuleCat.isZero_iff_subsingleton]
      rcases lt_or_gt_of_ne hn with h | h
      · exact isZero_of_isGE _ 0 n h
      · exact isZero_of_isLE _ 0 n h
    infer_instance

end DerivedCategory
