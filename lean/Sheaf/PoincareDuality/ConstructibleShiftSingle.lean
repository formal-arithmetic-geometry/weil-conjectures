/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! Geometric and shift components of the bounded-constructibility argument. -/

@[expose] public section

universe u u'

open CategoryTheory MonoidalCategory MonoidalClosed
open MonObj Limits ZeroObject
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}}
  (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]
private lemma constructible_of_iso
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) A) R} (e : M ≅ N)
    (hM : IsConstructibleModuleObject R M) : IsConstructibleModuleObject R N := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  obtain ⟨𝒰, h𝒰⟩ := hS a
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨n, m, f, ⟨e'⟩⟩ := h𝒰 i
  exact ⟨n, m, f, ⟨(((ProEtale.upperStar A (S.immersion a)).mapMod R ⋙
    (ProEtale.upperStar A (𝒰.f i)).mapMod _).mapIso e).symm ≪≫ e'⟩⟩

private lemma locallyFinitelyPresented_of_isZero
    {M : Mod (Sheaf (Scheme.ProEt.topology X) A) R} (hM : IsZero M) :
    IsLocallyFinitelyPresented R M := by
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨0, 0, 𝟙 _, ⟨?_⟩⟩
  exact (((ProEtale.upperStar A _).mapMod R).map_isZero hM).iso
    (isZero_cokernel_of_epi (𝟙 _))

private lemma constructible_of_isZero
    {M : Mod (Sheaf (Scheme.ProEt.topology X) A) R} (hM : IsZero M) :
    IsConstructibleModuleObject R M := by
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  refine ⟨S, fun a ↦ ?_⟩
  exact locallyFinitelyPresented_of_isZero _
    (((ProEtale.upperStar A _).mapMod R).map_isZero hM)


/-- A constructible module placed in degree zero stays bounded constructible after any shift.

Source: the shifted-single isomorphism and the defining homology criterion for
`boundedConstructible`. Its cohomology in degree `-n` is the original module, and all
other cohomology objects are zero. Transport constructibility through these isomorphisms.
(blueprint: lem-poincare-constructible-shift-single) -/
theorem boundedConstructible_shift_single
    (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R)
    (hM : IsConstructibleModuleObject R M) (n : ℤ) :
    boundedConstructible R
      ((shiftFunctor _ n).obj ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  let K := (shiftFunctor _ n).obj ((DerivedCategory.singleFunctor _ 0).obj M)
  let e : K ≅ (DerivedCategory.singleFunctor _ (-n)).obj M :=
    ((DerivedCategory.singleFunctors _).shiftIso n (-n) 0 (by simp)).app M
  have : K.IsGE (-n) := DerivedCategory.TStructure.t.isGE_of_iso e.symm (-n)
  have : K.IsLE (-n) := DerivedCategory.TStructure.t.isLE_of_iso e.symm (-n)
  apply (mem_boundedConstructible_iff R K).mpr
  constructor
  · refine ⟨-n, -n, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE K (-n) i hi
    · exact DerivedCategory.isZero_of_isLE K (-n) i hi
  · intro i
    by_cases hi : i = -n
    · subst i
      exact constructible_of_iso R
        (((DerivedCategory.homologyFunctor _ (-n)).mapIso e) ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso _ (-n)).app M).symm hM
    · apply constructible_of_isZero
      rcases lt_or_gt_of_ne hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE K (-n) i hi
      · exact DerivedCategory.isZero_of_isLE K (-n) i hi

end AlgebraicGeometry.ProEtale
