/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage

/-!
# Low-degree cohomology of a right derived functor

Source: Stacks Project, Derived Categories, Lemma 05TC, part (2), with the cone of a morphism
in place of the upper truncation.

## Main statements

* `CategoryTheory.Functor.isIso_homologyFunctor_rightDerivedFunctorPlus_map`:
  a cohomology isomorphism through degree `n`, monic in degree `n + 1`, remains a cohomology
  isomorphism through degree `n` after applying the right derived functor.
* `CategoryTheory.Functor.isIso_homologyFunctor_rightDerivedFunctorPlus_truncLEι`:
  the canonical lower truncation induces an isomorphism on degree-`n` derived cohomology.

`rightDerivedFunctorPlus` is the existing right derived functor on bounded-below derived
categories. It can be computed on bounded-below complexes of injectives, which are
K-injective.
`TStructure.t.onPlus` is the induced standard t-structure on the bounded-below subcategory.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The long exact sequence puts the cone in degrees at least `n + 1`. -/
private theorem isGE_cone_of_homology_map
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
    (n : ℤ) (T : Pretriangulated.Triangle (DerivedCategory.Plus A))
    (hT : T ∈ Pretriangulated.distinguishedTriangles)
    (hiso : ∀ i : ℤ, i ≤ n →
      IsIso ((DerivedCategory.Plus.homologyFunctor A i).map T.mor₁))
    (hmono : Mono ((DerivedCategory.Plus.homologyFunctor A (n + 1)).map T.mor₁)) :
    T.obj₃.IsGE (n + 1) := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
  intro i hi
  let U := (DerivedCategory.Plus.ι (C := A)).mapTriangle.obj T
  have hU : U ∈ Pretriangulated.distinguishedTriangles :=
    (DerivedCategory.Plus.ι (C := A)).map_distinguished T hT
  have : IsIso ((DerivedCategory.homologyFunctor A i).map U.mor₁) :=
    hiso i (by lia)
  have hm : Mono ((DerivedCategory.homologyFunctor A (i + 1)).map U.mor₁) := by
    by_cases h : i + 1 ≤ n
    · have : IsIso ((DerivedCategory.homologyFunctor A (i + 1)).map U.mor₁) :=
        hiso (i + 1) h
      infer_instance
    · have h' : i + 1 = n + 1 := by lia
      rw [h']
      exact hmono
  exact (DerivedCategory.HomologySequence.exact₃ U hU i (i + 1)).isZero_X₂
    ((DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff U hU i).1
      inferInstance)
    ((DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff U hU i (i + 1)).1 hm)

/-- A left exact additive functor between Grothendieck abelian categories preserves
cohomology isomorphisms through degree `n` under its right derived functor, provided the
original map is also monic on cohomology in degree `n + 1`.
Source: Stacks, Derived Categories, Lemma 05TC (2), applied to the cone of the morphism. -/
theorem mono_homologyFunctor_rightDerivedFunctorPlus_map
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{v₂} B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v]
    (n : ℤ) {L M : DerivedCategory.Plus A} (c : L ⟶ M)
    (hiso : ∀ i : ℤ, i ≤ n →
      IsIso ((DerivedCategory.Plus.homologyFunctor A i).map c))
    (hmono : Mono ((DerivedCategory.Plus.homologyFunctor A (n + 1)).map c)) :
    ∀ j : ℤ, j ≤ n →
      Mono ((DerivedCategory.Plus.homologyFunctor B j).map (v.rightDerivedFunctorPlus.map c)) := by
  intro j hj
  obtain ⟨C, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle c
  have : C.IsGE (n + 1) :=
    isGE_cone_of_homology_map n (Pretriangulated.Triangle.mk c g h) hT hiso hmono
  let U := (DerivedCategory.Plus.ι (C := B)).mapTriangle.obj
    (v.rightDerivedFunctorPlus.mapTriangle.obj (Pretriangulated.Triangle.mk c g h))
  have hU : U ∈ Pretriangulated.distinguishedTriangles :=
    (DerivedCategory.Plus.ι (C := B)).map_distinguished _
      (v.rightDerivedFunctorPlus.map_distinguished _ hT)
  exact (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
    U hU (j - 1) j (by lia)).2
    ((v.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
      C (n + 1) (q := j - 1) (by lia)).eq_of_src _ _)

/-- The cone argument of Stacks Lemma 05TC gives the epimorphism half in low degrees.
Source: Stacks Project, Derived Categories, Lemma 05TC, part (2). -/
theorem epi_homologyFunctor_rightDerivedFunctorPlus_map
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{v₂} B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v]
    (n : ℤ) {L M : DerivedCategory.Plus A} (c : L ⟶ M)
    (hiso : ∀ i : ℤ, i ≤ n →
      IsIso ((DerivedCategory.Plus.homologyFunctor A i).map c))
    (hmono : Mono ((DerivedCategory.Plus.homologyFunctor A (n + 1)).map c)) :
    ∀ j : ℤ, j ≤ n →
      Epi ((DerivedCategory.Plus.homologyFunctor B j).map (v.rightDerivedFunctorPlus.map c)) := by
  intro j hj
  obtain ⟨C, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle c
  have : C.IsGE (n + 1) :=
    isGE_cone_of_homology_map n (Pretriangulated.Triangle.mk c g h) hT hiso hmono
  let U := (DerivedCategory.Plus.ι (C := B)).mapTriangle.obj
    (v.rightDerivedFunctorPlus.mapTriangle.obj (Pretriangulated.Triangle.mk c g h))
  have hU : U ∈ Pretriangulated.distinguishedTriangles :=
    (DerivedCategory.Plus.ι (C := B)).map_distinguished _
      (v.rightDerivedFunctorPlus.map_distinguished _ hT)
  exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff U hU j).2
    ((v.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
      C (n + 1) (q := j) (by lia)).eq_of_tgt _ _)

set_option linter.style.haveILetI false in
theorem isIso_homologyFunctor_rightDerivedFunctorPlus_map
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{v₂} B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v]
    (n : ℤ) {L M : DerivedCategory.Plus A} (c : L ⟶ M)
    (hiso : ∀ i : ℤ, i ≤ n → IsIso ((DerivedCategory.Plus.homologyFunctor A i).map c))
    (hmono : Mono ((DerivedCategory.Plus.homologyFunctor A (n + 1)).map c)) :
    ∀ j : ℤ, j ≤ n →
      IsIso ((DerivedCategory.Plus.homologyFunctor B j).map (v.rightDerivedFunctorPlus.map c)) := by
  intro j hj
  have hm := mono_homologyFunctor_rightDerivedFunctorPlus_map v n c hiso hmono j hj
  have he := epi_homologyFunctor_rightDerivedFunctorPlus_map v n c hiso hmono j hj
  haveI := hm
  haveI := he
  exact isIso_of_mono_of_epi _

/-- The canonical truncation `τ≤n K → K` induces an isomorphism on degree-`n` cohomology
after applying the right derived functor of a left exact additive functor.
Source: Stacks, Derived Categories, Lemma 05TC (2). -/
theorem isIso_homologyFunctor_rightDerivedFunctorPlus_truncLEι
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{v₂} B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v]
    (n : ℤ) (K : DerivedCategory.Plus A) :
    IsIso ((DerivedCategory.Plus.homologyFunctor B n).map
      (v.rightDerivedFunctorPlus.map ((DerivedCategory.TStructure.t.onPlus.truncLEι n).app K))) :=
  by
    refine DerivedCategory.Plus.isIso_homologyFunctor_map_map_truncLEι_app
      (v.rightDerivedFunctorPlus) ?_ K n
    intro X a _ q hq
    exact v.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE X a hq

end CategoryTheory.Functor
