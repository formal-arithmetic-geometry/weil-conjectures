/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Functor.OfSequence

import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-!
# Surjective towers of module complexes

Source: Stacks Project, Tags 091D (3), (5) and 0CQD
(blueprint: lem-weil-pbc-surjective-module-complex-tower-limit).
Natural index `n` denotes the source's positive index `n + 1`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Restrict a varying-ring complex tower to the vertex of its ring cone, using the
canonical composition comparison for restriction of scalars. Source: Stacks Project,
Tag 091D, preceding setup (blueprint: lem-weil-pbc-surjective-module-complex-tower-limit).
The comparison has identity underlying additive maps, so these are the original transitions.
-/
noncomputable def restrictedComplexTower
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone A)
    (P : ∀ n : ℕ, CochainComplex (ModuleCat.{v} (A.obj (Opposite.op n))) ℤ)
    (t : ∀ n : ℕ, P (n + 1) ⟶
      ((restrictScalars (A.map (homOfLE (Nat.le_succ n)).op).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (P n)) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} c.pt) ℤ :=
  Functor.ofOpSequence (fun n ↦
    ((restrictScalars (c.π.app (Opposite.op (n + 1))).hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (t n) ≫
    (Functor.mapHomologicalComplexCompIso
      (restrictScalarsComp'
        (c.π.app (Opposite.op (n + 1))).hom
        (A.map (homOfLE (Nat.le_succ n)).op).hom
        (c.π.app (Opposite.op n)).hom
        (congrArg CommRingCat.Hom.hom (c.w (homOfLE (Nat.le_succ n)).op).symm)).symm
      (ComplexShape.up ℤ)).hom.app (P n))

/-- A degreewise surjective tower is represented by its termwise limit, with the original
projections. Source: Stacks Project, Tags 091D (3), (5) and 0CQD
(blueprint: lem-weil-pbc-surjective-module-complex-tower-limit).

Proof: (1) Restrict scalars along the limiting ring cone. Cone compatibility and the
linearity of t make every transition linear over the limit ring. Form B degreewise as
product of the restricted complexes; its differentials act componentwise. (2) The kernel
of u = 1-s on B is the termwise limit P, with its projection inclusion j. Surjectivity of
u in each degree follows by choosing x_0 = 0 and recursively lifting x_n-y_n under t_n.
Thus 0 → P → B → B → 0 is degreewise short exact; no linear choice is needed.
(3) By lem-pc-cone-short-exact-quasi-iso, the map q : Cone(j) → B induced by u is a
quasi-isomorphism. Transport the distinguished cone triangle along Q(q), with connecting
map -Q(p)Q(q)⁻¹, keeping its first two arrows unchanged.
(4) Products of modules are exact, by componentwise kernels and choice of preimages.
Apply lem-weil-derived-limit-products-core to identify Q(B) with the derived product,
including its projections. (5) Checking on projections identifies Q(u) with the tower
transition endomorphism 1-s, and Q(j) followed by the nth projection is Q of the original
limit projection. The resulting triangle is precisely IsDerivedLimitTriangle.
-/
theorem surjective_moduleComplexTower_limit
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone A) (hc : IsLimit c)
    (P : ∀ n : ℕ, CochainComplex (ModuleCat.{v} (A.obj (Opposite.op n))) ℤ)
    (t : ∀ n : ℕ, P (n + 1) ⟶
      ((restrictScalars (A.map (homOfLE (Nat.le_succ n)).op).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (P n))
    (ht : ∀ (n : ℕ) (i : ℤ), Function.Surjective ((t n).f i))
    [HasDerivedCategory.{w} (ModuleCat.{v} c.pt)] :
    HasProduct (fun n : ℕ ↦
      DerivedCategory.Q.obj ((restrictedComplexTower A c P t).obj (Opposite.op n))) ∧
    ∀ [HasProduct (fun n : ℕ ↦
      DerivedCategory.Q.obj ((restrictedComplexTower A c P t).obj (Opposite.op n)))],
      ∃ δ : (∏ᶜ fun n : ℕ ↦
        DerivedCategory.Q.obj ((restrictedComplexTower A c P t).obj (Opposite.op n))) ⟶
        (DerivedCategory.Q.obj
          (HomologicalComplex.coneOfHasLimitEval (restrictedComplexTower A c P t)).pt)
          ⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle
          (fun n : ℕ ↦ DerivedCategory.Q.map
            ((restrictedComplexTower A c P t).map (homOfLE (Nat.le_succ n)).op))
          (DerivedCategory.Q.obj
            (HomologicalComplex.coneOfHasLimitEval (restrictedComplexTower A c P t)).pt)
          (Pi.lift (fun n : ℕ ↦ DerivedCategory.Q.map
            ((HomologicalComplex.coneOfHasLimitEval (restrictedComplexTower A c P t)).π.app
              (Opposite.op n)))) δ := by
  sorry

end ModuleCat
