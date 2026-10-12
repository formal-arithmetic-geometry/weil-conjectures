/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Torsion homology of abelian étale sheaves

The abelian coefficient conditions in the proper base change theorem.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

/-- A sheaf of abelian groups on the small étale site of `X` is *torsion* if every
geometric stalk is a torsion abelian group: each element is killed by a positive integer.
This is the classical notion of a torsion abelian sheaf [Stacks 03SA]. -/
class Scheme.IsTorsionSheaf {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) : Prop where
  isTorsion_sheafFiber (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    IsAddTorsion (↥((pointSmallEtale s).sheafFiber.obj F))


/-- The geometric-stalk definition of torsion for abelian étale sheaves agrees with
local torsion of sections. -/
lemma Scheme.isTorsionSheaf_iff_isTorsion {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) : IsTorsionSheaf F ↔ F.IsTorsion := by
  rw [Scheme.isTorsion_iff_isAddTorsion_sheafFiber]
  exact ⟨fun h ↦ h.isTorsion_sheafFiber, fun h ↦ ⟨h⟩⟩


variable (X : Scheme.{u})

/-- An object of the bounded below derived category of étale sheaves of abelian groups has
*torsion cohomology* if all its cohomology sheaves are torsion
(`AlgebraicGeometry.Scheme.IsTorsionSheaf`). This is the hypothesis on the coefficient
complex in the general proper base change theorem. -/
noncomputable def Etale.DerivedCategory.Plus.torsionHomology :
    ObjectProperty (DerivedCategory.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})) :=
  fun K ↦ ∀ n : ℤ, IsTorsionSheaf
    ((DerivedCategory.Plus.homologyFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) n).obj K)


end AlgebraicGeometry
