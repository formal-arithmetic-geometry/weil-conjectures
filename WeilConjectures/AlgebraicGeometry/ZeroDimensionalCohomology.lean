/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Blueprint statements

lem-weil-pbc-zero-dimensional-cohomology, zero-dimensional-etale-finite.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Blueprint: zero-dimensional-etale-finite. -/
theorem zero_dimensional_etale_finite
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (hdim : topologicalKrullDim C ≤ 0) : Finite C := by
  sorry

/-- Blueprint: lem-weil-pbc-zero-dimensional-cohomology. -/
theorem zero_dimensional_etale_cohomology
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim C ≤ 0)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Ω : C → Type u) [∀ x, Field (Ω x)] [∀ x, IsAlgClosed (Ω x)]
    (s : ∀ x : C, Spec (.of (Ω x)) ⟶ C)
    (hs : ∀ x : C, (s x).base.hom default = x) :
    Finite C ∧
    (∀ q : ℕ, 0 < q → Subsingleton
      ((Etale.cohomology AddCommGrpCat.{u + 1} C q).obj
        ((DerivedCategory.singleFunctor
          (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ∧
      IsIso
        ((Functor.homologyRightDerivedFunctorObjSingleFunctorIso
            (CategoryTheory.Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}) F 0).hom ≫
          (Functor.rightDerivedZeroIsoSelf
            (CategoryTheory.Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1})).hom.app F ≫
          F.ΓRes (op (Scheme.Etale.mk (𝟙 C))) ≫
          Pi.lift (fun x : C =>
            (Scheme.pointSmallEtale (s x)).toPresheafFiber
              (Scheme.Etale.mk (𝟙 C))
              (Over.homMk (s x) (Category.comp_id (s x))) F.obj)) := by
  sorry

end AlgebraicGeometry
