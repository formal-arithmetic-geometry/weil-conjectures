/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
import WeilConjectures.CategoryTheory.SimplicialMatchingObject
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.Data.Finite.Sigma
import WeilConjectures.ProperBaseChange.SiteHypercoverFiniteExtensionSplit
import Mathlib.Data.Finite.Sum
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.IsConnected
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.CategoryTheory.Sites.PreservesLimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

/-!
# Geometric part of the affine acyclic hypercover construction

This theorem packages the finite-basis construction, its degreewise coproduct realization,
and the component evaluation comparisons.  The componentwise lifting theorem then supplies
weak contractibility. (blueprint: lem-weil-pbc-proetale-affine-acyclic-hypercover)
-/

@[expose] public section


universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

namespace GeometryRealization

open FormalCoproduct

end GeometryRealization

private theorem properFace_finite (n : ℕ) :
    Finite (SimplicialObject.ProperFaceCategory n) := by
  let f (a : SimplicialObject.ProperFaceCategory n) :
      Σ r : Fin n, (SimplexCategory.mk r.val ⟶ SimplexCategory.mk n) :=
    ⟨⟨a.obj.left.len, a.property.1⟩, a.obj.hom⟩
  apply Finite.of_injective f
  rintro ⟨⟨a, ar, ah⟩, ha⟩ ⟨⟨b, br, bh⟩, hb⟩ h
  have hab : a = b := SimplexCategory.ext (congrArg (fun x ↦ x.1.val) h)
  subst b
  cases ar
  cases br
  have hr : ah = bh := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  subst bh
  rfl

@[instance_reducible] private noncomputable def properFace_finCategory (n : ℕ) :
    FinCategory (SimplicialObject.ProperFaceCategory n) where
  fintypeObj := @Fintype.ofFinite _ (properFace_finite n)
  fintypeHom a b := by
    have : Finite (a.obj.left ⟶ b.obj.left) := inferInstance
    have : Finite (a ⟶ b) := Finite.of_injective (fun f ↦ f.hom.left) (by
      intro f g h
      apply ObjectProperty.hom_ext
      exact Over.OverMorphism.ext h)
    exact Fintype.ofFinite _

end AlgebraicGeometry.Scheme.ProEt
