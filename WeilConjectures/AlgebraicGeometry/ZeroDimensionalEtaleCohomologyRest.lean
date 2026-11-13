/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalGlobalSectionsExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalEtaleCohomologyIso
import Mathlib.Algebra.Category.Grp.Zero

/-! # Zero-dimensional étale cohomology: cohomological remainder

## References

* [Stacks Project, Tag 00KH](https://stacks.math.columbia.edu/tag/00KH)
* [Stacks Project, Tag 00FV](https://stacks.math.columbia.edu/tag/00FV)
* [Stacks Project, Tag 054M](https://stacks.math.columbia.edu/tag/054M)
* [Stacks Project, Tag 03QT](https://stacks.math.columbia.edu/tag/03QT)
* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU)
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Positive étale cohomology is zero, and the canonical degree-zero comparison
followed by the product of the chosen geometric stalk germs is invertible.
-/
theorem zero_dimensional_etale_cohomology_rest
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (hdim : topologicalKrullDim C ≤ 0)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Ω : C → Type u) [∀ x, Field (Ω x)] [∀ x, IsAlgClosed (Ω x)]
    (s : ∀ x : C, Spec (.of (Ω x)) ⟶ C)
    (hs : ∀ x : C, (s x).base.hom default = x) :
    (∀ q : ℕ, 0 < q → Subsingleton
      ((Etale.cohomology AddCommGrpCat.{u + 1} C q).obj
        ((DerivedCategory.singleFunctor
          (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ∧
      IsIso ((Functor.homologyRightDerivedFunctorObjSingleFunctorIso
        (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}) F 0).hom ≫
          (Functor.rightDerivedZeroIsoSelf
            (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1})).hom.app F ≫
          F.ΓRes (op (Scheme.Etale.mk (𝟙 C))) ≫ Pi.lift (fun x : C =>
            (Scheme.pointSmallEtale (s x)).toPresheafFiber
              (Scheme.Etale.mk (𝟙 C))
              (Over.homMk (s x) (Category.comp_id (s x))) F.obj)) := by
  have : PreservesFiniteColimits (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    zero_dimensional_global_sections_preservesFiniteColimits k C f hdim
  refine ⟨fun q hq => AddCommGrpCat.subsingleton_of_isZero ?_,
    zero_dimensional_etale_cohomology_iso k C f hdim F Ω s hs⟩
  change IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
    ((Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj F)))
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
    ((Functor.singleFunctorCompRightDerivedFunctorIso
      (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1})).app F))
  change IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
    ((DerivedCategory.singleFunctor AddCommGrpCat.{u + 1} 0).obj
      ((Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj F)))
  exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0
    ((Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj F)
    (q : ℤ) (by omega)).of_iso
    ((DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ AddCommGrpCat.{u + 1} 0).app
        ((Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj F)) ≪≫
      (DerivedCategory.homologyFunctorFactors _ (q : ℤ)).app _)

end AlgebraicGeometry
