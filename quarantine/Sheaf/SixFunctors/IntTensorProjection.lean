/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Sheaf.SixFunctors.OpenImmersionTensorProjection
import Sheaf.SixFunctors.ClosedImmersionTensorProjection
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Projection formula for extension by zero along a locally closed immersion

Source: `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/
 det-lem-int-tensor-projection.md` (blueprint: det-lem-int-tensor-projection).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Projection formula for a locally closed immersion, with `a_!` represented by `i_* u_!`.
Source: node `det-lem-int-tensor-projection`,
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/`
`det-lem-int-tensor-projection.md` (blueprint: det-lem-int-tensor-projection).

Apply the closed immersion formula to u_!M and N, then the open immersion formula
to M and i^*N, and postcompose with closed direct image. Derived composition,
upperStarComp and the given factorization identify u^*i^* with a^*. Whiskering and
postcomposition preserve both naturality variables.
-/
theorem locallyClosedImmersionTensorProjection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] {S Sbar X : Scheme.{u}}
    [S.Over (Spec (.of k))] [Sbar.Over (Spec (.of k))]
    [X.Over (Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (Sbar ↘ Spec (.of k))]
    [LocallyOfFiniteType (Sbar ↘ Spec (.of k))]
    [QuasiCompact (Sbar ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (a : S ⟶ X) (u : S ⟶ Sbar) (i : Sbar ⟶ X)
    (ha : a = u ≫ i) [a.IsOver (Spec (.of k))]
    [u.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
    [IsOpenImmersion u] [IsClosedImmersion i] :
    Nonempty (
      (((Functor.whiskeringLeft₂ _).obj
          ((openImmersionLowerShriek Λ u).mapDerivedCategory ⋙
            (lowerStar Λ i).rightDerivedFunctor)).obj (𝟭 _)).obj
        (derivedTensor Λ X) ≅
      (Functor.postcompose₂.obj
        ((openImmersionLowerShriek Λ u).mapDerivedCategory ⋙
          (lowerStar Λ i).rightDerivedFunctor)).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
          ((a)^*⟦Λ⟧.mapDerivedCategory)).obj (derivedTensor Λ S))) := by
  obtain ⟨eo⟩ := openImmersionTensorProjection Λ k u
  obtain ⟨ec⟩ := closedImmersionTensorProjection Λ k i
  let ep : (i)^*⟦Λ⟧.mapDerivedCategory ⋙ (u)^*⟦Λ⟧.mapDerivedCategory ≅
      (a)^*⟦Λ⟧.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso (i)^*⟦Λ⟧ (u)^*⟦Λ⟧).symm ≪≫
      Functor.mapDerivedCategoryNatIso (upperStarComp Λ u i).symm ≪≫
      eqToIso (congrArg (fun f ↦ (upperStar Λ f).mapDerivedCategory) ha.symm)
  refine ⟨?_⟩
  exact Functor.isoWhiskerLeft (openImmersionLowerShriek Λ u).mapDerivedCategory ec ≪≫
    (Functor.postcompose₂.obj (lowerStar Λ i).rightDerivedFunctor).mapIso
      (Functor.isoWhiskerRight eo
        ((Functor.whiskeringLeft _ _ _).obj (i)^*⟦Λ⟧.mapDerivedCategory)) ≪≫
    (Functor.postcompose₂.obj (lowerStar Λ i).rightDerivedFunctor).mapIso
      (Functor.isoWhiskerLeft
        ((Functor.postcompose₂.obj (openImmersionLowerShriek Λ u).mapDerivedCategory).obj
          (derivedTensor Λ S))
        ((Functor.whiskeringLeft _ _ _).mapIso ep))

end AlgebraicGeometry.ProEtale.CondensedRing
