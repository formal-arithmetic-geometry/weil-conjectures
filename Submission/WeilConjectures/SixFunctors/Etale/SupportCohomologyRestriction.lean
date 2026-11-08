/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.SupportsOpenImmersion
public import Submission.WeilConjectures.SixFunctors.Etale.SupportCohomologyHom

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The restriction triangle inside a closed support

Let `b : B ⟶ T` and `c : C ⟶ T` be closed immersions, `v : V ⟶ T` the open complement of `C`,
`d : D ⟶ T` a closed immersion onto `B ∩ C` and `b' : B ×_T V ⟶ V` the base change of `b`. For
a complex `F` of étale sheaves on `T` there is a distinguished triangle

`RΓ_{B ∩ C}(T, F) ⟶ RΓ_B(T, F) ⟶ RΓ_{B ∩ V}(V, v^* F) ⟶ RΓ_{B ∩ C}(T, F)[1]`.

## The argument

The derived sections with support are computed by the exceptional formalism:
`RΓ_B(T, -) ≅ RΓ(T, Rb_! Rb^! -)` (`AlgebraicGeometry.Etale.rightDerivedSectionsWithSupportIso`),
because `RΓ_B(T, -) ≅ RΓ(B, Rb^!_{sh} -)` for the derived functor of the sheaf functor `b^!`
(`AlgebraicGeometry.Etale.rightDerivedClosedUpperShriekCompIso`), which is right adjoint to
`b_* = Rb_!`, hence is `Rb^!`.

Put `E = Rb_! Rb^! F`. The supported localization triangle of `E` for the pair `(C, V)` is

`Rc_! Rc^! E ⟶ E ⟶ Rv_* Lv^* E ⟶ (Rc_! Rc^! E)[1]`,

and `Rc_! Rc^! E ≅ Rd_! Rd^! F` over `E`: both are supported on `D` and represent maps to `F`
out of objects supported on `D`. Applying `RΓ(T, -)`, the last term is
`RΓ(V, Lv^* E) ≅ RΓ(V, Rb'_! Rb'^! Lv^* F) ≅ RΓ_{B ∩ V}(V, v^* F)`, as restriction to an open
commutes with supports (`AlgebraicGeometry.Etale.isIso_supportedRestriction_of_isOpenImmersion`).

## Main statements

- `AlgebraicGeometry.Etale.rightDerivedSectionsWithSupportIso`
- `AlgebraicGeometry.Etale.supportRestrictionTriangle_distinguished`
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section UpperShriek

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The derived pushforward `Ri_!` along a closed immersion is the functor induced by the exact
functor `i_*`. -/
noncomputable def mapDerivedCategoryLowerStarIsoRightDerivedLowerShriek :
    ((i)_*[A]).mapDerivedCategory ≅ R(i)_![A] :=
  ((i)_*[A]).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    (rightDerivedLowerShriekIsoRightDerivedLowerStar A i).symm

/-- `i_* ⊣ Ri^!_{sh}`: the derived adjunction of `i_* ⊣ i^!`. -/
noncomputable def mapDerivedCategoryLowerStarClosedUpperShriekAdjunction :
    ((i)_*[A]).mapDerivedCategory ⊣
      (closedUpperShriek A i i.openComplement.ι).rightDerivedFunctor :=
  (lowerStarClosedUpperShriekAdjunction A i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι).mapDerivedCategoryRightDerivedAdjunction

/-- For a closed immersion `i`, the derived lower shriek `Ri_!` is a left adjoint, with right
adjoint the derived functor of the sheaf functor `i^!` of sections supported on `Z`. -/
instance isLeftAdjoint_rightDerivedLowerShriek_of_isClosedImmersion :
    (R(i)_![A]).IsLeftAdjoint :=
  ((mapDerivedCategoryLowerStarClosedUpperShriekAdjunction A i).ofNatIsoLeft
    (mapDerivedCategoryLowerStarIsoRightDerivedLowerShriek A i)).isLeftAdjoint

/-- For a closed immersion `i`, the exceptional inverse image `Ri^!` is the right derived functor
of the sheaf functor `i^!` of sections supported on `Z`, both being right adjoint to
`Ri_! ≅ i_*`. -/
noncomputable def rightDerivedClosedUpperShriekIso :
    (closedUpperShriek (ModuleCat.{u + 1} Λ) i i.openComplement.ι).rightDerivedFunctor ≅ R(i)^![Λ]
        :=
  ((mapDerivedCategoryLowerStarClosedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).ofNatIsoLeft
    (mapDerivedCategoryLowerStarIsoRightDerivedLowerShriek (ModuleCat.{u + 1} Λ)
        i)).rightAdjointUniq
      (rightDerivedUpperShriekAdjunction Λ i)

/-- `RΓ_Z(X, K) ≅ RΓ(X, Ri_! Ri^! K)`: the derived sections with support in `Z` are the derived
global sections of the supported term of the localization triangle. -/
noncomputable def rightDerivedSectionsWithSupportIso :
    rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) i ≅
      R(i)^![Λ] ⋙ R(i)_![ModuleCat.{u + 1} Λ] ⋙ rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X
          :=
  (rightDerivedClosedUpperShriekCompIso (ModuleCat.{u + 1} Λ) i).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedClosedUpperShriekIso Λ i) _ ≪≫
    Functor.isoWhiskerLeft _ ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u
        + 1} Λ) i).symm ≪≫
      Functor.isoWhiskerRight (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ)
          i).symm _)

end UpperShriek

section Triangle

variable {T B C D : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T) (d : D ⟶ T)
  [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
  (hd : Set.range d.base = Set.range b.base ∩ Set.range c.base)

lemma disjoint_range_openComplement_ι_of_subset {Z Z' : Scheme.{u}} (i : Z ⟶ T) (i' : Z' ⟶ T)
    [IsClosedImmersion i'] (h : Set.range i.base ⊆ Set.range i'.base) :
    Disjoint (Set.range i.base) (Set.range i'.openComplement.ι.base) := by
  refine Set.disjoint_of_subset_left h ?_
  rw [i'.range_eq_compl_range_openComplement_ι]
  exact disjoint_compl_left

instance (X : Scheme.{u}) : (rightDerivedGlobalSections A X).IsTriangulated :=
  inferInstanceAs ((Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctor.IsTriangulated)

end Triangle

end Etale

end AlgebraicGeometry
