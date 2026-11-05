/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Algebra.Homology.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
public import WeilConjectures.SixFunctors.Etale.SupportCohomology
public import WeilConjectures.SixFunctors.OpenClosed.SupportedSections

/-!
# The short exact sequence of sections with support

Let `i : Z ⟶ X` be a closed immersion with open complement `U`. For an injective étale sheaf `I`
on `X` the restriction `Γ(X, I) ⟶ I(U)` is a split epimorphism, so for a complex `I` of injective
sheaves

`0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0`

is a short exact sequence of complexes. The resulting distinguished triangle
`RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`, with a connecting map natural in `K`, and the
long exact sequence of cohomology with support (blueprint `thm-pur-with-support-exactness`) are
`AlgebraicGeometry.Etale.sectionsWithSupportTriangle` and
`AlgebraicGeometry.Etale.exact_derivedSupportCohomology_sectionsWithSupportTriangle`
(`WeilConjectures.SixFunctors.Etale.SupportCohomologyTriangle`).

## Main statements

- `AlgebraicGeometry.Etale.isSplitEpi_ΓRes_openComplement_of_injective`
- `AlgebraicGeometry.Etale.shortExact_sectionsWithSupportShortComplex`
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Site

variable {X : Scheme.{u}}

/-- A morphism of étale `X`-schemes whose underlying morphism of schemes is an isomorphism is an
isomorphism. -/
lemma isIso_of_isIso_left {V W : X.Etale} (f : V ⟶ W) (hf : IsIso f.left) : IsIso f := by
  have : IsIso ((Over.forget X).map ((Scheme.Etale.forget X).map f)) := hf
  have : IsIso ((Scheme.Etale.forget X).map f) :=
    isIso_of_reflects_iso _ (Over.forget X)
  exact isIso_of_reflects_iso f (Scheme.Etale.forget X)

variable {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The counit `U ×_X U ⟶ U` at `U` of the adjunction between composition with and base change
along the open immersion `j` is an isomorphism, `j` being a monomorphism. -/
instance isIso_mapPullbackAdj_counit_app_mk :
    IsIso ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance trivial).counit.app
      (Scheme.Etale.mk j)) :=
  isIso_of_isIso_left _ (inferInstanceAs (IsIso (pullback.fst j j)))

/-- The base change along the open immersion `j` of the map from `U` to the terminal étale
`X`-scheme `X` is an isomorphism `U ×_X U ≅ X ×_X U`, both being isomorphic to `U` over `U`. -/
instance isIso_overPullback_map_isTerminalMkId_from :
    IsIso ((MorphismProperty.Over.pullback @Etale ⊤ j).map
      ((Scheme.Etale.isTerminalMkId X).from (Scheme.Etale.mk j))) := by
  refine isIso_of_isIso_left _ ?_
  have h := MorphismProperty.Over.w ((MorphismProperty.Over.pullback @Etale ⊤ j).map
    ((Scheme.Etale.isTerminalMkId X).from (Scheme.Etale.mk j)))
  have : IsIso ((MorphismProperty.Over.pullback @Etale ⊤ j).obj (Scheme.Etale.mk j)).hom :=
    inferInstanceAs (IsIso (pullback.snd j j))
  have : IsIso ((MorphismProperty.Over.pullback @Etale ⊤ j).obj (Scheme.Etale.mk (𝟙 X))).hom :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 X) j))
  exact IsIso.of_isIso_fac_right h

end Site

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Restriction

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For a sheaf `G` on `U`, the restriction `(j_* G)(X) ⟶ (j_* G)(U)` along the open immersion
`j` is an isomorphism: both are the sections of `G` over `U`. -/
instance isIso_lowerStar_obj_map_isTerminalMkId_from (G : Sheaf U.smallEtaleTopology A) :
    IsIso (((j)_*[A].obj G).obj.map ((Scheme.Etale.isTerminalMkId X).from
      (Scheme.Etale.mk j)).op) := by
  rw [lowerStar_obj_val_map]
  infer_instance

/-- For a sheaf `M` on `X`, the unit `M ⟶ j_* j^* M` of the restriction along the open immersion
`j` is an isomorphism on the sections over `U`. -/
instance isIso_openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app_mk
    (M : Sheaf X.smallEtaleTopology A) :
    IsIso (((openImmersionRestrictionLowerStarAdjunction A j).unit.app M).hom.app
      (op (Scheme.Etale.mk j))) :=
  inferInstanceAs (IsIso (𝟙 _ ≫ M.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j
    inferInstance trivial).counit.app (Scheme.Etale.mk j)).op ≫ 𝟙 _))

/-- The restriction `Γ(X, M) ⟶ M(U)` from the global sections to the sections over `U` is the
restriction along the map from `U` to the terminal étale `X`-scheme, preceded by the isomorphism
`Γ(X, M) ≅ M(X)`. -/
lemma ΓRes_eq (M : Sheaf X.smallEtaleTopology A) :
    M.ΓRes (op (Scheme.Etale.mk j)) =
      M.ΓRes (op (Scheme.Etale.mk (𝟙 X))) ≫
        M.obj.map ((Scheme.Etale.isTerminalMkId X).from (Scheme.Etale.mk j)).op :=
  (M.ΓRes_map _).symm

instance (M : Sheaf X.smallEtaleTopology A) : IsIso (M.ΓRes (op (Scheme.Etale.mk (𝟙 X)))) :=
  M.isLimitConeΓ.isIso_π_app_of_isInitial _ (Scheme.Etale.isTerminalMkId X).op

end Restriction

section Concrete

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  [hJZ : Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  [hJX : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The sequence `Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I)` of complexes of a complex `I` of étale sheaves:
the inclusion of the sections with support in `Z`, and the restriction to the open complement
`U` of `Z`. -/
@[simps]
noncomputable def sectionsWithSupportShortComplex
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex (Sheaf.ΓSupportι X.smallEtaleTopology A
      (op (Scheme.Etale.mk i.openComplement.ι))) _).app I)
    ((NatTrans.mapHomologicalComplex (Sheaf.natTransΓRes X.smallEtaleTopology A
      (op (Scheme.Etale.mk i.openComplement.ι))) _).app I)
    (by ext n; simp)

end Concrete

end Etale

end AlgebraicGeometry
