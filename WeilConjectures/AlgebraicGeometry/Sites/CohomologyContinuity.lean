/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.Sites.LimitSystem.Cartesian
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyModuleForget
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuityDefs
public import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules

/-!
# Continuity of étale cohomology at inverse limits

Let `(Xᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over a scheme `S`, with
affine transition maps and limit `X`, and let `F` be an étale sheaf on `S`. Then
`H^q(X, F|_X) = colimᵢ H^q(Xᵢ, F|_{Xᵢ})` ([Stacks, Tag 09YQ]). This is blueprint
`lemma-weil-pbc-etale-cohomology-continuity`, proved for abelian sheaves in
`AlgebraicGeometry.Etale.cohomologyMap_isColimit_of_isLimit'` by dimension shifting along systems
of sheaves (`WeilConjectures.AlgebraicGeometry.Sites.LimitSystem`).

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- Blueprint `lemma-weil-pbc-etale-cohomology-continuity`: Etale cohomology continuity, in the
form of an elementwise colimit statement for the pullback maps.

Let `(Dᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over `S` with affine
transition maps, with limit `X = c.pt`, and let `F` be an abelian étale sheaf on `S`. Then
`Hᵠ(X, F|_X) = colimᵢ Hᵠ(Dᵢ, F|_{Dᵢ})` along the pullback maps
`AlgebraicGeometry.Etale.cohomologyMap`: every class on `X` comes from some `Dᵢ` (up to the
canonical identification `F|_X ≅ (F|_{Dᵢ})|_X` of `AlgebraicGeometry.Etale.upperStarComp`), and a
class on `Dᵢ` which vanishes on `X` already vanishes on some `Dⱼ`, `j ⟶ i`. -/
theorem cohomologyMap_isColimit_of_isLimit {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) {I : Type u} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ Over S) [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left] [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℕ) :
    (∀ x : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} c.pt.hom).obj F) q,
      ∃ (i : I) (y : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F) q),
        Etale.cohomologyMap (c.π.app i).left _ q y =
          Sheaf.H.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} (c.π.app i).left (D.obj i).hom
            c.pt.hom (Over.w (c.π.app i)).symm).hom.app F) q x) ∧
    ∀ (i : I) (y : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F) q),
      Etale.cohomologyMap (c.π.app i).left _ q y = 0 →
        ∃ (j : I) (g : j ⟶ i), Etale.cohomologyMap (D.map g).left _ q y = 0 :=
  cohomologyMap_isColimit_of_isLimit' F D c hc q


/-- The coefficient categories `A` for which étale cohomology with values in `A` is continuous
at cofiltered limits of quasi-compact quasi-separated schemes with affine transition maps, in the
vanishing form of `AlgebraicGeometry.Etale.isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit`.
Instances: abelian groups and modules over a finite ring. -/
class HasCohomologyContinuity : Prop where
  isZero_rightDerived_of_isLimit : ∀ {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology A)
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Over S)
    [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
    [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left] (c : Cone D)
    (_ : IsLimit ((Over.forget S).mapCone c)) (q : ℕ),
    (∀ i, IsZero (((sectionsFunctor A (D.obj i).left).rightDerived q).obj
      ((Etale.upperStar A (D.obj i).hom).obj F))) →
    IsZero (((sectionsFunctor A c.pt.left).rightDerived q).obj
      ((Etale.upperStar A c.pt.hom).obj F))

/-- Blueprint `lemma-weil-pbc-etale-cohomology-continuity`: Etale cohomology continuity.

Let `(Dᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over `S` with affine
transition maps, with limit `X = c.pt`, and let `F` be an étale sheaf on `S` with coefficients in
abelian groups or in modules over a finite ring (`AlgebraicGeometry.Etale.HasCohomologyContinuity`).
Then `H^q(X, F|_X) = colimᵢ H^q(Dᵢ, F|_{Dᵢ})`; in particular `H^q(X, F|_X)` vanishes as soon as all
the `H^q(Dᵢ, F|_{Dᵢ})` do. -/
theorem isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit [HasCohomologyContinuity A]
    {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology A) {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over S) [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left] [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℕ)
    (h : ∀ i, IsZero (((sectionsFunctor A (D.obj i).left).rightDerived q).obj
      ((Etale.upperStar A (D.obj i).hom).obj F))) :
    IsZero (((sectionsFunctor A c.pt.left).rightDerived q).obj
      ((Etale.upperStar A c.pt.hom).obj F)) :=
  HasCohomologyContinuity.isZero_rightDerived_of_isLimit F D c hc q h

instance hasCohomologyContinuity_addCommGrpCat :
    HasCohomologyContinuity AddCommGrpCat.{u + 1} where
  isZero_rightDerived_of_isLimit := by
    intro S F I _ _ D _ _ _ c hc q h
    refine (Sheaf.subsingleton_H_iff_isZero_rightDerived c.pt.left.smallEtaleTopology
      (MorphismProperty.Over.mkIdTerminal _ c.pt.left) q _).1 ?_
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨i, y, hy⟩ := (cohomologyMap_isColimit_of_isLimit' F D c hc q).1 x
    have : Subsingleton
        (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F) q) :=
      (Sheaf.subsingleton_H_iff_isZero_rightDerived (D.obj i).left.smallEtaleTopology
        (MorphismProperty.Over.mkIdTerminal _ (D.obj i).left) q _).2 (h i)
    rw [Subsingleton.elim y 0, map_zero] at hy
    exact eq_zero_of_sheafH_map_eq_zero _ hy.symm

instance hasCohomologyContinuity_moduleCat (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    HasCohomologyContinuity (ModuleCat.{u + 1} Λ) where
  isZero_rightDerived_of_isLimit := by
    intro S F I _ _ D _ _ _ c hc q h
    rw [isZero_rightDerived_sectionsFunctor_iff_forget₂]
    obtain ⟨e⟩ := pullback_forget_modules_iso Λ c.pt.hom F
    refine IsZero.of_iso ?_ (((sectionsFunctor _ _).rightDerived q).mapIso e)
    refine HasCohomologyContinuity.isZero_rightDerived_of_isLimit (A := AddCommGrpCat.{u + 1})
      _ D c hc q fun i ↦ ?_
    obtain ⟨e'⟩ := pullback_forget_modules_iso Λ (D.obj i).hom F
    exact ((isZero_rightDerived_sectionsFunctor_iff_forget₂ _ q).1 (h i)).of_iso
      (((sectionsFunctor _ _).rightDerived q).mapIso e'.symm)

end AlgebraicGeometry.Etale
