/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidalComp
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# The projection formula along a refinement of compactifications

Let `f : X ⟶ Y` be a morphism of schemes and `r : c.Refinement d` a refinement of
compactifications of `f` whose square over `X` is cartesian, with `q = r.hom : c.Z ⟶ d.Z`.
For torsion coefficients, we show that the projection map
`PF_c : Rf_!(c)K ⊗ᴸ L ⟶ Rf_!(c)(K ⊗ᴸ Lf^*L)` of
`AlgebraicGeometry.Etale.projectionMapOfCompactification` is an isomorphism if and only if
`PF_d` is
(`AlgebraicGeometry.Etale.isIso_projectionMapOfCompactification_app_app_iff_of_refinement`).

Up to isomorphisms, `PF_c` is the projection map of `R(c.g)_*` at `(c.i)_! K`
(`AlgebraicGeometry.Etale.isIso_projectionMapOfCompactification_app_app_iff`). Since
`c.g = q ≫ d.g`, the comparison `L(c.g)^*(a ⊗ᴸ b) ⟶ L(c.g)^*a ⊗ᴸ L(c.g)^*b` is the composite
of those of `q` and `d.g`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_eq_compComparison`), so the
projection map of `R(c.g)_*` is, up to isomorphisms, the projection map of `R(d.g)_*` at
`Rq_*((c.i)_! K)` followed by `R(d.g)_*` of the projection map of `Rq_*` at `(c.i)_! K`. The
latter is an isomorphism: `(c.i)_! K ≅ Lq^*((d.i)_! K)` and the unit of `Lq^* ⊣ Rq_*` is an
isomorphism at extensions by zero along `d.i`
(`Etale.isIso_mapDerivedUpperStarLowerStarAdjunction_unit_app_openImmersionLowerShriek`).
Finally `Rq_*((c.i)_! K) ≅ (d.i)_! K`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The projection map `PF_c` of a compactification `c = (X ⟶[i] Z ⟶[g] Y)` at `(K, L)` is an
isomorphism if and only if the projection map of `Rg_*` at `(i_! K, L)` is: the other factors of
`PF_c` are isomorphisms. -/
lemma isIso_projectionMapOfCompactification_app_app_iff (c : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso (((projectionMapOfCompactification A c).app K).app L) ↔
      IsIso (((rightDerivedLowerStarProjectionMap A c.g).app (D((c.i)_!open[A]).obj K)).app L) := by
  rw [projectionMapOfCompactification_app_app, isIso_comp_right_iff]

/-- For `g' = q ≫ g`, the projection map of `Rg'_*` at `(N, L)` is an isomorphism if and only if
the composite
```
  Rg_*(Rq_* N) ⊗ᴸ L ⟶ Rg_*(Rq_* N ⊗ᴸ Lg^*L) ⟶ Rg_*(Rq_*(N ⊗ᴸ Lq^*Lg^*L))
```
of the projection maps of `Rg_*` and `Rq_*` is. -/
lemma isIso_rightDerivedLowerStarProjectionMap_app_app_iff_comp {Z W : Scheme.{u}} (q : Z ⟶ W)
    (g : W ⟶ Y) (g' : Z ⟶ Y) (h : g' = q ≫ g)
    (N : DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso (((rightDerivedLowerStarProjectionMap A g').app N).app L) ↔
      IsIso (((rightDerivedLowerStarProjectionMap A g).app (R((q)_*[A]).obj N)).app L ≫
        R((g)_*[A]).map (((rightDerivedLowerStarProjectionMap A q).app N).app
          (L((g)^*[A]).obj L))) := by
  unfold rightDerivedLowerStarProjectionMap
  rw [leftDerivedUpperStarTensorComparison_eq_compComparison A q g g' h]
  exact Adjunction.isIso_rightAdjointProjectionMap_compComparison_app_app_iff _ _ _ _ _ _ N L

end

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The unit of the derived adjunction `Lg^* ⊣ Rg_*` is an isomorphism at `X` if and only if the
unit of `D(g^*) ⊣ Rg_*` is: the left adjoints are isomorphic. -/
lemma isIso_derivedUpperStarLowerStarAdjunction_unit_app_iff {Z W : Scheme.{u}} (g : Z ⟶ W)
    (X : DerivedCategory (Sheaf W.smallEtaleTopology A)) :
    IsIso ((derivedUpperStarLowerStarAdjunction A g).unit.app X) ↔
      IsIso ((mapDerivedUpperStarLowerStarAdjunction A g).unit.app X) := by
  rw [← Adjunction.unit_leftAdjointUniq_hom_app (mapDerivedUpperStarLowerStarAdjunction A g)
    (derivedUpperStarLowerStarAdjunction A g), isIso_comp_right_iff]

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

/-- The unit of `Lq^* ⊣ Rq_*` at an extension by zero along `d.i` is an isomorphism, for a
refinement `r : c.Refinement d` with cartesian square over `X` and `q = r.hom`. -/
lemma isIso_derivedUpperStarLowerStarAdjunction_unit_app_openImmersionLowerShriek
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r.hom).unit.app
      (D((d.i)_!open[ModuleCat.{u + 1} Λ]).obj K)) := by
  rw [isIso_derivedUpperStarLowerStarAdjunction_unit_app_iff]
  exact isIso_mapDerivedUpperStarLowerStarAdjunction_unit_app_openImmersionLowerShriek r Λ hcart K

/-- The projection map of `Rq_*` at `((c.i)_! K, M)` is an isomorphism, for a refinement
`r : c.Refinement d` with cartesian square over `X` and `q = r.hom`: since
`(c.i)_! K ≅ Lq^*((d.i)_! K)`, this follows from the unit of `Lq^* ⊣ Rq_*` being an isomorphism
at `(d.i)_! K` and at `(d.i)_! K ⊗ᴸ M ≅ (d.i)_!(K ⊗ᴸ L(d.i)^* M)`. -/
lemma isIso_rightDerivedLowerStarProjectionMap_app_openImmersionLowerShriek_app
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : DerivedCategory (Sheaf d.Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) r.hom).app
      (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj K)).app M) := by
  have e : D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj K ≅
      L((r.hom)^*[ModuleCat.{u + 1} Λ]).obj (D((d.i)_!open[ModuleCat.{u + 1} Λ]).obj K) :=
    (refinementLowerShriekBaseChangeDerivedIso _ r hcart).app K ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory _ r.hom).symm.app _
  refine (NatTrans.isIso_app_iff_of_iso
    (((flipFunctor _ _ _).map (rightDerivedLowerStarProjectionMap _ r.hom)).app M) e).2 ?_
  have := isIso_derivedUpperStarLowerStarAdjunction_unit_app_openImmersionLowerShriek Λ r hcart K
  have : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r.hom).unit.app
      (((-⊗ᴸ-(d.Z)[ModuleCat.{u + 1} Λ]).obj (D((d.i)_!open[ModuleCat.{u + 1} Λ]).obj K)).obj
        M)) :=
    (NatTrans.isIso_app_iff_of_iso _
      (((derivedOpenImmersionLowerShriekProjectionIso _ d.i).app K).app M)).1
      (isIso_derivedUpperStarLowerStarAdjunction_unit_app_openImmersionLowerShriek Λ r hcart _)
  exact Adjunction.isIso_rightAdjointProjectionMap_app_obj_app _ _ _ _

/-- **The projection formula along a refinement of compactifications**, for torsion
coefficients: for a refinement `r : c.Refinement d` whose square over `X` is cartesian, the
projection map `PF_c` at `(K, L)` is an isomorphism if and only if `PF_d` is. -/
theorem isIso_projectionMapOfCompactification_app_app_iff_of_refinement
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c).app K).app L) ↔
      IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) d).app K).app L) := by
  rw [isIso_projectionMapOfCompactification_app_app_iff,
    isIso_projectionMapOfCompactification_app_app_iff,
    isIso_rightDerivedLowerStarProjectionMap_app_app_iff_comp _ r.hom d.g c.g r.hom_g.symm]
  have := isIso_rightDerivedLowerStarProjectionMap_app_openImmersionLowerShriek_app Λ r hcart K
    (L((d.g)^*[ModuleCat.{u + 1} Λ]).obj L)
  have := isIso_mapDerivedUpperStarLowerStarAdjunction_unit_app_openImmersionLowerShriek r Λ hcart K
  rw [isIso_comp_right_iff]
  exact NatTrans.isIso_app_iff_of_iso
    (((flipFunctor _ _ _).map (rightDerivedLowerStarProjectionMap _ d.g)).app L)
    ((R((r.hom)_*[ModuleCat.{u + 1} Λ])).mapIso
        ((refinementLowerShriekBaseChangeDerivedIso _ r hcart).app K) ≪≫
      (asIso ((mapDerivedUpperStarLowerStarAdjunction _ r.hom).unit.app _)).symm)

end Torsion

end Etale

end AlgebraicGeometry
