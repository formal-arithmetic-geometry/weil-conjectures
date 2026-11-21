/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Finite.Exact

/-!
# Unbounded derived global sections and the Leray isomorphisms

Inputs of the ordinary Künneth formula about the derived global sections
`RΓ(X, -) : D(X_ét) ⥤ D(A)` on the *unbounded* derived category and the composition of derived
direct images.

## Main definitions and results

- `AlgebraicGeometry.Etale.rightDerivedGlobalSectionsObjQIso`.
- `AlgebraicGeometry.Etale.isIso_Q_map_globalSections_of_quasiIso`.
- `AlgebraicGeometry.Etale.rightDerivedGlobalSectionsPlusCompatibility`.
- `AlgebraicGeometry.Etale.isGE_rightDerivedLowerStar_obj'`.
- `AlgebraicGeometry.Etale.rightDerivedPlusLowerStarCompGlobalSectionsIso`.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarCompGlobalSectionsIso`.
- `AlgebraicGeometry.Etale.rightDerivedCompIsoOfIsFinite`.

## Implementation details

`RΓ(X, -)` is the total right derived functor
`AlgebraicGeometry.Etale.rightDerivedGlobalSections`, computed with K-injective resolutions,
which exist in the Grothendieck abelian category of étale sheaves. The direct images `f_*`
preserve K-injective complexes (being right adjoint to the exact `f^*`), so the Leray
isomorphism `RΓ(Y, Rf_* E) ≅ RΓ(X, E)` holds on the whole unbounded derived category, for every
morphism `f` and every coefficient category, without finiteness hypotheses.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- For a K-injective complex `I` of étale sheaves on `X`, the derived global sections are
computed by applying `Γ(X, -)` termwise: `RΓ(X, I) ≅ Γ(X, I)`. -/
noncomputable def rightDerivedGlobalSectionsObjQIso (X : Scheme.{u})
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) [I.IsKInjective] :
    (rightDerivedGlobalSections A X).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (((Sheaf.Γ X.smallEtaleTopology A).mapHomologicalComplex _).obj I) :=
  (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorObjQIso I

omit [HasSmallSiteSheafify A] in
/-- If `I` and `J` are K-injective complexes
of étale sheaves and `φ : I ⟶ J` is a quasi-isomorphism (for instance a comparison of two
K-injective resolutions of the same complex), then `Γ(X, φ) : Γ(X, I) ⟶ Γ(X, J)` is an
isomorphism in `D(A)`. -/
lemma isIso_Q_map_globalSections_of_quasiIso {X : Scheme.{u}}
    {I J : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ} [I.IsKInjective] [J.IsKInjective]
    (φ : I ⟶ J) [QuasiIso φ] :
    IsIso (DerivedCategory.Q.map
      (((Sheaf.Γ X.smallEtaleTopology A).mapHomologicalComplex _).map φ)) := by
  let F := Sheaf.Γ X.smallEtaleTopology A
  have h := F.rightDerivedFunctorUnit.naturality ((HomotopyCategory.quotient _ _).map φ)
  have : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map φ)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) φ).2 (by
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
      infer_instance)
  have : IsIso ((DerivedCategory.Qh ⋙ R(F)).map ((HomotopyCategory.quotient _ _).map φ)) := by
    dsimp only [Functor.comp_map]
    infer_instance
  have : IsIso ((F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map
      ((HomotopyCategory.quotient _ _).map φ)) :=
    IsIso.of_isIso_fac_right h
  exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) _).1 this

/-- On the bounded below derived category, the
unbounded derived global sections `RΓ(X, -)` (computed with K-injective resolutions) agree
canonically with the bounded below derived functor `R⁺Γ(X, -)` (computed with injective
resolutions). -/
noncomputable def rightDerivedGlobalSectionsPlusCompatibility (X : Scheme.{u}) :
    (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ rightDerivedGlobalSections A X :=
  (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorPlusCompatibility

omit [HasSmallSiteSheafify A] in
/-- The derived direct image is left t-exact: for a morphism
of schemes `f : X ⟶ Y` and `E ∈ D(X_ét)` with `H^i(E) = 0` for `i < b`, also
`H^i(Rf_* E) = 0` for `i < b`. (No boundedness of `E` is needed.) -/
lemma isGE_rightDerivedLowerStar_obj' {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) (b : ℤ) [E.IsGE b] :
    ((R((f)_*[A])).obj E).IsGE b :=
  ((f)_*[A]).isGE_rightDerivedFunctor_obj E b

/-- The Leray isomorphism on the bounded below derived
categories: for a morphism of schemes `f : X ⟶ Y`, `R⁺Γ(Y, R⁺f_* E) ≅ R⁺Γ(X, E)`, naturally in
`E ∈ D⁺(X_ét)`. -/
noncomputable def rightDerivedPlusLowerStarCompGlobalSectionsIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    ((f)_*[A]).rightDerivedFunctorPlus ⋙ (Sheaf.Γ Y.smallEtaleTopology A).rightDerivedFunctorPlus ≅
      (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorPlus :=
  have : ((f)_*[A]).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A f)
  Functor.rightDerivedFunctorPlusCompIso' _ _ (lowerStarCompGlobalSectionsIso A f)

/-- The Leray isomorphism `RΓ(Y, Rf_* E) ≅ RΓ(X, E)` for every morphism `f` and every
`E` in the *unbounded* derived category `D(X_ét)`, naturally in `E`. -/
noncomputable def rightDerivedLowerStarCompGlobalSectionsIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R((f)_*[A]) ⋙ rightDerivedGlobalSections A Y ≅ rightDerivedGlobalSections A X :=
  rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Let `π : X' ⟶ X` be a finite morphism and `h : Z ⟶ X'`
any morphism of schemes. For every étale sheaf `G` of `Λ`-modules on `Z` and every `q ≥ 0`,
`R^q(π ∘ h)_* G ≅ π_* R^q h_* G`. -/
noncomputable def rightDerivedCompIsoOfIsFinite {Z X' X : Scheme.{u}} (h : Z ⟶ X')
    (π : X' ⟶ X) [IsFinite π] (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (q : ℕ) :
    (((h ≫ π)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj G ≅
      (π)_*[ModuleCat.{u + 1} Λ].obj ((((h)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj G) :=
  (((h ≫ π)_*[ModuleCat.{u + 1} Λ]).homologyRightDerivedFunctorObjSingleFunctorIso G q).symm ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) h π).symm.app _ ≪≫
        (Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) π).app
          _) ≪≫
    ((π)_*[ModuleCat.{u + 1} Λ].mapDerivedCategoryHomologyFunctorIso q).symm.app _ ≪≫
    (π)_*[ModuleCat.{u + 1} Λ].mapIso
      (((h)_*[ModuleCat.{u + 1} Λ]).homologyRightDerivedFunctorObjSingleFunctorIso G q)

end Finite

end AlgebraicGeometry.Etale
