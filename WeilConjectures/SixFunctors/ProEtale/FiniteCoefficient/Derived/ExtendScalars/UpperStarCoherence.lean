/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Functor.Derived.LeftDerivedCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStarCounit
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionCoherence

/-!
# Coherence of the commutation of derived scalar extension with `Lg^*`

The isomorphisms `Lg^*(K ⊗ᴸ_R S) ≅ (Lg^* K) ⊗ᴸ_R S` of
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso` are compatible with the
identity isomorphisms `L(𝟙 Y)^* ≅ 𝟭`, with the composition isomorphisms
`L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` and with the transport along equalities of morphisms
(blueprint `thm-trf-finite-coefficient-map`).

## Implementation notes

The coherence statements are instances of general statements about natural transformations
induced on homotopy categories (`NatTrans.app_comp_map_mapHomotopyCategory_app` and
`NatTrans.app_comp_map_mapHomotopyCategory_app_eq_comp`) and on left derived functors
(`Functor.leftDerived_app_comp_map_app_eq_app` and
`Functor.leftDerived_app_comp_map_app_eq_app_comp`), applied once. Proving them directly at the
concrete pro-étale sheaf categories makes the kernel unfold the concrete derived categories and
the instances of the homotopy categories at every rewriting step.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]

section HomotopyCategory

/-- On the image of a complex, `mapHomotopyCategorySheafExtendScalarsCompUpperStarIso` is induced
by `sheafExtendScalarsCompUpperStarIso` degreewise. This holds by definition; a proof by `simp`
or `erw` makes the kernel unfold the concrete functors. -/
lemma mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_quotient
    {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (C : HomologicalComplex (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).hom.app
        ((HomotopyCategory.quotient _ _).obj C) =
      (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
        (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom (.up ℤ)).app C) :=
  rfl

/-- `mapHomotopyCategorySheafExtendScalarsCompUpperStarIso` is compatible with the identity
isomorphisms `(𝟙 X)^* ≅ 𝟭`. -/
lemma mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_id (X : Scheme.{u})
    (K : HomotopyCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S (𝟙 X)).hom.app K ≫
        ((sheafExtendScalars (algebraMap R S) X).mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory
            (ProEtale.upperStarId (ModuleCat.{u + 1} R) X).hom (.up ℤ)).app K) =
      (NatTrans.mapHomotopyCategory (ProEtale.upperStarId (ModuleCat.{u + 1} S) X).hom
        (.up ℤ)).app
          (((sheafExtendScalars (algebraMap R S) X).mapHomotopyCategory (.up ℤ)).obj K) :=
  NatTrans.app_comp_map_mapHomotopyCategory_app
    (e := (sheafExtendScalarsCompUpperStarIso (algebraMap R S) (𝟙 X)).hom)
    (e' := (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S (𝟙 X)).hom)
    (he' := mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_quotient R S (𝟙 X))
    (α := (ProEtale.upperStarId (ModuleCat.{u + 1} R) X).hom)
    (β := (ProEtale.upperStarId (ModuleCat.{u + 1} S) X).hom)
    (h := sheafExtendScalarsCompUpperStarIso_hom_app_id (algebraMap R S) X) K

/-- `mapHomotopyCategorySheafExtendScalarsCompUpperStarIso` is compatible with the composition
isomorphisms `(g₁ ≫ g)^* ≅ g^* ⋙ g₁^*`. -/
lemma mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_comp {T Z Y : Scheme.{u}}
    (g₁ : T ⟶ Z) (g : Z ⟶ Y)
    (K : HomotopyCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S (g₁ ≫ g)).hom.app K ≫
        ((sheafExtendScalars (algebraMap R S) T).mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory
            (ProEtale.upperStarComp (ModuleCat.{u + 1} R) g₁ g).hom (.up ℤ)).app K) =
      (NatTrans.mapHomotopyCategory (ProEtale.upperStarComp (ModuleCat.{u + 1} S) g₁ g).hom
          (.up ℤ)).app
            (((sheafExtendScalars (algebraMap R S) Y).mapHomotopyCategory (.up ℤ)).obj K) ≫
        ((g₁)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ)).map
          ((mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).hom.app K) ≫
        (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g₁).hom.app
          (((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ)).obj K) :=
  NatTrans.app_comp_map_mapHomotopyCategory_app_eq_comp
    (e := (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom)
    (e₁ := (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g₁).hom)
    (e₁₂ := (sheafExtendScalarsCompUpperStarIso (algebraMap R S) (g₁ ≫ g)).hom)
    (e' := (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).hom)
    (e₁' := (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g₁).hom)
    (e₁₂' := (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S (g₁ ≫ g)).hom)
    (he' := mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_quotient R S g)
    (he₁' := fun _ ↦
      mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_quotient R S g₁ _)
    (he₁₂' :=
      mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_quotient R S (g₁ ≫ g))
    (γR := (ProEtale.upperStarComp (ModuleCat.{u + 1} R) g₁ g).hom)
    (γS := (ProEtale.upperStarComp (ModuleCat.{u + 1} S) g₁ g).hom)
    (h := sheafExtendScalarsCompUpperStarIso_hom_app_comp (algebraMap R S) g₁ g) K

end HomotopyCategory

variable [IsNoetherianRing R] {Y Z : Scheme.{u}} (g : Z ⟶ Y)

/-- `leftDerivedUpperStarExtendScalarsIso` is compatible with the identifications
`L(𝟙 Y)^* ≅ 𝟭`. -/
@[reassoc]
lemma leftDerivedUpperStarExtendScalarsIso_hom_app_id
    (K : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))) :
    (leftDerivedUpperStarExtendScalarsIso R S (𝟙 Y)).hom.app K ≫
        L(sheafExtendScalars (algebraMap R S) Y).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} R) Y).hom.app K) =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} S) Y).hom.app
        (L(sheafExtendScalars (algebraMap R S) Y).obj K) :=
  Functor.leftDerived_app_comp_map_app_eq_app (HomotopyCategory.quasiIso _ (.up ℤ))
    (αE := (sheafExtendScalars (algebraMap R S) Y).leftDerivedFunctorCounit)
    (αp := ((𝟙 Y)^*[ModuleCat.{u + 1} R]).leftDerivedFunctorCounit)
    (αq := ((𝟙 Y)^*[ModuleCat.{u + 1} S]).leftDerivedFunctorCounit)
    (Φ := (leftDerivedUpperStarExtendScalarsIso R S (𝟙 Y)).hom)
    (eH := (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S (𝟙 Y)).hom)
    (hΦ := leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit R S (𝟙 Y))
    (ιR := (leftDerivedUpperStarId (ModuleCat.{u + 1} R) Y).hom)
    (βR := (ProEtale.upperStarId (ModuleCat.{u + 1} R) Y).hom)
    (hR := leftDerivedUpperStarId_hom_app_Qh (ModuleCat.{u + 1} R) Y)
    (ιS := (leftDerivedUpperStarId (ModuleCat.{u + 1} S) Y).hom)
    (βS := (ProEtale.upperStarId (ModuleCat.{u + 1} S) Y).hom)
    (hS := leftDerivedUpperStarId_hom_app_Qh (ModuleCat.{u + 1} S) Y)
    (he := mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_id R S Y) K

/-- `leftDerivedUpperStarExtendScalarsIso` is compatible with the composition isomorphisms
`L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*`. -/
@[reassoc]
lemma leftDerivedUpperStarExtendScalarsIso_hom_app_comp {T : Scheme.{u}} (g₁ : T ⟶ Z)
    (K : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))) :
    (leftDerivedUpperStarExtendScalarsIso R S (g₁ ≫ g)).hom.app K ≫
        L(sheafExtendScalars (algebraMap R S) T).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} R) g₁ g).hom.app K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} S) g₁ g).hom.app
          (L(sheafExtendScalars (algebraMap R S) Y).obj K) ≫
        L((g₁)^*[ModuleCat.{u + 1} S]).map
          ((leftDerivedUpperStarExtendScalarsIso R S g).hom.app K) ≫
        (leftDerivedUpperStarExtendScalarsIso R S g₁).hom.app
          (L((g)^*[ModuleCat.{u + 1} R]).obj K) :=
  Functor.leftDerived_app_comp_map_app_eq_app_comp (HomotopyCategory.quasiIso _ (.up ℤ))
    (αEY := (sheafExtendScalars (algebraMap R S) Y).leftDerivedFunctorCounit)
    (αEZ := (sheafExtendScalars (algebraMap R S) Z).leftDerivedFunctorCounit)
    (αET := (sheafExtendScalars (algebraMap R S) T).leftDerivedFunctorCounit)
    (αp := ((g)^*[ModuleCat.{u + 1} R]).leftDerivedFunctorCounit)
    (αp₁ := ((g₁)^*[ModuleCat.{u + 1} R]).leftDerivedFunctorCounit)
    (αp₁₂ := ((g₁ ≫ g)^*[ModuleCat.{u + 1} R]).leftDerivedFunctorCounit)
    (αq := ((g)^*[ModuleCat.{u + 1} S]).leftDerivedFunctorCounit)
    (αq₁ := ((g₁)^*[ModuleCat.{u + 1} S]).leftDerivedFunctorCounit)
    (αq₁₂ := ((g₁ ≫ g)^*[ModuleCat.{u + 1} S]).leftDerivedFunctorCounit)
    (hLp₁₂ := isLeftDerivedFunctor_leftDerivedUpperStarSheafExtendScalars R S (g₁ ≫ g))
    (Φ := (leftDerivedUpperStarExtendScalarsIso R S g).hom)
    (eH := (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).hom)
    (hΦ := leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit R S g)
    (Φ₁ := (leftDerivedUpperStarExtendScalarsIso R S g₁).hom)
    (e₁H := (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g₁).hom)
    (hΦ₁ := leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit R S g₁)
    (Φ₁₂ := (leftDerivedUpperStarExtendScalarsIso R S (g₁ ≫ g)).hom)
    (e₁₂H := (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S (g₁ ≫ g)).hom)
    (hΦ₁₂ := leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit R S (g₁ ≫ g))
    (cR := leftDerivedUpperStarComp (ModuleCat.{u + 1} R) g₁ g)
    (γR := ProEtale.upperStarComp (ModuleCat.{u + 1} R) g₁ g)
    (hcR := leftDerivedUpperStarComp_inv_app_Qh (ModuleCat.{u + 1} R) g₁ g)
    (cS := (leftDerivedUpperStarComp (ModuleCat.{u + 1} S) g₁ g).hom)
    (γS := (ProEtale.upperStarComp (ModuleCat.{u + 1} S) g₁ g).hom)
    (hcS := leftDerivedUpperStarComp_hom_app_Qh (ModuleCat.{u + 1} S) g₁ g)
    (he := mapHomotopyCategorySheafExtendScalarsCompUpperStarIso_hom_app_comp R S g₁ g) K

/-- `leftDerivedUpperStarExtendScalarsIso` is compatible with the transport
`leftDerivedUpperStarCongr` along an equality of morphisms. -/
@[reassoc]
lemma leftDerivedUpperStarExtendScalarsIso_hom_app_congr {g' : Z ⟶ Y} (h : g = g')
    (K : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))) :
    (leftDerivedUpperStarExtendScalarsIso R S g).hom.app K ≫
        L(sheafExtendScalars (algebraMap R S) Z).map
          ((leftDerivedUpperStarCongr (ModuleCat.{u + 1} R) h).hom.app K) =
      (leftDerivedUpperStarCongr (ModuleCat.{u + 1} S) h).hom.app
          (L(sheafExtendScalars (algebraMap R S) Y).obj K) ≫
        (leftDerivedUpperStarExtendScalarsIso R S g').hom.app K := by
  subst h
  simp

/-- The inverse form of `leftDerivedUpperStarExtendScalarsIso_hom_app_congr`. -/
@[reassoc]
lemma leftDerivedUpperStarExtendScalarsIso_hom_app_congr_inv {g' : Z ⟶ Y} (h : g = g')
    (K : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))) :
    (leftDerivedUpperStarExtendScalarsIso R S g').hom.app K ≫
        L(sheafExtendScalars (algebraMap R S) Z).map
          ((leftDerivedUpperStarCongr (ModuleCat.{u + 1} R) h).inv.app K) =
      (leftDerivedUpperStarCongr (ModuleCat.{u + 1} S) h).inv.app
          (L(sheafExtendScalars (algebraMap R S) Y).obj K) ≫
        (leftDerivedUpperStarExtendScalarsIso R S g).hom.app K := by
  subst h
  simp

end AlgebraicGeometry.ProEtale
