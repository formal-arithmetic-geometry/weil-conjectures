/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.ExtendScalars

/-!
# Coherence of the commutation of derived scalar extension with `Lg^*`

The isomorphisms `Lg^*(K ⊗ᴸ_R S) ≅ (Lg^* K) ⊗ᴸ_R S` of
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso` are compatible with the
identity isomorphisms `L(𝟙 Y)^* ≅ 𝟭`, with the composition isomorphisms
`L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` and with the transport along equalities of morphisms
(blueprint `thm-trf-finite-coefficient-map`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
  {Y Z : Scheme.{u}} (g : Z ⟶ Y)

/-- `leftDerivedUpperStarExtendScalarsIso` is compatible with the identifications
`L(𝟙 Y)^* ≅ 𝟭`. -/
@[reassoc]
lemma leftDerivedUpperStarExtendScalarsIso_hom_app_id
    (K : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))) :
    (leftDerivedUpperStarExtendScalarsIso R S (𝟙 Y)).hom.app K ≫
        L(sheafExtendScalars (algebraMap R S) Y).map
          ((leftDerivedUpperStarId (ModuleCat.{u + 1} R) Y).hom.app K) =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} S) Y).hom.app
        (L(sheafExtendScalars (algebraMap R S) Y).obj K) := by
  sorry

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
          (L((g)^*[ModuleCat.{u + 1} R]).obj K) := by
  sorry

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

end AlgebraicGeometry.ProEtale
