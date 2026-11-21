/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeIntegralRational
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeIntegral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangePadicAlgCl.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClLowerStarHom

/-!

# The pullback comparisons of the `ℓ`-adic coefficient changes and composition

The comparisons **(Pull)** `Lf^* ⋙ T ≅ T ⋙ Lf^*` on bounded constructible complexes, for the
extensions of scalars `T` along `𝒪_E ⟶ E`
(`ProEtale.CondensedRing.boundedConstructibleUpperStarExtendScalarsIso`) and `E ⟶ ℚ̄_ℓ`
(`ProEtale.CondensedRing.boundedConstructibleUpperStarToPadicAlgClIso`), are compatible with the
composition isomorphisms `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`
(`ProEtale.CondensedRing.boundedConstructibleUpperStarExtendScalarsIso_hom_app_comp`,
`ProEtale.CondensedRing.boundedConstructibleUpperStarToPadicAlgClIso_hom_app_comp`). Both are
restrictions of the coherence of the derived comparison `derivedPullIso` for flat coefficient
changes (`ProEtale.CondensedRing.derivedPullIsoCompCoherence`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- The pullback comparisons for `𝒪_E ⟶ E` are compatible with the composition
isomorphisms of the pullbacks. -/
theorem boundedConstructibleUpperStarExtendScalarsIso_hom_app_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : Dᵇc(Z.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    (boundedConstructibleUpperStarExtendScalarsIso ℓ E (f ≫ g)).hom.app K ≫
        (boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj E.1) ℓ f g).hom.app
          ((boundedConstructibleExtendScalars Z.left ℓ E).obj K) =
      (boundedConstructibleExtendScalars X.left ℓ E).map
          ((boundedConstructibleUpperStarComp
            (Profinite.padicIntegersRingObj ℓ E.1) ℓ f g).hom.app K) ≫
        (boundedConstructibleUpperStarExtendScalarsIso ℓ E f).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ g).obj K) ≫
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E.1) ℓ f).map
          ((boundedConstructibleUpperStarExtendScalarsIso ℓ E g).hom.app K) := by
  ext
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    boundedConstructibleUpperStarExtendScalarsIso_hom_app_hom,
    boundedConstructibleUpperStarComp_hom_app_hom, boundedConstructibleExtendScalars_map_hom,
    boundedConstructibleUpperStar_map_hom, Over.comp_left,
    boundedConstructibleExtendScalars_obj_obj,
    boundedConstructibleUpperStar_obj_obj]
  convert derivedPullIsoCompCoherence (padicIntegersRingObjToContinuousMapRingObj ℓ E) f.left
    g.left K.obj

/-- The pullback comparisons for `E ⟶ ℚ̄_ℓ` are compatible with the composition
isomorphisms of the pullbacks. -/
theorem boundedConstructibleUpperStarToPadicAlgClIso_hom_app_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : Dᵇc(Z.left)⟦Profinite.continuousMapRingObj E.1⟧) :
    (boundedConstructibleUpperStarToPadicAlgClIso ℓ E (f ≫ g)).hom.app K ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).hom.app
          ((boundedConstructibleToPadicAlgCl Z.left ℓ E).obj K) =
      (boundedConstructibleToPadicAlgCl X.left ℓ E).map
          ((boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj E.1) ℓ f g).hom.app
            K) ≫
        (boundedConstructibleUpperStarToPadicAlgClIso ℓ E f).hom.app
          ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E.1) ℓ g).obj K) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map
          ((boundedConstructibleUpperStarToPadicAlgClIso ℓ E g).hom.app K) := by
  ext
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    boundedConstructibleUpperStarToPadicAlgClIso_hom_app_hom,
    boundedConstructibleUpperStarComp_hom_app_hom, boundedConstructibleToPadicAlgCl_map_hom,
    boundedConstructibleUpperStar_map_hom, Over.comp_left,
    boundedConstructibleToPadicAlgCl_obj_obj,
    boundedConstructibleUpperStar_obj_obj]
  convert derivedPullIsoCompCoherence (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f.left
    g.left K.obj

end AlgebraicGeometry.ProEtale.CondensedRing
