/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.TmpLowerShriekIterateFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap

/-!
# The inverse of the absolute Frobenius of the base

Let `s` be a scheme of characteristic `p` whose absolute `p ^ n`-power Frobenius `F_s` is proper,
and let `w` be an inverse of `F_s`. The trivialization `L(F_s)^* ≅ 𝟭` induces an isomorphism
`𝟭 ≅ Lw^*`, hence, with the counit of `Lw^* ⊣ Rw_*` and `Rw_! ≅ Rw_*`, an isomorphism
`Rw_! ≅ 𝟭`. This file shows that it is compatible with the composition isomorphism
`R(w ≫ F_s)_! ≅ Rw_! ⋙ R(F_s)_!`, the trivialization `R(F_s)_! ≅ 𝟭` and `R(𝟙)_! ≅ 𝟭`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso_hom_app_comp_iterateFrobenius`), and
the analogous statement for the direct images
(`AlgebraicGeometry.Etale.rightDerivedLowerStarCompIsoOfComp_inv_app_comp_iterateFrobenius`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} (hp : p.Prime) (n : ℕ) {s : Scheme.{u}}
  (hs : (p : Γ(s, ⊤)) = 0)

/-- For an inverse `w` of the absolute Frobenius of `s`, the composition isomorphism
`Rw_* ⋙ R(F_s)_* ≅ R(𝟙)_*`, the trivialization of `R(F_s)_*`, the isomorphism `𝟭 ≅ Lw^*` and the
counit of `Lw^* ⊣ Rw_*` compose to `R(𝟙)_* ≅ 𝟭`. -/
lemma rightDerivedLowerStarCompIsoOfComp_inv_app_comp_iterateFrobenius {w : s ⟶ s}
    (hw : w ≫ s.iterateFrobenius hp hs n = 𝟙 s)
    (N : DerivedCategory (Sheaf s.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} Λ) w (s.iterateFrobenius hp hs n)
        (𝟙 s) hw).inv.app N ≫
      (rightDerivedLowerStarIterateFrobeniusIso Λ hp n hs).hom.app
        ((R((w)_*[ModuleCat.{u + 1} Λ])).obj N) ≫
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) s).inv.app
        ((R((w)_*[ModuleCat.{u + 1} Λ])).obj N) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) w (s.iterateFrobenius hp hs n) (𝟙 s)
        hw.symm).hom.app ((R((w)_*[ModuleCat.{u + 1} Λ])).obj N) ≫
      (L((w)^*[ModuleCat.{u + 1} Λ])).map
        ((leftDerivedUpperStarIterateFrobeniusTriv Λ hp n hs).hom.app
          ((R((w)_*[ModuleCat.{u + 1} Λ])).obj N)) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) w).counit.app N =
    (rightDerivedLowerStarIdNatIso Λ s).hom.app N := by
  have hc := derivedUpperStarLowerStarAdjunction_id_counit_app Λ s N
  have hk := map_rightDerivedLowerStarCompIsoOfComp_hom_app_comp_counit (ModuleCat.{u + 1} Λ) w
    (s.iterateFrobenius hp hs n) (𝟙 s) hw N
  have hu := Adjunction.rightAdjointUniq_ofNatIsoLeft_id_hom_app_counit
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (s.iterateFrobenius hp hs n))
    (leftDerivedUpperStarIterateFrobeniusTriv Λ hp n hs) ((R((w)_*[ModuleCat.{u + 1} Λ])).obj N)
  rw [← cancel_epi ((rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} Λ) w
    (s.iterateFrobenius hp hs n) (𝟙 s) hw).hom.app N), Iso.hom_inv_id_app_assoc]
  have hρ : (rightDerivedLowerStarIdNatIso Λ s).hom.app N =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) s).inv.app
        ((R((𝟙 s)_*[ModuleCat.{u + 1} Λ])).obj N) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 s)).counit.app N := by
    rw [hc, Iso.inv_hom_id_app_assoc]
  have hn₁ := (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) s).inv.naturality
    ((rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} Λ) w
      (s.iterateFrobenius hp hs n) (𝟙 s) hw).hom.app N)
  have hn₂ := (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) s).inv.naturality
    ((rightDerivedLowerStarIterateFrobeniusIso Λ hp n hs).hom.app
      ((R((w)_*[ModuleCat.{u + 1} Λ])).obj N))
  have hn₃ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) w (s.iterateFrobenius hp hs n)
    (𝟙 s) hw.symm).hom.naturality
    ((rightDerivedLowerStarIterateFrobeniusIso Λ hp n hs).hom.app
      ((R((w)_*[ModuleCat.{u + 1} Λ])).obj N))
  dsimp only [Functor.id_map, Functor.comp_map] at hn₁ hn₂ hn₃
  rw [hρ, reassoc_of% hn₁, hk, reassoc_of% hn₂, reassoc_of% hn₃, ← Functor.map_comp_assoc,
    rightDerivedLowerStarIterateFrobeniusIso, hu]

variable [Finite Λ]

/-- The isomorphism `Rw_! ≅ 𝟭` given by the inverse `w` of the absolute Frobenius of `s` (the
composite of `Rw_! ≅ Rw_*`, the isomorphism `𝟭 ≅ Lw^*` from the trivialization of `L(F_s)^*` and
the counit of `Lw^* ⊣ Rw_*`) is compatible with the composition isomorphism
`R(w ≫ F_s)_! ≅ Rw_! ⋙ R(F_s)_!`, the trivialization of `R(F_s)_!` and `R(𝟙)_! ≅ 𝟭`. -/
lemma rightDerivedLowerShriekCompIso_hom_app_comp_iterateFrobenius {w : s ⟶ s} [IsIso w]
    [IsProper (s.iterateFrobenius hp hs n)] (hw : w ≫ s.iterateFrobenius hp hs n = 𝟙 s)
    (N : DerivedCategory (Sheaf s.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekCongrIso Λ hw).inv.app N ≫
      (rightDerivedLowerShriekCompIso Λ w (s.iterateFrobenius hp hs n)).hom.app N ≫
      (rightDerivedLowerShriekIterateFrobeniusIso Λ hp n hs).hom.app
        ((R(w)_![ModuleCat.{u + 1} Λ]).obj N) ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) w).hom.app N ≫
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) s).inv.app
        ((R((w)_*[ModuleCat.{u + 1} Λ])).obj N) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) w (s.iterateFrobenius hp hs n) (𝟙 s)
        hw.symm).hom.app ((R((w)_*[ModuleCat.{u + 1} Λ])).obj N) ≫
      (L((w)^*[ModuleCat.{u + 1} Λ])).map
        ((leftDerivedUpperStarIterateFrobeniusTriv Λ hp n hs).hom.app
          ((R((w)_*[ModuleCat.{u + 1} Λ])).obj N)) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) w).counit.app N =
    (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) s).hom.app N := by
  have hI₀ : rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) s =
      rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) (𝟙 s) ≪≫
        rightDerivedLowerStarIdNatIso Λ s := rfl
  have hρ₀ : rightDerivedLowerShriekIterateFrobeniusIso Λ hp n hs =
      rightDerivedLowerShriekIsoRightDerivedLowerStar _ _ ≪≫
        rightDerivedLowerStarIterateFrobeniusIso Λ hp n hs := rfl
  have hI : (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) s).hom.app N =
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) (𝟙 s)).hom.app N ≫
        (rightDerivedLowerStarIdNatIso Λ s).hom.app N := by
    rw [hI₀]; rfl
  have hρ : (rightDerivedLowerShriekIterateFrobeniusIso Λ hp n hs).hom.app
        ((R(w)_![ModuleCat.{u + 1} Λ]).obj N) =
      (rightDerivedLowerShriekIsoRightDerivedLowerStar _ _).hom.app
          ((R(w)_![ModuleCat.{u + 1} Λ]).obj N) ≫
        (rightDerivedLowerStarIterateFrobeniusIso Λ hp n hs).hom.app
          ((R(w)_![ModuleCat.{u + 1} Λ]).obj N) := by
    rw [hρ₀]; rfl
  have hn := (rightDerivedLowerStarIterateFrobeniusIso Λ hp n hs).hom.naturality
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) w).hom.app N)
  dsimp only [Functor.id_map] at hn
  have hP := rightDerivedLowerShriekCompIso_hom_app_comp_isoRightDerivedLowerStar_of_eq Λ w
    (s.iterateFrobenius hp hs n) (𝟙 s) hw N
  rw [hI, hρ, Category.assoc, ← reassoc_of% hn, reassoc_of% hP,
    rightDerivedLowerStarCompIsoOfComp_inv_app_comp_iterateFrobenius Λ hp n hs hw N]

end AlgebraicGeometry.Etale
