/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.OpenComplement
public import WeilConjectures.SixFunctors.Etale.Derived.Localization

/-!
# Amplitude of the exceptional inverse image along a closed immersion

Let `i : Z ⟶ T` be a closed immersion with open complement `j : U ⟶ T` and `Λ` a finite ring.
If `R^q j_* M = 0` for every sheaf `M` of `Λ`-modules and every `q > c`, then the exceptional
inverse image `Ri^!` (the right adjoint of `Ri_! = Ri_*` on `D(T_ét, Λ)`) carries complexes with
homology in `[a, b]` to complexes with homology in `[a, b + c + 1]`
(`AlgebraicGeometry.Etale.homologyConcentratedIn_rightDerivedUpperShriek`), and under the full
open-complement condition `D_c^{[a, b]}(T, Λ)` into `D_c^{[a, b + c + 1]}(Z, Λ)`
(`AlgebraicGeometry.Etale.constructibleIn_rightDerivedUpperShriek`). Together these are blueprint
`lem-exc-closed-amplitude`.

The proof uses the supported localization triangle
`Ri_! Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶ (Ri_! Ri^! K)[1]`
(`AlgebraicGeometry.Etale.supportedLocalizationTriangle_mem_distTriang`): `Rj_* j^* K` has
homology in `[a, b + c]`, so `Ri_! Ri^! K` has homology in `[a, b + c + 1]`, and
`Ri^! K ≅ i^* Ri_! Ri^! K` since `Ri_!` is fully faithful
(`AlgebraicGeometry.Etale.mapDerivedUpperStarRightDerivedLowerShriekIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {Z T U : Scheme.{u}}

/-- For a closed immersion `i`, the pullback `i^*` is left inverse to `Ri_!`:
`i^* Ri_! N ≅ N`. Indeed `Ri_!` is fully faithful
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekAdjunction_unit_app`) and isomorphic to
`Ri_*`, so the counit of `i^* ⊣ Ri_*` is an isomorphism. -/
noncomputable def mapDerivedUpperStarRightDerivedLowerShriekIso (i : Z ⟶ T) [IsClosedImmersion i]
    [HasCompactification i]
    (N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D((i)^*[ModuleCat.{u + 1} Λ]).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj N) ≅ N :=
  have := isIso_rightDerivedUpperShriekAdjunction_unit_app (ModuleCat.{u + 1} Λ) i
  have : IsIso (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).unit :=
    NatIso.isIso_of_isIso_app _
  let hff := (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).fullyFaithfulLOfIsIsoUnit
  have := hff.full
  have := hff.faithful
  let e := rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i
  have : (R((i)_*[ModuleCat.{u + 1} Λ])).Full := Functor.Full.of_iso e
  have : (R((i)_*[ModuleCat.{u + 1} Λ])).Faithful := Functor.Faithful.of_iso e
  have : IsIso (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).counit :=
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).counit_isIso_of_R_fully_faithful
  D((i)^*[ModuleCat.{u + 1} Λ]).mapIso (e.app N) ≪≫
    asIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).counit.app N)

variable (i : Z ⟶ T) (j : U ⟶ T) [IsClosedImmersion i] [HasCompactification i] [IsOpenImmersion j]
  (hij : Set.range i.base = (Set.range j.base)ᶜ)

include hij in
/-- The supported term `Ri_! Ri^! K` of the supported localization triangle has homology in
`[a, b + c + 1]` if `K` has homology in `[a, b]` and `R^q j_*` vanishes above `c`. -/
lemma homologyConcentratedIn_rightDerivedLowerShriek_rightDerivedUpperShriek {c : ℕ}
    (hc : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), c < q →
      IsZero (higherDirectImage Λ j q M))
    {a b : ℤ} {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    _root_.DerivedCategory.homologyConcentratedIn a (b + c + 1)
      ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![ModuleCat.{u + 1} Λ]).obj K)) := by
  obtain ⟨hKa, hKb⟩ := hK
  let A := ModuleCat.{u + 1} Λ
  have hT := inv_rot_of_distTriang _
    (supportedLocalizationTriangle_mem_distTriang A i j hij K)
  -- the third term `Rj_* j^* K` has homology in `[a, b + c]`
  let C := (R((j)_*[A])).obj ((L((j)^*[A])).obj K)
  have e := (leftDerivedUpperStarIsoMapDerivedCategory A j).app K
  have : ((L((j)^*[A])).obj K).IsGE a :=
    _root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm a
  have : ((L((j)^*[A])).obj K).IsLE b :=
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm b
  have : C.IsGE a := isGE_rightDerivedLowerStar_obj Λ j _ a
  have : C.IsLE (b + c) := isLE_rightDerivedLowerStar_obj_of_isZero_higherDirectImage hc _ b
  have : (C⟦(-1 : ℤ)⟧).IsGE (a + 1) :=
    _root_.DerivedCategory.TStructure.t.isGE_shift C a (-1) (a + 1)
  have : (C⟦(-1 : ℤ)⟧).IsLE (b + c + 1) :=
    _root_.DerivedCategory.TStructure.t.isLE_shift C (b + c) (-1) (b + c + 1)
  constructor
  · refine _root_.DerivedCategory.TStructure.t.isGE₂ _ hT a ?_ hKa
    exact _root_.DerivedCategory.TStructure.t.isGE_of_ge _ a (a + 1) (by lia)
  · refine _root_.DerivedCategory.TStructure.t.isLE₂ _ hT (b + c + 1) ‹_› ?_
    have : K.IsLE b := hKb
    exact _root_.DerivedCategory.TStructure.t.isLE_of_le _ b (b + c + 1) (by lia)

include hij in
/-- Blueprint `lem-exc-closed-amplitude`: Closed-support amplitude.

Let `i : Z ⟶ T` be a closed immersion with open complement `j : U ⟶ T`, and `Λ` a finite ring.
Suppose that `R^q j_* M = 0` for every sheaf `M` of `Λ`-modules on `U_ét` and every `q > c`. Then
the exceptional inverse image `Ri^!` carries `D^{[a, b]}(T_ét, Λ)` into
`D^{[a, b + c + 1]}(Z_ét, Λ)`. The constructible version is
`AlgebraicGeometry.Etale.constructibleIn_rightDerivedUpperShriek`.

The supported localization triangle `Ri_! Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶` puts `Ri_! Ri^! K` in
`[a, b + c + 1]`, as `Rj_* j^* K` lies in `[a, b + c]`
(`AlgebraicGeometry.Etale.homologyConcentratedIn_rightDerivedLowerShriek_rightDerivedUpperShriek`),
and the exact `i^*` recovers `Ri^! K ≅ i^* Ri_! Ri^! K`
(`AlgebraicGeometry.Etale.mapDerivedUpperStarRightDerivedLowerShriekIso`). -/
theorem homologyConcentratedIn_rightDerivedUpperShriek {c : ℕ}
    (hc : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), c < q →
      IsZero (higherDirectImage Λ j q M))
    {a b : ℤ} {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    _root_.DerivedCategory.homologyConcentratedIn a (b + c + 1)
      ((R(i)^![ModuleCat.{u + 1} Λ]).obj K) := by
  obtain ⟨h₁, h₂⟩ :=
    homologyConcentratedIn_rightDerivedLowerShriek_rightDerivedUpperShriek i j hij hc hK
  have := h₁
  have := h₂
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso
      (mapDerivedUpperStarRightDerivedLowerShriekIso i _) a,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso
      (mapDerivedUpperStarRightDerivedLowerShriekIso i _) (b + c + 1)⟩

end Etale

end AlgebraicGeometry
