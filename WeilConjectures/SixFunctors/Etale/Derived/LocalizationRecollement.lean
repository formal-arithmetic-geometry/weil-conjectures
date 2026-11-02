/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.SixFunctors.ClosedImmersionStages
public import WeilConjectures.SixFunctors.Etale.Derived.Localization

/-!
# The ambient recollement data on `D(X_ét, Λ)`

For a closed immersion `i : Z ⟶ X` and an open immersion `j : U ⟶ X`, the facts on the unbounded
derived categories `D(-_ét, Λ)` behind the supported localization triangle, in the form used by
`CategoryTheory.Pretriangulated.Recollement`: `Rj_*` and `Ri_*` are fully faithful, `j^* Ri_* = 0`
for disjoint ranges, and an object with `j^* K = 0` lies in the essential image of `Ri_*`. They
are used in `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Ideal Λ} {ϖ : Λ}

/-! ### The ambient recollement data

The facts behind the supported localization triangle on the whole of `D(X_ét, Λ)`
(`AlgebraicGeometry.Etale.existsUnique_distTriang_supportedLocalization`), in the form used by
`CategoryTheory.Pretriangulated.Recollement`. -/

section Recollement

variable {U Z X : Scheme.{u}}

variable (Λ) in
/-- Blueprint `lem-exc-open-fully-faithful`, first half: for an open immersion `j`, the counit
`Lj^* Rj_* ⟶ 𝟭` is an isomorphism: `Rj_*` is fully faithful. In the adjoint triple
`D(j_!) ⊣ D(j^*) ⊣ Rj_*` the unit of the first adjunction is invertible, hence so is the counit
of the second. -/
instance isIso_derivedUpperStarLowerStarAdjunction_counit (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit := by
  let adj := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j
  have : IsIso adj.counit :=
    (Adjunction.Triple.mk
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
      adj).isIso_unit_iff_isIso_counit.1 inferInstance
  have hff := adj.fullyFaithfulROfIsIsoCounit
  have := hff.full
  have := hff.faithful
  exact
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit_isIso_of_R_fully_faithful

variable (Λ) in
/-- The adjunction `Ri_* ⊣ Ri^!` for a closed immersion `i`: the exceptional adjunction
`Ri_! ⊣ Ri^!` transported along `Ri_! ≅ Ri_*`. -/
noncomputable def rightDerivedLowerStarUpperShriekAdjunction (i : Z ⟶ X) [IsClosedImmersion i]
    [HasCompactification i] [(R(i)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] :
    R((i)_*[ModuleCat.{u + 1} Λ]) ⊣ (R(i)_![ModuleCat.{u + 1} Λ]).rightAdjoint :=
  (Adjunction.ofIsLeftAdjoint (R(i)_![ModuleCat.{u + 1} Λ])).ofNatIsoLeft
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i)

/-- Blueprint `lem-exc-open-fully-faithful`, second half: `j^* i_* = 0` for an open immersion `j`
whose range is disjoint from that of the closed immersion `i`
(`AlgebraicGeometry.Etale.isZero_upperStar_rightDerivedLowerShriek`). -/
lemma isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj (i : Z ⟶ X)
    [IsClosedImmersion i] [HasCompactification i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Disjoint (Set.range i.base) (Set.range j.base)) (M : 𝐃(Z, Λ)) :
    IsZero ((L((j)^*[ModuleCat.{u + 1} Λ])).obj ((R((i)_*[ModuleCat.{u + 1} Λ])).obj M)) :=
  (isZero_upperStar_rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) i j hij M).of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app _ ≪≫
      D((j)^*[ModuleCat.{u + 1} Λ]).mapIso
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i).app M).symm)

/-- An object `K` of `D(X_ét, Λ)` with `j^* K = 0` has invertible unit `K ⟶ Ri_* i^* K`, by the
open–closed triangle `j_! j^* K ⟶ K ⟶ Ri_* i^* K ⟶`
(`AlgebraicGeometry.Etale.exists_distTriang_openClosed`). -/
lemma isIso_mapDerivedUpperStarLowerStarAdjunction_unit_app_of_isZero (i : Z ⟶ X)
    [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) {K : 𝐃(X, Λ)}
    (hK : IsZero ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    IsIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app K) := by
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) j i hij K
  exact (Triangle.isZero₁_iff_isIso₂ _ hw).1 (D((j)_!open[ModuleCat.{u + 1} Λ]).map_isZero
    (hK.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app K).symm))

/-- An object `K` of `D(X_ét, Λ)` with `j^* K = 0` lies in the essential image of `Ri_*`. -/
lemma rightDerivedLowerStar_essImage_of_isZero (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] (hij : Set.range i.base = (Set.range j.base)ᶜ) {K : 𝐃(X, Λ)}
    (hK : IsZero ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    (R((i)_*[ModuleCat.{u + 1} Λ])).essImage K :=
  have := isIso_mapDerivedUpperStarLowerStarAdjunction_unit_app_of_isZero i j hij hK
  ⟨_, ⟨(asIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app
    K)).symm⟩⟩

end Recollement

section Localization

variable {U Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]

/-- The direct image `Ri_*` along a closed immersion is fully faithful on `D(Z_ét, Λ)`. -/
noncomputable def fullyFaithfulRightDerivedLowerStarOfIsClosedImmersion :
    (R((i)_*[ModuleCat.{u + 1} Λ])).FullyFaithful :=
  .ofFullyFaithful _

end Localization

end Etale

end AlgebraicGeometry
