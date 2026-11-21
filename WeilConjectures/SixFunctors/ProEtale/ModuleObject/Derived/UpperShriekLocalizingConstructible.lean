/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosureRightAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizingEllAdic

/-!
# Properties of `Rf_!` and `f^!` on `Loc(Dᵇc)`, `ℓ`-adic coefficients

Let `Λ` be a commutative condensed ring and `c` a compactification of `f : X ⟶ Y` whose
compact-support direct image has the properties `LowerShriekLocalizingHypotheses`, so that it
restricts to `Rf_! : Loc(Dᵇc(X)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)`
(`AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekLocalizing`). For the
`ℓ`-adic coefficient rings `Λ = E, 𝒪_E, ℚ̄_ℓ`, for which `Dᵇc = Dctf`, it has a right adjoint `f^!`
given by Brown representability
(`AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedUpperShriekLocalizing_continuousMapRingObj`
and its analogues).

## Main statements

- `rightDerivedLowerShriekLocalizing` is triangulated, preserves direct sums and maps `Dᵇc` into
  `Dᵇc` (`isTriangulated_rightDerivedLowerShriekLocalizing`,
  `preservesColimitsOfShape_rightDerivedLowerShriekLocalizing`,
  `boundedConstructible_rightDerivedLowerShriekLocalizing_obj`).
- `boundedConstructibleUpperShriekLocalizingAdjunction`: an adjunction `Rf_! ⊣ G` whose right
  adjoint maps `Dᵇc` into `Dᵇc` restricts to `Dᵇc`.
- `isTriangulated_rightDerivedUpperShriekLocalizing_continuousMapRingObj` and its analogues for
  `𝒪_E` and `ℚ̄_ℓ`: `f^!` is triangulated.

All names are in the namespace `AlgebraicGeometry.ProEtale.CondensedRing`.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section General

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ]
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (hc : LowerShriekLocalizingHypotheses Λ c)

/-- The compact-support direct image `Rf_! : Loc(Dᵇc(X)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)` is triangulated. -/
theorem isTriangulated_rightDerivedLowerShriekLocalizing :
    (rightDerivedLowerShriekLocalizing hc).IsTriangulated :=
  inferInstance

/-- The compact-support direct image `Rf_! : Loc(Dᵇc(X)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)` preserves direct
sums. -/
theorem preservesColimitsOfShape_rightDerivedLowerShriekLocalizing (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J) (rightDerivedLowerShriekLocalizing hc) :=
  inferInstance

/-- The compact-support direct image `Rf_! : Loc(Dᵇc(X)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)` maps `Dᵇc(X)⟦Λ⟧`
into `Dᵇc(Y)⟦Λ⟧`. -/
theorem boundedConstructible_rightDerivedLowerShriekLocalizing_obj
    (K : LocalizingBoundedConstructible Λ X) (hK : boundedConstructible _ K.obj) :
    boundedConstructible _ ((rightDerivedLowerShriekLocalizing hc).obj K).obj :=
  hc.2.1 _ hK

/-- An adjunction `Rf_! ⊣ G` on `Loc(Dᵇc)` whose right adjoint maps `Dᵇc(Y)⟦Λ⟧` into
`Dᵇc(X)⟦Λ⟧` restricts to the full subcategories `Dᵇc`. -/
noncomputable def boundedConstructibleUpperShriekLocalizingAdjunction
    {G : LocalizingBoundedConstructible Λ Y ⥤ LocalizingBoundedConstructible Λ X}
    (adj : rightDerivedLowerShriekLocalizing hc ⊣ G)
    (hG : ∀ L, boundedConstructible (condensedRingObj Λ Y) (ObjectProperty.ι _ |>.obj L) →
      boundedConstructible (condensedRingObj Λ X) (G.obj L).obj) :
    ((boundedConstructible (condensedRingObj Λ Y)).inverseImage (ObjectProperty.ι _)).lift
        (((boundedConstructible (condensedRingObj Λ X)).inverseImage (ObjectProperty.ι _)).ι ⋙
          rightDerivedLowerShriekLocalizing hc)
        (fun K ↦ hc.2.1 _ K.property) ⊣
      ((boundedConstructible (condensedRingObj Λ X)).inverseImage (ObjectProperty.ι _)).lift
        (((boundedConstructible (condensedRingObj Λ Y)).inverseImage (ObjectProperty.ι _)).ι ⋙
          G)
        (fun L ↦ hG L.obj L.property) :=
  adj.restrictObjectProperty _ _ (fun _ hK ↦ hc.2.1 _ hK) hG

end General

section EllAdic

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [IsSeparated aX] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  [IsSeparated aY] {f : X ⟶ Y} (c : Compactification f)
  (hk : Finite k ∨ IsSepClosed k)

/-- The exceptional inverse image `f^! : Loc(Dᵇc(Y)⟦E⟧) ⥤ Loc(Dᵇc(X)⟦E⟧)` with coefficients in a
finite extension `E` of `ℚ_ℓ` is triangulated. -/
theorem isTriangulated_rightDerivedUpperShriekLocalizing_continuousMapRingObj (E : Type)
    [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    (rightDerivedUpperShriekLocalizing_continuousMapRingObj ℓ aX aY c hk E).IsTriangulated :=
  have := (rightDerivedUpperShriekLocalizingAdjunction_continuousMapRingObj ℓ aX aY c hk
    E).commShift_of_leftAdjoint ℤ
  (rightDerivedUpperShriekLocalizingAdjunction_continuousMapRingObj ℓ aX aY c hk
    E).isTriangulated_rightAdjoint

/-- The exceptional inverse image `f^! : Loc(Dᵇc(Y)⟦𝒪_E⟧) ⥤ Loc(Dᵇc(X)⟦𝒪_E⟧)` with coefficients
in the ring of integers `𝒪_E` of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` is triangulated. -/
theorem isTriangulated_rightDerivedUpperShriekLocalizing_padicIntegersRingObj (E : Type)
    [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    (rightDerivedUpperShriekLocalizing_padicIntegersRingObj ℓ aX aY c hk E).IsTriangulated :=
  have := (rightDerivedUpperShriekLocalizingAdjunction_padicIntegersRingObj ℓ aX aY c hk
    E).commShift_of_leftAdjoint ℤ
  (rightDerivedUpperShriekLocalizingAdjunction_padicIntegersRingObj ℓ aX aY c hk
    E).isTriangulated_rightAdjoint

/-- The exceptional inverse image `f^! : Loc(Dᵇc(Y)⟦ℚ̄_ℓ⟧) ⥤ Loc(Dᵇc(X)⟦ℚ̄_ℓ⟧)` is
triangulated. -/
theorem isTriangulated_rightDerivedUpperShriekLocalizing_padicAlgClRingObj :
    (rightDerivedUpperShriekLocalizing_padicAlgClRingObj ℓ aX aY c hk).IsTriangulated :=
  have := (rightDerivedUpperShriekLocalizingAdjunction_padicAlgClRingObj ℓ aX aY c
    hk).commShift_of_leftAdjoint ℤ
  (rightDerivedUpperShriekLocalizingAdjunction_padicAlgClRingObj ℓ aX aY c
    hk).isTriangulated_rightAdjoint

end EllAdic

end AlgebraicGeometry.ProEtale.CondensedRing
