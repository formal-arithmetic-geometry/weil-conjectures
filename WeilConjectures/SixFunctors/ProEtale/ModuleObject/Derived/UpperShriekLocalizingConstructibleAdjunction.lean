/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperUpperShriekExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizingConstructible

/-!
# The exceptional adjunction on `Loc(Dᵇc)` restricts to `Dᵇc`, `ℓ`-adic coefficients

For the `ℓ`-adic coefficient rings `Λ = E, 𝒪_E, ℚ̄_ℓ` and a compactification `c` of a morphism
`f : X ⟶ Y` of separated finite-type `k`-schemes, the exceptional inverse image
`f^! : Loc(Dᵇc(Y)⟦Λ⟧) ⥤ Loc(Dᵇc(X)⟦Λ⟧)` maps `Dᵇc(Y)⟦Λ⟧` into `Dᵇc(X)⟦Λ⟧`
(`boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_continuousMapRingObj` and
its analogues), so the adjunction `Rf_! ⊣ f^!` restricts to the full subcategories `Dᵇc = Dctf`
(`boundedConstructibleUpperShriekLocalizingAdjunction_continuousMapRingObj` and its analogues).
All names are in the namespace `AlgebraicGeometry.ProEtale.CondensedRing`.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [IsSeparated aX] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  [IsSeparated aY] {f : X ⟶ Y} (c : Compactification f)
  (hk : Finite k ∨ IsSepClosed k) (hf : f ≫ aY = aX)

/-- The adjunction `Rf_! ⊣ f^!` on `Loc(Dᵇc)` with coefficients in a finite extension `E ⊆ ℚ̄_ℓ`
of `ℚ_ℓ` restricts to the full subcategories `Dᵇc = Dctf`. -/
noncomputable def boundedConstructibleUpperShriekLocalizingAdjunction_continuousMapRingObj
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  boundedConstructibleUpperShriekLocalizingAdjunction _
    (rightDerivedUpperShriekLocalizingAdjunction_continuousMapRingObj ℓ aX aY c hk E)
    (boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_continuousMapRingObj ℓ
      aX aY c E hf (rightDerivedUpperShriekLocalizingAdjunction_continuousMapRingObj ℓ aX aY c hk
        E))

/-- The adjunction `Rf_! ⊣ f^!` on `Loc(Dᵇc)` with coefficients in the ring of integers `𝒪_E` of a
finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` restricts to the full subcategories `Dᵇc = Dctf`. -/
noncomputable def boundedConstructibleUpperShriekLocalizingAdjunction_padicIntegersRingObj
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :=
  boundedConstructibleUpperShriekLocalizingAdjunction _
    (rightDerivedUpperShriekLocalizingAdjunction_padicIntegersRingObj ℓ aX aY c hk E)
    (boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_padicIntegersRingObj ℓ
      aX aY c E hf (rightDerivedUpperShriekLocalizingAdjunction_padicIntegersRingObj ℓ aX aY c
        hk E))

/-- The adjunction `Rf_! ⊣ f^!` on `Loc(Dᵇc)` with coefficients `ℚ̄_ℓ` restricts to the full
subcategories `Dᵇc = Dctf`. -/
noncomputable def boundedConstructibleUpperShriekLocalizingAdjunction_padicAlgClRingObj :=
  boundedConstructibleUpperShriekLocalizingAdjunction _
    (rightDerivedUpperShriekLocalizingAdjunction_padicAlgClRingObj ℓ aX aY c hk)
    (boundedConstructible_rightAdjoint_rightDerivedLowerShriekLocalizing_padicAlgClRingObj ℓ
      aX aY c hf (rightDerivedUpperShriekLocalizingAdjunction_padicAlgClRingObj ℓ aX aY c hk))

end AlgebraicGeometry.ProEtale.CondensedRing
