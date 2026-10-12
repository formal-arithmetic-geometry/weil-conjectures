/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# The projection map of the derived pushforward, with the pulled-back factor on the left

Let `p : X ⟶ Y` be a morphism of schemes. Besides the projection map
`Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` of `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`,
there is the projection map with the factor from the base on the left,

`K ⊗ᴸ Rp_*M ⟶ Rp_*(Lp^*K ⊗ᴸ M)`,

the transpose along `Lp^* ⊣ Rp_*` of
`Lp^*(K ⊗ᴸ Rp_*M) ⟶ Lp^*K ⊗ᴸ Lp^*Rp_*M ⟶ Lp^*K ⊗ᴸ M` (tensor comparison, then the counit).
This is the form in which the proper projection formula is stated in the blueprint
(`lem-amb-proper-coproducts-projection`), and in which the projective-line trace is extended to
a counit (`def-amb-p1-trace`). The two forms differ by the symmetry of the derived tensor
product, which is not used here.

## Main definitions and statements

- `AlgebraicGeometry.Etale.rightDerivedLowerStarLeftProjectionMap`: the projection map
  `K ⊗ᴸ Rp_*M ⟶ Rp_*(Lp^*K ⊗ᴸ M)`.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarLeftProjectionMap_naturality_left`,
  `AlgebraicGeometry.Etale.rightDerivedLowerStarLeftProjectionMap_naturality_right`: naturality.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarLeftProjectionMap_leftUnitor`: unitality.
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarLeftProjectionMap_of_finite`: the proper
  projection formula at finite coefficients.
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- The projection map `K ⊗ᴸ Rp_*M ⟶ Rp_*(Lp^*K ⊗ᴸ M)` of the derived pushforward along
`p : X ⟶ Y`, with the factor from the base on the left: the transpose along `Lp^* ⊣ Rp_*` of
the tensor comparison `Lp^*(K ⊗ᴸ Rp_*M) ⟶ Lp^*K ⊗ᴸ Lp^*Rp_*M` followed by `𝟙 ⊗ ε_M`. -/
noncomputable def rightDerivedLowerStarLeftProjectionMap
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((-⊗ᴸ-(Y)[A]).obj K).obj (R((p)_*[A]).obj M) ⟶
      R((p)_*[A]).obj (((-⊗ᴸ-(X)[A]).obj (L((p)^*[A]).obj K)).obj M) :=
  (derivedUpperStarLowerStarAdjunction A p).homEquiv _ _
    (((leftDerivedUpperStarTensorComparison A p).app K).app (R((p)_*[A]).obj M) ≫
      ((-⊗ᴸ-(X)[A]).obj (L((p)^*[A]).obj K)).map
        ((derivedUpperStarLowerStarAdjunction A p).counit.app M))

/-- The transpose of the left projection map is the tensor comparison followed by the
counit. -/
lemma homEquiv_symm_rightDerivedLowerStarLeftProjectionMap
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedUpperStarLowerStarAdjunction A p).homEquiv _ _).symm
        (rightDerivedLowerStarLeftProjectionMap A p K M) =
      ((leftDerivedUpperStarTensorComparison A p).app K).app (R((p)_*[A]).obj M) ≫
        ((-⊗ᴸ-(X)[A]).obj (L((p)^*[A]).obj K)).map
          ((derivedUpperStarLowerStarAdjunction A p).counit.app M) :=
  Equiv.symm_apply_apply _ _

/-- The left projection map is natural in the pushed-forward factor. -/
@[reassoc]
lemma rightDerivedLowerStarLeftProjectionMap_naturality_right
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    {M M' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : M ⟶ M') :
    ((-⊗ᴸ-(Y)[A]).obj K).map (R((p)_*[A]).map f) ≫
        rightDerivedLowerStarLeftProjectionMap A p K M' =
      rightDerivedLowerStarLeftProjectionMap A p K M ≫
        R((p)_*[A]).map (((-⊗ᴸ-(X)[A]).obj (L((p)^*[A]).obj K)).map f) := by
  rw [rightDerivedLowerStarLeftProjectionMap, rightDerivedLowerStarLeftProjectionMap,
    ← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  congr 1
  have h : L((p)^*[A]).map (((-⊗ᴸ-(Y)[A]).obj K).map (R((p)_*[A]).map f)) ≫
      ((leftDerivedUpperStarTensorComparison A p).app K).app (R((p)_*[A]).obj M') =
      ((leftDerivedUpperStarTensorComparison A p).app K).app (R((p)_*[A]).obj M) ≫
        ((-⊗ᴸ-(X)[A]).obj (L((p)^*[A]).obj K)).map (L((p)^*[A]).map (R((p)_*[A]).map f)) :=
    ((leftDerivedUpperStarTensorComparison A p).app K).naturality (R((p)_*[A]).map f)
  rw [reassoc_of% h, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  exact (derivedUpperStarLowerStarAdjunction A p).counit.naturality f

/-- The left projection map is natural in the factor from the base. -/
@[reassoc]
lemma rightDerivedLowerStarLeftProjectionMap_naturality_left
    {K K' : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (f : K ⟶ K')
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((-⊗ᴸ-(Y)[A]).map f).app (R((p)_*[A]).obj M) ≫
        rightDerivedLowerStarLeftProjectionMap A p K' M =
      rightDerivedLowerStarLeftProjectionMap A p K M ≫
        R((p)_*[A]).map (((-⊗ᴸ-(X)[A]).map (L((p)^*[A]).map f)).app M) := by
  rw [rightDerivedLowerStarLeftProjectionMap, rightDerivedLowerStarLeftProjectionMap,
    ← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  congr 1
  have h : L((p)^*[A]).map (((-⊗ᴸ-(Y)[A]).map f).app (R((p)_*[A]).obj M)) ≫
      ((leftDerivedUpperStarTensorComparison A p).app K').app (R((p)_*[A]).obj M) =
      ((leftDerivedUpperStarTensorComparison A p).app K).app (R((p)_*[A]).obj M) ≫
        ((-⊗ᴸ-(X)[A]).map (L((p)^*[A]).map f)).app (L((p)^*[A]).obj (R((p)_*[A]).obj M)) :=
    NatTrans.congr_app ((leftDerivedUpperStarTensorComparison A p).naturality f)
      (R((p)_*[A]).obj M)
  rw [reassoc_of% h, Category.assoc]
  congr 1
  exact (((-⊗ᴸ-(X)[A]).map (L((p)^*[A]).map f)).naturality _).symm

/-- **Unitality of the left projection map**: at the unit `Λ_Y`, the left projection map
followed by `Rp_*(ε ▷ M ≫ λ)`, for the identification `ε : Lp^* Λ_Y ≅ Λ_X`, is the left
unitor of `Rp_* M`. -/
@[reassoc]
lemma rightDerivedLowerStarLeftProjectionMap_leftUnitor
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    rightDerivedLowerStarLeftProjectionMap A p (𝟙_ _) M ≫
        R((p)_*[A]).map ((leftDerivedUpperStarUnitIso A p).hom ▷ M ≫ (λ_ M).hom) =
      (λ_ (R((p)_*[A]).obj M)).hom := by
  rw [rightDerivedLowerStarLeftProjectionMap, ← Adjunction.homEquiv_naturality_right]
  have h := leftDerivedUpperStarTensorComparison_leftUnitor_hom A p (R((p)_*[A]).obj M)
  have e : ((leftDerivedUpperStarTensorComparison A p).app (𝟙_ _)).app (R((p)_*[A]).obj M) ≫
      ((-⊗ᴸ-(X)[A]).obj (L((p)^*[A]).obj (𝟙_ _))).map
        ((derivedUpperStarLowerStarAdjunction A p).counit.app M) ≫
        ((leftDerivedUpperStarUnitIso A p).hom ▷ M ≫ (λ_ M).hom) =
      L((p)^*[A]).map (λ_ (R((p)_*[A]).obj M)).hom ≫
        (derivedUpperStarLowerStarAdjunction A p).counit.app M := by
    rw [← h]
    change _ ≫ (_ ◁ _) ≫ _ = _
    simp only [Category.assoc]
    erw [whisker_exchange_assoc, leftUnitor_naturality]
  rw [Category.assoc, e, Adjunction.homEquiv_naturality_left]
  simp [Adjunction.homEquiv_unit]

end General

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

/-- Blueprint `lem-amb-proper-coproducts-projection`: The proper projection formula on the
ambient category

For a finite coefficient ring `Λ` and a proper morphism `r : V ⟶ T`, for all complexes `L` on
`V` and `K` on `T`, the derived tensor projection map

`K ⊗ᴸ Rr_* L ⟶ Rr_*(Lr^* K ⊗ᴸ L)`

(`AlgebraicGeometry.Etale.rightDerivedLowerStarLeftProjectionMap`) is an isomorphism in the
unbounded derived category. This is the statement of the blueprint node, with the factor from the
base on the left; the form with the factors in the other order is
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite`. -/
theorem isIso_rightDerivedLowerStarLeftProjectionMap_of_finite [Finite Λ] {V T : Scheme.{u}}
    (r : V ⟶ T) [IsProper r]
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (rightDerivedLowerStarLeftProjectionMap (ModuleCat.{u + 1} Λ) r K L) :=
  sorry

/-- The proper projection formula `K ⊗ᴸ Rr_* L ≅ Rr_*(Lr^* K ⊗ᴸ L)` at finite coefficients, as an
isomorphism (`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarLeftProjectionMap_of_finite`). -/
noncomputable def rightDerivedLowerStarLeftProjectionIso [Finite Λ] {V T : Scheme.{u}}
    (r : V ⟶ T) [IsProper r]
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((-⊗ᴸ-(T)[ModuleCat.{u + 1} Λ]).obj K).obj (R((r)_*[ModuleCat.{u + 1} Λ]).obj L) ≅
      R((r)_*[ModuleCat.{u + 1} Λ]).obj
        (((-⊗ᴸ-(V)[ModuleCat.{u + 1} Λ]).obj (L((r)^*[ModuleCat.{u + 1} Λ]).obj K)).obj L) :=
  have := isIso_rightDerivedLowerStarLeftProjectionMap_of_finite Λ r K L
  asIso (rightDerivedLowerStarLeftProjectionMap (ModuleCat.{u + 1} Λ) r K L)

@[simp]
lemma rightDerivedLowerStarLeftProjectionIso_hom [Finite Λ] {V T : Scheme.{u}}
    (r : V ⟶ T) [IsProper r]
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerStarLeftProjectionIso Λ r K L).hom =
      rightDerivedLowerStarLeftProjectionMap (ModuleCat.{u + 1} Λ) r K L :=
  rfl

end Finite

end Etale

end AlgebraicGeometry
