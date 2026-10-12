/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerStarProjectionBaseChange
public import WeilConjectures.SixFunctors.ProEtale.Derived.PerfectProjection

/-!
# Naturality of the projection formula in the coefficients and in the complex

Let `f : X ⟶ Y` be a morphism of schemes. The projection map
`π_{f,K,P} : Rf_*K ⊗ᴸ P ⟶ Rf_*(K ⊗ᴸ Lf^*P)`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap`) is a natural transformation of
bifunctors, so it is natural both in the coefficient object `P` and in `K`. We record the
resulting compatibilities of blueprint `lemma-weil-pbc-projection-formula-tower-compatibility`
(the projection formulas along a tower of coefficients `P : ℕᵒᵖ ⥤ D(Y_proét)` form a morphism of
towers, an isomorphism of towers with inverse `ρ` when every `π_{f,K,Pₙ}` is invertible) and of
blueprint `lemma-weil-pbc-projection-formula-base-change-naturality` (naturality in `K`, in
particular for an endomorphism `φ` of `K` and its reductions `φₙ = φ ⊗ᴸ 1`; the base change part
is `AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap_derivedBaseChangeMap`).

## Main definitions and results

- `AlgebraicGeometry.ProEtale.projectionFormulaTowerMap f K P` and
  `AlgebraicGeometry.ProEtale.projectionFormulaTowerIso f K P`: the projection maps
  `π_n : Rf_*K ⊗ᴸ Pₙ ⟶ Rf_*(K ⊗ᴸ Lf^*Pₙ)` as a morphism (isomorphism) of towers.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap_tower_comm` and
  `AlgebraicGeometry.ProEtale.inv_rightDerivedLowerStarProjectionMap_tower_comm`
  (blueprint `lemma-weil-pbc-projection-formula-tower-compatibility`).
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap_naturality_left`,
  `AlgebraicGeometry.ProEtale.inv_rightDerivedLowerStarProjectionMap_naturality_left`
  (blueprint `lemma-weil-pbc-projection-formula-base-change-naturality`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A]

namespace ProEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section Coefficients

/-- The projection map `π_{f,K,-}` is natural in the coefficient object: for `q : P ⟶ P'`, the
square
```
Rf_*K ⊗ᴸ P  ──π_P──▶  Rf_*(K ⊗ᴸ Lf^*P)
    │1 ⊗ q                  │Rf_*(1 ⊗ Lf^*q)
    ▼                       ▼
Rf_*K ⊗ᴸ P' ──π_P'─▶  Rf_*(K ⊗ᴸ Lf^*P')
```
commutes. -/
@[reassoc]
lemma rightDerivedLowerStarProjectionMap_naturality_right
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    {P P' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)} (q : P ⟶ P') :
    ((-⊗ᴸ-(Y)[A]).obj (R((f)_*[A]).obj K)).map q ≫
        ((rightDerivedLowerStarProjectionMap A f).app K).app P' =
      ((rightDerivedLowerStarProjectionMap A f).app K).app P ≫
        R((f)_*[A]).map (((-⊗ᴸ-(X)[A]).obj K).map (L((f)^*[A]).map q)) :=
  ((rightDerivedLowerStarProjectionMap A f).app K).naturality q

/-- The inverses `ρ = π⁻¹` of the projection maps are natural in the coefficient object, where
they exist. -/
@[reassoc]
lemma inv_rightDerivedLowerStarProjectionMap_naturality_right
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    {P P' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)} (q : P ⟶ P')
    [IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app P)]
    [IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app P')] :
    inv (((rightDerivedLowerStarProjectionMap A f).app K).app P) ≫
        ((-⊗ᴸ-(Y)[A]).obj (R((f)_*[A]).obj K)).map q =
      R((f)_*[A]).map (((-⊗ᴸ-(X)[A]).obj K).map (L((f)^*[A]).map q)) ≫
        inv (((rightDerivedLowerStarProjectionMap A f).app K).app P') := by
  rw [IsIso.inv_comp_eq, reassoc_of% rightDerivedLowerStarProjectionMap_naturality_right,
    IsIso.hom_inv_id, Category.comp_id]

/-- The projection maps `π_n : Rf_*K ⊗ᴸ Pₙ ⟶ Rf_*(K ⊗ᴸ Lf^*Pₙ)` along a tower of coefficients
`P : ℕᵒᵖ ⥤ D(Y_proét)`, as a morphism of towers. -/
noncomputable def projectionFormulaTowerMap
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (P : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    P ⋙ (derivedTensorRightDerivedLowerStar A f).obj K ⟶
      P ⋙ (rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar A f).obj K :=
  Functor.whiskerLeft P ((rightDerivedLowerStarProjectionMap A f).app K)

@[simp]
lemma projectionFormulaTowerMap_app
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (P : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) (n : ℕᵒᵖ) :
    (projectionFormulaTowerMap A f K P).app n =
      ((rightDerivedLowerStarProjectionMap A f).app K).app (P.obj n) :=
  rfl

/-- **Projection formulas form a coefficient tower** (blueprint
`lemma-weil-pbc-projection-formula-tower-compatibility`, forward square). For a tower of
coefficients `P : ℕᵒᵖ ⥤ D(Y_proét)` with transition maps `qₙ : Pₙ₊₁ ⟶ Pₙ`, the square
```
Rf_*K ⊗ᴸ Pₙ₊₁ ──π_{n+1}──▶ Rf_*(K ⊗ᴸ Lf^*Pₙ₊₁)
     │1 ⊗ qₙ                     │Rf_*(1 ⊗ qₙ)
     ▼                           ▼
Rf_*K ⊗ᴸ Pₙ   ───π_n────▶ Rf_*(K ⊗ᴸ Lf^*Pₙ)
```
commutes. -/
@[reassoc]
lemma rightDerivedLowerStarProjectionMap_tower_comm
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (P : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) (n : ℕ) :
    ((-⊗ᴸ-(Y)[A]).obj (R((f)_*[A]).obj K)).map (P.map (homOfLE (Nat.le_succ n)).op) ≫
        ((rightDerivedLowerStarProjectionMap A f).app K).app (P.obj (op n)) =
      ((rightDerivedLowerStarProjectionMap A f).app K).app (P.obj (op (n + 1))) ≫
        R((f)_*[A]).map (((-⊗ᴸ-(X)[A]).obj K).map
          (L((f)^*[A]).map (P.map (homOfLE (Nat.le_succ n)).op))) :=
  rightDerivedLowerStarProjectionMap_naturality_right A f K _

/-- **Projection formulas form a coefficient tower** (blueprint
`lemma-weil-pbc-projection-formula-tower-compatibility`, inverse square): when the projection
maps `π_n` and `π_{n+1}` are invertible, their inverses `ρ_n`, `ρ_{n+1}` commute with the
quotient maps `qₙ : Pₙ₊₁ ⟶ Pₙ`. -/
@[reassoc]
lemma inv_rightDerivedLowerStarProjectionMap_tower_comm
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (P : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) (n : ℕ)
    [IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app (P.obj (op n)))]
    [IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app (P.obj (op (n + 1))))] :
    inv (((rightDerivedLowerStarProjectionMap A f).app K).app (P.obj (op (n + 1)))) ≫
        ((-⊗ᴸ-(Y)[A]).obj (R((f)_*[A]).obj K)).map (P.map (homOfLE (Nat.le_succ n)).op) =
      R((f)_*[A]).map (((-⊗ᴸ-(X)[A]).obj K).map
          (L((f)^*[A]).map (P.map (homOfLE (Nat.le_succ n)).op))) ≫
        inv (((rightDerivedLowerStarProjectionMap A f).app K).app (P.obj (op n))) :=
  inv_rightDerivedLowerStarProjectionMap_naturality_right A f K _

/-- The projection maps along a tower of coefficients `P` at which they are all invertible (for
instance a tower of perfect complexes), as an isomorphism of towers. Its inverse is the tower of
the arrows `ρ_n = π_n⁻¹`. -/
noncomputable def projectionFormulaTowerIso
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (P : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (hP : ∀ n, IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app (P.obj n))) :
    P ⋙ (derivedTensorRightDerivedLowerStar A f).obj K ≅
      P ⋙ (rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar A f).obj K :=
  haveI : ∀ n, IsIso ((projectionFormulaTowerMap A f K P).app n) := hP
  haveI : IsIso (projectionFormulaTowerMap A f K P) := NatIso.isIso_of_isIso_app _
  asIso (projectionFormulaTowerMap A f K P)

@[simp]
lemma projectionFormulaTowerIso_hom_app
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (P : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (hP : ∀ n, IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app (P.obj n)))
    (n : ℕᵒᵖ) :
    (projectionFormulaTowerIso A f K P hP).hom.app n =
      ((rightDerivedLowerStarProjectionMap A f).app K).app (P.obj n) :=
  rfl

/-- A tower of dualizable (perfect) coefficients: the projection maps form an isomorphism of
towers (blueprint `lemma-weil-pbc-projection-formula-tower-compatibility`). -/
noncomputable def projectionFormulaTowerIsoOfIsDualizable
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (P : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (hP : ∀ n, IsDualizable (P.obj n)) :
    P ⋙ (derivedTensorRightDerivedLowerStar A f).obj K ≅
      P ⋙ (rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar A f).obj K :=
  projectionFormulaTowerIso A f K P fun n ↦
    isIso_rightDerivedLowerStarProjectionMap_of_isDualizable A f K (hP n)

end Coefficients

section Complex

/-- **Operator naturality of the projection formula** (blueprint
`lemma-weil-pbc-projection-formula-base-change-naturality`, first part). The projection map is
natural in `K`: for `φ : K ⟶ L`,
`Rf_*(φ ⊗ᴸ 1) ∘ π_{f,K,P} = π_{f,L,P} ∘ (Rf_*φ ⊗ᴸ 1)`. -/
@[reassoc]
lemma rightDerivedLowerStarProjectionMap_naturality_left
    {K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (φ : K ⟶ L)
    (P : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((-⊗ᴸ-(Y)[A]).map (R((f)_*[A]).map φ)).app P ≫
        ((rightDerivedLowerStarProjectionMap A f).app L).app P =
      ((rightDerivedLowerStarProjectionMap A f).app K).app P ≫
        R((f)_*[A]).map (((-⊗ᴸ-(X)[A]).map φ).app (L((f)^*[A]).obj P)) :=
  NatTrans.congr_app ((rightDerivedLowerStarProjectionMap A f).naturality φ) P

/-- The inverses `ρ = π⁻¹` of the projection maps are natural in `K`, where they exist
(blueprint `lemma-weil-pbc-projection-formula-base-change-naturality`). -/
@[reassoc]
lemma inv_rightDerivedLowerStarProjectionMap_naturality_left
    {K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (φ : K ⟶ L)
    (P : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    [IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app P)]
    [IsIso (((rightDerivedLowerStarProjectionMap A f).app L).app P)] :
    inv (((rightDerivedLowerStarProjectionMap A f).app K).app P) ≫
        ((-⊗ᴸ-(Y)[A]).map (R((f)_*[A]).map φ)).app P =
      R((f)_*[A]).map (((-⊗ᴸ-(X)[A]).map φ).app (L((f)^*[A]).obj P)) ≫
        inv (((rightDerivedLowerStarProjectionMap A f).app L).app P) := by
  rw [IsIso.inv_comp_eq, reassoc_of% rightDerivedLowerStarProjectionMap_naturality_left,
    IsIso.hom_inv_id, Category.comp_id]

/-- **Operator naturality of the projection formula** (blueprint
`lemma-weil-pbc-projection-formula-base-change-naturality`), for an endomorphism `φ` of `K` and
its reduction `φₙ = φ ⊗ᴸ 1` on `Kₙ = K ⊗ᴸ Lf^*Pₙ`:
`Rf_*φₙ ∘ πₙ = πₙ ∘ (Rf_*φ ⊗ᴸ 1)` and, when `πₙ` is invertible,
`(Rf_*φ ⊗ᴸ 1) ∘ ρₙ = ρₙ ∘ Rf_*φₙ`. -/
lemma rightDerivedLowerStarProjectionMap_endomorphism
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (φ : K ⟶ K)
    (P : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((rightDerivedLowerStarProjectionMap A f).app K).app P ≫
        R((f)_*[A]).map (((-⊗ᴸ-(X)[A]).map φ).app (L((f)^*[A]).obj P)) =
      ((-⊗ᴸ-(Y)[A]).map (R((f)_*[A]).map φ)).app P ≫
        ((rightDerivedLowerStarProjectionMap A f).app K).app P ∧
    ∀ [IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app P)],
      ((-⊗ᴸ-(Y)[A]).map (R((f)_*[A]).map φ)).app P ≫
          inv (((rightDerivedLowerStarProjectionMap A f).app K).app P) =
        inv (((rightDerivedLowerStarProjectionMap A f).app K).app P) ≫
          R((f)_*[A]).map (((-⊗ᴸ-(X)[A]).map φ).app (L((f)^*[A]).obj P)) :=
  ⟨(rightDerivedLowerStarProjectionMap_naturality_left A f φ P).symm,
    (inv_rightDerivedLowerStarProjectionMap_naturality_left A f φ P).symm⟩

end Complex

end ProEtale

end AlgebraicGeometry
