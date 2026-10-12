/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.Derived.PerfectProjection

/-!
# The compactified projection formula for perfect coefficients

Let `f : X ⟶ Y` be a morphism of schemes with a compactification
`c = (X ⟶[j] X̄ ⟶[p] Y)` (blueprint `def-weil-pbc-projection-compactification`, the functor
`Rf_!^{(j,p)} = Rp_* ∘ j_!` being
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`).
The compactified projection map
```
PF_c : (Rp_*j_!E) ⊗ᴸ Q ⟶ Rp_*(j_!E ⊗ᴸ Lp^*Q) ≅ Rp_*j_!(E ⊗ᴸ Lf^*Q)
```
(`AlgebraicGeometry.ProEtale.projectionMapOfCompactification`) is the projection map
`π_{p,j_!E,Q}` of the proper piece followed by the open-piece isomorphism
`θ_j : j_!E ⊗ᴸ Lp^*Q ≅ j_!(E ⊗ᴸ Lj^*Lp^*Q)`
(`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionIso`, blueprint
`lemma-weil-pbc-projection-formula-open-piece`). We show that it is an isomorphism for perfect
`Q`, and give its inverse `ρ_{p,j_!E,Q} ∘ Rp_*(θ_j⁻¹)` explicitly.

## Main results

- `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarProjectionMap_properPiece` (blueprint
  `lemma-weil-pbc-projection-formula-proper-piece`).
- `AlgebraicGeometry.ProEtale.projectionMapOfCompactificationInv` and
  `AlgebraicGeometry.ProEtale.isIso_projectionMapOfCompactification_app_app_of_strictPerfectPackage`
  (blueprint `lemma-weil-pbc-projection-formula-compactified`), and
  `AlgebraicGeometry.ProEtale.isIso_projectionMapOfCompactification_app_app_of_isDualizable`
  for an arbitrary perfect (dualizable) `Q`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

attribute [local instance] Abelian.hasFiniteBiproducts

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  [ProEtale.UpperStarPreservesFlat A]

/-- **Proper compactification piece** (blueprint
`lemma-weil-pbc-projection-formula-proper-piece`). For a compactification
`c = (X ⟶[j] X̄ ⟶[p] Y)`, an object `E` of `D(X_proét)` and a bounded complex `F` of finite
projective modules on `Y_proét` with a strict-perfect package, the projection map
`π_{p,j_!E,F} : (Rp_*j_!E) ⊗ᴸ F ⟶ Rp_*(j_!E ⊗ᴸ Lp^*F)` is an isomorphism; its inverse is
`ρ_{p,j_!E,F} = AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionInv`. -/
lemma isIso_rightDerivedLowerStarProjectionMap_properPiece
    (E : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    {F : CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ}
    (P : F.StrictPerfectPackage (𝟙_ (Sheaf (Scheme.ProEt.topology Y) A))) :
    IsIso (((rightDerivedLowerStarProjectionMap A c.g).app (D((c.i)_!open[A]).obj E)).app
      (DerivedCategory.Q.obj F)) :=
  isIso_rightDerivedLowerStarProjectionMap_of_strictPerfectPackage A c.g _ P

omit [ProEtale.UpperStarPreservesFlat A] in
private lemma comp_hom_comp_inv_comp_eq_id {C : Type*} [Category* C] {a b c : C} (π : a ⟶ b)
    (e : b ≅ c) (ρ : b ⟶ a) (h : π ≫ ρ = 𝟙 a) : (π ≫ e.hom) ≫ (e.inv ≫ ρ) = 𝟙 a := by
  simp [h]

omit [ProEtale.UpperStarPreservesFlat A] in
private lemma inv_comp_comp_hom_eq_id {C : Type*} [Category* C] {a b c : C} (π : a ⟶ b)
    (e : b ≅ c) (ρ : b ⟶ a) (h : ρ ≫ π = 𝟙 b) : (e.inv ≫ ρ) ≫ (π ≫ e.hom) = 𝟙 c := by
  simp [reassoc_of% h]

/-- The isomorphism `Rp_*(j_!E ⊗ᴸ Lp^*M) ≅ Rp_*j_!(E ⊗ᴸ Lf^*M)` by which the compactified
projection map differs from the projection map of the proper piece: `Rp_*` of the open-piece
isomorphism `θ_j` (`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionIso`,
blueprint `lemma-weil-pbc-projection-formula-open-piece`) followed by
`Lj^*Lp^* ≅ Lf^*`. -/
noncomputable def compactificationOpenPieceIso
    (E : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar A c.g).obj
        (D((c.i)_!open[A]).obj E)).obj M ≅
      ((rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar A c).obj E).obj M :=
  R((c.g)_*[A]).mapIso (((derivedOpenImmersionLowerShriekProjectionIso A c.i).app E).app
      (L((c.g)^*[A]).obj M)).symm ≪≫
    R((c.g)_*[A]).mapIso (D((c.i)_!open[A]).mapIso (((-⊗ᴸ-(X)[A]).obj E).mapIso
      ((leftDerivedUpperStarCompactificationIso A c).app M)))

/-- The compactified projection map `PF_c` is the projection map `π_{p,j_!E,M}` of the proper
piece followed by `AlgebraicGeometry.ProEtale.compactificationOpenPieceIso`. -/
lemma projectionMapOfCompactification_app_app_eq
    (E : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((projectionMapOfCompactification A c).app E).app M =
      ((rightDerivedLowerStarProjectionMap A c.g).app (D((c.i)_!open[A]).obj E)).app M ≫
        (compactificationOpenPieceIso A c E M).hom :=
  rfl

/-- The compactified projection map `PF_c` at `(E, Q)` is an isomorphism as soon as the
projection map `π_{p,j_!E,Q}` of the proper piece is one: the remaining factors are
isomorphisms. -/
lemma isIso_projectionMapOfCompactification_app_app_of_isIso
    (E : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (Q : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (h : IsIso (((rightDerivedLowerStarProjectionMap A c.g).app (D((c.i)_!open[A]).obj E)).app
      Q)) :
    IsIso (((projectionMapOfCompactification A c).app E).app Q) := by
  rw [projectionMapOfCompactification_app_app_eq]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h (Iso.isIso_hom _)

/-- The inverse `ρ_{p,j_!E,F} ∘ Rp_*(θ_j⁻¹)` of the compactified projection map of blueprint
`lemma-weil-pbc-projection-formula-compactified`, for a complex `F` with a strict-perfect
package: the composite
```
Rp_*j_!(E ⊗ᴸ Lf^*F) ≅ Rp_*j_!(E ⊗ᴸ Lj^*Lp^*F) --Rp_*θ_j--> Rp_*(j_!E ⊗ᴸ Lp^*F)
    --ρ_{p,j_!E,F}--> (Rp_*j_!E) ⊗ᴸ F.
``` -/
noncomputable def projectionMapOfCompactificationInv
    (E : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    {F : CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ}
    (P : F.StrictPerfectPackage (𝟙_ (Sheaf (Scheme.ProEt.topology Y) A))) :
    ((rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar A c).obj E).obj
        (DerivedCategory.Q.obj F) ⟶
      ((derivedTensorRightDerivedLowerShriek A c).obj E).obj (DerivedCategory.Q.obj F) :=
  (compactificationOpenPieceIso A c E (DerivedCategory.Q.obj F)).inv ≫
    rightDerivedLowerStarProjectionInv A c.g (D((c.i)_!open[A]).obj E) P

@[reassoc (attr := simp)]
lemma projectionMapOfCompactification_comp_inv
    (E : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    {F : CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ}
    (P : F.StrictPerfectPackage (𝟙_ (Sheaf (Scheme.ProEt.topology Y) A))) :
    ((projectionMapOfCompactification A c).app E).app (DerivedCategory.Q.obj F) ≫
      projectionMapOfCompactificationInv A c E P = 𝟙 _ := by
  rw [projectionMapOfCompactification_app_app_eq, projectionMapOfCompactificationInv]
  exact comp_hom_comp_inv_comp_eq_id _ _ _ (rightDerivedLowerStarProjectionMap_comp_inv A c.g _ P)

@[reassoc (attr := simp)]
lemma projectionMapOfCompactificationInv_comp
    (E : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    {F : CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ}
    (P : F.StrictPerfectPackage (𝟙_ (Sheaf (Scheme.ProEt.topology Y) A))) :
    projectionMapOfCompactificationInv A c E P ≫
      ((projectionMapOfCompactification A c).app E).app (DerivedCategory.Q.obj F) = 𝟙 _ := by
  rw [projectionMapOfCompactification_app_app_eq, projectionMapOfCompactificationInv]
  exact inv_comp_comp_hom_eq_id _ _ _ (rightDerivedLowerStarProjectionInv_comp A c.g _ P)

/-- **Compactified finite-level projection formula** (blueprint
`lemma-weil-pbc-projection-formula-compactified`). For a compactification
`c = (X ⟶[j] X̄ ⟶[p] Y)` of `f` and a perfect complex `F` on `Y_proét` presented by a
strict-perfect package, the compactified projection map
```
(Rp_*j_!E) ⊗ᴸ F --π_{p,j_!E,F}--> Rp_*(j_!E ⊗ᴸ Lp^*F) --Rp_*θ_j--> Rp_*j_!(E ⊗ᴸ Lf^*F)
```
is an isomorphism, with inverse
`AlgebraicGeometry.ProEtale.projectionMapOfCompactificationInv` (that is,
`ρ_{p,j_!E,F} ∘ Rp_*(θ_j⁻¹)`). -/
lemma isIso_projectionMapOfCompactification_app_app_of_strictPerfectPackage
    (E : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    {F : CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ}
    (P : F.StrictPerfectPackage (𝟙_ (Sheaf (Scheme.ProEt.topology Y) A))) :
    IsIso (((projectionMapOfCompactification A c).app E).app (DerivedCategory.Q.obj F)) :=
  ⟨⟨_, projectionMapOfCompactification_comp_inv A c E P,
    projectionMapOfCompactificationInv_comp A c E P⟩⟩

/-- The compactified projection map `PF_c` at `(E, Q)` is an isomorphism for every perfect
(that is, dualizable) `Q` in `D(Y_proét)` (blueprint
`lemma-weil-pbc-projection-formula-compactified`, without choosing a strict-perfect
package). -/
lemma isIso_projectionMapOfCompactification_app_app_of_isDualizable
    (E : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    {Q : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)} (hQ : IsDualizable Q) :
    IsIso (((projectionMapOfCompactification A c).app E).app Q) :=
  isIso_projectionMapOfCompactification_app_app_of_isIso A c E Q
    (isIso_rightDerivedLowerStarProjectionMap_of_isDualizable A c.g _ hQ)

end ProEtale

end AlgebraicGeometry
