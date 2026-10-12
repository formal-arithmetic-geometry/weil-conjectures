/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.StrictPerfectPackage
public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal.Oplax
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal.Shift

/-!
# The projection formula for perfect coefficients

Let `f : X ⟶ Y` be a morphism of schemes and `K ∈ D(X_proét)`. The projection map
```
π_{f,K,P} : Rf_*K ⊗ᴸ P ⟶ Rf_*(K ⊗ᴸ Lf^*P)
```
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap`, blueprint
`def-weil-pbc-projection-formula-map`) is the transpose along `Lf^* ⊣ Rf_*` of the tensor
comparison of `Lf^*` followed by the counit. We show that the objects `P` of `D(Y_proét)` at which
it is an isomorphism form a thick triangulated subcategory
(`AlgebraicGeometry.ProEtale.projectionFormulaLocus`) containing the unit, hence every perfect
complex.

## Main definitions and results

- `AlgebraicGeometry.ProEtale.projectionFormulaLocus f K`: the objects `P` at which `π_{f,K,P}` is
  an isomorphism; `AlgebraicGeometry.ProEtale.isTriangulated_projectionFormulaLocus`: it is a
  triangulated subcategory, closed under isomorphisms and stable under retracts.
- `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarProjectionMap_shift_biproduct_unit`
  (blueprint `lemma-weil-pbc-projection-formula-finite-free`): `π` is an isomorphism at a shifted
  finite free module `Λᴺ[a]`.
- `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarProjectionMap_of_strictPerfectPackage`
  (blueprint `lemma-weil-pbc-projection-formula-totalization`): `π` is an isomorphism at a bounded
  complex of finite projective modules, given by a strict-perfect package; its inverse is
  `AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionInv`.
- `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarProjectionMap_of_isDualizable`: `π` is
  an isomorphism at every perfect (that is, dualizable) complex.

## Implementation notes

The blueprint (`def-weil-pbc-projection-formula-arrows`) defines an inverse `ρ` of `π` termwise on
a strict-perfect package and totalizes it. Here the termwise inverses are
`CategoryTheory.Adjunction.rightAdjointProjectionMapInvOfRetract` (for a retract of a finite free
module) and the inverse of `π` at a finite free module; the total inverse is the inverse of `π`,
which exists because the objects at which `π` is invertible form a triangulated subcategory. An
inverse being unique, this is the totalization of the termwise inverses.

To prove that this subcategory is triangulated, `Lf^*` and `Rf_*` are given the commutations with
the shifts of `AlgebraicGeometry.ProEtale.commShiftLeftDerivedUpperStar'` and
`AlgebraicGeometry.ProEtale.commShiftRightDerivedLowerStar'`; the statements do not depend on
this choice.
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

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [ProEtale.UpperStarPreservesFlat A]

/-- The objects `P` of `D(Y_proét)` at which the projection map
`π_{f,K,P} : Rf_*K ⊗ᴸ P ⟶ Rf_*(K ⊗ᴸ Lf^*P)` is an isomorphism, for a fixed `K`. -/
def projectionFormulaLocus (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :=
  NatTrans.isoLocus ((rightDerivedLowerStarProjectionMap A f).app K)

lemma projectionFormulaLocus_iff (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (P : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    projectionFormulaLocus A f K P ↔
      IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app P) :=
  Iff.rfl

instance (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (projectionFormulaLocus A f K).IsClosedUnderIsomorphisms :=
  inferInstanceAs (NatTrans.isoLocus _).IsClosedUnderIsomorphisms

instance (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (projectionFormulaLocus A f K).IsStableUnderRetracts :=
  inferInstanceAs (NatTrans.isoLocus _).IsStableUnderRetracts

/-- The objects `P` at which the projection map `π_{f,K,P}` is an isomorphism form a triangulated
subcategory of `D(Y_proét)`. Being closed under isomorphisms and stable under retracts, it is a
thick triangulated subcategory. This is the first assertion of blueprint
`lemma-weil-pbc-perfect-projection-formula`. -/
instance isTriangulated_projectionFormulaLocus
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (projectionFormulaLocus A f K).IsTriangulated := by
  let := commShiftRightDerivedLowerStar' A f
  let := commShiftLeftDerivedUpperStar' A f
  have := commShift_derivedUpperStarLowerStarAdjunction' A f
  have := isTriangulated_leftDerivedUpperStar' A f
  have := isTriangulated_rightDerivedLowerStar' A f
  exact (derivedUpperStarLowerStarAdjunction A f).isTriangulated_isoLocus_projectionMap
    (leftDerivedUpperStarTensorComparison A f) K

/-- The projection map `π_{f,K,𝟙} : Rf_*K ⊗ᴸ 𝟙 ⟶ Rf_*(K ⊗ᴸ Lf^*𝟙)` at the unit is an
isomorphism: it is the composite of the unitors and of the unit comparison `Lf^*𝟙 ≅ 𝟙`. -/
lemma projectionFormulaLocus_tensorUnit
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    projectionFormulaLocus A f K (𝟙_ _) := by
  let := leftDerivedUpperStarOplaxMonoidal A f
  have := isIso_leftDerivedUpperStarOplaxMonoidal_η A f
  exact (derivedUpperStarLowerStarAdjunction A f).isIso_rightAdjointProjectionMap_app_app_tensorUnit
    (leftDerivedUpperStarTensorComparison A f) (fun _ _ ↦ rfl) K

omit [ProEtale.UpperStarPreservesFlat A] in
/-- The unit comparison `𝟙_ ⟶ Q(𝟙_)` of the localization functor
`Q : C(Y_proét) ⥤ D(Y_proét)` is an isomorphism: the unit of `D(Y_proét)` is the unit sheaf
placed in degree `0`. -/
lemma isIso_ε_Q (Y : Scheme.{u}) :
    IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology Y) A))) := by
  have := DerivedCategory.isIso_ε_Qh (Sheaf (Scheme.ProEt.topology Y) A)
  change IsIso ((Functor.LaxMonoidal.ε DerivedCategory.Qh ≫ DerivedCategory.Qh.map
    (Functor.LaxMonoidal.ε (HomotopyCategory.quotient _ (ComplexShape.up ℤ)))) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app _)
  infer_instance

/-- The monoidal unit `Λ_Y` of pro-étale sheaves placed in degree `0` lies in
`AlgebraicGeometry.ProEtale.projectionFormulaLocus`. -/
lemma projectionFormulaLocus_singleFunctor_tensorUnit
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    projectionFormulaLocus A f K
      ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ (Sheaf (Scheme.ProEt.topology Y) A))) := by
  exact (projectionFormulaLocus A f K).prop_of_iso
    (@asIso _ _ _ _ (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology Y) A)))
      (isIso_ε_Q A Y))
    (projectionFormulaLocus_tensorUnit A f K)

/-- **Finite-free projection formula** (blueprint
`lemma-weil-pbc-projection-formula-finite-free`). The projection map is an isomorphism at a
shifted finite sum `Λᴺ[a]` of copies of the unit of `D(Y_proét)`. -/
lemma isIso_rightDerivedLowerStarProjectionMap_shift_biproduct_unit
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (N : ℕ) (a : ℤ) :
    IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app
      ((⨁ fun _ : Fin N ↦ 𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)))⟦a⟧)) := by
  let P := projectionFormulaLocus A f K
  have h : P (⨁ fun _ : Fin N ↦ 𝟙_ _) :=
    P.prop_of_isLimit_fan (biproduct.isLimit _) fun _ ↦ projectionFormulaLocus_tensorUnit A f K
  exact P.le_shift a _ h

/-- The projection map is an isomorphism at a finite free sheaf of modules `Λᴺ` placed in
degree `a` (blueprint `lemma-weil-pbc-projection-formula-finite-free`). -/
lemma isIso_rightDerivedLowerStarProjectionMap_singleFunctor_biproduct_unit
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (N : ℕ) (a : ℤ) :
    IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app
      ((DerivedCategory.singleFunctor _ a).obj
        (⨁ fun _ : Fin N ↦ 𝟙_ (Sheaf (Scheme.ProEt.topology Y) A)))) := by
  let P := projectionFormulaLocus A f K
  have h : P ((DerivedCategory.singleFunctor _ 0).obj
      (⨁ fun _ : Fin N ↦ 𝟙_ (Sheaf (Scheme.ProEt.topology Y) A))) :=
    P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapBiproduct _).symm
      (P.prop_of_isLimit_fan (biproduct.isLimit _) fun _ ↦
        projectionFormulaLocus_singleFunctor_tensorUnit A f K)
  exact P.prop_of_iso (((DerivedCategory.singleFunctors _).shiftIso (-a) a 0
    (by omega)).app _) (P.le_shift (-a) _ h)

section Package

/-- The arrow `ρ_{F^r} : Rf_*(K ⊗ᴸ Lf^*F^r) ⟶ Rf_*K ⊗ᴸ F^r` of blueprint
`def-weil-pbc-projection-formula-arrows`, for a finite projective sheaf of modules `F^r`
presented as a retract of `Λᴺ` (maps `i : F^r ⟶ Λᴺ` and `p : Λᴺ ⟶ F^r` with `p ∘ i = 1`): the
composite
```
Rf_*(K ⊗ᴸ Lf^*F^r) --Rf_*(1 ⊗ Lf^* i)--> Rf_*(K ⊗ᴸ Lf^*Λᴺ) --ρ_N--> Rf_*K ⊗ᴸ Λᴺ --1 ⊗ p--> Rf_*K ⊗ᴸ F^r
```
where `ρ_N` is the inverse of the finite-sum identification `π_{f,K,Λᴺ}`. By
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionInvOfRetract_eq` it is the inverse of
`π_{f,K,F^r}`. -/
noncomputable def rightDerivedLowerStarProjectionInvOfRetract
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    {F : Sheaf (Scheme.ProEt.topology Y) A} {N : ℕ}
    (h : Retract F (⨁ fun _ : Fin N ↦ 𝟙_ (Sheaf (Scheme.ProEt.topology Y) A))) :
    R((f)_*[A]).obj (((-⊗ᴸ-(X)[A]).obj K).obj
        (L((f)^*[A]).obj ((DerivedCategory.singleFunctor _ 0).obj F))) ⟶
      ((-⊗ᴸ-(Y)[A]).obj (R((f)_*[A]).obj K)).obj ((DerivedCategory.singleFunctor _ 0).obj F) :=
  haveI : IsIso (((derivedUpperStarLowerStarAdjunction A f).rightAdjointProjectionMap
      (leftDerivedUpperStarTensorComparison A f)).app K).app ((DerivedCategory.singleFunctor _ 0).obj
        (⨁ fun _ : Fin N ↦ 𝟙_ (Sheaf (Scheme.ProEt.topology Y) A)))) :=
    isIso_rightDerivedLowerStarProjectionMap_singleFunctor_biproduct_unit A f K N 0
  (derivedUpperStarLowerStarAdjunction A f).rightAdjointProjectionMapInvOfRetract
    (leftDerivedUpperStarTensorComparison A f) (h.map (DerivedCategory.singleFunctor _ 0)) K

/-- **Finite-projective summand equations** (blueprint
`lemma-weil-pbc-projection-formula-projective-summand`): for a finite projective `F^r`, the arrow
`ρ_{F^r}` is the inverse of the projection map `π_{f,K,F^r}`; in particular it does not depend on
the presentation of `F^r` as a retract of a finite free module. -/
lemma rightDerivedLowerStarProjectionInvOfRetract_eq
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    {F : Sheaf (Scheme.ProEt.topology Y) A} {N : ℕ}
    (h : Retract F (⨁ fun _ : Fin N ↦ 𝟙_ (Sheaf (Scheme.ProEt.topology Y) A))) :
    ∃ _ : IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app
        ((DerivedCategory.singleFunctor _ 0).obj F)),
      rightDerivedLowerStarProjectionInvOfRetract A f K h =
        inv (((rightDerivedLowerStarProjectionMap A f).app K).app
          ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  have : IsIso (((derivedUpperStarLowerStarAdjunction A f).rightAdjointProjectionMap
      (leftDerivedUpperStarTensorComparison A f)).app K).app ((DerivedCategory.singleFunctor _ 0).obj
        (⨁ fun _ : Fin N ↦ 𝟙_ (Sheaf (Scheme.ProEt.topology Y) A)))) :=
    isIso_rightDerivedLowerStarProjectionMap_singleFunctor_biproduct_unit A f K N 0
  exact ⟨_, (derivedUpperStarLowerStarAdjunction A f).rightAdjointProjectionMapInvOfRetract_eq
    (leftDerivedUpperStarTensorComparison A f) (h.map (DerivedCategory.singleFunctor _ 0)) K⟩

/-- **Signed totalization of the perfect formula** (blueprint
`lemma-weil-pbc-projection-formula-totalization`). Let `F` be a bounded complex of finite
projective sheaves of modules on `Y_proét`, presented by a strict-perfect package. Then the
projection map `π_{f,K,F} : Rf_*K ⊗ᴸ F ⟶ Rf_*(K ⊗ᴸ Lf^*F)` is an isomorphism, with inverse
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionInv`. -/
lemma isIso_rightDerivedLowerStarProjectionMap_of_strictPerfectPackage
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    {F : CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ}
    (P : F.StrictPerfectPackage (𝟙_ (Sheaf (Scheme.ProEt.topology Y) A))) :
    IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app (DerivedCategory.Q.obj F)) :=
  P.prop_Q_obj (projectionFormulaLocus A f K) (projectionFormulaLocus_singleFunctor_tensorUnit A f K)

/-- The total arrow `ρ_{f,K,F} : Rf_*(K ⊗ᴸ Lf^*F) ⟶ Rf_*K ⊗ᴸ F` of blueprint
`def-weil-pbc-projection-formula-arrows`, for a complex `F` with a strict-perfect package. The
blueprint obtains it by totalizing the termwise arrows
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionInvOfRetract`; it is the inverse of
the projection map `π_{f,K,F}`, which we take as its definition (an inverse being unique). -/
noncomputable def rightDerivedLowerStarProjectionInv
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    {F : CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ}
    (P : F.StrictPerfectPackage (𝟙_ (Sheaf (Scheme.ProEt.topology Y) A))) :
    R((f)_*[A]).obj (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj (DerivedCategory.Q.obj F))) ⟶
      ((-⊗ᴸ-(Y)[A]).obj (R((f)_*[A]).obj K)).obj (DerivedCategory.Q.obj F) :=
  haveI := isIso_rightDerivedLowerStarProjectionMap_of_strictPerfectPackage A f K P
  inv (((rightDerivedLowerStarProjectionMap A f).app K).app (DerivedCategory.Q.obj F))

@[reassoc (attr := simp)]
lemma rightDerivedLowerStarProjectionMap_comp_inv
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    {F : CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ}
    (P : F.StrictPerfectPackage (𝟙_ (Sheaf (Scheme.ProEt.topology Y) A))) :
    ((rightDerivedLowerStarProjectionMap A f).app K).app (DerivedCategory.Q.obj F) ≫
      rightDerivedLowerStarProjectionInv A f K P = 𝟙 _ := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_strictPerfectPackage A f K P
  simp [rightDerivedLowerStarProjectionInv]

@[reassoc (attr := simp)]
lemma rightDerivedLowerStarProjectionInv_comp
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    {F : CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ}
    (P : F.StrictPerfectPackage (𝟙_ (Sheaf (Scheme.ProEt.topology Y) A))) :
    rightDerivedLowerStarProjectionInv A f K P ≫
      ((rightDerivedLowerStarProjectionMap A f).app K).app (DerivedCategory.Q.obj F) = 𝟙 _ := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_strictPerfectPackage A f K P
  simp [rightDerivedLowerStarProjectionInv]

end Package

/-- The projection map `π_{f,K,P}` is an isomorphism at every perfect complex `P`, perfectness
being rendered as dualizability for the derived tensor product. -/
lemma isIso_rightDerivedLowerStarProjectionMap_of_isDualizable
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    {P : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)} (hP : IsDualizable P) :
    IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app P) := by
  obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory (Sheaf (Scheme.ProEt.topology Y) A)
  let := leftDerivedUpperStarMonoidal A f
  exact (derivedUpperStarLowerStarAdjunction A f).isIso_rightAdjointProjectionMap_app_app_of_isDualizable
    (leftDerivedUpperStarTensorComparison A f) (fun _ _ ↦ rfl) K hP

end ProEtale

end AlgebraicGeometry
