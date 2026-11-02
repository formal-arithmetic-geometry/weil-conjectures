/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationCoefficientsFrame
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationCoefficientsTensor
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionTateTwist
public import WeilConjectures.CategoryTheory.Sites.SheafComposeBraided
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.RestrictScalarsBraided

/-!
# The reduction of coefficients as a monoidal change of coefficients

Let `Ψ` be the derived extension of scalars along a surjective morphism `ρ : Λ →+* Λ'` of
finite rings with principal kernel. With the tensor comparisons `δ : Ψ(M ⊗ᴸ N) ≅ Ψ M ⊗ᴸ Ψ N`
of its monoidal structure (`AlgebraicGeometry.Etale.extendScalarsDerivedMonoidal`), the change
of coefficients with supports `AlgebraicGeometry.Etale.reductionSupportedCoefficientChange` is a
monoidal change of coefficients
(`AlgebraicGeometry.Etale.reductionMonoidalSupportedCoefficientChange`, blueprint
`det-sp-purity-coefficient-change`).

All statements are written with the instances used in the definition of the derived tensor
product (`SymmetricCategory.toBraidedCategory` on `ModuleCat`,
`AlgebraicGeometry.Etale.sheafBraidedCategory`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme Functor.OplaxMonoidal

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})

section Tensor

variable (X : Scheme.{u})

/-- The tensor comparison `Ψ(M ⊗ᴸ N) ≅ Ψ M ⊗ᴸ Ψ N` of the derived extension of scalars, the
inverse of the comparison `μ` of its monoidal structure
(`AlgebraicGeometry.Etale.extendScalarsDerivedMonoidal`). -/
noncomputable def derivedExtendScalarsTensorObjIso (M N : 𝐃(X, Λ)) :
    (derivedExtendScalars hρ ha X).obj (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).obj N) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ') X).obj
        ((derivedExtendScalars hρ ha X).obj M)).obj ((derivedExtendScalars hρ ha X).obj N) :=
  letI := extendScalarsDerivedMonoidal hρ ha X
  (Functor.Monoidal.μIso (derivedExtendScalars hρ ha X) M N).symm

/-- The tensor comparison of `Ψ` is the comparison `δ` of its monoidal structure. -/
lemma derivedExtendScalarsTensorObjIso_hom (M N : 𝐃(X, Λ)) :
    letI := extendScalarsDerivedMonoidal hρ ha X
    (derivedExtendScalarsTensorObjIso hρ ha X M N).hom = δ (derivedExtendScalars hρ ha X) M N :=
  rfl

/-- Naturality of the tensor comparison of `Ψ` in the first variable. -/
lemma derivedExtendScalarsTensorObjIso_hom_naturality_left {M M' : 𝐃(X, Λ)} (φ : M ⟶ M')
    (N : 𝐃(X, Λ)) :
    (derivedExtendScalars hρ ha X).map (((derivedTensor (ModuleCat.{u + 1} Λ) X).map φ).app N) ≫
        (derivedExtendScalarsTensorObjIso hρ ha X M' N).hom =
      (derivedExtendScalarsTensorObjIso hρ ha X M N).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ') X).map
          ((derivedExtendScalars hρ ha X).map φ)).app _ :=
  letI := extendScalarsDerivedMonoidal hρ ha X
  (δ_natural_left (derivedExtendScalars hρ ha X) φ N).symm

/-- Naturality of the tensor comparison of `Ψ` in the second variable. -/
lemma derivedExtendScalarsTensorObjIso_hom_naturality_right (M : 𝐃(X, Λ)) {N N' : 𝐃(X, Λ)}
    (ψ : N ⟶ N') :
    (derivedExtendScalars hρ ha X).map (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).map ψ) ≫
        (derivedExtendScalarsTensorObjIso hρ ha X M N').hom =
      (derivedExtendScalarsTensorObjIso hρ ha X M N).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ') X).obj _).map
          ((derivedExtendScalars hρ ha X).map ψ) :=
  letI := extendScalarsDerivedMonoidal hρ ha X
  (δ_natural_right (derivedExtendScalars hρ ha X) M ψ).symm

/-- The tensor comparison of `Ψ` is compatible with the left unitors, through
`Ψ Λ_X ≅ Λ'_X`. -/
lemma derivedExtendScalars_map_derivedTensorLeftUnitor (M : 𝐃(X, Λ)) :
    (derivedExtendScalars hρ ha X).map (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X M).hom =
      (derivedExtendScalarsTensorObjIso hρ ha X (constantComplex Λ X) M).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ') X).map
          (derivedExtendScalarsConstantComplexIso hρ ha X).hom).app _ ≫
          (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ') X _).hom :=
  letI := extendScalarsDerivedMonoidal hρ ha X
  (left_unitality_hom (derivedExtendScalars hρ ha X) M).symm

omit hρ ha in
/-- The symmetry `M ⊗ᴸ N ≅ N ⊗ᴸ M` is the braiding `DerivedCategory.braidedCategory'`. -/
lemma derivedTensorBraidingIso_hom_eq (Λ : Type (u + 1)) [CommRing Λ] (M N : 𝐃(X, Λ)) :
    (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) X M N).hom =
      letI := DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (β_ M N).hom :=
  rfl

omit hρ ha in
/-- The extension of scalars of étale sheaves is compatible with the braidings: it is the strong
monoidal left adjoint of the lax braided restriction of scalars. -/
lemma sheafExtendScalars_map_braiding_comp_δ
    (P Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.extendScalars X.smallEtaleTopology ρ).map (β_ P Q).hom ≫
        δ (Sheaf.extendScalars X.smallEtaleTopology ρ) Q P =
      δ (Sheaf.extendScalars X.smallEtaleTopology ρ) P Q ≫
        (β_ ((Sheaf.extendScalars X.smallEtaleTopology ρ).obj P)
          ((Sheaf.extendScalars X.smallEtaleTopology ρ).obj Q)).hom := by
  have := isMonoidal_sheafAdjunction X.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} ρ)
  exact Adjunction.map_braiding_comp_δ (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ) P Q

/-- The braided structure of the derived extension of scalars `Ψ`, for the derived braidings
`DerivedCategory.braidedCategory'` (`CategoryTheory.Functor.leftDerivedFunctorBraided`). Its
monoidal structure is `AlgebraicGeometry.Etale.extendScalarsDerivedMonoidal`
(`AlgebraicGeometry.Etale.derivedExtendScalarsMonoidal_eq_toMonoidal`). -/
@[instance_reducible]
noncomputable def derivedExtendScalarsBraided :
    letI := extendScalarsDerivedMonoidal hρ ha X
    letI := DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    letI := DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
    (derivedExtendScalars hρ ha X).Braided :=
  haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
  (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorBraided
    (sheafExtendScalars_map_braiding_comp_δ X)

/-- The monoidal structure underlying `AlgebraicGeometry.Etale.derivedExtendScalarsBraided` is
`AlgebraicGeometry.Etale.extendScalarsDerivedMonoidal`. -/
lemma derivedExtendScalarsMonoidal_eq_toMonoidal :
    letI := DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    letI := DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
    extendScalarsDerivedMonoidal hρ ha X = (derivedExtendScalarsBraided hρ ha X).toMonoidal :=
  rfl

/-- The comparison `δ` of the braided structure
`AlgebraicGeometry.Etale.derivedExtendScalarsBraided` is compatible with the braidings. -/
lemma derivedExtendScalarsBraided_map_braiding_comp_δ (M N : 𝐃(X, Λ)) :
    letI := DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    letI := DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
    letI := derivedExtendScalarsBraided hρ ha X
    (derivedExtendScalars hρ ha X).map (β_ M N).hom ≫ δ (derivedExtendScalars hρ ha X) N M =
      δ (derivedExtendScalars hρ ha X) M N ≫
        (β_ ((derivedExtendScalars hρ ha X).obj M) ((derivedExtendScalars hρ ha X).obj N)).hom := by
  let := DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let := DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
  let := derivedExtendScalarsBraided hρ ha X
  rw [Functor.map_braiding, Category.assoc, Category.assoc, Functor.Monoidal.μ_δ,
    Category.comp_id]

/-- The tensor comparison of `Ψ` is compatible with the symmetries. -/
lemma derivedExtendScalars_map_derivedTensorBraidingIso (M N : 𝐃(X, Λ)) :
    (derivedExtendScalars hρ ha X).map
        (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) X M N).hom ≫
        (derivedExtendScalarsTensorObjIso hρ ha X N M).hom =
      (derivedExtendScalarsTensorObjIso hρ ha X M N).hom ≫
        (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ') X _ _).hom := by
  have h := derivedExtendScalarsBraided_map_braiding_comp_δ hρ ha X M N
  rw [← derivedExtendScalarsMonoidal_eq_toMonoidal] at h
  rw [derivedTensorBraidingIso_hom_eq, derivedTensorBraidingIso_hom_eq,
    derivedExtendScalarsTensorObjIso_hom, derivedExtendScalarsTensorObjIso_hom]
  exact h

variable {X} in
/-- The tensor comparison of `Ψ` is natural with respect to tensor products of morphisms. -/
@[reassoc]
lemma map_derivedTensorHom_comp_derivedExtendScalarsDerivedTensorIso_hom {K K₁ M M₁ : 𝐃(X, Λ)}
    (f : K ⟶ K₁) (g : M ⟶ M₁) :
    (derivedExtendScalars hρ ha X).map (derivedTensorHom (ModuleCat.{u + 1} Λ) f g) ≫
        (derivedExtendScalarsTensorObjIso hρ ha X K₁ M₁).hom =
      (derivedExtendScalarsTensorObjIso hρ ha X K M).hom ≫
        derivedTensorHom (ModuleCat.{u + 1} Λ') ((derivedExtendScalars hρ ha X).map f)
          ((derivedExtendScalars hρ ha X).map g) := by
  rw [derivedTensorHom, Functor.map_comp, Category.assoc,
    derivedExtendScalarsTensorObjIso_hom_naturality_right,
    reassoc_of% (derivedExtendScalarsTensorObjIso_hom_naturality_left hρ ha X f M),
    derivedTensorHom]

end Tensor

section Diagonal

variable [Finite Λ] [Finite Λ'] [NeZero (ringChar Λ)] [NeZero (ringChar Λ')] (U : Scheme.{u})
  [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U]

omit [Finite Λ] [Finite Λ'] [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U] in
/-- A family of morphisms `Ψ(Λ_U(m)) ⟶ Λ'_U(m)` is compatible with the equality transports
along `m = m'`. -/
@[reassoc]
lemma map_eqToHom_comp_tateObject {r : ∀ m : ℤ,
    (derivedExtendScalars hρ ha U).obj (tateObject Λ U m) ⟶ tateObject Λ' U m} {m m' : ℤ}
    (h : m = m') (e : tateObject Λ U m = tateObject Λ U m')
    (e' : tateObject Λ' U m = tateObject Λ' U m') :
    (derivedExtendScalars hρ ha U).map (eqToHom e) ≫ r m' = r m ≫ eqToHom e' := by
  subst h
  simp

/-- The diagonal `Λ_U ⟶ Λ_U ⊗ᴸ Λ_U`, with its last factor written as a tensor product of
morphisms. -/
lemma constantComplexDiagonal_eq_derivedTensorHom (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [NeZero (ringChar Λ)] [HasInvertibleExponent Λ U] :
    constantComplexDiagonal Λ U =
      (HasTateTwist.twistObjectZeroIso (Λ := Λ) U).inv ≫ eqToHom (by rw [add_zero]) ≫
        (HasTateTwist.twistObjectAddIso U 0 0).inv ≫
          derivedTensorHom (ModuleCat.{u + 1} Λ) (HasTateTwist.twistObjectZeroIso U).hom
            (HasTateTwist.twistObjectZeroIso U).hom :=
  rfl

/-- **The derived extension of scalars is compatible with the diagonal** `Λ_U ⟶ Λ_U ⊗ᴸ Λ_U`
(`AlgebraicGeometry.Etale.constantComplexDiagonal`), through `Ψ Λ_U ≅ Λ'_U`, given a family of
identifications `r m : Ψ(Λ_U(m)) ≅ Λ'_U(m)` which is compatible with `Λ(0) ≅ Λ` (`h₀`) and with
the product `Λ(0) ⊗ᴸ Λ(0) ≅ Λ(0 + 0)` (`hμ`). -/
lemma derivedExtendScalars_map_constantComplexDiagonal
    (r : ∀ m : ℤ, (derivedExtendScalars hρ ha U).obj (tateObject Λ U m) ≅ tateObject Λ' U m)
    (h₀ : (derivedExtendScalars hρ ha U).map (HasTateTwist.twistObjectZeroIso (Λ := Λ) U).hom ≫
        (derivedExtendScalarsConstantComplexIso hρ ha U).hom =
      (r 0).hom ≫ (HasTateTwist.twistObjectZeroIso (Λ := Λ') U).hom)
    (hμ : (derivedExtendScalars hρ ha U).map
          (HasTateTwist.twistObjectAddIso (Λ := Λ) U 0 0).hom ≫ (r (0 + 0)).hom =
      (derivedExtendScalarsTensorObjIso hρ ha U _ _).hom ≫
        derivedTensorHom (ModuleCat.{u + 1} Λ') (r 0).hom (r 0).hom ≫
          (HasTateTwist.twistObjectAddIso (Λ := Λ') U 0 0).hom) :
    (derivedExtendScalars hρ ha U).map (constantComplexDiagonal Λ U) ≫
        (derivedExtendScalarsTensorObjIso hρ ha U _ _).hom ≫
          derivedTensorHom (ModuleCat.{u + 1} Λ')
            (derivedExtendScalarsConstantComplexIso hρ ha U).hom
            (derivedExtendScalarsConstantComplexIso hρ ha U).hom =
      (derivedExtendScalarsConstantComplexIso hρ ha U).hom ≫ constantComplexDiagonal Λ' U := by
  have hμ' : (derivedExtendScalarsTensorObjIso hρ ha U _ _).hom ≫
      derivedTensorHom (ModuleCat.{u + 1} Λ') (r 0).hom (r 0).hom =
      (derivedExtendScalars hρ ha U).map (HasTateTwist.twistObjectAddIso (Λ := Λ) U 0 0).hom ≫
        (r (0 + 0)).hom ≫ (HasTateTwist.twistObjectAddIso (Λ := Λ') U 0 0).inv := by
    rw [reassoc_of% hμ, Iso.hom_inv_id, Category.comp_id]
  have h₀' : (derivedExtendScalars hρ ha U).map (HasTateTwist.twistObjectZeroIso (Λ := Λ) U).inv ≫
      (r 0).hom = (derivedExtendScalarsConstantComplexIso hρ ha U).hom ≫
        (HasTateTwist.twistObjectZeroIso (Λ := Λ') U).inv := by
    rw [← cancel_mono (HasTateTwist.twistObjectZeroIso (Λ := Λ') U).hom, Category.assoc,
      ← h₀, Category.assoc, Iso.inv_hom_id, Category.comp_id, ← Functor.map_comp_assoc,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [constantComplexDiagonal_eq_derivedTensorHom, constantComplexDiagonal_eq_derivedTensorHom]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [tateObject] at hμ' ⊢
  rw [
    map_derivedTensorHom_comp_derivedExtendScalarsDerivedTensorIso_hom_assoc,
    derivedTensorHom_comp, h₀, ← derivedTensorHom_comp, reassoc_of% hμ',
    Iso.map_inv_hom_id_assoc,
    map_eqToHom_comp_tateObject_assoc hρ ha U (r := fun m ↦ (r m).hom) (add_zero 0).symm,
    reassoc_of% h₀']

end Diagonal

section UpperShriek

variable [Finite Λ] [Finite Λ']

/-- The tensor comparison of `Ψ` is compatible with the tensor maps
`Ri^! M ⊗ᴸ Li^* N ⟶ Ri^!(M ⊗ᴸ N)` of a closed immersion `i`, through the comparisons of `Ψ`
with `Ri^!` and `Li^*`. -/
lemma derivedExtendScalars_map_rightDerivedUpperShriekTensorMap {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (M N : 𝐃(X, Λ)) :
    (derivedExtendScalars hρ ha Z).map (rightDerivedUpperShriekTensorMap i M N) ≫
        (derivedExtendScalarsUpperShriekMap hρ ha i).app
          (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).obj N) ≫
          (R(i)^![Λ']).map (derivedExtendScalarsTensorObjIso hρ ha X M N).hom =
      (derivedExtendScalarsTensorObjIso hρ ha Z ((R(i)^![Λ]).obj M)
          ((L((i)^*[ModuleCat.{u + 1} Λ])).obj N)).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ') Z).map
          ((derivedExtendScalarsUpperShriekMap hρ ha i).app M)).app _ ≫
          ((derivedTensor (ModuleCat.{u + 1} Λ') Z).obj _).map
            ((derivedExtendScalarsPullbackIso hρ ha i).hom.app N) ≫
            rightDerivedUpperShriekTensorMap i _ _ := by
  sorry

end UpperShriek

section Structure

variable [Finite Λ] [Finite Λ'] [HasTateTwist Λ] [HasTateTwist Λ']

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The reduction of coefficients is a monoidal change of coefficients**: the change of
coefficients with supports `AlgebraicGeometry.Etale.reductionSupportedCoefficientChange`, with
the tensor comparisons `δ : Ψ(M ⊗ᴸ N) ≅ Ψ M ⊗ᴸ Ψ N` of the derived extension of scalars. -/
noncomputable def reductionMonoidalSupportedCoefficientChange
    (τ : DerivedExtendScalarsTateShiftData Λ Λ' hρ ha) :
    MonoidalSupportedCoefficientChange Λ Λ' where
  toSupportedCoefficientChange := reductionSupportedCoefficientChange hρ ha τ
  tensorIso X M N := derivedExtendScalarsTensorObjIso hρ ha X M N
  tensorIso_hom_naturality_left X _ _ φ N :=
    derivedExtendScalarsTensorObjIso_hom_naturality_left hρ ha X φ N
  tensorIso_hom_naturality_right X M _ _ ψ :=
    derivedExtendScalarsTensorObjIso_hom_naturality_right hρ ha X M ψ
  map_derivedTensorLeftUnitor X M := derivedExtendScalars_map_derivedTensorLeftUnitor hρ ha X M
  map_derivedTensorBraidingIso X M N :=
    derivedExtendScalars_map_derivedTensorBraidingIso hρ ha X M N
  map_rightDerivedUpperShriekTensorMap i _ M N :=
    derivedExtendScalars_map_rightDerivedUpperShriekTensorMap hρ ha i M N

end Structure

section Reduction

variable [Finite Λ] [Finite Λ'] [NeZero (ringChar Λ)] [NeZero (ringChar Λ')] (k : ℕ)
  (hk : ringChar Λ = ringChar Λ' * k)

/-- The hypothesis `hΔ` of
`Etale.MonoidalSupportedCoefficientChange.mapSupportedClass_cupWithSupportsTateObject`
for the reduction of coefficients: `Ψ` is compatible with the diagonal `Λ_U ⟶ Λ_U ⊗ᴸ Λ_U`. -/
lemma reductionMonoidalSupportedCoefficientChange_constantComplexDiagonal (U : Scheme.{u})
    [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U] :
    ((reductionMonoidalSupportedCoefficientChange hρ ha
        (reductionTateTwistShiftData hρ ha k hk)).functor U).map (constantComplexDiagonal Λ U) ≫
        (reductionMonoidalSupportedCoefficientChange hρ ha
          (reductionTateTwistShiftData hρ ha k hk)).tensorMap
          ((reductionMonoidalSupportedCoefficientChange hρ ha
            (reductionTateTwistShiftData hρ ha k hk)).constantComplexIso U).hom
          ((reductionMonoidalSupportedCoefficientChange hρ ha
            (reductionTateTwistShiftData hρ ha k hk)).constantComplexIso U).hom =
      ((reductionMonoidalSupportedCoefficientChange hρ ha
          (reductionTateTwistShiftData hρ ha k hk)).constantComplexIso U).hom ≫
        constantComplexDiagonal Λ' U :=
  derivedExtendScalars_map_constantComplexDiagonal hρ ha U (reductionTateTwistIso hρ ha k hk U)
    (map_twistObjectZeroIso_hom_comp_derivedExtendScalarsConstantComplexIso_hom hρ ha k hk U)
    (by
      let := extendScalarsDerivedMonoidal hρ ha U
      rw [reductionTateTwistIso_mul, MonoidalCategory.tensorHom_def]
      rfl)

/-- The hypothesis `hμ` of
`Etale.MonoidalSupportedCoefficientChange.mapSupportedClass_cupWithSupportsTateObject`
for the reduction of coefficients with its canonical Tate data
(`AlgebraicGeometry.Etale.reductionTateTwistShiftData_mul`). -/
lemma reductionMonoidalSupportedCoefficientChange_shiftTateObjectAddIso (U : Scheme.{u})
    [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U] (m m' : ℤ) :
    ((reductionMonoidalSupportedCoefficientChange hρ ha
        (reductionTateTwistShiftData hρ ha k hk)).functor U).map
        (shiftTateObjectAddIso Λ U m m').hom ≫
        ((reductionMonoidalSupportedCoefficientChange hρ ha
          (reductionTateTwistShiftData hρ ha k hk)).tateShiftIso U (m + m')).hom =
      (reductionMonoidalSupportedCoefficientChange hρ ha
          (reductionTateTwistShiftData hρ ha k hk)).tensorMap
          ((reductionMonoidalSupportedCoefficientChange hρ ha
            (reductionTateTwistShiftData hρ ha k hk)).tateShiftIso U m).hom
          ((reductionMonoidalSupportedCoefficientChange hρ ha
            (reductionTateTwistShiftData hρ ha k hk)).tateShiftIso U m').hom ≫
        (shiftTateObjectAddIso Λ' U m m').hom :=
  (reductionTateTwistShiftData_mul hρ ha k hk U m m').trans (by
    rw [MonoidalSupportedCoefficientChange.tensorMap, Category.assoc]
    rfl)

end Reduction

end AlgebraicGeometry.Etale
