/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionTateTwist
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReduction
public import WeilConjectures.TateTwist.IntegralReduction

/-!
# The products of the reductions of the integral Tate twists

Let `Λ = 𝒪_E ⧸ ℓᵐ` and `red_m` the reduction modulo `ℓᵐ` read on the small étale site. Through
`red_m(𝒪_{E,X}(d)) ≅ Λ_X(d) ≅ (Λ_X(1)^{⊗ d})[0]`, the products of the Tate twists become
products of sheaves placed in degree zero. This file isolates the two inputs of the recursion
`ProEtale.CondensedRing.integersModPowReductionTateTwistIso_step`:

* `Etale.tateTwistIntTensorFamily_step_hom_comp_tateObjectNatIsoSingleFunctor_hom`: the product
  `Λ_X(1) ⊗ᴸ Λ_X(d) ≅ Λ_X(d + 1)` of the Tate twists is, in degree zero, the product
  `Λ_X(1)^{⊗ 1} ⊗ Λ_X(1)^{⊗ d} ≅ Λ_X(1)^{⊗ (d + 1)}` of sheaves
  (`Etale.tateSheafPowOneTensorIso`);
* `ProEtale.CondensedRing.map_etaleReductionIntegralTateTwistMulIso_hom_comp`: the reduction
  `β : Ψ(red_{n+1} -) ≅ red_n -` is compatible with these products
  (`ProEtale.CondensedRing.etaleReductionIntegralTateTwistMulIso`), through the monoidal
  structure of `Ψ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

-- the instances used in the definitions of the Tate twist families
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace CategoryTheory.MonoidalCategory.IntTensorFamily

open Functor.OplaxMonoidal

variable {C : Type*} [Category* C] [MonoidalCategory C] {D : Type*} [Category* D]
  [MonoidalCategory D] (P : IntTensorFamily C) (F : C ⥤ D) [F.OplaxMonoidal] [IsIso (η F)]
  [∀ X Y, IsIso (δ F X Y)]

/-- The successor multiplication of the image of a coherent family under a functor is the image
of the successor multiplication, through the tensor comparison `δ`. -/
lemma map_step_hom (a : ℤ) :
    ((P.map F).step a).hom = inv (δ F _ _) ≫ F.map (P.step a).hom := by
  simp [step, mulIso, map, eqToHom_map]

end CategoryTheory.MonoidalCategory.IntTensorFamily

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [NeZero (ringChar Λ)] (X : Scheme.{u})
  [HasInvertibleExponent Λ X]

/-- The tensor powers `Λ_X(1)^{⊗ d}` of the Tate sheaf are flat. -/
lemma flat_tateSheafPow (d : ℕ) : ObjectProperty.flat (tateSheafPow Λ X d) :=
  ObjectProperty.prop_of_iso _ (tateTwistSheafNatIso Λ X d) (flat_tateTwistSheaf Λ X d)

/-- The product `Λ_X(1)^{⊗ 1} ⊗ Λ_X(1)^{⊗ d} ≅ Λ_X(1)^{⊗ (d + 1)}` of the tensor powers of the
Tate sheaf: `Λ_X(1)^{⊗ 1} = 𝟙 ⊗ Λ_X(1)`, followed by the braiding. -/
noncomputable def tateSheafPowOneTensorIso (d : ℕ) :
    tateSheafPow Λ X 1 ⊗ tateSheafPow Λ X d ≅ tateSheafPow Λ X (d + 1) :=
  whiskerRightIso (λ_ (tateSheaf Λ X)) (tateSheafPow Λ X d) ≪≫
    β_ (tateSheaf Λ X) (tateSheafPow Λ X d)

/-- **The product of the Tate twists in degree zero**: through
`Λ_X(d) ≅ (Λ_X(1)^{⊗ d})[0]` (`Etale.tateObjectNatIsoSingleFunctor`), the product
`Λ_X(1) ⊗ᴸ Λ_X(d) ≅ Λ_X(d + 1)` of the coherent family of the Tate twists is the product
`Λ_X(1)^{⊗ 1} ⊗ Λ_X(1)^{⊗ d} ≅ Λ_X(1)^{⊗ (d + 1)}` of sheaves, placed in degree zero (the
tensor product of flat sheaves in degree zero is underived,
`Etale.singleFunctorObjTensorIso`). -/
@[reassoc]
lemma tateTwistIntTensorFamily_step_hom_comp_tateObjectNatIsoSingleFunctor_hom (d : ℕ) :
    ((tateTwistIntTensorFamily Λ X).step d).hom ≫ (tateObjectNatIsoSingleFunctor Λ X (d + 1)).hom =
      ((tateObjectNatIsoSingleFunctor Λ X 1).hom ⊗ₘ (tateObjectNatIsoSingleFunctor Λ X d).hom) ≫
        (singleFunctorObjTensorIso _ _ (flat_tateSheafPow Λ X 1)).hom ≫
          (DerivedCategory.singleFunctor _ 0).map (tateSheafPowOneTensorIso Λ X d).hom := by
  sorry

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor.OplaxMonoidal

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

section Level

variable (m : ℕ) [NeZero (ringChar (integersModPowCoeff.{u} ℓ E m))]
  [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E m) X.left]

/-- The reduction of the integral Tate twist as a sheaf in degree zero:
`red_m(𝒪_{E,X}(d)) ≅ Λ_X(d) ≅ (Λ_X(1)^{⊗ d})[0]`. -/
noncomputable def etaleReductionIntegralTateTwistSingleIso (d : ℕ) :
    (etaleReduction ℓ E m X).obj (integralTateTwistBoundedConstructible ℓ E X.hom d) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (Etale.tateSheafPow (integersModPowCoeff.{u} ℓ E m) X.left d) :=
  etaleReductionIntegralTateTwistIso ℓ E m X d ≪≫ Etale.tateObjectNatIsoSingleFunctor _ _ d

/-- The product `red_m(𝒪_{E,X}(1)) ⊗ᴸ red_m(𝒪_{E,X}(d)) ≅ red_m(𝒪_{E,X}(d + 1))` of the
reductions of the integral Tate twists, read in degree zero: the product
`Λ_X(1)^{⊗ 1} ⊗ Λ_X(1)^{⊗ d} ≅ Λ_X(1)^{⊗ (d + 1)}` of sheaves
(`Etale.tateSheafPowOneTensorIso`). -/
noncomputable def etaleReductionIntegralTateTwistMulIso (d : ℕ) :
    (etaleReduction ℓ E m X).obj (integralTateTwistBoundedConstructible ℓ E X.hom 1) ⊗
        (etaleReduction ℓ E m X).obj (integralTateTwistBoundedConstructible ℓ E X.hom d) ≅
      (etaleReduction ℓ E m X).obj (integralTateTwistBoundedConstructible ℓ E X.hom (d + 1)) :=
  tensorIso (etaleReductionIntegralTateTwistSingleIso ℓ E X m 1)
      (etaleReductionIntegralTateTwistSingleIso ℓ E X m d) ≪≫
    Etale.singleFunctorObjTensorIso _ _ (Etale.flat_tateSheafPow _ X.left 1) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (Etale.tateSheafPowOneTensorIso _ X.left d) ≪≫
    (etaleReductionIntegralTateTwistSingleIso ℓ E X m (d + 1)).symm

/-- Through `red_m(𝒪_{E,X}(d)) ≅ Λ_X(d)`, the product of the reductions of the integral Tate
twists is the product of the Tate twists. -/
lemma etaleReductionIntegralTateTwistMulIso_hom (d : ℕ) :
    (etaleReductionIntegralTateTwistMulIso ℓ E X m d).hom =
      ((etaleReductionIntegralTateTwistIso ℓ E m X 1).hom ⊗ₘ
          (etaleReductionIntegralTateTwistIso ℓ E m X d).hom) ≫
        ((Etale.tateTwistIntTensorFamily (integersModPowCoeff.{u} ℓ E m) X.left).step d).hom ≫
          (etaleReductionIntegralTateTwistIso ℓ E m X (d + 1)).inv := by
  simp only [etaleReductionIntegralTateTwistMulIso, etaleReductionIntegralTateTwistSingleIso,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, tensorIso_hom, Functor.mapIso_hom,
    ← tensorHom_comp_tensorHom, Category.assoc]
  erw [← Etale.tateTwistIntTensorFamily_step_hom_comp_tateObjectNatIsoSingleFunctor_hom_assoc]
  rw [Iso.hom_inv_id_assoc]

end Level

variable (n : ℕ) [NeZero (ringChar (integersModPowCoeff.{u} ℓ E (n + 1)))]
  [NeZero (ringChar (integersModPowCoeff.{u} ℓ E n))]
  [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E (n + 1)) X.left]
  [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E n) X.left]

/-- **`β` is compatible with the products of the reductions of the integral Tate twists**: the
reduction `β : Ψ(red_{n+1} -) ≅ red_n -` carries the product
`red_{n+1}(𝒪_{E,X}(1)) ⊗ᴸ red_{n+1}(𝒪_{E,X}(d)) ≅ red_{n+1}(𝒪_{E,X}(d + 1))` to the product
for `red_n`, through the monoidal structure of `Ψ`. Everything is in degree zero: the integral
Tate twists are flat. -/
@[reassoc]
lemma map_etaleReductionIntegralTateTwistMulIso_hom_comp (d : ℕ) :
    letI := Etale.derivedExtendScalarsMonoidal (integersModPowCoeffTransition_surjective ℓ E n)
      (ker_integersModPowCoeffTransition ℓ E n) X.left
    (integersModPowDerivedExtendScalars ℓ E n X.left).map
        (etaleReductionIntegralTateTwistMulIso ℓ E X (n + 1) d).hom ≫
      (etaleReductionExtendScalarsIsoApp ℓ E n X _).hom =
    δ (integersModPowDerivedExtendScalars ℓ E n X.left) _ _ ≫
      ((etaleReductionExtendScalarsIsoApp ℓ E n X _).hom ⊗ₘ
        (etaleReductionExtendScalarsIsoApp ℓ E n X _).hom) ≫
        (etaleReductionIntegralTateTwistMulIso ℓ E X n d).hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
