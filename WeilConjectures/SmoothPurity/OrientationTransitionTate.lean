/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionTateTwist
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReduction
public import WeilConjectures.SmoothPurity.OrientationTransitionTateStep
public import WeilConjectures.SmoothPurity.OrientationTransitionTateZero
public import WeilConjectures.SmoothPurity.OrientationTransitionUpperShriek
public import WeilConjectures.TateTwist.IntegralReduction

/-!
# The reduction of the integral Tate twists under the reduction of coefficients

Let `Ψ` be the derived extension of scalars along `Λ = 𝒪_E ⧸ ℓⁿ⁺¹ ⟶ Λ' = 𝒪_E ⧸ ℓⁿ` and
`β : Ψ(red_{n+1} -) ≅ red_n -` (`ProEtale.CondensedRing.etaleReductionExtendScalarsIsoApp`).
Through the identifications `ιₘ : red_m(𝒪_{E,X}(d)) ≅ Λ_m(d)`
(`ProEtale.CondensedRing.etaleReductionIntegralTateTwistIso`), `β` induces isomorphisms
`Ψ(Λ_X(d)) ≅ Λ'_X(d)` (`ProEtale.CondensedRing.integersModPowReductionTateTwistIso`). This file
shows that they are the canonical reductions of the Tate twists
(`Etale.reductionTateTwistIso`, the multiplicative extension of the `ℓ`-th power map on the roots
of unity): `ProEtale.CondensedRing.integersModPowReductionTateTwistIso_eq`. Both families agree
in degree zero and one and satisfy the same recursion in `d`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

-- the instances used in the definitions of the Tate twist families
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [NeZero (ringChar (integersModPowCoeff.{u} ℓ E (n + 1)))]
  [NeZero (ringChar (integersModPowCoeff.{u} ℓ E n))]
  [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E (n + 1)) X.left]
  [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E n) X.left]

/-- The canonical reduction `Ψ(Λ_X(m)) ≅ Λ'_X(m)` of the Tate twists along
`𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ` (`Etale.reductionTateTwistIso`, for the `ℓ`-th power map on the roots
of unity). -/
noncomputable abbrev integersModPowCanonicalTateTwistIso (m : ℤ) :=
  Etale.reductionTateTwistIso (integersModPowCoeffTransition_surjective ℓ E n)
    (ker_integersModPowCoeffTransition ℓ E n) ℓ (ringChar_integersModPowCoeff_succ ℓ E n) X.left m

/-- The reduction `Ψ(Λ_X(d)) ≅ Λ'_X(d)` of the Tate twists induced by the reduction of the
integral Tate twist: `Ψ(Λ_X(d)) ≅ Ψ(red_{n+1} 𝒪_{E,X}(d)) ≅ red_n 𝒪_{E,X}(d) ≅ Λ'_X(d)`, through
`etaleReductionIntegralTateTwistIso` and `β`. -/
noncomputable def integersModPowReductionTateTwistIso (d : ℕ) :
    (integersModPowDerivedExtendScalars ℓ E n X.left).obj
        (Etale.tateObject (integersModPowCoeff.{u} ℓ E (n + 1)) X.left d) ≅
      Etale.tateObject (integersModPowCoeff.{u} ℓ E n) X.left d :=
  ((integersModPowDerivedExtendScalars ℓ E n X.left).mapIso
      (etaleReductionIntegralTateTwistIso ℓ E (n + 1) X d)).symm ≪≫
    etaleReductionExtendScalarsIsoApp ℓ E n X _ ≪≫ etaleReductionIntegralTateTwistIso ℓ E n X d

/-- In degree zero, the reduction of the integral Tate twist is, through `Λ(0) ≅ Λ`, the unit
comparison of `Ψ`. -/
lemma integersModPowReductionTateTwistIso_zero :
    letI := Etale.derivedExtendScalarsMonoidal (integersModPowCoeffTransition_surjective ℓ E n)
      (ker_integersModPowCoeffTransition ℓ E n) X.left
    (integersModPowReductionTateTwistIso ℓ E n X 0).hom ≫
        (Etale.HasTateTwist.twistObjectZeroIso (Λ := integersModPowCoeff.{u} ℓ E n) X.left).hom =
      (integersModPowDerivedExtendScalars ℓ E n X.left).map
          (Etale.HasTateTwist.twistObjectZeroIso
            (Λ := integersModPowCoeff.{u} ℓ E (n + 1)) X.left).hom ≫
        Functor.OplaxMonoidal.η (integersModPowDerivedExtendScalars ℓ E n X.left) := by
  let _ := Etale.derivedExtendScalarsMonoidal (integersModPowCoeffTransition_surjective ℓ E n)
    (ker_integersModPowCoeffTransition ℓ E n) X.left
  have hβ := (etaleReductionExtendScalarsIso ℓ E n X).hom.naturality
    (integralTateTwistBoundedConstructibleNatZeroIso ℓ E X).hom
  rw [Functor.comp_map, etaleReductionExtendScalarsIso_hom_app_eq,
    etaleReductionExtendScalarsIso_hom_app_eq] at hβ
  rw [integersModPowReductionTateTwistIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Category.assoc, Category.assoc,
    etaleReductionIntegralTateTwistIso_zero_hom_comp_twistObjectZeroIso_hom, ← reassoc_of% hβ,
    ← map_etaleReductionUnitIso_hom_comp_constantComplexIso,
    Etale.derivedExtendScalarsConstantComplexIso_hom_eq_η,
    (Iso.eq_inv_comp _).mpr
      (etaleReductionIntegralTateTwistIso_zero_hom_comp_twistObjectZeroIso_hom ℓ E X (n + 1)),
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]

/-- **The degree-one case in restriction form**: the transpose under `Ψ ⊣ Res` of
`β : Ψ(red_{n+1} 𝒪_{E,X}(1)) ≅ red_n 𝒪_{E,X}(1)`, followed by `red_n 𝒪_{E,X}(1) ≅ Λ'_X(1)`, is
`red_{n+1} 𝒪_{E,X}(1) ≅ Λ_X(1)` followed by the change of coefficients `Λ_X(1) ⟶ Res Λ'_X(1)`
of the Tate twists (the `ℓ`-th power map `μ_{ℓⁿ⁺¹} ⟶ μ_{ℓⁿ}`). -/
lemma unit_app_comp_map_etaleReductionExtendScalarsIsoApp_hom_comp_tateTwistObjectOneChangeMap :
    (Etale.derivedExtendScalarsAdjunction (integersModPowCoeffTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n) X.left).unit.app
        ((etaleReduction ℓ E (n + 1) X).obj (integralTateTwistBoundedConstructible ℓ E X.hom 1)) ≫
      (Sheaf.derivedRestrictScalars X.left.smallEtaleTopology
        (integersModPowCoeffTransition ℓ E n)).map
          ((etaleReductionExtendScalarsIsoApp ℓ E n X _).hom ≫
            (etaleReductionIntegralTateTwistIso ℓ E n X 1).hom) =
    (etaleReductionIntegralTateTwistIso ℓ E (n + 1) X 1).hom ≫
      Etale.tateTwistObjectOneChangeMap (integersModPowCoeffTransition ℓ E n) X.left ℓ
        (ringChar_integersModPowCoeff_succ ℓ E n) := by
  sorry

/-- **In degree one**, the reduction of the integral Tate twist is the canonical
`Ψ(Λ_X(1)) ≅ Λ'_X(1)`, adjoint to the `ℓ`-th power map `μ_{ℓⁿ⁺¹} ⟶ μ_{ℓⁿ}`. -/
lemma integersModPowReductionTateTwistIso_one :
    integersModPowReductionTateTwistIso ℓ E n X 1 =
      Etale.reductionTateTwistOneIso (integersModPowCoeffTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n) ℓ (ringChar_integersModPowCoeff_succ ℓ E n)
        X.left := by
  refine Iso.ext ((Equiv.eq_symm_apply _).mpr ?_)
  refine (Adjunction.homEquiv_unit _ _ _ _).trans ?_
  rw [integersModPowReductionTateTwistIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, CategoryTheory.Functor.map_comp]
  erw [← (Etale.derivedExtendScalarsAdjunction (integersModPowCoeffTransition_surjective ℓ E n)
    (ker_integersModPowCoeffTransition ℓ E n) X.left).unit.naturality_assoc]
  rw [Functor.id_map,
    unit_app_comp_map_etaleReductionExtendScalarsIsoApp_hom_comp_tateTwistObjectOneChangeMap,
    Iso.inv_hom_id_assoc]

/-- The reduction of the integral Tate twists satisfies the recursion of the multiplicative
extension of its degree-one part (`IntTensorFamily.iso_step`): it is compatible with the
multiplications `Λ_X(1) ⊗ᴸ Λ_X(d) ≅ Λ_X(d + 1)`, through the monoidal structure of `Ψ`. -/
lemma integersModPowReductionTateTwistIso_step (d : ℕ) :
    letI := Etale.derivedExtendScalarsMonoidal (integersModPowCoeffTransition_surjective ℓ E n)
      (ker_integersModPowCoeffTransition ℓ E n) X.left
    (((Etale.tateTwistIntTensorFamily (integersModPowCoeff.{u} ℓ E (n + 1)) X.left).map
        (integersModPowDerivedExtendScalars ℓ E n X.left)).step d).hom ≫
        (integersModPowReductionTateTwistIso ℓ E n X (d + 1)).hom =
      ((integersModPowReductionTateTwistIso ℓ E n X 1).hom ⊗ₘ
          (integersModPowReductionTateTwistIso ℓ E n X d).hom) ≫
        ((Etale.tateTwistIntTensorFamily (integersModPowCoeff.{u} ℓ E n) X.left).step d).hom := by
  let _ := Etale.derivedExtendScalarsMonoidal (integersModPowCoeffTransition_surjective ℓ E n)
    (ker_integersModPowCoeffTransition ℓ E n) X.left
  have hs : ((Etale.tateTwistIntTensorFamily (integersModPowCoeff.{u} ℓ E (n + 1)) X.left).step
      d).hom = ((etaleReductionIntegralTateTwistIso ℓ E (n + 1) X 1).inv ⊗ₘ
        (etaleReductionIntegralTateTwistIso ℓ E (n + 1) X d).inv) ≫
      (etaleReductionIntegralTateTwistMulIso ℓ E X (n + 1) d).hom ≫
        (etaleReductionIntegralTateTwistIso ℓ E (n + 1) X (d + 1)).hom := by
    rw [etaleReductionIntegralTateTwistMulIso_hom]
    simp [tensorHom_comp_tensorHom_assoc]
  rw [IntTensorFamily.map_step_hom, Category.assoc, IsIso.inv_comp_eq, hs]
  simp only [integersModPowReductionTateTwistIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc _ (etaleReductionIntegralTateTwistIso ℓ E (n + 1) X (d + 1)).hom,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    map_etaleReductionIntegralTateTwistMulIso_hom_comp_assoc]
  erw [← Functor.OplaxMonoidal.δ_natural_assoc]
  rw [etaleReductionIntegralTateTwistMulIso_hom]
  simp [tensorHom_comp_tensorHom_assoc]
  rfl

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The reduction of the integral Tate twists is the canonical reduction of the Tate twists**: the
isomorphism `Ψ(Λ_X(d)) ≅ Λ'_X(d)` induced by `β` and `etaleReductionIntegralTateTwistIso` is
`Etale.reductionTateTwistIso`. Both agree in degree zero and one, and satisfy the same recursion. -/
theorem integersModPowReductionTateTwistIso_eq (d : ℕ) :
    integersModPowReductionTateTwistIso ℓ E n X d =
      integersModPowCanonicalTateTwistIso ℓ E n X d := by
  let _ := Etale.derivedExtendScalarsMonoidal (integersModPowCoeffTransition_surjective ℓ E n)
    (ker_integersModPowCoeffTransition ℓ E n) X.left
  induction d with
  | zero =>
    refine Iso.ext ?_
    rw [← cancel_mono (Etale.HasTateTwist.twistObjectZeroIso
      (Λ := integersModPowCoeff.{u} ℓ E n) X.left).hom,
      integersModPowReductionTateTwistIso_zero]
    exact (Etale.reductionTateTwistIso_zero _ _ _ _ _).symm
  | succ d ih =>
    refine Iso.ext ?_
    rw [← cancel_epi (((Etale.tateTwistIntTensorFamily (integersModPowCoeff.{u} ℓ E (n + 1))
      X.left).map (integersModPowDerivedExtendScalars ℓ E n X.left)).step d).hom,
      integersModPowReductionTateTwistIso_step, ih, integersModPowReductionTateTwistIso_one]
    exact (IntTensorFamily.iso_step ((Etale.tateTwistIntTensorFamily
      (integersModPowCoeff.{u} ℓ E (n + 1)) X.left).map
        (integersModPowDerivedExtendScalars ℓ E n X.left))
      (Etale.tateTwistIntTensorFamily (integersModPowCoeff.{u} ℓ E n) X.left)
      (Etale.reductionTateTwistOneIso (integersModPowCoeffTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n) ℓ (ringChar_integersModPowCoeff_succ ℓ E n)
        X.left) (d : ℤ)).symm

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The reduction of the integral Tate twist, unshifted**: through `β`, the identifications
`red_m(𝒪_{E,X}(d)) ≅ Λ_m(d)` for `m = n + 1` and `m = n` correspond under the canonical reduction
`Ψ(Λ_X(d)) ≅ Λ'_X(d)` of the Tate twists. -/
theorem map_etaleReductionIntegralTateTwistIso_hom_comp_reductionTateTwistIso_hom (d : ℕ) :
    (integersModPowDerivedExtendScalars ℓ E n X.left).map
        (etaleReductionIntegralTateTwistIso ℓ E (n + 1) X d).hom ≫
      (integersModPowCanonicalTateTwistIso ℓ E n X d).hom =
    (etaleReductionExtendScalarsIsoApp ℓ E n X _).hom ≫
      (etaleReductionIntegralTateTwistIso ℓ E n X d).hom := by
  rw [← integersModPowReductionTateTwistIso_eq, integersModPowReductionTateTwistIso,
    Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, ← Functor.map_comp_assoc,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  exact Category.id_comp _

end AlgebraicGeometry.ProEtale.CondensedRing
