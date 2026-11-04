/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerDefs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerEtaleArbitraryBase
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerComparisonTransport
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerCoefficientComparison

/-! # Relative Kummer maps over an arbitrary base

Source: blueprint latest, relative Kummer proof, Steps 1 and 2 and the comparison
paragraph (blueprint: lem-pur-relative-kummer-arbitrary-base-maps).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting


attribute [local instance] coefficientNeZero

/-- Transport of `Hⁿ` of the untwisted relative unit from the étale unit. -/
theorem isIso_homology_map_relativeUnit_false (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (n : ℤ)
    (he : IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) f).unit.app
        ((DerivedCategory.singleFunctor _ 0).obj (P.constantEtale Y))))) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map (P.relativeUnit h f false)) := by
  have key := ProEtale.isIso_homology_map_homEquiv_comparison P.Coefficient f (P.constantEtale Y)
    (P.constantEtale X)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) f).hom.app
      (ModuleCat.of P.Coefficient P.Coefficient)) n (by
        rw [Adjunction.homEquiv_unit, Functor.map_comp]
        infer_instance)
  rw [relativeUnit, ← Adjunction.homEquiv_unit]
  exact key

theorem isIso_homology_map_relativeUnit_true (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (hr : IsUnit (P.exponent : Γ(Y, ⊤))) (n : ℤ)
    (he : IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) f).unit.app
        ((DerivedCategory.singleFunctor _ 0).obj (P.twistEtale h Y))))) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map (P.relativeUnit h f true)) := by
  have := P.isIso_twistEtalePullback h f hr
  have key := ProEtale.isIso_homology_map_homEquiv_comparison P.Coefficient f (P.twistEtale h Y)
    (P.twistEtale h X) (P.twistEtalePullback h f) n (by
        rw [Adjunction.homEquiv_unit, Functor.map_comp]
        infer_instance)
  rw [relativeUnit, ← Adjunction.homEquiv_unit]
  exact key

/-- The Kummer generator is invertible as soon as `H⁰` of the adjoint of the coordinate class
is. -/
theorem isIso_kummerGenerator_of_isIso_homology (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (B : Scheme.{u})
    (a : B ⟶ Spec (CommRingCat.of P.field.k))
    (hK : IsIso ((DerivedCategory.homologyFunctor _ 0).map
      ((ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
        (puncturedProjection B)).homEquiv _ _
          (P.derivedCoefficientPullback h (puncturedProjection B) false ≫
            (P.coordinateKummer h B a).hom)))) :
    IsIso (P.kummerGenerator h B a) := by
  unfold kummerGenerator
  rw [Functor.map_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (@IsIso.comp_isIso _ _ _ _ _ _ _
    (@IsIso.comp_isIso _ _ _ _ _ _ _ hK inferInstance) inferInstance)

/-- The five specified relative maps over an arbitrary k-scheme. No finiteness,
separatedness or geometric-point assumption is made on B. Affine higher vanishing is
omitted here: it follows formally from the affine unit isomorphism.
Source: blueprint latest, sk-lem-sp-reduction/prop-pur-gm-relative-kummer.proof.md,
Steps 1 and 2 and the comparison paragraph
(blueprint: lem-pur-relative-kummer-arbitrary-base-maps).

Proof: write r=ell^N, choose a primitive r-th root in k, and normalize the finite
coefficient and root-line maps. The absolute Kummer computation gives the normalized
constant isomorphisms in degree zero, the coordinate generator in degree one, and
vanishing in the other positive degrees on the two absolute curves. Identify the
actual affine line with the polynomial model and its basic open with the Laurent
model, preserving projections and the coordinate unit. For every geometric point of
B let S be its strict localization. Apply strict-local derived invariance to the
smooth curve C over k and the affine morphism S to Spec k. The normalized-stalk
comparison carries the relative unit to the absolute constant map and the relative
edge of the coordinate boundary to the absolute Kummer generator. Conservative
etale stalks detect the two affine unit isomorphisms, the punctured degree-zero unit,
the punctured degree-one generator and all the stated higher vanishings. Both actual
projections are affine and hence qcqs over arbitrary B. Apply the exact etale-to-
pro-etale comparison, normalized on the actual units and scalar Kummer class; its
unit and edge identities identify the transported maps with precisely the displayed
maps. Thus the five conclusions hold without imposing finite type on B. -/
theorem relative_kummer_arbitrary_base_maps (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (B : Scheme.{u})
    (a : B ⟶ Spec (CommRingCat.of P.field.k)) :
    IsIso (P.relativeUnit h (lineProjection B) false) ∧
    IsIso (P.relativeUnit h (lineProjection B) true) ∧
    IsIso ((DerivedCategory.homologyFunctor _ 0).map
      (P.relativeUnit h (puncturedProjection B) true)) ∧
    IsIso (P.kummerGenerator h B a) ∧
    (∀ (q : ℕ), 2 ≤ q → IsZero
      ((DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection B)).rightDerivedFunctor.obj
            (P.derivedSheaf h (Punctured B) true)))) := by
  have : HasInvertibleExponent P.Coefficient B := P.coefficientHasInvertibleExponent B a
  have : HasInvertibleExponent P.Coefficient (Punctured B) :=
    P.coefficientHasInvertibleExponent _ (puncturedProjection B ≫ a)
  have hrB := P.exponent_isUnit B a
  have hrU := P.exponent_isUnit (Punctured B) (puncturedProjection B ≫ a)
  have : QuasiCompact (puncturedProjection B) := by
    unfold puncturedProjection lineProjection openImmersion
    infer_instance
  have : QuasiSeparated (puncturedProjection B) := by
    unfold puncturedProjection lineProjection openImmersion
    infer_instance
  have : QuasiCompact (lineProjection B) := by
    unfold lineProjection
    infer_instance
  have : QuasiSeparated (lineProjection B) := by
    unfold lineProjection
    infer_instance
  obtain ⟨e₁B, e₂B, -⟩ := exists_kummerEtale_hom_eq P h B hrB 1
  obtain ⟨e₁U, e₂U, hx⟩ := exists_kummerEtale_hom_eq P h (Punctured B) hrU (coordinateUnit B)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [DerivedCategory.isIso_iff]
    intro n
    refine isIso_homology_map_relativeUnit_false P h _ n ?_
    have hE : IsIso ((Etale.derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) (lineProjection B)).unit.app
          (Etale.constantComplex P.Coefficient B)) :=
      Etale.isIso_unit_constantComplex_affineLine_of_hasInvertibleExponent P.Coefficient B
    have := (NatTrans.isIso_app_iff_of_iso _ e₁B).2 hE
    infer_instance
  · rw [DerivedCategory.isIso_iff]
    intro n
    refine isIso_homology_map_relativeUnit_true P h _ hrB n ?_
    have hE : IsIso ((Etale.derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) (lineProjection B)).unit.app
          (Etale.tateObject P.Coefficient B 1)) :=
      Etale.isIso_unit_tateObject_affineLine_of_strictlyHenselian P.Coefficient B
    have := (NatTrans.isIso_app_iff_of_iso _ e₂B).1 hE
    infer_instance
  · refine isIso_homology_map_relativeUnit_true P h _ hrB 0 ?_
    have hE : IsIso ((DerivedCategory.homologyFunctor _ 0).map
        ((Etale.derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} P.Coefficient) (puncturedProjection B)).unit.app
            (Etale.tateObject P.Coefficient B 1))) :=
      Etale.isIso_homology_zero_unit_tateObject_multiplicativeGroup_of_hasInvertibleExponent
        P.Coefficient B
    exact (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight
      (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
        (puncturedProjection B)).unit (DerivedCategory.homologyFunctor _ 0)) e₂B).1 hE
  · refine isIso_kummerGenerator_of_isIso_homology P h B a ?_
    let φc := (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient)
      (puncturedProjection B)).hom.app (ModuleCat.of P.Coefficient P.Coefficient)
    have key := ProEtale.isIso_homology_map_homEquiv_ext_comparison P.Coefficient
      (puncturedProjection B) (P.constantEtale B) (P.constantEtale (Punctured B))
      (P.twistEtale h (Punctured B)) φc (P.kummerEtale h (Punctured B) hrU (coordinateUnit B))
      0 ?_
    · rw [derivedCoefficientPullback, Category.assoc]
      exact key
    let γ := (Etale.singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} P.Coefficient)
        (puncturedProjection B)).hom.app (P.constantEtale B) ≫
      (DerivedCategory.singleFunctor _ 0).map φc
    have : IsIso γ := inferInstance
    let β := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (puncturedProjection B)).leftDerivedFunctor.mapIso e₁B.symm ≪≫ asIso γ ≪≫ e₁U
    have hC4 := Etale.isIso_homology_zero_homEquiv_kummerClass_of_hasInvertibleExponent
      P.Coefficient B β
    rw [hx]
    have e3 : (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
        (puncturedProjection B)).homEquiv _ _
          (γ ≫ e₁U.hom ≫ Etale.kummerClass P.Coefficient (coordinateUnit B) ≫
            e₂U.hom⟦(1 : ℤ)⟧') =
        e₁B.hom ≫ (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection B)).homEquiv _ _
            (β.hom ≫ Etale.kummerClass P.Coefficient (coordinateUnit B)) ≫
          (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} P.Coefficient)
            (puncturedProjection B)).map (e₂U.hom⟦(1 : ℤ)⟧') := by
      simp only [β, Adjunction.homEquiv_unit, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        asIso_hom, Functor.map_comp, Category.assoc, Adjunction.unit_naturality_assoc,
        Iso.hom_inv_id_assoc]
      rfl
    have e5 := congrArg (DerivedCategory.homologyFunctor _ 0).map e3
    rw [Functor.map_comp, Functor.map_comp] at e5
    simp only [γ, Category.assoc] at e5
    exact (congrArg IsIso e5).mpr (@IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
      (@IsIso.comp_isIso _ _ _ _ _ _ _ hC4 inferInstance))
  · intro q hq
    refine ProEtale.isZero_homology_rightDerived_comparison P.Coefficient (puncturedProjection B)
      (P.twistEtale h (Punctured B)) q ?_
    exact (Etale.isZero_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup_of_hasInvertibleExponent
      P.Coefficient B q (by omega) (by omega)).of_iso
        ((DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
          ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} P.Coefficient)
            (puncturedProjection B)).mapIso e₂U.symm))


end WeilConjectures.PurityFiniteSetting
