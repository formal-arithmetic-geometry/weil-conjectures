/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrientationFiniteReductionTwists
public import WeilConjectures.AlgebraicGeometry.FiniteTateSiteDescent

/-! Canonical finite quotient and realization of the completed root lines.
Source: def-coefficient-twists-detailed (blueprint: def-sf-orientation-finite-line-comparisons). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

private theorem fixedRoot_scalar_fac
    (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≫
      ((constantCommuteCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
          (CommRingCat.of (ULift.{u + 1} A))).hom =
      ProEtale.finiteCoefficientIntrinsicScalarMap X A := by
  let J := ProEt.topology X
  let U := forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  let i := (constantCommuteCompose J U).app (CommRingCat.of (ULift.{u + 1} A))
  have hf : ProEtale.finiteCoefficientIntrinsicScalarMap X A ≫ i.hom.hom =
      toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) := by
    dsimp only [i, Iso.app_hom]
    rw [constantCommuteCompose_hom_app_hom]
    unfold ProEtale.finiteCoefficientIntrinsicScalarMap
    rw [← Category.assoc, sheafComposeIso_inv_fac]
    exact (toSheafify_naturality J
      (Functor.constComp X.ProEtᵒᵖ (CommRingCat.of (ULift.{u + 1} A)) U).hom).symm.trans
        (by rfl)
  change _ ≫ i.inv.hom = _
  rw [← hf, Category.assoc, ObjectProperty.isoHom_inv_id_hom]
  ext W a
  rfl

private theorem fixedRoot_existsUnique
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (m : ℕ)
    (N : SheafOfModules.{u + 1} (integralCoefficientSheaf l E X m)) :
    ∃! c : (sfIntrinsicModuleEquivalence X
      (Padic.coefficientExtensionRing l E (m + 1))).inverse.obj N ≅
        (finiteTateConstantRestriction l E m X).obj N,
      ∀ (W : X.ProEtᵒᵖ)
        (x : ((finiteTateConstantRestriction l E m X).obj N).obj.obj W),
        ((sfIntrinsicModuleEquivalence X
          (Padic.coefficientExtensionRing l E (m + 1))).counitIso.hom.app N).val.app W
          (sfIntrinsicRealizationUnit X (Padic.coefficientExtensionRing l E (m + 1))
            ((sfIntrinsicModuleEquivalence X
              (Padic.coefficientExtensionRing l E (m + 1))).inverse.obj N) W
                (c.inv.hom.app W x)) = x := by
  let A := Padic.coefficientExtensionRing l E (m + 1)
  let e := sfIntrinsicModuleEquivalence X A
  let M := e.inverse.obj N
  let α := ProEtale.finiteCoefficientIntrinsicScalarMap X A
  let P := (ProEtale.finiteCoefficientModulePresheaf X.ProEt
    (ULift.{u + 1} A)).obj M.obj
  let η := (PresheafOfModules.sheafificationAdjunction α).unit.app P
  let g := η ≫ (PresheafOfModules.restrictScalars α).map
    (e.counitIso.hom.app N).val
  let h : M ⟶ (finiteTateConstantRestriction l E m X).obj N :=
    { hom :=
      { app := fun W ↦ ModuleCat.ofHom
          (X := M.obj.obj W) (Y := ((finiteTateConstantRestriction l E m X).obj N).obj.obj W)
          { toFun := fun x ↦ g.app W x
            map_add' := (g.app W).hom.map_add
            map_smul' := by
              intro a x
              change g.app W (a • x) =
                @SMul.smul _ _ (N.val.obj W).isModule.toSMul
                ((((constantCommuteCompose (ProEt.topology X)
                  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
                    (CommRingCat.of (ULift.{u + 1} A))).hom.app W)
                  ((toSheafify (ProEt.topology X)
                    ((Functor.const X.ProEtᵒᵖ).obj
                      (RingCat.of (ULift.{u + 1} A)))).app W a)) (g.app W x)
              have hs := congrArg (fun f ↦ f.app W a) (fixedRoot_scalar_fac X A)
              simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hs
              exact ((g.app W).hom.map_smul a x).trans
                (congrArg (fun b ↦ @SMul.smul _ _ (N.val.obj W).isModule.toSMul
                  b (g.app W x)) hs.symm) }
        naturality := by
          intro W V f
          ext x
          exact PresheafOfModules.naturality_apply g f x } }
  have hη : IsIso η := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    change IsIso (toSheafify (ProEt.topology X) P.presheaf)
    apply isIso_toSheafify
    exact ((sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) AddCommGrpCat.{u + 1})).obj M).property
  have hh : IsIso h := by
    rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
    rw [NatTrans.isIso_iff_isIso_app]
    intro W
    rw [ConcreteCategory.isIso_iff_bijective]
    have : IsIso (e.counitIso.hom.app N).val := by
      change IsIso ((SheafOfModules.forget _).map (e.counitIso.hom.app N))
      infer_instance
    have : IsIso g := by
      dsimp only [g]
      infer_instance
    exact ConcreteCategory.bijective_of_isIso ((PresheafOfModules.evaluation _ W).map g)
  refine ⟨asIso h, ?_, ?_⟩
  · intro W x
    change h.hom.app W ((asIso h).inv.hom.app W x) = x
    exact ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.app W) (asIso h).inv_hom_id) x
  · intro c hc
    apply Iso.symm_bijective.injective
    apply Iso.ext
    apply (cancel_mono h).mp
    have hc' : c.inv ≫ h = 𝟙 _ := by
      apply Sheaf.hom_ext
      ext W x
      exact hc W x
    exact hc'.trans (asIso h).inv_hom_id.symm


/-- The fixed-scalar inverse realization of a finite root power is its explicit
constant-scalar restriction. The equation fixes it on every local section through
the published scalar-unit section and equivalence counit.
Source: finite coefficient conventions (blueprint: def-sf-orientation-finite-line-comparisons).
Proof: restrict the intrinsic module action along constant scalars. The scalar-unit
map into the canonical intrinsic realization gives a morphism from its realization
to the original intrinsic line. Constant sections locally generate the constant
ring sheaf, so this map is an isomorphism and satisfies the displayed equation.
Transport through the fully faithful equivalence. The equation on all sections,
local generation by scalar-unit sections, and sheaf separatedness prove uniqueness. -/
theorem sfOrientationFixedRootSheaf_existsUnique
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (m d : ℕ) :
    ∃! c : (sfIntrinsicModuleEquivalence X
      (Padic.coefficientExtensionRing l E (m + 1))).inverse.obj
        (finiteCoefficientTwist l E X m (d : ℤ)) ≅ finiteTateProSheaf l E m X d,
      ∀ (W : X.ProEtᵒᵖ) (x : (finiteTateProSheaf l E m X d).obj.obj W),
        ((sfIntrinsicModuleEquivalence X
          (Padic.coefficientExtensionRing l E (m + 1))).counitIso.hom.app
            (finiteCoefficientTwist l E X m (d : ℤ))).val.app W
          (sfIntrinsicRealizationUnit X (Padic.coefficientExtensionRing l E (m + 1))
            ((sfIntrinsicModuleEquivalence X
              (Padic.coefficientExtensionRing l E (m + 1))).inverse.obj
                (finiteCoefficientTwist l E X m (d : ℤ))) W (c.inv.hom.app W x)) = x := by
  exact fixedRoot_existsUnique l E X m (finiteCoefficientTwist l E X m (d : ℤ))

/-- The specified finite ordinary-etale shifted line. This notation only packages
already defined coefficients and ordinary Tate powers.
Source: coefficient conventions (blueprint: def-sf-orientation-finite-line-comparisons). -/
def sfOrientationFiniteEtaleLine
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (m r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E m) = 0) (d : ℕ) :=
  ((DerivedCategory.singleFunctor _ 0).obj
    (finiteEtaleTateTwist X (l ^ (r + 1)) (finiteTateCoefficient l E m) hA d))⟦2 * (d : ℤ)⟧

/-- Realization of the actual finite reduction line. The root comparison is
selected by IsFiniteTateSiteComparison, the quotient comparison by the actual
scalar adjunction, and the intrinsic realization by its scalar-unit counit.
Source: realization and finite reduction conventions
(blueprint: def-sf-orientation-finite-line-comparisons). -/
def sfOrientationFiniteSiteLine
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (hX : IsUnit (l : Γ(X, ⊤)))
    (m r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E m) = 0) (d : ℕ) :
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l E m)) X).mapDerivedCategory.obj
      (sfOrientationFiniteEtaleLine l E X m r hA d) ≅
    (sfIntrinsicDerivedEquivalence X
      (Padic.coefficientExtensionRing l E (m + 1))).inverse.obj
        ((scalarReductionDerivedExtension l E X m).obj
        (DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d))) :=
  let A := finiteTateCoefficient l E m
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X
  let R := (sfIntrinsicModuleEquivalence X
    (Padic.coefficientExtensionRing l E (m + 1))).inverse
  (F.mapDerivedCategory.commShiftIso (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          ((finite_tate_site_descent l E m).choose X hX r hA d)) ≪≫
    ((DerivedCategory.singleFunctors _).shiftIso (2 * (d : ℤ)) (-2 * (d : ℤ)) 0
      (by omega)).app _ ≪≫
    (DerivedCategory.singleFunctor _ (-2 * (d : ℤ))).mapIso
      (sfOrientationFixedRootSheaf_existsUnique l E X m d).exists.choose.symm ≪≫
    ((R.mapDerivedCategorySingleFunctor (-2 * (d : ℤ))).app _).symm ≪≫
    R.mapDerivedCategory.mapIso (sfOrientationFiniteReduction l E X m d).symm

end WeilConjectures
