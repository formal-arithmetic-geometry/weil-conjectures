/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportedHomAdjunctionClass
import all WeilConjectures.AlgebraicGeometry.Support.SupportSiteComparison
import all WeilConjectures.AlgebraicGeometry.SupportedConstantNormalization.SupportedConstantExchangeNormalization
import all WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedExteriorProduct
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedHomPullback

/-! # The injective cocycle formula for the supported adjunction comparison

Source: latest blueprint, `lem-pur-supported-hom.proof.md`, derived closed adjunction
(blueprint: lem-pur-supported-hom-pair-adjunction-cocycle).
-/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem supportedHomPair_cycleClass_compat
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    [∀ n : ℤ, Injective (I.obj.X n)] (a : ℤ)
    (s : ((proEtaleSupportHomPair P i).complex I).cycles a) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) a).map
        ((ProEtale.supportSections i P.Coefficient).rightDerivedFunctorPlusCompatibility.hom.app
          (DerivedCategory.Plus.Q.obj I))
        ((proEtaleSupportHomPair P i).cycleClass I a s) =
      ProEtale.supportedHomCycleClass P.Coefficient i I a s := by
  let E := ProEtale.supportSections i P.Coefficient
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) a
  have hc := ProEtale.compatibility_fac E ((HomotopyCategory.Plus.quotient _).obj I)
  have hh :
      (Sheaf.supportSequenceModelIso (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} P.Coefficient) E I
        (DerivedCategory.Plus.Q.obj I) (Iso.refl _) a).hom ≫
          H.map (E.rightDerivedFunctorPlusCompatibility.hom.app
            (DerivedCategory.Plus.Q.obj I)) =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} P.Coefficient) a).inv.app
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj) ≫
        H.map (ProEtale.supportedHomDerivedUnit P.Coefficient i I.obj) := by
    simp only [Sheaf.supportSequenceModelIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, asIso_hom, Iso.refl_hom, Functor.comp_map,
      Category.assoc]
    erw [E.rightDerivedFunctorPlus.map_id,
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) a).map_id,
      Category.id_comp]
    change (DerivedCategory.Plus.homologyFunctorObjQIso
        (E.mapCochainComplexPlus.obj I) a).inv ≫
        H.map (DerivedCategory.Plus.ι.map (E.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient _).obj I))) ≫
        H.map (E.rightDerivedFunctorPlusCompatibility.hom.app
          (DerivedCategory.Plus.Q.obj I)) = _
    rw [← H.map_comp]
    erw [hc]
    simp only [DerivedCategory.Plus.homologyFunctorObjQIso, Iso.trans_inv, Iso.app_inv]
    erw [DerivedCategory.homologyFunctorFactorsh_inv_app_quotient_obj]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app_assoc]
    change _ = _ ≫ H.map (_ ≫ _)
    rw [H.map_comp]
    rfl
  exact ConcreteCategory.congr_hom hh (((proEtaleSupportHomPair P i).complex I).homologyπ a s)

private theorem supportedHomPair_adjoint_evaluation
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
    (f : (proEtaleSupportHomPair P i).supported ⟶ F) :
    (constantSheafAdj (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)
        (Scheme.ProEt.isTerminalMkId X)).homEquiv _ _
        ((proEtaleSupportHomPair P i).constantRestriction ≫ f) =
      (ProEtale.supportedCoefficientAdjunction P.Coefficient i).homEquiv _ _
          ((supportedHomPairCoefficientIso P i).inv ≫ f) ≫
        kernel.ι (F.obj.map (proEtaleSupportHomPair P i).restriction.op) := by
  let A := ModuleCat.of P.Coefficient P.Coefficient
  let ax := constantSheafΓAdj (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)
  let aT := constantSheafAdj (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)
    (Scheme.ProEt.isTerminalMkId X)
  let e := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} P.Coefficient) (Scheme.ProEt.isTerminalMkId X)
  let g := (ProEtale.supportedCoefficientAdjunction P.Coefficient i).homEquiv _ _
    ((supportedHomPairCoefficientIso P i).inv ≫ f)
  have hn := (ProEtale.exists_unique_supportedCoefficientAdjunction
    P.Coefficient i).choose_spec.1 A F g
  change ProEtale.supportedCoefficientQuotient P.Coefficient i A ≫
      ((ProEtale.supportedCoefficientAdjunction P.Coefficient i).homEquiv _ _).symm g =
    (ax.homEquiv _ _).symm (g ≫ (ProEtale.supportedModuleSectionsι P.Coefficient i).app F)
      at hn
  dsimp only [g] at hn
  rw [Equiv.symm_apply_apply] at hn
  have hq : ProEtale.supportedCoefficientQuotient P.Coefficient i A =
      (proEtaleSupportHomPair P i).constantRestriction ≫
        (supportedHomPairCoefficientIso P i).hom := by
    change (SupportedConstantNormalization.adj P.Coefficient true i).homEquiv _ _
        (SupportedConstantNormalization.unitIso P.Coefficient true i).hom = _
    rw [SupportedConstantNormalization.pro_unit_adjunct]
    exact (supportHomProEtaleSupportedIso_spec P i).symm
  rw [hq, Category.assoc, Iso.hom_inv_id_assoc] at hn
  have hg := congrArg (ax.homEquiv _ _) hn
  rw [Equiv.apply_symm_apply] at hg
  have ht (v : (constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient)).obj A ⟶ F) :
      aT.homEquiv _ _ v = ax.homEquiv _ _ v ≫ e.hom.app F := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    rw [Category.assoc, e.hom.naturality, ← Category.assoc]
    change aT.unit.app A ≫ _ =
      (ax.unit.app A ≫ (ax.rightAdjointUniq aT).hom.app _) ≫ _
    rw [Adjunction.unit_rightAdjointUniq_hom_app]
  change aT.homEquiv _ _ _ = g ≫ _
  rw [ht, hg]
  change (g ≫ (ProEtale.supportedModuleSectionsToSections P.Coefficient i).app F ≫
    e.inv.app F) ≫ e.hom.app F = g ≫ _
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rfl

/-- The unbounded supported-adjunction normalization, expressed on the actual pair's
supported injective cocycles and its bounded-below derived-unit model.
Source: Milne, Etale Cohomology, Theorem 9.4 and Example 9.5; the supported-Hom
identification in `lem-pur-gysin-structure.proof.md`
(blueprint: lem-pur-supported-hom-pair-adjunction-cocycle).

Proof:
1. Write d for lowerStar.mapIso(comparisonUpperStarUnitIso). The cocycle with ordinary
   constant source is d.inv followed by f. Its differential is zero because f is a
   cocycle. The pair's constant restriction followed by d.hom is the ordinary
   supported constant restriction: its inverse comparison cancels d.hom.
2. The ordinary supported-adjunction quotient normalization identifies the adjoint
   of d.inv followed by f, evaluated on one, with the supported section in the
   hypothesis. Verify this after the kernel inclusion, which is monic. The
   constant-sheaf/global-section adjunction and terminal-evaluation comparison give
   precisely the pair's displayed evaluation, with no coefficient automorphism.
3. The D+/unbounded derived compatibility satisfies the derived-unit equation.
   Apply H^a and the homology-of-localization comparisons. This takes the published
   bounded-below cycleClass to supportedHomCycleClass of the same cycle.
4. Apply the assumed unbounded cocycle normalization to d.inv followed by f. Its
   right side is the localized Hom cocycle with that generic source. Precomposition
   by single(d.hom) changes this to the localized cocycle of f: naturality of the
   single comparison and Cocycle.fromSingleMk_precomp give the formula, and the
   hom/inverse of d cancel. All maps use the same cochain shift, so there is no
   extra sign. The calculation includes zero cycles and empty support. -/
theorem supportedHomPairAdjunctionCocycle
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (a : ℤ)
    (χ : ProEtale.supportedHomCohomologyFunctor P.Coefficient i a ≅
      ProEtale.supportedHomMorphismFunctor P.Coefficient i a)
    (hχ : ProEtale.SupportedHomEvaluationNormalization P.Coefficient i a χ)
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    [∀ n : ℤ, Injective (I.obj.X n)]
    (f : (proEtaleSupportHomPair P i).supported ⟶ I.obj.X a)
    (hf : f ≫ I.obj.d a (a + 1) = 0)
    (s : ((proEtaleSupportHomPair P i).complex I).cycles a)
    (hs : kernel.ι ((I.obj.X a).obj.map (proEtaleSupportHomPair P i).restriction.op)
        (((proEtaleSupportHomPair P i).complex I).iCycles a s) =
      ((constantSheafAdj (proEtaleSupportHomPair P i).topology
        (ModuleCat.{u + 1} P.Coefficient) (proEtaleSupportHomPair P i).isTerminal).homEquiv _ _
          ((proEtaleSupportHomPair P i).constantRestriction ≫ f)) 1) :
    (DerivedCategory.singleFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) 0).map
        (supportedHomPairCoefficientIso P i).hom ≫
      χ.hom.app (DerivedCategory.Plus.Q.obj I)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) a).map
          ((ProEtale.supportSections i P.Coefficient).rightDerivedFunctorPlusCompatibility.hom.app
            (DerivedCategory.Plus.Q.obj I))
          ((proEtaleSupportHomPair P i).cycleClass I a s)) =
      (proEtaleSupportHomPair P i).cocycleMorphism I a f hf := by
  let d := supportedHomPairCoefficientIso P i
  let g := d.inv ≫ f
  have hg : g ≫ I.obj.d a (a + 1) = 0 := by
    dsimp only [g]
    rw [Category.assoc, hf, comp_zero]
  have heval := supportedHomPair_adjoint_evaluation P i (I.obj.X a) f
  have hs' : ((proEtaleSupportHomPair P i).complex I).iCycles a s =
      ((ProEtale.supportedCoefficientAdjunction P.Coefficient i).homEquiv _ _ g) 1 := by
    apply (ModuleCat.mono_iff_injective
      (kernel.ι ((I.obj.X a).obj.map (proEtaleSupportHomPair P i).restriction.op))).mp
        inferInstance
    exact hs.trans (ConcreteCategory.congr_hom heval (1 : P.Coefficient))
  rw [supportedHomPair_cycleClass_compat]
  rw [hχ I inferInstance g hg s hs']
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  rw [← supportedHomLocalizedCocycle_eq]
  change (DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) 0).map d.hom ≫
    supportedHomLocalizedCocycle I.obj a g hg ≫
      ((DerivedCategory.quotientCompQhIso _).inv.app I.obj)⟦a⟧' =
    supportedHomLocalizedCocycle I.obj a f hf ≫
      ((DerivedCategory.quotientCompQhIso _).hom.app I.obj)⟦a⟧'
  have hp := supportHomCocycle_precomp d.inv I.obj a f hf hg
  rw [hp]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl


end AlgebraicGeometry
