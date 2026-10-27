/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.Paper.FiniteSmoothGammaNormalization
import Sheaf.AlgebraicGeometry.SfEtaleUnitTensorArbitraryBase
import all Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphTensorCore
import all Sheaf.AlgebraicGeometry.UnboundedProperOpenComposition
import all Sheaf.AlgebraicGeometry.SmoothTensorDuality
import all WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality

/-! # The tensor mate in etale unit coordinates

Source: blueprint sec-smooth-purity/sk-thm-smooth-purity, tensor mate formula
(blueprint: lem-pur-finite-smooth-omega-tensor-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

attribute [local irreducible] upperStar lowerStar etaleLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  leftDerivedUpperStarIsoMapDerivedCategory

private theorem normalizedComparison_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (C : FiniteSmoothCompactSupportComparisons A)
    (hC : FiniteSmoothComparisonNormalized A C)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f]
    (c : Compactification f) :
    (C f c).inv = compactificationEtaleComparison A f c := by
  obtain ⟨a, ha⟩ := hC
  let N := canonicalEtaleCompactSupportNormalization A
  have he : a f c = N.sheafComparison f c := by
    apply NatTrans.ext
    funext M
    have : Mono ((openImmersionLowerShriekToLowerStar
        (ModuleCat.{u + 1} A) c.i).app M) := open_compare_mono A c.i M
    have : Mono ((compactificationSheafToDirectImage A c).app M) := by
      dsimp only [compactificationSheafToDirectImage, NatTrans.comp_app,
        Functor.whiskerRight_app]
      have : Mono ((lowerStar (ModuleCat.{u + 1} A) c.g).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M)) :=
          Functor.map_mono _ _
      exact mono_comp
        ((lowerStar (ModuleCat.{u + 1} A) c.g).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M))
        ((lowerStarComp.{u + 2, u} (ModuleCat.{u + 1} A) c.i c.g f c.comm).app M).hom
    apply (cancel_mono ((compactificationSheafToDirectImage A c).app M)).1
    exact ((ha f c).1 M).trans (N.sheaf_normalization f c M).symm
  have hd : (C f c).inv = (N.comparison f c).inv := by
    apply Localization.natTrans_ext DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
        (.up ℤ))
    intro P
    rw [(ha f c).2 P, N.derived_normalization f c P, he]
  exact hd.trans (normalizedComparison_eq_source A N f c)

private theorem rightAdjointUniq_ofNatIsoLeft
    {C D : Type*} [Category C] [Category D]
    {F S : C ⥤ D} {G E : D ⥤ C} (adj : F ⊣ G) (sa : S ⊣ E) (s : F ≅ S) :
    (adj.rightAdjointUniq (sa.ofNatIsoLeft s.symm)).hom =
      conjugateEquiv adj sa s.inv := by
  ext K
  simp only [Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom,
    conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app, Iso.refl_hom, NatTrans.id_app, Iso.symm_hom, Category.assoc]
  simp

private theorem adjointCoordinates_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (C : FiniteSmoothCompactSupportComparisons A)
    (hC : FiniteSmoothComparisonNormalized A C)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f] [HasCompactification f] :
    (finiteSmoothAdjointCoordinates A C f).hom ≫
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom =
      sfEtaleRightAdjointComparison A f (HasCompactification.compactification f)
        (rightDerivedUpperShriek (ModuleCat.{u + 1} A) f)
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f) := by
  have hs : (finiteSmoothSumComparison A C f).inv =
      compactificationEtaleComparison A f (HasCompactification.compactification f) := by
    unfold finiteSmoothSumComparison rightDerivedLowerShriekIso
    rw [(unboundedEtaleCompactSupport_comparison_coherence A f).1]
    simpa only [Iso.trans_inv, Iso.symm_inv, Iso.refl_hom, Category.comp_id] using
      normalizedComparison_eq A C hC f (HasCompactification.compactification f)
  simp only [finiteSmoothAdjointCoordinates, Iso.trans_hom, Iso.symm_hom,
    rightAdjointUniq_ofNatIsoLeft, hs, sfEtaleRightAdjointComparison,
    derivedEtaleLowerShriekMapAdjunction, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rfl

private theorem tensorNormalizationTransport
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    {P E : D ⥤ C} (i : P ≅ E) (K : D) (ω Z : C)
    (θ : ω ⊗ P.obj K ⟶ Z) (r : Z ⟶ P.obj K) (η : ω ⟶ 𝟙_ C)
    (h : (ω ◁ i.inv.app K) ≫ θ ≫ r ≫ i.hom.app K =
      (η ▷ E.obj K) ≫ (λ_ (E.obj K)).hom) :
    θ ≫ r = (η ▷ P.obj K) ≫ (λ_ (P.obj K)).hom := by
  apply (cancel_mono (i.hom.app K)).mp
  apply (cancel_epi (ω ◁ i.inv.app K)).mp
  simp only [Category.assoc]
  rw [h]
  rw [whisker_exchange_assoc, leftUnitor_naturality_assoc]
  simp only [Iso.inv_hom_id_app, Category.comp_id]

private theorem orientedTensorMate
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    (P ω Z : C) (θ : ω ⊗ P ⟶ Z) (r : Z ≅ P) (η : ω ≅ 𝟙_ C)
    (h : θ ≫ r.hom = (η.hom ▷ P) ≫ (λ_ P).hom) :
    (ρ_ P).inv ≫ (P ◁ η.inv) ≫ (β_ P ω).hom ≫ θ = r.inv := by
  apply (cancel_mono r.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id]
  rw [h, BraidedCategory.braiding_naturality_right_assoc]
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id,
    id_whiskerRight, Category.id_comp]
  rw [braiding_leftUnitor, Iso.inv_hom_id]

/-- The tensor mate at the graph-normalized coefficient-unit orientation.
Source: blueprint sec-smooth-purity/sk-thm-smooth-purity, displayed tensor mate;
lem-pur-finite-smooth-gamma-normalization, proof steps 8--9
(blueprint: lem-pur-finite-smooth-omega-tensor-coordinates).

Proof: the sheaf comparison in FiniteSmoothComparisonNormalized is uniquely fixed
by its composite to direct image: the graph extension is monic and its restriction
on each sheet is the identity. Its homotopy normalization then fixes the derived
comparison by the localization universal property. Thus its adjoint coordinates
are those of the graph sum/evaluation adjunction. In these coordinates the
projection map sends a sheet section tensored with a coefficient section to their
pullback tensor on that sheet. The inverse projection followed by the counit at
the unit and the right unitor is therefore evaluation. Sum extension preserves
flat and K-flat complexes, so this calculation descends to every unbounded K.
The adjunction Hom bijection identifies its transpose with the inverse right-adjoint
comparison. This is precisely finiteSmoothGammaMap at finiteSmoothOmegaCoordinates.
The argument uses arbitrary finite coefficients directly, so is independent of
any universe lift of a residue ring. Empty sheets and zero coefficients give zero
objects with their identity morphisms, hence require no nonemptiness assumption. -/
theorem finiteSmoothOmegaTensorCoordinates
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f] [Etale f]
    (C : FiniteSmoothCompactSupportComparisons A)
    (hC : FiniteSmoothComparisonNormalized A C)
    (K : DerivedCategoryModule A Y) :
    finiteSmoothGammaMap A f (finiteSmoothOmegaCoordinates A C f) K =
      (finiteSmoothAdjointCoordinates A C f).inv.app K := by
  let c := HasCompactification.compactification f
  let G := rightDerivedUpperShriek (ModuleCat.{u + 1} A) f
  let adj := rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f
  let i := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f
  let r := finiteSmoothAdjointCoordinates A C f
  let η := finiteSmoothOmegaCoordinates A C f
  let θ := sfEtaleAmbientTensorMap A c G adj K
  have hr : r.hom ≫ i.hom = sfEtaleRightAdjointComparison A f c G adj :=
    adjointCoordinates_eq A C hC f
  have hη : sfEtaleRightAdjointUnit A f c G adj = η.hom := by
    dsimp only [sfEtaleRightAdjointUnit]
    rw [← hr]
    simp only [NatTrans.comp_app, etaleSumPullbackUnitIso, Iso.trans_hom,
      Iso.app_hom, Iso.symm_hom, Category.assoc, i, constantComplex,
      Iso.hom_inv_id_app_assoc, η, finiteSmoothOmegaCoordinates, r]
  have hn := (sfEtaleUnitTensorArbitraryBase A f c G adj).2.2.1 K
  rw [← hr, hη] at hn
  have ht : θ ≫ r.hom.app K =
      (η.hom ▷ ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) ≫
        (λ_ ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).hom := by
    apply tensorNormalizationTransport i K (dualizingComplex (ModuleCat.{u + 1} A) f)
      (G.obj K) θ (r.hom.app K) η.hom
    simpa only [sfEtaleExactAmbientTensorMap, NatTrans.comp_app,
      derivedTensor_map_app, derivedTensor_obj_map, derivedTensorLeftUnitor,
      i, θ, G, constantComplex, dualizingComplex, Category.assoc] using hn
  let := derivedBraidedCategory (ModuleCat.{u + 1} A) X
  have hs : smoothTensorDualityMap (ModuleCat.{u + 1} A) f
      (isIso_projectionMap_of_finite A f) K =
        (β_ ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)
          (dualizingComplex (ModuleCat.{u + 1} A) f)).hom ≫ θ := by
    rw [smoothTensorDualityMap_eq]
    rw [show θ = dualizingComplexTensorMap A f K from ambientTensorMap_eq A f K]
    rfl
  dsimp only [finiteSmoothGammaMap]
  rw [hs]
  simpa only [derivedTensorRightUnitor, derivedTensor_obj_map, G, constantComplex,
    dualizingComplex, η, r, Iso.app_inv, Category.assoc] using
    orientedTensorMate _ _ _ θ (r.app K) η ht

end AlgebraicGeometry.Etale.FiniteSmoothPurity
