/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SemilinearSystemModels
import all Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat

/-! # Totalization of an ordinary open tensor comparison

The direct-sum totalization is natural in both complexes and retains its specified
summand formula. Source: Stacks 0GL1 and Homology 012Z
(blueprint: lem-coef-native-open-tensor-totalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections
namespace WeilConjectures.CoefSupportOpenTensor

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall
attribute [local irreducible] SheafOfModules.monoidalCategory

set_option maxHeartbeats 500000 in
-- Comparing the two canonical total-tensor presentations uses colimit-instance elaboration.
/-- Totalize an ordinary natural extension/tensor isomorphism, with its summand equation.
Source: Stacks, sites-cohomology.tex Tag 0GL1 and Homology Tag 012Z.
(blueprint: lem-coef-native-open-tensor-totalization).

Proof: use the existing map-bifunctor totalization of the inverse ordinary
comparison. The left adjoint preserves the coproducts in each total degree;
naturality for the differentials makes the component maps a chain map.
Invert this comparison. Cancel its invertible component in the insertion
identity to obtain the stated summand equation. Invert its simultaneous
naturality square to get naturality of the resulting chain comparison. -/
theorem nativeOpenTensor_totalization_exists
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{max c v r})
    {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C') (R' : Sheaf J' CommRingCat.{max c v r})
    (F : SemilinearSections.Mod.{c, v, max c v r} J' R' ⥤
      SemilinearSections.Mod.{c, v, max c v r} J R)
    (G : SemilinearSections.Mod.{c, v, max c v r} J R ⥤
      SemilinearSections.Mod.{c, v, max c v r} J' R')
    [hF : F.Additive] [hG : G.Additive] (adj : F ⊣ G)
    (ordinary : ∀ (M : SemilinearSections.Mod.{c, v, max c v r} J' R')
      (N : SemilinearSections.Mod.{c, v, max c v r} J R),
      ordinaryTensor.{c, v, r} J R (F.obj M) N ≅
        F.obj (ordinaryTensor.{c, v, r} J' R' M (G.obj N)))
    (hn : ∀ {M M' : SemilinearSections.Mod.{c, v, max c v r} J' R'}
      {N N' : SemilinearSections.Mod.{c, v, max c v r} J R} (f : M ⟶ M') (g : N ⟶ N'),
      ordinaryTensorHom.{c, v, r} J R (F.map f) g ≫ (ordinary M' N').hom =
        (ordinary M N).hom ≫ F.map (ordinaryTensorHom.{c, v, r} J' R' f (G.map g))) :
    ∃ chain : ∀ (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ)
        (Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ),
      (totalTensor.{c, v, r} J R).obj ((F.mapHomologicalComplex (.up ℤ)).obj P, Q) ≅
        (F.mapHomologicalComplex (.up ℤ)).obj ((totalTensor.{c, v, r} J' R').obj
          (P, (G.mapHomologicalComplex (.up ℤ)).obj Q)),
      (∀ P Q (a b k : ℤ) (h : a + b = k),
        tensorSummand.{c, v, r} J R ((F.mapHomologicalComplex (.up ℤ)).obj P) Q a b k h ≫
            (chain P Q).hom.f k =
          (ordinary (P.X a) (Q.X b)).hom ≫
            F.map (tensorSummand.{c, v, r} J' R' P
              ((G.mapHomologicalComplex (.up ℤ)).obj Q) a b k h)) ∧
      (∀ {P P' : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ}
        {Q Q' : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ}
        (f : P ⟶ P') (g : Q ⟶ Q'),
        (totalTensor.{c, v, r} J R).map
            (Prod.mkHom ((F.mapHomologicalComplex (.up ℤ)).map f) g) ≫ (chain P' Q').hom =
          (chain P Q).hom ≫ (F.mapHomologicalComplex (.up ℤ)).map
            ((totalTensor.{c, v, r} J' R').map
              (Prod.mkHom f ((G.mapHomologicalComplex (.up ℤ)).map g)))) := by
  let A := SemilinearSections.Mod.{c, v, max c v r} J' R'
  let B := SemilinearSections.Mod.{c, v, max c v r} J R
  let : MonoidalCategory A := SheafOfModules.cochainModulesMonoidal R'
  let : MonoidalCategory B := SheafOfModules.cochainModulesMonoidal R
  let : MonoidalPreadditive A := SheafOfModules.cochainModulesPreadditive R'
  let : MonoidalPreadditive B := SheafOfModules.cochainModulesPreadditive R
  let : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
  let H := MonoidalCategory.curriedTensor A
  let H' := MonoidalCategory.curriedTensor B
  let : H.PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R'
  let : ∀ M, (H.obj M).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R'
  let : H'.PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let : ∀ M, (H'.obj M).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := SheafOfModules.precompose_preservesZero H G
  let := SheafOfModules.precompose_obj_preservesZero H G
  let : ∀ (P Q : CochainComplex A ℤ),
      HomologicalComplex.HasMapBifunctor P Q H (.up ℤ) :=
    SheafOfModules.ringedOpenHasTotalTensor.{c, v, r} R'
  let : ∀ (P Q : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P Q H' (.up ℤ) :=
    SheafOfModules.ringedOpenHasTotalTensor.{c, v, r} R
  let : ∀ (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P Q
        (H ⋙ (Functor.whiskeringLeft B A A).obj G) (.up ℤ) :=
    SheafOfModules.precompose_hasTotal H G
  obtain ⟨Φ, hi, hnat⟩ := SheafOfModules.comparisonFromComponents_exists F G H H'
    (fun M N ↦ (ordinary M N).symm) (by
      intro M M' N N' f g
      dsimp only [H, H', MonoidalCategory.curriedTensor_map_app,
        MonoidalCategory.curriedTensor_obj_map]
      simpa only [ordinaryTensorHom, ordinaryTensor, SheafOfModules.cochainModulesMonoidal,
        MonoidalCategory.curriedTensor_obj_obj, Iso.symm_hom,
        MonoidalCategory.tensorHom_def, Category.assoc] using
        SheafOfModules.inverse_square _ _ _ _ (hn f g))
    (SheafOfModules.ringedOpenTotalTensor.{c, v, r} R')
    (SheafOfModules.ringedOpenTotalTensor.{c, v, r} R)
    (SheafOfModules.ringedOpenTensorι.{c, v, r} R')
    (SheafOfModules.ringedOpenTensorι.{c, v, r} R)
    (SheafOfModules.ringedOpenTotalTensor_presentation.{c, v, r} R')
    (SheafOfModules.ringedOpenTotalTensor_presentation.{c, v, r} R)
  refine ⟨fun P Q ↦ (Φ P Q).symm, ?_, ?_⟩
  · intro P Q a b k h
    have hi' : F.map (tensorSummand.{c, v, r} J' R' P
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) a b k h) ≫ (Φ P Q).hom.f k =
      (ordinary (P.X a) (Q.X b)).inv ≫
        tensorSummand.{c, v, r} J R ((F.mapHomologicalComplex (.up ℤ)).obj P)
          Q a b k h := hi P Q a b k h
    change tensorSummand.{c, v, r} J R
        ((F.mapHomologicalComplex (.up ℤ)).obj P) Q a b k h ≫ (Φ P Q).inv.f k = _
    apply (cancel_mono ((Φ P Q).hom.f k)).mp
    have he : (Φ P Q).inv.f k ≫ (Φ P Q).hom.f k = 𝟙 _ :=
      congrArg (fun f ↦ f.f k) (Φ P Q).inv_hom_id
    erw [Category.assoc, he, Category.comp_id, Category.assoc, hi',
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · intro P P' Q Q' f g
    have hnat' : (F.mapHomologicalComplex (.up ℤ)).map
        ((totalTensor.{c, v, r} J' R').map
          (Prod.mkHom f ((G.mapHomologicalComplex (.up ℤ)).map g))) ≫ (Φ P' Q').hom =
      (Φ P Q).hom ≫ (totalTensor.{c, v, r} J R).map
        (Prod.mkHom ((F.mapHomologicalComplex (.up ℤ)).map f) g) :=
      hnat P P' Q Q' f g
    exact SheafOfModules.inverse_square _ _ _ _ hnat'


end WeilConjectures.CoefSupportOpenTensor
