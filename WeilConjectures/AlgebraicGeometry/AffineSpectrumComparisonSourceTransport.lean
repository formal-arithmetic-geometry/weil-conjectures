/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.AlgebraicGeometry.AffineSpectrumCompositionCounitSquare
import WeilConjectures.AlgebraicGeometry.AffineSpectrumOrdinaryComparisonSquare

/-! # Affine spectrum transport before the coefficient morphism

Source: Stacks Project, Tags 0DJ8, 0098 and 0D5S.
(blueprint: lem-pc-affine-spectrum-comparison-source-transport).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

private theorem transport_representatives
    {C₁ C₂ D₁ D₂ A₀ : Type*}
    [Category C₁] [Category C₂] [Category D₁] [Category D₂] [Category A₀]
    (L : C₁ ⥤ D₁) (L0 : C₂ ⥤ D₂) (J : C₁ ⥤ C₂) (J' : D₁ ⥤ D₂)
    (H : D₁ ⥤ A₀) (H0 : D₂ ⥤ A₀)
    (T : H ≅ J' ⋙ H0) (c : J ⋙ L0 ≅ L ⋙ J')
    {P K : C₁} {Q : C₂} {U V : A₀}
    (e : P ≅ K) (e0 : Q ≅ J.obj K) (d : Q ≅ J.obj P)
    (q : U ⟶ H.obj (L.obj P)) (q0 : V ⟶ H0.obj (L0.obj Q))
    (l0 : U ≅ V) (a : Q ≅ Q) (b : V ≅ V)
    (ha : a.hom ≫ d.hom ≫ J.map e.hom = e0.hom)
    (hb : b.hom ≫ q0 = q0 ≫ H0.map (L0.map a.hom))
    (h : l0.hom ≫ q0 ≫ H0.map (L0.map d.hom) =
      q ≫ T.hom.app (L.obj P) ≫ H0.map (c.inv.app P)) :
    (l0 ≪≫ b.symm).hom ≫ q0 ≫ H0.map (L0.map e0.hom) =
      q ≫ H.map (L.map e.hom) ≫ T.hom.app (L.obj K) ≫ H0.map (c.inv.app K) := by
  have hb' : b.inv ≫ q0 ≫ H0.map (L0.map a.hom) = q0 := by
    apply (cancel_epi b.hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hb.symm
  have hn : b.inv ≫ q0 ≫ H0.map (L0.map e0.hom) =
      q0 ≫ H0.map (L0.map d.hom) ≫ H0.map (L0.map (J.map e.hom)) := by
    rw [← ha]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun k ↦ k ≫ H0.map (L0.map d.hom) ≫
        H0.map (L0.map (J.map e.hom))) hb'
  have hc := congrArg (fun k ↦ H0.map k) (c.inv.naturality e.hom)
  simp only [Functor.comp_map, Functor.map_comp] at hc
  have ht := T.hom.naturality (L.map e.hom)
  simp only [Functor.comp_map] at ht
  have hh := congrArg (fun k ↦ k ≫ H0.map (L0.map (J.map e.hom))) h
  have hc' := congrArg (fun k ↦ q ≫ T.hom.app (L.obj P) ≫ k) hc.symm
  have ht' := congrArg (fun k ↦ q ≫ k ≫ H0.map (c.inv.app K)) ht.symm
  calc
    _ = l0.hom ≫ q0 ≫ H0.map (L0.map d.hom) ≫
        H0.map (L0.map (J.map e.hom)) := by
      simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using
        congrArg (fun k ↦ l0.hom ≫ k) hn
    _ = q ≫ T.hom.app (L.obj P) ≫ H0.map (c.inv.app P) ≫
        H0.map (L0.map (J.map e.hom)) := by
      simpa only [Category.assoc] using hh
    _ = q ≫ T.hom.app (L.obj P) ≫ H0.map (J'.map (L.map e.hom)) ≫
        H0.map (c.inv.app K) := by simpa only [Category.assoc] using hc'
    _ = _ := by simpa only [Category.assoc] using ht'


set_option linter.unusedVariables false in
-- The quantified proof hypotheses occur only in the proof, not in the conclusion.
set_option maxHeartbeats 1600000 in
-- Elaborating the stalk tensor-model instances and their scalar extensions needs this budget.
/-- Transport the localized tensor comparison into derived pullback, independently
of any coefficient morphism or target representative.

Proof: use isoPullbackStalkCohomologyIso along X'.isoSpec.inv for T.
This is a concrete natural isomorphism obtained from restriction-stalks,
exact homology factors and the invertible universal pullback counit.
Apply exists_affineSpectrum_canonicalComparison_square to P and Q with the
canonical isomorphism d from the spectrum pullback counit. For arbitrary e
and e0, put a = e0 followed by pullback of e inverse followed by d inverse.
This is an automorphism of the derived object represented by Q. The theorem
exists_comparisonSourceIso lifts a to a tensor-algebra source automorphism;
comparisonIntoPullback_naturality gives its commuting square. Extend scalars
and forget to obtain b on the additive source. Set l = l0 followed by b inverse.
The identity a;d;J(e)=e0 and cancellation of b first replace the canonical
target identification by e0. Naturality of T and of the specified inverse
composition comparison then give the displayed equation with e. The private
transport_representatives lemma proves this categorical diagram calculation.
No localized comparison is required to be invertible. Empty schemes, zero
complexes and rings, arbitrary degrees and unbounded complexes are covered.
Source: Stacks Project, Tag 0DJ8, equation-bc and affine reduction;
Tag 0098, lemma-stalk-pullback; Tag 0D5S, lemma-pullback-composition.
(blueprint: lem-pc-affine-spectrum-comparison-source-transport). -/
theorem exists_affineSpectrum_comparisonIntoPullback_transport
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤)) (i : ℤ) :
    let z := X'.isoSpec.inv z0
    let H := comparisonStalkCohomology X' z i
    let H0 := comparisonStalkCohomology (Spec Γ(X', ⊤)) z0 i
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
      AddCommGrpCat.{u}
    ∃ T : H ⋙ F ≅ derivedPullback X'.isoSpec.inv ⋙ H0 ⋙ F0,
      ∀ (K : schemeDerivedCategory X)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
        (Q : CochainComplex
          (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace)) ℤ)
        (hP : P.IsKFlatTensor) (hQ : Q.IsKFlatTensor)
        (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
        (hcQ : IsIso ((counit (Spec.map g'.appTop)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
        (e : DerivedCategory.Q.obj P ≅ K)
        (e0 : DerivedCategory.Q.obj Q ≅ affineSpectrumDerivedObject X K)
        (hQ0 : Q = ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
          (.up ℤ)).obj P),
      ∃ l : F.obj (Arrow.mk (comparisonIntoPullback f f' g g' sq z P hcP i)).left ≅
          F0.obj (Arrow.mk
            (comparisonIntoPullback (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 Q hcQ i)).left,
        l.hom ≫ F0.map
          (comparisonIntoPullback (Spec.map f.appTop) (Spec.map f'.appTop)
            (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 Q hcQ i ≫
              H0.map ((derivedPullback (Spec.map g'.appTop)).map e0.hom)) =
        F.map (comparisonIntoPullback f f' g g' sq z P hcP i ≫
          H.map ((derivedPullback g').map e.hom)) ≫
            T.hom.app ((derivedPullback g').obj K) ≫
              F0.map (H0.map ((affineSpectrumDerivedPullbackIso g').inv.app K)) := by
  -- Reconstruct the canonical square locally from the surviving composition equations.
  have affineSpectrum_composition_counit_square
      [∀ Y : Scheme.{u},
        HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
      {X X' : Scheme.{u}} [IsAffine X] [IsAffine X']
      (g' : X' ⟶ X)
      (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
      let a : Scheme.Modules.tensorPullback X.isoSpec.inv ⋙
          Scheme.Modules.tensorPullback (Spec.map g'.appTop) ≅
          Scheme.Modules.tensorPullback g' ⋙ Scheme.Modules.tensorPullback X'.isoSpec.inv :=
        (Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
          ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
        Scheme.Modules.tensorPullbackCompositionIso X'.isoSpec.inv g'
          ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm
      (derivedPullback (Spec.map g'.appTop)).map
          ((counit X.isoSpec.inv).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (counit (Spec.map g'.appTop)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
              (.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).hom.app P) =
      (affineSpectrumDerivedPullbackIso g').hom.app (DerivedCategory.Q.obj P) ≫
        (derivedPullback X'.isoSpec.inv).map
          ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (counit X'.isoSpec.inv).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)) := by
    let b₁ := Scheme.Modules.tensorPullbackCompositionIso
      (Spec.map g'.appTop) X.isoSpec.inv ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl
    let b₂ := Scheme.Modules.tensorPullbackCompositionIso
      X'.isoSpec.inv g' ((Spec.map g'.appTop) ≫ X.isoSpec.inv)
      (Scheme.isoSpec_inv_naturality g').symm
    let c₁ := selectedComposition.{u, w} (Spec.map g'.appTop) X.isoSpec.inv
    let c₂ := selectedComposition.{u, w} X'.isoSpec.inv g' ≪≫
      (eqToIso (congrArg (fun k ↦ derivedPullback.{u, w} k)
        (Scheme.isoSpec_inv_naturality g'))).symm
    have h₁ := composition_factorization (Spec.map g'.appTop) X.isoSpec.inv P
    have h₂ := composition_factorization_transport X'.isoSpec.inv g'
      ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm P
    erw [eqToIso_congr_symm (fun k ↦ derivedPullback.{u, w} k)
      (Scheme.isoSpec_inv_naturality g')] at h₂
    have h := compare_counit_factorizations
      (c₁.app (DerivedCategory.Q.obj P)) (c₂.app (DerivedCategory.Q.obj P))
      (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex b₁ (.up ℤ)).app P))
      (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex b₂ (.up ℤ)).app P))
      ((counit ((Spec.map g'.appTop) ≫ X.isoSpec.inv)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) _ _ h₁ h₂
    dsimp only
    have he : affineSpectrumDerivedPullbackIso g' = c₁ ≪≫ c₂.symm := by
      dsimp only [affineSpectrumDerivedPullbackIso, c₁, c₂, selectedComposition]
      simp only [Iso.trans_symm, Iso.symm_symm_eq]
    conv_rhs => rw [he]
    simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      NatIso.mapHomologicalComplex,
      NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app, Functor.map_comp,
      Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc] using h

  have affineSpectrum_counit_square
      [∀ Y : Scheme.{u},
        HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
      {X X' : Scheme.{u}} [IsAffine X] [IsAffine X'] (g' : X' ⟶ X)
      (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (hP : P.IsKFlatTensor)
      (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
      (hcQ : IsIso ((counit (Spec.map g'.appTop)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
            (.up ℤ)).obj P)))) :
      let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
      let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj P
      (derivedPullback X'.isoSpec.inv).map
          (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) ≫
        (affineSpectrumDerivedPullbackIso g').inv.app (DerivedCategory.Q.obj P) =
      (isoPullbackComplexCounitIso X'.isoSpec.inv).hom.app Pg ≫
        DerivedCategory.Q.map (affineSpectrumTensorComplexIso g' P).inv ≫
        inv ((counit (Spec.map g'.appTop)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P0)) ≫
        (derivedPullback (Spec.map g'.appTop)).map
          ((isoPullbackComplexCounitIso X.isoSpec.inv).inv.app P) := by
    have _hFlat := hP
    let := hcP
    let := hcQ
    dsimp only
    have h := affineSpectrum_composition_counit_square g' P
    change (derivedPullback (Spec.map g'.appTop)).map
        ((counit X.isoSpec.inv).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (counit (Spec.map g'.appTop)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
            (.up ℤ)).obj P)) ≫
      DerivedCategory.Q.map (affineSpectrumTensorComplexIso g' P).hom = _ at h
    have hj : (isoPullbackComplexCounitIso X.isoSpec.inv).hom.app P =
        (counit X.isoSpec.inv).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
      simp only [isoPullbackComplexCounitIso, DerivedCategory.quotientCompQhIso,
        Functor.mapHomotopyCategoryFactors, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
        Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Iso.symm_hom, asIso_hom, Functor.comp_obj]
      erw [(derivedPullback X.isoSpec.inv).map_id, DerivedCategory.Qh.map_id]
      erw [Category.id_comp, Category.comp_id, Category.comp_id]
    have hj' : (isoPullbackComplexCounitIso X'.isoSpec.inv).hom.app
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) =
        (counit X'.isoSpec.inv).app ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)) := by
      simp only [isoPullbackComplexCounitIso, DerivedCategory.quotientCompQhIso,
        Functor.mapHomotopyCategoryFactors, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
        Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Iso.symm_hom, asIso_hom, Functor.comp_obj]
      erw [(derivedPullback X'.isoSpec.inv).map_id, DerivedCategory.Qh.map_id]
      erw [Category.id_comp, Category.comp_id, Category.comp_id]
    rw [← hj, ← hj'] at h
    let e := (derivedPullback (Spec.map g'.appTop)).mapIso
      ((isoPullbackComplexCounitIso X.isoSpec.inv).app P)
    let c := asIso ((counit (Spec.map g'.appTop)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex (.up ℤ)).obj P)))
    let a := DerivedCategory.Q.mapIso (affineSpectrumTensorComplexIso g' P)
    let d := (affineSpectrumDerivedPullbackIso g').app (DerivedCategory.Q.obj P)
    let b := (derivedPullback X'.isoSpec.inv).mapIso (asIso
      ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    let f := (isoPullbackComplexCounitIso X'.isoSpec.inv).app
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
    change b.inv ≫ d.inv = f.hom ≫ a.inv ≫ c.inv ≫ e.inv
    change e.hom ≫ c.hom ≫ a.hom = d.hom ≫ b.hom ≫ f.hom at h
    apply (cancel_mono (d.hom ≫ b.hom ≫ f.hom)).1
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← h]
    simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

  have comparisonIntoPullback_eq
      [∀ Y : Scheme.{u},
        HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
      {X X' S S' : Scheme.{u}}
      (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
      (sq : IsPullback g' f' f g) (z : X')
      (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (hc : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
      (i : ℤ) :
      comparisonIntoPullback f f' g g' sq z P hc i =
        comparisonIntoTensorPullback f f' g g' sq z P i ≫
          (comparisonStalkCohomology X' z i).map
            (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) := by
    simp only [comparisonIntoPullback, comparisonIntoTensorPullback, Category.assoc]

  have exists_affineSpectrum_canonicalComparison_square
      [∀ Y : Scheme.{u},
        HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
      {X X' S S' : Scheme.{u}}
      (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
      (sq : IsPullback g' f' f g)
      [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
      (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
        (Spec.map f.appTop) (Spec.map g.appTop))
      (z0 : Spec Γ(X', ⊤)) (i : ℤ)
      (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (Q : CochainComplex
        (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace)) ℤ)
      (hP : P.IsKFlatTensor) (hQ : Q.IsKFlatTensor)
      (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
      (hcQ : IsIso ((counit (Spec.map g'.appTop)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
      (hQ0 : Q = ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj P) :
      let z := X'.isoSpec.inv z0
      let H0 := comparisonStalkCohomology (Spec Γ(X', ⊤)) z0 i
      let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
      let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
        AddCommGrpCat.{u}
      let d : DerivedCategory.Q.obj Q ≅
          affineSpectrumDerivedObject X (DerivedCategory.Q.obj P) :=
        eqToIso (congrArg (fun W ↦ DerivedCategory.Q.obj W) hQ0) ≪≫
          (isoPullbackComplexCounitIso X.isoSpec.inv).symm.app P
        ∃ l : F.obj (Arrow.mk (comparisonIntoPullback f f' g g' sq z P hcP i)).left ≅
            F0.obj (Arrow.mk
              (comparisonIntoPullback (Spec.map f.appTop) (Spec.map f'.appTop)
                (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 Q hcQ i)).left,
          l.hom ≫ F0.map
            (comparisonIntoPullback (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 Q hcQ i ≫
                H0.map ((derivedPullback (Spec.map g'.appTop)).map d.hom)) =
          F.map (comparisonIntoPullback f f' g g' sq z P hcP i) ≫
              (isoPullbackStalkCohomologyIso X'.isoSpec.inv z0 i).hom.app
                ((derivedPullback g').obj (DerivedCategory.Q.obj P)) ≫
                F0.map (H0.map ((affineSpectrumDerivedPullbackIso g').inv.app
                  (DerivedCategory.Q.obj P))) := by
    subst Q
    dsimp only
    let := hcP
    let := hcQ
    let z := X'.isoSpec.inv z0
    let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
    let H0 := comparisonStalkCohomology (Spec Γ(X', ⊤)) z0 i
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
      AddCommGrpCat.{u}
    let T := isoPullbackStalkCohomologyIso X'.isoSpec.inv z0 i
    obtain ⟨l, hl⟩ := exists_affineSpectrum_ordinaryComparison_square
      f f' g g' sq sq0 z0 i P
    refine ⟨l, ?_⟩
    have hn := T.hom.naturality
      (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    have hc := affineSpectrum_counit_square g' P hP hcP hcQ
    have hcH := congrArg (fun k ↦ F0.map (H0.map k)) hc
    simp only [Functor.map_comp] at hcH
    simp only [Functor.comp_map] at hn
    let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj P
    let c0 := F0.map (H0.map (inv ((counit (Spec.map g'.appTop)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P0))))
    let d0 := F0.map (H0.map ((derivedPullback (Spec.map g'.appTop)).map
      ((isoPullbackComplexCounitIso X.isoSpec.inv).inv.app P)))
    let b := F.map (comparisonIntoTensorPullback f f' g g' sq z P i)
    let a0 := F0.map (H0.map ((affineSpectrumDerivedPullbackIso g').inv.app
      (DerivedCategory.Q.obj P)))
    have hL := congrArg (fun k ↦ k ≫ c0 ≫ d0) hl
    have hC := congrArg (fun k ↦ b ≫ T.hom.app (DerivedCategory.Q.obj Pg) ≫ k) hcH
    have hN := congrArg (fun k ↦ b ≫ k ≫ a0) hn
    simp only [Functor.map_comp, Category.assoc] at hL hC hN
    have hh := hL.trans (hC.symm.trans hN.symm)
    simp only [comparisonIntoPullback_eq, Functor.map_comp, Category.assoc,
      eqToIso_refl, Iso.trans_hom, Iso.refl_hom, Iso.app_hom, Iso.symm_hom,
      Category.id_comp, c0, d0, b, a0, P0, T, F, F0, H0, z] at hh ⊢
    convert hh using 1 <;> rfl
  dsimp only
  let T := isoPullbackStalkCohomologyIso X'.isoSpec.inv z0 i
  refine ⟨T, ?_⟩
  intro K P Q hP hQ hcP hcQ e e0 hQ0
  let z := X'.isoSpec.inv z0
  let H := comparisonStalkCohomology X' z i
  let H0 := comparisonStalkCohomology (Spec Γ(X', ⊤)) z0 i
  let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
  let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
    AddCommGrpCat.{u}
  let j := X.isoSpec.inv
  let g0 := Spec.map g'.appTop
  let f0 := Spec.map f.appTop
  let f0' := Spec.map f'.appTop
  let s0 := Spec.map g.appTop
  let d : DerivedCategory.Q.obj Q ≅ affineSpectrumDerivedObject X
      (DerivedCategory.Q.obj P) :=
    eqToIso (congrArg (fun W ↦ DerivedCategory.Q.obj W) hQ0) ≪≫
      (isoPullbackComplexCounitIso j).symm.app P
  obtain ⟨l0, hl0⟩ := exists_affineSpectrum_canonicalComparison_square
    f f' g g' sq sq0 z0 i P Q hP hQ hcP hcQ hQ0
  change DerivedCategory.Q.obj Q ≅ (derivedPullback j).obj K at e0
  change DerivedCategory.Q.obj Q ≅ (derivedPullback j).obj (DerivedCategory.Q.obj P) at d
  let a : DerivedCategory.Q.obj Q ≅ DerivedCategory.Q.obj Q :=
    e0 ≪≫ (derivedPullback j).mapIso e.symm ≪≫ d.symm
  let := leftAlgebra f0 g0 z0
  let := rightAlgebra f0 f0' s0 g0 sq0 z0
  let := (tensorMap f0 f0' s0 g0 sq0 z0).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (R f0 g0 z0))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f0' z0))
  obtain ⟨c, hc, _⟩ := exists_comparisonSourceIso f0 f0' s0 g0 sq0 z0 Q Q a i
  let E := ModuleCat.extendScalars.{u, u, u}
    (algebraMap (TensorProduct (R f0 g0 z0) (A g0 z0) (B f0' z0)) (C z0))
  let b := F0.mapIso (E.mapIso c)
  have hn := comparisonIntoPullback_naturality f0 f0' s0 g0 sq0 z0
    Q Q hQ hQ hcQ hcQ a i c hc
  have ha : a.hom ≫ d.hom ≫ (derivedPullback j).map e.hom = e0.hom := by
    simp only [a, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp, Iso.inv_hom_id]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hb := congrArg (fun k ↦ F0.map k) hn.symm
  simp only [Functor.map_comp] at hb
  change l0.hom ≫ F0.map
      (comparisonIntoPullback f0 f0' s0 g0 sq0 z0 Q hcQ i ≫
        H0.map ((derivedPullback g0).map d.hom)) =
    F.map (comparisonIntoPullback f f' g g' sq z P hcP i) ≫
        T.hom.app ((derivedPullback g').obj (DerivedCategory.Q.obj P)) ≫
          F0.map (H0.map ((affineSpectrumDerivedPullbackIso g').inv.app
            (DerivedCategory.Q.obj P))) at hl0
  simp only [Functor.map_comp] at hl0
  refine ⟨l0 ≪≫ b.symm, ?_⟩
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
    transport_representatives (derivedPullback g') (derivedPullback g0)
      (derivedPullback j) (derivedPullback X'.isoSpec.inv) (H ⋙ F) (H0 ⋙ F0)
      T (affineSpectrumDerivedPullbackIso g') e e0 d
      (F.map (comparisonIntoPullback f f' g g' sq z P hcP i))
      (F0.map (comparisonIntoPullback f0 f0' s0 g0 sq0 z0 Q hcQ i))
      l0 a b ha hb hl0

end AlgebraicGeometry.SingleComplexBaseChange
