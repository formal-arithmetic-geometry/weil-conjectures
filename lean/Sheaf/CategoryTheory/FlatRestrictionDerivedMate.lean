/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.CategoryTheory.FlatRingedDiagramRestrictionComparisonAdjuncts
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Invertibility and normalization of the coefficient derived mate

Source: Stacks Project, Derived Categories, Tags 0FND, 070I, 070K and 070Y.
(blueprint: lem-weil-pbc-flat-restriction-derived-mate).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.FlatRingedDiagramInput

private theorem adjunct_counit
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R) (N : B) :
    a.homEquiv _ _ (a.counit.app N) = 𝟙 (R.obj N) := by
  rw [← a.homEquiv_symm_id N]
  exact Equiv.apply_symm_apply _ _

private theorem adjunct_mate
    {A B E F : Type*} [Category A] [Category B] [Category E] [Category F]
    {LS : A ⥤ B} {FS : B ⥤ A} {LR : E ⥤ F} {FR : F ⥤ E}
    (aS : LS ⊣ FS) (aR : LR ⊣ FR) (rV : A ⥤ E) (rU : B ⥤ F)
    (b : LS ⋙ rU ≅ rV ⋙ LR) (M : A) (N : B) (t : LS.obj M ⟶ N) :
    aR.homEquiv (rV.obj M) (rU.obj N) (b.inv.app M ≫ rU.map t) =
      rV.map (aS.homEquiv M N t) ≫
        (mateEquiv aS aR (TwoSquare.mk _ _ _ _ b.inv)).app N := by
  let d := mateEquiv aS aR (TwoSquare.mk _ _ _ _ b.inv)
  have h := unit_mateEquiv aS aR (TwoSquare.mk _ _ _ _ b.inv) M
  change rV.map (aS.unit.app M) ≫ d.app (LS.obj M) =
    aR.unit.app (rV.obj M) ≫ FR.map (b.inv.app M) at h
  rw [aR.homEquiv_unit, FR.map_comp, ← Category.assoc, ← h, Category.assoc]
  have hd : d.app (LS.obj M) ≫ FR.map (rU.map t) =
      rV.map (FS.map t) ≫ d.app N := d.natTrans.naturality t |>.symm
  rw [hd]
  rw [aS.homEquiv_unit, rV.map_comp, Category.assoc]


private theorem same_adjunction
    {A B : Type*} [Category A] [Category B]
    {L L' : A ⥤ B} {R R' : B ⥤ A}
    (a : L ⊣ R) (a' : L' ⊣ R') (hL : L = L') (hR : R = R')
    (ha : HEq a a') (M : A) (N : B) (f : L'.obj M ⟶ N) :
    a'.homEquiv M N f ≫ eqToHom (congrArg (fun F ↦ F.obj N) hR.symm) =
      a.homEquiv M N (eqToHom (congrArg (fun F ↦ F.obj M) hL) ≫ f) := by
  subst hL
  subst hR
  cases ha
  simp

set_option maxHeartbeats 800000 in
-- The underlying restriction functors require several sheaf coercion comparisons.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinary_adjunct
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J]
    (b0 : x.inverseS J ⋙ x.restrictU J ≅ x.restrictV J ⋙ x.inverseR J)
    (d0 : x.directS J ⋙ x.restrictV J ≅ x.restrictU J ⋙ x.directR J)
    (ordinary : x.OrdinaryComparisonsNormalized J b0 d0)
    (M : x.diagramsSV J) (N : x.diagramsSU J) (f : (x.inverseS J).obj M ⟶ N) :
    (Adjunction.whiskerRight J x.R.adjunction).homEquiv _ _
        (b0.inv.app M ≫ (x.restrictU J).map f) =
      (x.restrictV J).map ((Adjunction.whiskerRight J x.S.adjunction).homEquiv _ _ f) ≫
        d0.hom.app N := by
  apply NatTrans.ext
  refine funext (fun j ↦ ?_)
  apply (SheafOfModules.toSheaf _ ⋙ sheafCompose K (forget AddCommGrpCat)).map_injective
  apply (cancel_mono (x.R.morphism.underlying.hom.app
    (((x.restrictU J).obj N).obj j))).mp
  change (SheafOfModules.toSheaf _ ⋙ sheafCompose K (forget AddCommGrpCat)).map
      (x.R.adjunction.homEquiv _ _
        ((b0.inv.app M).app j ≫ ((x.restrictU J).map f).app j)) ≫ _ = _
  rw [← x.R.transpose]
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [ordinary.2 N j]
  have hs := x.S.transpose (M.obj j) (N.obj j) (f.app j)
  have ht := same_adjunction x.R.morphism.adj x.S.morphism.adj
    x.sameInverse x.sameDirect x.sameAdjunction
    ((SheafOfModules.toSheaf _ ⋙ sheafCompose K (forget AddCommGrpCat)).obj (M.obj j))
    ((SheafOfModules.toSheaf _ ⋙ sheafCompose H (forget AddCommGrpCat)).obj (N.obj j))
    (x.S.inverse.moduleUnderlying.inv.app (M.obj j) ≫
      (SheafOfModules.toSheaf _ ⋙ sheafCompose H (forget AddCommGrpCat)).map (f.app j))
  simp only [← Category.assoc]
  erw [← hs]
  erw [ht]
  apply congrArg (x.R.morphism.adj.homEquiv _ _)
  have hb := eq_of_heq (ordinary.1 M j)
  have hi :
      x.R.inverse.moduleUnderlying.inv.app (((x.restrictV J).obj M).obj j) ≫
        (SheafOfModules.toSheaf _ ⋙ sheafCompose H (forget AddCommGrpCat)).map
          ((b0.inv.app M).app j) =
      eqToHom (congrArg (fun F ↦ F.obj
        ((SheafOfModules.toSheaf _ ⋙ sheafCompose K (forget AddCommGrpCat)).obj
          (M.obj j))) x.sameInverse) ≫
        x.S.inverse.moduleUnderlying.inv.app (M.obj j) := by
    have h := congrArg (fun k ↦
      eqToHom (congrArg (fun F ↦ F.obj
        ((SheafOfModules.toSheaf _ ⋙ sheafCompose K (forget AddCommGrpCat)).obj
          (M.obj j))) x.sameInverse) ≫
      x.S.inverse.moduleUnderlying.inv.app (M.obj j) ≫ k ≫
        (SheafOfModules.toSheaf _ ⋙ sheafCompose H (forget AddCommGrpCat)).map
          ((b0.inv.app M).app j)) hb
    simp only [Category.assoc, ← Functor.map_comp, ← NatTrans.comp_app,
      Functor.map_id,
      Iso.hom_inv_id, NatTrans.id_app,
      Iso.inv_hom_id_app_assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      at h
    erw [Category.comp_id] at h
    exact h.symm
  rw [hi]
  rfl


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem complex_adjunct
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J]
    (b0 : x.inverseS J ⋙ x.restrictU J ≅ x.restrictV J ⋙ x.inverseR J)
    (d0 : x.directS J ⋙ x.restrictV J ≅ x.restrictU J ⋙ x.directR J)
    (ordinary : x.OrdinaryComparisonsNormalized J b0 d0)
    (P : cochainSV x J) (I : cochainSU x J)
    (f : (inverseSComplex x J).obj P ⟶ I) :
    (((Adjunction.whiskerRight J x.R.adjunction).mapHomologicalComplex (.up ℤ)).homEquiv
      _ _ ((NatIso.mapHomologicalComplex b0 (.up ℤ)).inv.app P ≫
        (restrictUComplex x J).map f)) =
    (restrictVComplex x J).map
      (((Adjunction.whiskerRight J x.S.adjunction).mapHomologicalComplex (.up ℤ)).homEquiv
        _ _ f) ≫ (NatIso.mapHomologicalComplex d0 (.up ℤ)).hom.app I := by
  ext n : 1
  exact ordinary_adjunct x J b0 d0 ordinary (P.X n) (I.X n) (f.f n)

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {H : GrothendieckTopology D}
  (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J]
  [HasDerivedCategory.{w} (x.diagramsRU J)]
  [HasDerivedCategory.{w} (x.diagramsSU J)]
  [HasDerivedCategory.{w} (x.diagramsRV J)]
  [HasDerivedCategory.{w} (x.diagramsSV J)]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- The counit calculation compares several presentations of composite complex functors.
/-- The mate of the localized inverse coefficient comparison is an isomorphism,
with the prescribed right-derived-unit normalization.
Source: Stacks Project, Tags 0FND, 070I, 070K and 070Y; Modules on Sites, Tag 03D3.
(blueprint: lem-weil-pbc-flat-restriction-derived-mate).

Proof: Apply the faithful underlying-set-sheaf functor to the ordinary
adjunct equation. The normalized comparisons, the two transpose formulas and
the equality of geometric adjunctions reduce it to cancellation of the underlying
comparison isomorphisms. This gives the ordinary equation on all diagram arrows,
and degreewise on complexes. Apply the supplied derived transpose formulas to the
ordinary counit of LS. Its ordinary transpose is the identity. The mate-unit identity,
the inverse normalization hb and naturality of qU then give the displayed
normalization on every complex, directly. At a K-injective I, both derived units
are invertible by computesS, computesR and hU; every other factor in that equation
is an isomorphism, so delta at QI is an isomorphism. Small diagrams of module
sheaves are Grothendieck abelian, hence every complex admits a K-injective
resolution. Localization inverts its quasi-isomorphism, and naturality of delta
transports invertibility from the resolution to the original complex. Essential
surjectivity of localization gives invertibility at every derived object. -/
theorem flatRestriction_derived_mate
    (LR : derivedRV x J ⥤ derivedRU x J)
    (FR : derivedRU x J ⥤ derivedRV x J)
    (qLR : DerivedCategory.Q ⋙ LR ≅ inverseRComplex x J ⋙ DerivedCategory.Q)
    (ηR : directRComplex x J ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ FR)
    (aR : LR ⊣ FR)
    (_derivedR : FR.IsRightDerivedFunctor ηR
      (HomologicalComplex.quasiIso (x.diagramsRU J) (.up ℤ)))
    (computesR : ∀ I : cochainRU x J, I.IsKInjective → IsIso (ηR.app I))
    (transposeR : ∀ (P : cochainRV x J) (I : cochainRU x J)
      (f : (inverseRComplex x J).obj P ⟶ I),
      aR.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
        (qLR.hom.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
        (((Adjunction.whiskerRight J x.R.adjunction).mapHomologicalComplex (.up ℤ)).homEquiv
          P I f) ≫ ηR.app I)
    (LS : derivedSV x J ⥤ derivedSU x J)
    (FS : derivedSU x J ⥤ derivedSV x J)
    (qLS : DerivedCategory.Q ⋙ LS ≅ inverseSComplex x J ⋙ DerivedCategory.Q)
    (ηS : directSComplex x J ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ FS)
    (aS : LS ⊣ FS)
    (_derivedS : FS.IsRightDerivedFunctor ηS
      (HomologicalComplex.quasiIso (x.diagramsSU J) (.up ℤ)))
    (computesS : ∀ I : cochainSU x J, I.IsKInjective → IsIso (ηS.app I))
    (transposeS : ∀ (P : cochainSV x J) (I : cochainSU x J)
      (f : (inverseSComplex x J).obj P ⟶ I),
      aS.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
        (qLS.hom.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
        (((Adjunction.whiskerRight J x.S.adjunction).mapHomologicalComplex (.up ℤ)).homEquiv
          P I f) ≫ ηS.app I)
    (rU : derivedSU x J ⥤ derivedRU x J)
    (rV : derivedSV x J ⥤ derivedRV x J)
    (qU : DerivedCategory.Q ⋙ rU ≅ restrictUComplex x J ⋙ DerivedCategory.Q)
    (qV : DerivedCategory.Q ⋙ rV ≅ restrictVComplex x J ⋙ DerivedCategory.Q)
    (b0 : x.inverseS J ⋙ x.restrictU J ≅ x.restrictV J ⋙ x.inverseR J)
    (d0 : x.directS J ⋙ x.restrictV J ≅ x.restrictU J ⋙ x.directR J)
    (ordinary : x.OrdinaryComparisonsNormalized J b0 d0)
    (hU : ∀ I : cochainSU x J, I.IsKInjective →
      CochainComplex.IsKInjective ((restrictUComplex x J).obj I))
    (b : LS ⋙ rU ≅ rV ⋙ LR)
    (hb : ∀ P : cochainSV x J,
      rU.map (qLS.hom.app P) ≫ qU.hom.app ((inverseSComplex x J).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b0 (.up ℤ)).hom.app P) =
      b.hom.app (DerivedCategory.Q.obj P) ≫ LR.map (qV.hom.app P) ≫
        qLR.hom.app ((restrictVComplex x J).obj P)) :
    let δ := (mateEquiv aS aR (TwoSquare.mk _ _ _ _ b.inv)).natTrans
    IsIso δ ∧ ∀ I : cochainSU x J,
      rV.map (ηS.app I) ≫ δ.app (DerivedCategory.Q.obj I) ≫ FR.map (qU.hom.app I) =
        qV.hom.app ((directSComplex x J).obj I) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex d0 (.up ℤ)).hom.app I) ≫
          ηR.app ((restrictUComplex x J).obj I) := by
  let δ := (mateEquiv aS aR (TwoSquare.mk _ _ _ _ b.inv)).natTrans
  have hn : ∀ I : cochainSU x J,
      rV.map (ηS.app I) ≫ δ.app (DerivedCategory.Q.obj I) ≫ FR.map (qU.hom.app I) =
        qV.hom.app ((directSComplex x J).obj I) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex d0 (.up ℤ)).hom.app I) ≫
          ηR.app ((restrictUComplex x J).obj I) := by
    intro I
    let P := (directSComplex x J).obj I
    let c := ((Adjunction.whiskerRight J x.S.adjunction).mapHomologicalComplex
      (.up ℤ)).counit.app I
    have hs := transposeS P I c
    have hc : (((Adjunction.whiskerRight J x.S.adjunction).mapHomologicalComplex
        (.up ℤ)).homEquiv P I c) = 𝟙 P := by
      exact adjunct_counit
        ((Adjunction.whiskerRight J x.S.adjunction).mapHomologicalComplex (.up ℤ)) I
    rw [hc, DerivedCategory.Q.map_id, Category.id_comp] at hs
    have hm := adjunct_mate aS aR rV rU b (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj I) (qLS.hom.app P ≫ DerivedCategory.Q.map c)
    rw [hs] at hm
    change _ = rV.map (ηS.app I) ≫ δ.app (DerivedCategory.Q.obj I) at hm
    erw [← Category.assoc, ← hm]
    erw [← aR.homEquiv_naturality_right]
    have hb' : b.inv.app (DerivedCategory.Q.obj P) ≫ rU.map (qLS.hom.app P) ≫
        qU.hom.app ((inverseSComplex x J).obj P) =
        LR.map (qV.hom.app P) ≫ qLR.hom.app ((restrictVComplex x J).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b0 (.up ℤ)).inv.app P) := by
      calc
        _ = b.inv.app (DerivedCategory.Q.obj P) ≫
            (rU.map (qLS.hom.app P) ≫ qU.hom.app ((inverseSComplex x J).obj P) ≫
              DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b0 (.up ℤ)).hom.app P)) ≫
              DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b0 (.up ℤ)).inv.app P) := by
          simp only [Category.assoc]
          erw [← DerivedCategory.Q.map_comp, Iso.hom_inv_id_app, Functor.map_id,
            Category.comp_id]
        _ = _ := by rw [hb]; simp [Category.assoc]
    have hq := qU.hom.naturality c
    change rU.map (DerivedCategory.Q.map c) ≫ qU.hom.app I =
      qU.hom.app ((inverseSComplex x J).obj P) ≫
        DerivedCategory.Q.map ((restrictUComplex x J).map c) at hq
    rw [← Category.assoc] at hb'
    erw [rU.map_comp, Category.assoc, Category.assoc, hq,
      ← Category.assoc, ← Category.assoc, hb']
    rw [Category.assoc, Category.assoc, ← DerivedCategory.Q.map_comp]
    erw [aR.homEquiv_naturality_left, transposeR]
    rw [complex_adjunct x J b0 d0 ordinary P I c, hc]
    simp [P]
  refine ⟨?_, hn⟩
  have : IsGrothendieckAbelian.{u} (x.diagramsSU J) :=
    smallModuleDiagrams_isGrothendieckAbelian H
      ((sheafCompose H (forget₂ CommRingCat RingCat)).obj x.SU) J
  have hki (I : cochainSU x J) (hI : I.IsKInjective) :
      IsIso (δ.app (DerivedCategory.Q.obj I)) := by
    have : IsIso (ηS.app I) := computesS I hI
    have : IsIso (ηR.app ((restrictUComplex x J).obj I)) := computesR _ (hU I hI)
    have : IsIso (rV.map (ηS.app I) ≫ δ.app (DerivedCategory.Q.obj I) ≫
        FR.map (qU.hom.app I)) := by
      rw [hn I]
      infer_instance
    have : IsIso (δ.app (DerivedCategory.Q.obj I) ≫ FR.map (qU.hom.app I)) :=
      IsIso.of_isIso_comp_left (rV.map (ηS.app I)) _
    exact IsIso.of_isIso_comp_right _ (FR.map (qU.hom.app I))
  change IsIso δ
  have : ∀ M, IsIso (δ.app M) := by
    intro M
    let Q := DerivedCategory.Q (C := x.diagramsSU J)
    let K := Q.objPreimage M
    obtain ⟨I, hI, i, _, hi⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
    have := hi
    have : IsIso (Q.map i) := by dsimp [Q]; infer_instance
    have : IsIso (δ.app (Q.obj I)) := hki I hI
    have : IsIso (δ.app (Q.obj K)) :=
      (NatTrans.isIso_app_iff_of_iso δ (asIso (Q.map i))).mpr inferInstance
    exact (NatTrans.isIso_app_iff_of_iso δ (Q.objObjPreimageIso M)).mp inferInstance
  exact NatIso.isIso_of_isIso_app δ

end CategoryTheory.FlatRingedDiagramInput
