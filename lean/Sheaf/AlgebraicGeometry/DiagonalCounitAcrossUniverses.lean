/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackAcrossUniverses
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure
import Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh

/-! # Diagonal counit in independent localization universes

Source: Stacks Project, Equation 48.12.8.1, Tag 0E2Q; localization uniqueness, Tag 05RU.
(blueprint: lem-sc-diagonal-counit-across-universes).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wS wP

open CategoryTheory Limits

namespace AlgebraicGeometry


private instance qc_closed (X : Scheme.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    (schemeDerivedQCohProperty X).IsClosedUnderIsomorphisms where
  of_iso e h n := (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso e) (h n)

private noncomputable def standard_homology (X : Scheme.{u})
    [h : HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (n : ℤ) :
    (schemeDerivedStandardEquivalence X).functor ⋙
      @DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) n ≅
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let q := @DerivedCategory.Qh C _ _ h
  let qs := @DerivedCategory.Qh C _ _ (HasDerivedCategory.standard _)
  let e := Localization.compUniqFunctor q qs (HomotopyCategory.quasiIso C (.up ℤ))
  exact ((Functor.whiskeringLeft _ _ _).obj q).preimageIso
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e _ ≪≫
      @DerivedCategory.homologyFunctorFactorsh C _ _ (HasDerivedCategory.standard _) n ≪≫
      (@DerivedCategory.homologyFunctorFactorsh C _ _ h n).symm)

private theorem standard_qc (X : Scheme.{u})
    [h : HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    (@schemeDerivedQCohProperty X (HasDerivedCategory.standard _)).inverseImage
      (schemeDerivedStandardEquivalence X).functor = schemeDerivedQCohProperty X := by
  funext E
  apply propext
  constructor
  · intro hE n
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((standard_homology X n).app E) (hE n)
  · intro hE n
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((standard_homology X n).app E).symm (hE n)

private noncomputable def qc_equivalence (X : Scheme.{u})
    [h : HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    schemeDerivedQCohCategory X ≌
      @schemeDerivedQCohCategory X (HasDerivedCategory.standard _) :=
  (schemeDerivedStandardEquivalence X).congrFullSubcategory (standard_qc X)

private noncomputable def standard_single (X : Scheme.{u})
    [h : HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (schemeDerivedStandardEquivalence X).functor.obj
      ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj M :=
  (Localization.compUniqFunctor (@DerivedCategory.Qh _ _ _ h)
    (@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _))
      (HomotopyCategory.quasiIso _ (.up ℤ))).app
        (((HomotopyCategory.singleFunctors _).functor 0).obj M)

private theorem qc_single (X : Scheme.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (hM : M.IsQuasicoherent) :
    schemeDerivedQCohProperty X ((DerivedCategory.singleFunctor _ 0).obj M) := by
  intro n
  by_cases hn : n = 0
  · subst n
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hM
  · let e := (DerivedCategory.homologyFunctorFactors _ n).app
      ((CochainComplex.singleFunctor _ 0).obj M)
    have hz := HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 M n hn
    have hz' : IsZero ((DerivedCategory.homologyFunctor _ n).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) := IsZero.of_iso hz e
    let F : SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
      SheafOfModules.free PEmpty.{u+1}
    have hf : IsZero F := by
      rw [IsZero.iff_id_eq_zero]
      apply Limits.Sigma.hom_ext
      intro i
      exact PEmpty.elim i
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (hf.iso hz') (SheafOfModules.isQuasicoherent_free PEmpty.{u+1})


private noncomputable def standard_Q (X : Scheme.{u})
    [h : HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    DerivedCategory.Q ⋙ (schemeDerivedStandardEquivalence X).functor ≅
      @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _) :=
  Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (Localization.compUniqFunctor (@DerivedCategory.Qh _ _ _ h)
        (@DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _))
          (HomotopyCategory.quasiIso _ (.up ℤ))) ≪≫
    @DerivedCategory.quotientCompQhIso _ _ _ (HasDerivedCategory.standard _)

set_option maxHeartbeats 800000 in
-- Full-faithfulness unfolds the chosen localization and resolution functors.
set_option backward.isDefEq.respectTransparency false in
private theorem standard_directImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hx : HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [hy : HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    Nonempty (schemeDerivedDirectImage f ⋙ (schemeDerivedStandardEquivalence Y).functor ≅
      (schemeDerivedStandardEquivalence X).functor ⋙
        @schemeDerivedDirectImage X Y (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _) f) := by
  let q := @DerivedCategory.Q _ _ _ hx
  let qs := @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  let eX := (schemeDerivedStandardEquivalence X).functor
  let eY := (schemeDerivedStandardEquivalence Y).functor
  let R := schemeDerivedDirectImage f
  let Rs := @schemeDerivedDirectImage X Y (HasDerivedCategory.standard _)
    (HasDerivedCategory.standard _) f
  obtain ⟨α⟩ := RingedSpace.derivedModuleDirectImageFactorization f.toLRSHom.toShHom
  obtain ⟨β⟩ := @RingedSpace.derivedModuleDirectImageFactorization _ _
    (HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    f.toLRSHom.toShHom
  let γ : RingedSpace.resolvedModuleDirectImage f.toLRSHom.toShHom ⋙ eY ≅
      @RingedSpace.resolvedModuleDirectImage _ _
        (HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
        f.toLRSHom.toShHom :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (standard_Q Y))
  have := Localization.full_whiskeringLeft q
    (HomologicalComplex.quasiIso _ (.up ℤ))
    (@schemeDerivedCategory Y (HasDerivedCategory.standard _))
  have := Localization.faithful_whiskeringLeft q
    (HomologicalComplex.quasiIso _ (.up ℤ))
    (@schemeDerivedCategory Y (HasDerivedCategory.standard _))
  exact ⟨((Functor.whiskeringLeft _ _ _).obj q).preimageIso
    ((Functor.associator q R eY).symm ≪≫ Functor.isoWhiskerRight α eY ≪≫
      γ ≪≫ β.symm ≪≫ Functor.isoWhiskerRight (standard_Q X).symm Rs ≪≫
      Functor.associator q eX Rs)⟩

/-- The first equality of the diagonal evaluation chain, for the specified adjoints.
Source: Stacks Project, Tag 0E2Q, and localization uniqueness, Tag 05RU.
(blueprint: lem-sc-diagonal-counit-across-universes).

Proof: properness makes f finite type and quasi-compact; the base-changed projection
is again proper. Hence P = X ×_S X is Noetherian. Flat pullback preserves quasi-coherent
cohomology, so the mixed-universe pullback of a(O) has a preservation witness hK.
For each scheme compare the specified localization with the standard localization of
complexes using `schemeDerivedStandardEquivalence`. The comparison commutes with Qh by
`Localization.compUniqFunctor`. The homology comparisons then show that it restricts to
an equivalence of quasi-coherent full subcategories: evaluate the factorization of each
homology functor on Qh and use full faithfulness of precomposition with Qh. Likewise it
commutes with the single functor, by its factorization through Qh. Transport R using the
restricted equivalences. Its given comparison identifies it with the restriction of
standard derived direct image, because right derived functors commute with equivalences
of their localizations by the right Kan universal property. Transfer adj along this
comparison. Transfer adjC in the same way; changes of the preservation proof are invisible
in the full subcategory. The Noetherian direct-image theorem supplies the preservation
witnesses for the standard f and diagonal. Flat pullback supplies the first-projection
witness; the structure single objects have quasi-coherent homology. Apply
`diagonal_counit_identity` in the standard universe, with these transported adjunctions.
This gives O_X[0] isomorphic to c(Lpr_1* a(O_S[0])). Transport back, use hO through a,
and the explicit definition of `derivedPullbackAcrossUniverses` to identify the middle
object. The inverse of the resulting isomorphism has the displayed orientation. This
argument never uses perfection of the diagonal or its tensor formula. For f = id the
projection and both adjoints identify with identity functors; for an empty source all
objects involved are zero. These cases require no nonemptiness hypotheses. -/
theorem diagonal_counit_acrossUniverses
    (X S : Scheme.{u}) [IsNoetherian X] [IsNoetherian S]
    (f : X ⟶ S) [Flat f] [IsProper f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{wP}
      (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace))]
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory S)
    (comparison : R ⋙ (schemeDerivedQCohProperty S).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory X)
    (adj : R ⊣ a) (O : schemeDerivedQCohCategory S)
    (hO : O.obj ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
          (SheafOfModules.unit S.ringCatSheaf))
    (hRΔ : ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty (pullback f f)
        ((schemeDerivedDirectImage (pullback.diagonal f)).obj E.obj))
    (c : schemeDerivedQCohCategory (pullback f f) ⥤ schemeDerivedQCohCategory X)
    (adjC : (schemeDerivedQCohProperty (pullback f f)).lift
      ((schemeDerivedQCohProperty X).ι ⋙
        schemeDerivedDirectImage (pullback.diagonal f)) hRΔ ⊣ c)
 :
    ∃ hK : schemeDerivedQCohProperty (pullback f f)
        ((derivedPullbackAcrossUniverses (pullback.fst f f)).obj (a.obj O).obj),
      Nonempty ((c.obj ⟨(derivedPullbackAcrossUniverses (pullback.fst f f)).obj
          (a.obj O).obj, hK⟩).obj ≅
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (SheafOfModules.unit X.ringCatSheaf)) := by
  classical
  let hx : HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := inferInstance
  let hs : HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) := inferInstance
  let hp : HasDerivedCategory.{wP}
      (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace)) := inferInstance
  let P := pullback f f
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f f)
  have : CompactSpace (P : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
  have : IsNoetherian P := ⟨⟩
  let sx := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let ss := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings S.toRingedSpace))
  let sp := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings P.toRingedSpace))
  let eX := @qc_equivalence X hx
  let eS := @qc_equivalence S hs
  let eP := @qc_equivalence P hp
  let qX := @schemeDerivedQCohProperty X hx
  let qS := @schemeDerivedQCohProperty S hs
  let qP := @schemeDerivedQCohProperty P hp
  let pX := @schemeDerivedQCohProperty X sx
  let pS := @schemeDerivedQCohProperty S ss
  let pP := @schemeDerivedQCohProperty P sp
  let Rfs := @schemeDerivedDirectImage X S sx ss f
  let RΔs := @schemeDerivedDirectImage X P sx sp (pullback.diagonal f)
  let Ls := @derivedPullback P X (pullback.fst f f) sx sp
  have hRf : ∀ E : @schemeDerivedQCohCategory X sx, pS (Rfs.obj E.obj) := by
    let _ := sx
    let _ := ss
    obtain ⟨h, _⟩ := noetherian_schemeDerivedDirectImage_has_rightAdjoint f
    exact h
  have hRd : ∀ E : @schemeDerivedQCohCategory X sx, pP (RΔs.obj E.obj) := by
    let _ := sx
    let _ := sp
    obtain ⟨h, _⟩ :=
      noetherian_schemeDerivedDirectImage_has_rightAdjoint (pullback.diagonal f)
    exact h
  have hL : ∀ E : @schemeDerivedQCohCategory X sx, pP (Ls.obj E.obj) := by
    let _ := sx
    let _ := sp
    exact fun E ↦ (derivedPullback_tensor_preserve_QCoh (pullback.fst f f)).1
      E.obj E.property
  let RF := pS.lift (pX.ι ⋙ Rfs) hRf
  let RD := pP.lift (pX.ι ⋙ RΔs) hRd
  let LD := pP.lift (pX.ι ⋙ Ls) hL
  let as := eS.inverse ⋙ a ⋙ eX.functor
  let cs := eP.inverse ⋙ c ⋙ eX.functor
  obtain ⟨tf⟩ := @standard_directImage X S f hx hs
  obtain ⟨td⟩ := @standard_directImage X P (pullback.diagonal f) hx hp
  let κ : R ⋙ eS.functor ≅ eX.functor ⋙ RF :=
    ((Functor.whiskeringRight _ _ _).obj pS.ι).preimageIso
      (Functor.isoWhiskerRight comparison (@schemeDerivedStandardEquivalence S hs).functor ≪≫
        Functor.isoWhiskerLeft qX.ι tf)
  let RΔ := qP.lift
    (qX.ι ⋙ @schemeDerivedDirectImage X P hx hp (pullback.diagonal f)) hRΔ
  let κd : RΔ ⋙ eP.functor ≅ eX.functor ⋙ RD :=
    ((Functor.whiskeringRight _ _ _).obj pP.ι).preimageIso
      (Functor.isoWhiskerLeft qX.ι td)
  have adjAs : RF ⊣ as :=
    ((eX.symm.toAdjunction.comp adj).comp eS.toAdjunction).ofNatIsoLeft
      (Functor.isoWhiskerLeft eX.inverse κ ≪≫
        Functor.isoWhiskerRight eX.counitIso RF ≪≫ RF.leftUnitor)
  have adjCs : RD ⊣ cs :=
    ((eX.symm.toAdjunction.comp adjC).comp eP.toAdjunction).ofNatIsoLeft
      (Functor.isoWhiskerLeft eX.inverse κd ≪≫
        Functor.isoWhiskerRight eX.counitIso RD ≪≫ RD.leftUnitor)
  have hOX : pX ((@DerivedCategory.singleFunctor _ _ _ sx 0).obj
      (SheafOfModules.unit X.ringCatSheaf)) := by
    let _ := sx
    exact qc_single X _ (SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf))
  have hOS : pS ((@DerivedCategory.singleFunctor _ _ _ ss 0).obj
      (SheafOfModules.unit S.ringCatSheaf)) := by
    let _ := ss
    exact qc_single S _ (SheafOfModules.isQuasicoherent_unit (R := S.ringCatSheaf))
  let OXs : @schemeDerivedQCohCategory X sx := ⟨_, hOX⟩
  let OSs : @schemeDerivedQCohCategory S ss := ⟨_, hOS⟩
  obtain ⟨η⟩ := @diagonal_counit_identity _ _ _ _ sx ss f _ _ sp
    hRf hRd hL hOX hOS as adjAs cs adjCs
  have ε : eS.functor.obj O ≅ OSs := pS.isoMk
    ((@schemeDerivedStandardEquivalence S hs).functor.mapIso hO ≪≫ @standard_single S hs _)
  let A := a.obj O
  have α : as.obj OSs ≅ eX.functor.obj A :=
    (eS.inverse ⋙ a ⋙ eX.functor).mapIso ε.symm ≪≫
      (a ⋙ eX.functor).mapIso ((eS.unitIso.app O).symm)
  let K := (@derivedPullbackAcrossUniverses P X (pullback.fst f f) hp hx).obj A.obj
  have hK : qP K := by
    change qP
      ((@schemeDerivedStandardEquivalence P hp).inverse.obj (Ls.obj
        ((@schemeDerivedStandardEquivalence X hx).functor.obj A.obj)))
    exact (eP.inverse.obj (LD.obj (eX.functor.obj A))).property
  let Kq : @schemeDerivedQCohCategory P hp := ⟨K, hK⟩
  have β : eP.functor.obj Kq ≅ LD.obj (eX.functor.obj A) :=
    pP.isoMk ((@schemeDerivedStandardEquivalence P hp).counitIso.app _)
  have γ : cs.obj (eP.functor.obj Kq) ≅ eX.functor.obj (c.obj Kq) :=
    (c ⋙ eX.functor).mapIso ((eP.unitIso.app Kq).symm)
  have ζ : eX.functor.obj (c.obj Kq) ≅ OXs :=
    γ.symm ≪≫ cs.mapIso β ≪≫ cs.mapIso (LD.mapIso α.symm) ≪≫ η.symm
  refine ⟨hK, ⟨?_⟩⟩
  exact (@schemeDerivedStandardEquivalence X hx).functor.preimageIso
    (pX.ι.mapIso ζ ≪≫ (@standard_single X hx _).symm)


end AlgebraicGeometry
