/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleIsomorphicStageProjectionInterfaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleOrdinaryInverseTransport
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleFiniteOrdinaryInverseTransport
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleDerivedInverseTransportFaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleTransportScalarCounit
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Normalized geometric projection faces

Source: Zheng, Construction 5.15 and Lemma 5.22.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

private theorem mate_of_counit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (E : A ⥤ C) (F : B ⥤ D)
    (α : L ⋙ F ≅ E ⋙ L') (β : R ⋙ E ≅ F ⋙ R')
    (h : ∀ K, α.hom.app (R.obj K) ≫ L'.map (β.hom.app K) ≫
      adj'.counit.app (F.obj K) = F.map (adj.counit.app K)) :
    (mateEquiv adj adj' (.mk _ _ _ _ α.inv)).natTrans = β.hom := by
  ext K
  apply (adj'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit]
  rw [mateEquiv_counit]
  apply (cancel_epi (α.hom.app (R.obj K))).1
  simpa only [Adjunction.homEquiv_counit, Category.assoc,
    Iso.hom_inv_id_app_assoc] using (h K).symm

private theorem mate_evaluation
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {Ln : A' ⥤ B'} {Rn : B' ⥤ A'} {Ln' : C' ⥤ D'} {Rn' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (adjn : Ln ⊣ Rn) (adjn' : Ln' ⊣ Rn')
    (U : A ⥤ C) (V : B ⥤ D) (Un : A' ⥤ C') (Vn : B' ⥤ D')
    (EA : A ⥤ A') (EB : B ⥤ B') (EC : C ⥤ C') (ED : D ⥤ D')
    (α : L ⋙ EB ≅ EA ⋙ Ln) (β : R ⋙ EA ≅ EB ⋙ Rn)
    (α' : L' ⋙ ED ≅ EC ⋙ Ln') (β' : R' ⋙ EC ≅ ED ⋙ Rn')
    (u : U ⋙ EC ≅ EA ⋙ Un) (v : V ⋙ ED ≅ EB ⋙ Vn)
    (θ : U ⋙ L' ⟶ L ⋙ V) (θn : Un ⋙ Ln' ⟶ Ln ⋙ Vn)
    (ha : ∀ K, α.hom.app (R.obj K) ≫ Ln.map (β.hom.app K) ≫
      adjn.counit.app (EB.obj K) = EB.map (adj.counit.app K))
    (hb : ∀ K, α'.hom.app (R'.obj K) ≫ Ln'.map (β'.hom.app K) ≫
      adjn'.counit.app (ED.obj K) = ED.map (adj'.counit.app K))
    (hc : ∀ K, Ln'.map (u.inv.app K) ≫ α'.inv.app (U.obj K) ≫ ED.map (θ.app K) =
      θn.app (EA.obj K) ≫ Vn.map (α.inv.app K) ≫ v.inv.app (L.obj K)) (K : B) :
    u.hom.app (R.obj K) ≫ Un.map (β.hom.app K) ≫
        (mateEquiv adjn adjn' (.mk _ _ _ _ θn)).natTrans.app (EB.obj K) =
      EC.map ((mateEquiv adj adj' (.mk _ _ _ _ θ)).natTrans.app K) ≫
        β'.hom.app (V.obj K) ≫ Rn'.map (v.hom.app K) := by
  have h := exchangeMate_cube adj adj' adjn adjn' EA EB EC ED α u v α' θ θn hc K
  change EC.map ((mateEquiv adj adj' (.mk _ _ _ _ θ)).natTrans.app K) ≫
      (mateEquiv adj' adjn' (.mk _ _ _ _ α'.inv)).natTrans.app (V.obj K) ≫
      Rn'.map (v.hom.app K) =
    u.hom.app (R.obj K) ≫
      Un.map ((mateEquiv adj adjn (.mk _ _ _ _ α.inv)).natTrans.app K) ≫
      (mateEquiv adjn adjn' (.mk _ _ _ _ θn)).natTrans.app (EB.obj K) at h
  rw [show (mateEquiv adj adjn (.mk _ _ _ _ α.inv)).natTrans = β.hom from
    mate_of_counit adj adjn EA EB α β ha,
    show (mateEquiv adj' adjn' (.mk _ _ _ _ α'.inv)).natTrans = β'.hom from
    mate_of_counit adj' adjn' EC ED α' β' hb] at h
  exact h.symm

private theorem mate_quotient
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {Ln : A' ⥤ B'} {Rn : B' ⥤ A'} {Ln' : C' ⥤ D'} {Rn' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (adjn : Ln ⊣ Rn) (adjn' : Ln' ⊣ Rn')
    (U : A ⥤ C) (V : B ⥤ D) (Un : A' ⥤ C') (Vn : B' ⥤ D')
    (EA : A ⥤ A') (EB : B ⥤ B') (EC : C ⥤ C') (ED : D ⥤ D')
    (α : EA ⋙ Ln ≅ L ⋙ EB) (β : EB ⋙ Rn ≅ R ⋙ EA)
    (α' : EC ⋙ Ln' ≅ L' ⋙ ED) (β' : ED ⋙ Rn' ≅ R' ⋙ EC)
    (u : EA ⋙ Un ≅ U ⋙ EC) (v : EB ⋙ Vn ≅ V ⋙ ED)
    (θ : U ⋙ L' ≅ L ⋙ V) (θn : Un ⋙ Ln' ≅ Ln ⋙ Vn)
    (m : R ⋙ U ≅ V ⋙ R') (mn : Rn ⋙ Un ≅ Vn ⋙ Rn')
    (ha : β.inv = (mateEquiv adj adjn (.mk _ _ _ _ α.hom)).natTrans)
    (hb : β'.inv = (mateEquiv adj' adjn' (.mk _ _ _ _ α'.hom)).natTrans)
    (hm : m.hom = (mateEquiv adj adj' (.mk _ _ _ _ θ.hom)).natTrans)
    (hmn : mn.hom = (mateEquiv adjn adjn' (.mk _ _ _ _ θn.hom)).natTrans)
    (hc : ∀ K, Ln'.map (u.hom.app K) ≫ α'.hom.app (U.obj K) ≫ ED.map (θ.hom.app K) =
      θn.hom.app (EA.obj K) ≫ Vn.map (α.hom.app K) ≫ v.hom.app (L.obj K)) (K : B) :
    Rn'.map (v.hom.app K) ≫ β'.hom.app (V.obj K) ≫ EC.map (m.inv.app K) =
      mn.inv.app (EB.obj K) ≫ Un.map (β.hom.app K) ≫ u.hom.app (R.obj K) := by
  have h := exchangeMate_cube adj adj' adjn adjn' EA EB EC ED
    α.symm u.symm v.symm α'.symm θ.hom θn.hom hc K
  change EC.map ((mateEquiv adj adj' (.mk _ _ _ _ θ.hom)).natTrans.app K) ≫
      (mateEquiv adj' adjn' (.mk _ _ _ _ α'.hom)).natTrans.app (V.obj K) ≫
      Rn'.map (v.inv.app K) =
    u.inv.app (R.obj K) ≫
      Un.map ((mateEquiv adj adjn (.mk _ _ _ _ α.hom)).natTrans.app K) ≫
      (mateEquiv adjn adjn' (.mk _ _ _ _ θn.hom)).natTrans.app (EB.obj K) at h
  rw [← hm, ← hmn, ← ha, ← hb] at h
  let i := EC.mapIso (m.app K) ≪≫ β'.symm.app (V.obj K) ≪≫ Rn'.mapIso (v.symm.app K)
  let j := u.symm.app (R.obj K) ≪≫ Un.mapIso (β.symm.app K) ≪≫ mn.app (EB.obj K)
  have hij : i = j := Iso.ext h
  have hi := congrArg Iso.inv hij
  change (Rn'.map (v.hom.app K) ≫ β'.hom.app (V.obj K)) ≫ EC.map (m.inv.app K) =
    (mn.inv.app (EB.obj K) ≫ Un.map (β.hom.app K)) ≫ u.hom.app (R.obj K) at hi
  simpa only [Category.assoc] using hi

private theorem evaluation_jointlyReflects
    (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O] (ell : O) :
    JointlyReflectIsomorphisms
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell)) where
  isIso {M N} f hf := by
    have hi (n : ℕ) : IsIso (f.app n) := hf n
    let g : N ⟶ M := {
      app := fun n ↦ inv (f.app n)
      comm := by
        intro n
        apply (cancel_epi (f.app (n + 1))).1
        simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
        rw [f.comm, Category.assoc]
        simp only [← Functor.map_comp, IsIso.hom_inv_id]
        rw [(coefficientRestriction (J := T.smallEtaleTopology) O ell
          (Nat.le_succ n)).map_id]
        exact (Category.comp_id _).symm }
    have ext {A B : strictEtaleCoefficientSystem T O ell} (f g : A ⟶ B)
        (h : f.app = g.app) : f = g := by
      cases f
      cases g
      cases h
      rfl
    refine ⟨g, ?_, ?_⟩
    · change CoefficientSystem.Hom.compose f g = CoefficientSystem.identity M
      apply ext
      funext n
      exact IsIso.hom_inv_id (f.app n)
    · change CoefficientSystem.Hom.compose g f = CoefficientSystem.identity N
      apply ext
      funext n
      exact IsIso.inv_hom_id (f.app n)

private theorem evaluation_detectsIso
    {T : Scheme.{u}} {O : Type (u + 1)} [CommRing O] {ell : O}
    (P : StrictEtaleEvaluation T O ell)
    {M N : DerivedCategory (strictEtaleCoefficientSystem T O ell)} (f : M ⟶ N)
    (hf : ∀ n, IsIso ((P.evaluation n).map f)) : IsIso f := by
  have hl (n : ℕ) : PreservesFiniteLimits
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) n) :=
    (coefficientEvaluation_exact (J := T.smallEtaleTopology) (O := O) (ell := ell) n).1
  have hc (n : ℕ) : PreservesFiniteColimits
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) n) :=
    (coefficientEvaluation_exact (J := T.smallEtaleTopology) (O := O) (ell := ell) n).2
  apply ((Functor.jointlyReflectIsomorphisms_mapDerivedCategory
    (evaluation_jointlyReflects T O ell)).isIso_iff f).2
  intro n
  let e := coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) n
  let α : P.evaluation n ≅ e.mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (strictEtaleCoefficientSystem T O ell) (.up ℤ))
      (DerivedCategory.Q ⋙ P.evaluation n) (DerivedCategory.Q ⋙ e.mapDerivedCategory)
      (P.evaluation n) e.mapDerivedCategory
      (P.evaluationFactors n ≪≫ e.mapDerivedCategoryFactors.symm)
  exact (NatIso.isIso_map_iff α f).1 (hf n)

section DerivedSquare
universe a b c d av bv cv dv w
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{w} B]
  {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type d} [Category.{dv} D] [Abelian D] [HasDerivedCategory.{w} D]
  (F : A ⥤ B) (eA : A ⥤ C) (eB : B ⥤ D) (L : C ⥤ D)
  [F.Additive] [eA.Additive] [eB.Additive] [L.Additive]
  (FD : DerivedCategory A ⥤ DerivedCategory B)
  (EA : DerivedCategory A ⥤ DerivedCategory C)
  (EB : DerivedCategory B ⥤ DerivedCategory D)
  (LD : DerivedCategory C ⥤ DerivedCategory D)
  (φF : DerivedCategory.Q ⋙ FD ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φA : DerivedCategory.Q ⋙ EA ≅ eA.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φB : DerivedCategory.Q ⋙ EB ≅ eB.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φL : DerivedCategory.Q ⋙ LD ≅ L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (α : F ⋙ eB ≅ eA ⋙ L)

private theorem inverseDerivedSquare :
    ∃ δ : FD ⋙ EB ≅ EA ⋙ LD, ∀ P,
      δ.hom.app (DerivedCategory.Q.obj P) ≫ LD.map (φA.hom.app P) ≫
        φL.hom.app ((eA.mapHomologicalComplex (.up ℤ)).obj P) =
      EB.map (φF.hom.app P) ≫ φB.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex α (.up ℤ)).hom.app P) := by
  let ψF : DerivedCategory.Q ⋙ (FD ⋙ EB) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙
        eB.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight φF EB ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ φB
  let ψL : DerivedCategory.Q ⋙ (EA ⋙ LD) ≅
      eA.mapHomologicalComplex (.up ℤ) ⋙
        L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight φA LD ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ φL
  let γ := Functor.mapHomologicalComplexCompIso α (.up ℤ)
  let τ := ψF ≪≫ isoWhiskerRight γ DerivedCategory.Q ≪≫ ψL.symm
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) (DerivedCategory D)
  let δ := ff.preimageIso τ
  refine ⟨δ, ?_⟩
  intro P
  have hd : δ.hom.app (DerivedCategory.Q.obj P) = τ.hom.app P := by
    exact congr_app (ff.map_preimage τ.hom) P
  rw [hd]
  dsimp only [τ, ψF, ψL, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_inv, isoWhiskerLeft_inv, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp, Category.comp_id, Category.assoc,
    ← LD.map_comp_assoc, Iso.inv_hom_id_app]
  erw [LD.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  rfl
end DerivedSquare

private theorem properProjectionFaces_of_inverse
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
    (TY : StrictEtaleCoefficientTransport a Y SA.PY SB.PY)
    (hTZ : ∀ n, (TZ.level n).derived.IsEquivalence)
    (hTY : ∀ n, (TY.level n).derived.IsEquivalence)
    (qZ : StrictEtaleTransportQuotient TZ) (qY : StrictEtaleTransportQuotient TY)
    (square : StrictEtaleInverseTransport TZ TY SA.properImage SB.properImage
      SA.properDerived.system SB.properDerived.system)
    (e : ∀ n, (TY.level n).derived ⋙ (SB.properDerived.level n).inverse ≅
      (SA.properDerived.level (index n)).inverse ⋙ (TZ.level n).derived)
    (he : ∀ n K,
      (SB.properDerived.level n).inverse.map ((TY.derivedEvaluation n).inv.app K) ≫
          (SB.properDerived.inverseEvaluation n).inv.app (TY.derived.obj K) ≫
          (SB.PZ.evaluation n).map (square.derived.hom.app K) =
        (e n).hom.app ((SA.PY.evaluation (index n)).obj K) ≫
          (TZ.level n).derived.map ((SA.properDerived.inverseEvaluation (index n)).inv.app K) ≫
          (TZ.derivedEvaluation n).inv.app (SA.properDerived.system.inverse.obj K))
    (hq : ∀ {m n : ℕ} (h : n ≤ m) K,
      (SB.properDerived.level n).inverse.map ((qY.derived h).hom.app K) ≫
          (SB.properDerived.derivedTensor h).hom.app ((TY.level m).derived.obj K) ≫
          (SB.PZ.scalar h).derived.map ((e m).hom.app K) =
        (e n).hom.app ((SA.PY.scalar (index.monotone h)).derived.obj K) ≫
          (TZ.level n).derived.map
            ((SA.properDerived.derivedTensor (index.monotone h)).hom.app K) ≫
          (qZ.derived h).hom.app ((SA.properDerived.level (index m)).inverse.obj K)) :
    ∃ (square : StrictEtaleInverseTransport TZ TY SA.properImage SB.properImage
        SA.properDerived.system SB.properDerived.system)
      (proper : SA.properDerived.system.direct ⋙ TY.derived ≅
        TZ.derived ⋙ SB.properDerived.system.direct)
      (level : ∀ n, (SA.properDerived.level (index n)).direct ⋙ (TY.level n).derived ≅
        (TZ.level n).derived ⋙ (SB.properDerived.level n).direct),
      (proper.hom =
        (mateEquiv SA.properDerived.system.adjunction SB.properDerived.system.adjunction
          (.mk _ _ _ _ square.derived.hom)).natTrans) ∧
      (∀ n K,
        (TY.derivedEvaluation n).hom.app (SA.properDerived.system.direct.obj K) ≫
            (TY.level n).derived.map ((SA.properDerived.directEvaluation (index n)).hom.app K) ≫
            (level n).hom.app ((SA.PZ.evaluation (index n)).obj K) =
          (SB.PY.evaluation n).map (proper.hom.app K) ≫
            (SB.properDerived.directEvaluation n).hom.app (TZ.derived.obj K) ≫
            (SB.properDerived.level n).direct.map ((TZ.derivedEvaluation n).hom.app K)) ∧
      (∀ (QA : StrictEtaleQuotientProjection SA) (QB : StrictEtaleQuotientProjection SB)
          {m n : ℕ} (h : n ≤ m) K,
        (SB.properDerived.level n).direct.map ((qZ.derived h).hom.app K) ≫
            (QB.proper h).hom.app ((TZ.level m).derived.obj K) ≫
            (SB.PY.scalar h).derived.map ((level m).inv.app K) =
          (level n).inv.app ((SA.PZ.scalar (index.monotone h)).derived.obj K) ≫
            (TY.level n).derived.map ((QA.proper (index.monotone h)).hom.app K) ≫
            (qY.derived h).hom.app ((SA.properDerived.level (index m)).direct.obj K)) := by
  have hi (n : ℕ) : IsIso
      (mateEquiv (SA.properDerived.level (index n)).adjunction
        (SB.properDerived.level n).adjunction (.mk _ _ _ _ (e n).hom)).natTrans := by
    let := hTZ n
    let := hTY n
    exact isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
      (SA.properDerived.level (index n)).adjunction
      (SB.properDerived.level n).adjunction (TY.level n).derived (TZ.level n).derived (e n)
  let level n : (SA.properDerived.level (index n)).direct ⋙ (TY.level n).derived ≅
      (TZ.level n).derived ⋙ (SB.properDerived.level n).direct :=
    asIso (mateEquiv (SA.properDerived.level (index n)).adjunction
      (SB.properDerived.level n).adjunction (.mk _ _ _ _ (e n).hom)).natTrans
  let M := (mateEquiv SA.properDerived.system.adjunction SB.properDerived.system.adjunction
    (.mk _ _ _ _ square.derived.hom)).natTrans
  have heval (n : ℕ) (K) :
      (TY.derivedEvaluation n).hom.app (SA.properDerived.system.direct.obj K) ≫
          (TY.level n).derived.map ((SA.properDerived.directEvaluation (index n)).hom.app K) ≫
          (level n).hom.app ((SA.PZ.evaluation (index n)).obj K) =
        (SB.PY.evaluation n).map (M.app K) ≫
          (SB.properDerived.directEvaluation n).hom.app (TZ.derived.obj K) ≫
          (SB.properDerived.level n).direct.map ((TZ.derivedEvaluation n).hom.app K) := by
    exact mate_evaluation SA.properDerived.system.adjunction SB.properDerived.system.adjunction
      (SA.properDerived.level (index n)).adjunction (SB.properDerived.level n).adjunction
      TY.derived TZ.derived (TY.level n).derived (TZ.level n).derived
      (SA.PY.evaluation (index n)) (SA.PZ.evaluation (index n))
      (SB.PY.evaluation n) (SB.PZ.evaluation n)
      (SA.properDerived.inverseEvaluation (index n))
      (SA.properDerived.directEvaluation (index n))
      (SB.properDerived.inverseEvaluation n) (SB.properDerived.directEvaluation n)
      (TY.derivedEvaluation n) (TZ.derivedEvaluation n) square.derived.hom (e n).hom
      (SA.properDerived.counit (index n)) (SB.properDerived.counit n) (he n) K
  have hm (K) : IsIso (M.app K) := by
    apply evaluation_detectsIso SB.PY
    intro n
    let t := (SB.properDerived.directEvaluation n).hom.app (TZ.derived.obj K) ≫
      (SB.properDerived.level n).direct.map ((TZ.derivedEvaluation n).hom.app K)
    have : IsIso ((SB.PY.evaluation n).map (M.app K) ≫ t) := by
      rw [show (SB.PY.evaluation n).map (M.app K) ≫ t =
        (TY.derivedEvaluation n).hom.app (SA.properDerived.system.direct.obj K) ≫
          (TY.level n).derived.map ((SA.properDerived.directEvaluation (index n)).hom.app K) ≫
          (level n).hom.app ((SA.PZ.evaluation (index n)).obj K) from (heval n K).symm]
      infer_instance
    exact IsIso.of_isIso_comp_right _ t
  let : IsIso M := NatIso.isIso_of_isIso_app M
  let proper := asIso M
  refine ⟨square, proper, level, rfl, heval, ?_⟩
  intro QA QB m n h K
  exact mate_quotient
    (SA.properDerived.level (index m)).adjunction (SB.properDerived.level m).adjunction
    (SA.properDerived.level (index n)).adjunction (SB.properDerived.level n).adjunction
    (TY.level m).derived (TZ.level m).derived (TY.level n).derived (TZ.level n).derived
    (SA.PY.scalar (index.monotone h)).derived (SA.PZ.scalar (index.monotone h)).derived
    (SB.PY.scalar h).derived (SB.PZ.scalar h).derived
    (SA.properDerived.derivedTensor (index.monotone h)) (QA.proper (index.monotone h))
    (SB.properDerived.derivedTensor h) (QB.proper h)
    (qY.derived h) (qZ.derived h) (e m) (e n) (level m) (level n)
    (QA.proper_mate (index.monotone h)) (QB.proper_mate h) rfl rfl (hq h) K

/-- The proper-direct-image face of coefficient transport, with evaluation and
its quotient square. Only the proper part of the compactification is involved.
Source: Zheng, Construction 5.15, Lemma 5.16 and Lemma 5.22.
(blueprint: lem-pur-strict-etale-proper-projection-faces).

Proof: form the ordinary inverse-image/scalar comparison, normalized by tensor
units, at every coefficient stage. Its unit characterization and the transition
normalizations make it a comparison of strict systems. Localize this exact square
using the specified factorization isomorphisms. Take its mate under the proper
inverse/direct adjunctions. The finite-level mates are invertible because the two
vertical scalar functors are equivalences. The supplied evaluation counit equation
identifies the mate of each inverse-evaluation comparison with direct evaluation.
Apply the exchange-mate cube to the inverse-image evaluation cube; this gives the
displayed direct-evaluation equation. Ordinary evaluations jointly reflect
isomorphisms by componentwise inversion, and the existing exact-derived reflection
theorem transfers this to the specified derived evaluations. Thus the system mate
is invertible. For the quotient cube, the ordinary scalar/inverse-image
squares commute by their tensor units and the coefficient generator square.
Their normalized derived counits give the derived inverse-image cube. Transpose
this cube under the proper adjunctions; the horizontal mates law and the triangle
identities give the displayed direct-image cube. QA and QB have precisely these
mates by their proper_mate equations, so the equation holds for all such records. -/
theorem nonempty_strictEtaleProperProjectionFaces
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
    (TY : StrictEtaleCoefficientTransport a Y SA.PY SB.PY)
    (hTZ : ∀ n, (TZ.level n).derived.IsEquivalence)
    (hTY : ∀ n, (TY.level n).derived.IsEquivalence)
    (qZ : StrictEtaleTransportQuotient TZ) (qY : StrictEtaleTransportQuotient TY) :
    ∃ (square : StrictEtaleInverseTransport TZ TY SA.properImage SB.properImage
        SA.properDerived.system SB.properDerived.system)
      (proper : SA.properDerived.system.direct ⋙ TY.derived ≅
        TZ.derived ⋙ SB.properDerived.system.direct)
      (level : ∀ n, (SA.properDerived.level (index n)).direct ⋙ (TY.level n).derived ≅
        (TZ.level n).derived ⋙ (SB.properDerived.level n).direct),
      (proper.hom =
        (mateEquiv SA.properDerived.system.adjunction SB.properDerived.system.adjunction
          (.mk _ _ _ _ square.derived.hom)).natTrans) ∧
      (∀ n K,
        (TY.derivedEvaluation n).hom.app (SA.properDerived.system.direct.obj K) ≫
            (TY.level n).derived.map ((SA.properDerived.directEvaluation (index n)).hom.app K) ≫
            (level n).hom.app ((SA.PZ.evaluation (index n)).obj K) =
          (SB.PY.evaluation n).map (proper.hom.app K) ≫
            (SB.properDerived.directEvaluation n).hom.app (TZ.derived.obj K) ≫
            (SB.properDerived.level n).direct.map ((TZ.derivedEvaluation n).hom.app K)) ∧
      (∀ (QA : StrictEtaleQuotientProjection SA) (QB : StrictEtaleQuotientProjection SB)
          {m n : ℕ} (h : n ≤ m) K,
        (SB.properDerived.level n).direct.map ((qZ.derived h).hom.app K) ≫
            (QB.proper h).hom.app ((TZ.level m).derived.obj K) ≫
            (SB.PY.scalar h).derived.map ((level m).inv.app K) =
          (level n).inv.app ((SA.PZ.scalar (index.monotone h)).derived.obj K) ≫
            (TY.level n).derived.map ((QA.proper (index.monotone h)).hom.app K) ≫
            (qY.derived h).hom.app ((SA.properDerived.level (index m)).direct.obj K)) := by
  classical
  choose finite finite_unit using
    (fun n ↦ strictEtaleFiniteOrdinaryInverseTransport a SA.properImage SB.properImage n)
  obtain ⟨ordinary, hn⟩ := nonempty_strictEtaleOrdinaryInverseTransport TZ TY
    SA.properImage SB.properImage finite finite_unit
  obtain ⟨derived, hd⟩ := inverseDerivedSquare TY.ordinary SA.properImage.inverse
    SB.properImage.inverse TZ.ordinary TY.derived SA.properDerived.system.inverse
    SB.properDerived.system.inverse TZ.derived TY.factors
    SA.properDerived.system.inverseFactors SB.properDerived.system.inverseFactors TZ.factors
    ordinary
  let square : StrictEtaleInverseTransport TZ TY SA.properImage SB.properImage
      SA.properDerived.system SB.properDerived.system := ⟨⟨ordinary, derived⟩, hn, hd⟩
  obtain ⟨e, he, hq⟩ := nonempty_strictEtaleDerivedInverseTransportFaces TZ TY
    SA.properImage SB.properImage SA.properDerived SB.properDerived qZ qY square
    (strictEtaleTransport_scalarCounit_isIso TZ) (strictEtaleTransport_scalarCounit_isIso TY)
  exact properProjectionFaces_of_inverse a c SA SB TZ TY hTZ hTY qZ qY square e he hq

end AlgebraicGeometry
