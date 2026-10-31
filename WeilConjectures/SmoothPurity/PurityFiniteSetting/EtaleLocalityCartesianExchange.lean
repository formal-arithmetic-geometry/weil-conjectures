/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrdinaryCoefficientDualizingExchange
import WeilConjectures.AlgebraicGeometry.Etale.EtaleHorizontalDoubleCounit
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientLeftComparisonBaseChange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition
import WeilConjectures.AlgebraicGeometry.Tensor.TensorMateEtalePrecomp
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # Two source-locality maps through a common target-open restriction

Source: orientation-charts proof Step 3, equations (Lj) and (Lv).
Factor source locality by conjugating its compact-support comparison. The horizontal
double-counit formula factors each actual exchange through the same target factor.
Cancel the exact-pullback comparison, evaluate at the unit and apply the fixed
coefficient-unit identifications.
(blueprint: new-lem-pur-etale-locality-cartesian-exchange).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] Etale.upperStar Etale.rightDerivedUpperShriek
  Etale.rightDerivedUpperShriekAdjunction Functor.mapDerivedCategory
  Functor.rightDerivedFunctor conjugateIsoEquiv

private def rho (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : Etale.EtaleCompactSupportNormalization A)
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [QuasiCompact j]
    [HasCompactification j] :=
  conjugateIsoEquiv (Etale.rightDerivedUpperShriekAdjunction A j)
    (Etale.derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
      inferInstance) (Etale.etaleCanonicalCompactSupportComparison A j N).symm

private theorem locality_factor (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : Etale.EtaleCompactSupportNormalization A)
    {U X S : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [QuasiCompact j]
    [HasCompactification j]
    (f : X ⟶ S) [HasCompactification f] [HasCompactification (j ≫ f)]
    [QuasiCompact (j ≫ f)] :
    (Etale.tensorMateEtalePrecompLocalityIso A N j f).symm =
      finiteExceptionalComposition A j f ≪≫
        Functor.isoWhiskerLeft (Etale.rightDerivedUpperShriek A f) (rho A N j) := by
  have hc : Etale.rightDerivedLowerShriekIso A
      (HasCompactification.compactification j) = Iso.refl _ := by
    unfold Etale.rightDerivedLowerShriekIso
    rw [(Etale.unboundedEtaleCompactSupport_comparison_coherence A j).1]
  have hα := Etale.left_comparison_chosen A N j f
  have hd : Etale.etaleCanonicalCompactSupportComparison A j N =
      N.comparison j (HasCompactification.compactification j) := by
    unfold Etale.etaleCanonicalCompactSupportComparison
    rw [hc]
    exact Iso.refl_trans _
  rw [← hd] at hα
  apply Iso.ext
  simp only [Iso.symm_hom, Etale.tensorMateEtalePrecompLocalityIso, Iso.symm_inv,
    conjugateIsoEquiv_apply_hom]
  rw [hα]
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom]
  rw [← conjugateEquiv_comp _
    ((Etale.rightDerivedUpperShriekAdjunction A j).comp
      (Etale.rightDerivedUpperShriekAdjunction A f))]
  rw [conjugateEquiv_whiskerRight]
  simp only [finiteExceptionalComposition, rho, Functor.isoWhiskerLeft_hom,
    conjugateIsoEquiv_apply_hom, Iso.symm_hom]
  rw [AlgebraicGeometry.ProEtale.FiniteEtaleNormalization.derivedAdj_eq]

private theorem mateTransport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (a' : L' ⊣ R')
    {G G' : C ⥤ E} {H H' : D ⥤ F} (i : G ≅ G') (j : H ≅ H')
    (α : G ⋙ L' ⟶ L ⋙ H) :
    (mateEquiv a a' (TwoSquare.mk _ _ _ _
      (Functor.whiskerRight i.inv L' ≫ α ≫ Functor.whiskerLeft L j.hom))).natTrans =
      Functor.whiskerLeft R i.inv ≫
        (mateEquiv a a' (TwoSquare.mk _ _ _ _ α)).natTrans ≫
          Functor.whiskerRight j.hom R' := by
  ext K
  apply (a'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [a'.counit_naturality]
  rw [mateEquiv_counit]
  simp only [TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc]
  rw [← j.hom.naturality]
  have hm := mateEquiv_counit a a' (TwoSquare.mk _ _ _ _ α) K
  simpa only [TwoSquare.mk, TwoSquare.natTrans, Functor.id_obj,
    Functor.comp_obj, Category.assoc] using congrArg
    (fun z ↦ L'.map (i.inv.app (R.obj K)) ≫ z ≫ j.hom.app K) hm.symm


private theorem rawExchange_exact
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z T : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z] [IsNoetherian T]
    {f : X ⟶ Y} {r : Z ⟶ T} {i : T ⟶ Y} {j : Z ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification r] [QuasiCompact r]
    (sq : IsPullback j r f i) (K : Etale.DerivedCategoryModule A Y) :
    (Etale.rightDerivedUpperShriekBaseChangeMap A sq).app K ≫
        (Etale.rightDerivedUpperShriek A r).map
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) i).hom.app K) =
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) j).hom.app
        ((Etale.rightDerivedUpperShriek A f).obj K) ≫
        (Etale.etaleHorizontalCounitRightExchange A sq
          (Etale.rightDerivedUpperShriekAdjunction A f)
          (Etale.rightDerivedUpperShriekAdjunction A r)).app K := by
  let C := ModuleCat.{u + 1} A
  let cj := Etale.leftDerivedUpperStarIsoMapDerivedCategory C j
  let ci := Etale.leftDerivedUpperStarIsoMapDerivedCategory C i
  let B := Etale.rightDerivedLowerShriekBaseChangeMap A sq
  letI := Etale.isIso_rightDerivedLowerShriekBaseChangeMap A sq
  have ht := mateTransport (Etale.rightDerivedUpperShriekAdjunction A f)
    (Etale.rightDerivedUpperShriekAdjunction A r) cj ci (inv B)
  letI := (Etale.unboundedEtaleCompactSupport_baseChange A sq).1
  have hinv : inv (Etale.unboundedEtaleCompactSupportBaseChange A sq) =
      Functor.whiskerRight cj.inv _ ≫ inv B ≫ Functor.whiskerLeft _ ci.hom := by
    ext M
    apply (cancel_epi
      ((Etale.unboundedEtaleCompactSupportBaseChange A sq).app M)).mp
    simp only [NatIso.isIso_inv_app, IsIso.hom_inv_id]
    simp only [Etale.unboundedEtaleCompactSupportBaseChange,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc]
    dsimp only [C, cj, ci, B]
    simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, NatIso.isIso_inv_app,
      IsIso.hom_inv_id_assoc, Iso.inv_hom_id_app]
    rfl
  rw [← hinv] at ht
  have hh := NatTrans.congr_app ht K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hh
  apply (cancel_epi (cj.inv.app ((Etale.rightDerivedUpperShriek A f).obj K))).mp
  simp only [C, cj, Iso.inv_hom_id_app_assoc]
  simpa only [Etale.rightDerivedUpperShriekBaseChangeMap,
    Etale.etaleHorizontalCounitRightExchange, Etale.etaleHorizontalSupportBaseChangeIso,
    asIso_inv, C, cj, ci, B, TwoSquare.natTrans] using hh.symm

private def excCongr (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [HasCompactification f] [HasCompactification g] (w : f = g) :
    Etale.rightDerivedUpperShriek A f ≅ Etale.rightDerivedUpperShriek A g :=
  eqToIso (by cases w; rfl)

private theorem congr_conjugate (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [HasCompactification f] [HasCompactification g] (w : f = g) :
    excCongr A w = conjugateIsoEquiv
      (Etale.rightDerivedUpperShriekAdjunction A f)
      (Etale.rightDerivedUpperShriekAdjunction A g)
      (Etale.unboundedEtaleLowerShriekCongr A w).symm := by
  subst g
  apply Iso.ext
  simp only [excCongr, eqToIso_refl, conjugateIsoEquiv_apply_hom,
    Etale.unboundedEtaleLowerShriekCongr, Iso.symm_hom, Iso.refl_inv, Iso.refl_hom,
    conjugateEquiv_id]

private theorem lowerCongr_symm (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [HasCompactification f] [HasCompactification g] (w : f = g) :
    (Etale.unboundedEtaleLowerShriekCongr A w).inv =
      (Etale.unboundedEtaleLowerShriekCongr A w.symm).hom := by
  subst w
  rfl

private theorem exact_locality_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : Etale.EtaleCompactSupportNormalization A)
    {X Y Z T : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z] [IsNoetherian T]
    {f : X ⟶ Y} {r : Z ⟶ T} {i : T ⟶ Y} {j : Z ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType r] [HasCompactification f] [HasCompactification r]
    [QuasiCompact r] [Etale i] [IsSeparated i] [QuasiCompact i]
    [Etale j] [IsSeparated j] [QuasiCompact j]
    [HasCompactification i] [HasCompactification j]
    [HasCompactification (j ≫ f)] [HasCompactification (r ≫ i)]
    (sq : IsPullback j r f i) :
    Etale.etaleHorizontalCounitRightExchange A sq
        (Etale.rightDerivedUpperShriekAdjunction A f)
        (Etale.rightDerivedUpperShriekAdjunction A r) =
      ((Etale.tensorMateEtalePrecompLocalityIso A N j f) ≪≫
        excCongr A sq.w ≪≫ finiteExceptionalComposition A r i ≪≫
        Functor.isoWhiskerRight (rho A N i) (Etale.rightDerivedUpperShriek A r)).hom := by
  let cs : ChosenCartesianSquare j r f i :=
    { toCommSq := sq.toCommSq
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd }
  have hd := Etale.etaleHorizontalDoubleCounit_compositors A cs N
    (Etale.rightDerivedUpperShriekAdjunction A f)
    (Etale.rightDerivedUpperShriekAdjunction A r)
    (Etale.rightDerivedUpperShriekAdjunction A i)
    (Etale.rightDerivedUpperShriekAdjunction A j)
    (Etale.rightDerivedUpperShriekAdjunction A (j ≫ f))
  have hex := Etale.etaleHorizontalDoubleCounit_exchange A cs N
    (Etale.rightDerivedUpperShriekAdjunction A f)
    (Etale.rightDerivedUpperShriekAdjunction A r)
  have hx : conjugateIsoEquiv
      (Etale.rightDerivedUpperShriekAdjunction A (j ≫ f))
      ((Etale.rightDerivedUpperShriekAdjunction A r).comp
        (Etale.rightDerivedUpperShriekAdjunction A i))
      (Etale.unboundedEtaleLowerShriekCompIso A r i ≪≫
        (Etale.unboundedEtaleLowerShriekCongr A sq.w).symm) =
      excCongr A sq.w ≪≫ finiteExceptionalComposition A r i := by
    apply Iso.ext
    simp only [finiteExceptionalComposition, congr_conjugate,
      conjugateIsoEquiv_apply_hom, Iso.trans_hom, Iso.symm_hom]
    rw [lowerCongr_symm, conjugateEquiv_comp]
  rw [hx] at hd
  have hl := locality_factor A N j f
  have hi : (Etale.tensorMateEtalePrecompLocalityIso A N j f) =
      (Functor.isoWhiskerLeft (Etale.rightDerivedUpperShriek A f) (rho A N j)).symm ≪≫
        (finiteExceptionalComposition A j f).symm := by
    rw [← Iso.trans_symm, ← hl, Iso.symm_symm_eq]
  rw [hi]
  rw [← hex, hd]
  simp only [rho, finiteExceptionalComposition, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerLeft_hom]

private def sourceLocality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : Etale.EtaleCompactSupportNormalization A)
    {Z X S : Scheme.{u}} [IsNoetherian Z] [IsNoetherian X] [IsNoetherian S]
    (j : Z ⟶ X) (f : X ⟶ S)
    [Etale j] [IsSeparated j] [QuasiCompact j]
    [HasCompactification f] [HasCompactification (j ≫ f)] :=
  Functor.isoWhiskerLeft (Etale.rightDerivedUpperShriek A f)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j) ≪≫
    Etale.tensorMateEtalePrecompLocalityIso A N j f

private theorem excCongr_trans (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f g h : X ⟶ S}
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    (w : f = g) (w' : g = h) :
    excCongr A (w.trans w') = excCongr A w ≪≫ excCongr A w' := by
  cases w
  cases w'
  simp only [excCongr, eqToIso_refl, Iso.refl_trans]

private theorem raw_exchange_compare
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : Etale.EtaleCompactSupportNormalization A)
    {X Y Z S T : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [IsNoetherian S] [IsNoetherian T]
    {f : X ⟶ S} {g : Y ⟶ S} {i : T ⟶ S} {r : Z ⟶ T}
    {j : Z ⟶ X} {v : Z ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [LocallyOfFiniteType r] [QuasiCompact r]
    [Etale i] [IsSeparated i] [QuasiCompact i]
    [Etale j] [IsSeparated j] [QuasiCompact j]
    [Etale v] [IsSeparated v] [QuasiCompact v]
    [HasCompactification f] [HasCompactification g] [HasCompactification r]
    [HasCompactification i] [HasCompactification j] [HasCompactification v]
    [HasCompactification (j ≫ f)] [HasCompactification (v ≫ g)]
    [HasCompactification (r ≫ i)]
    (qj : IsPullback j r f i) (qv : IsPullback v r g i)
    (w : v ≫ g = j ≫ f) (K : Etale.DerivedCategoryModule A S) :
    (Etale.rightDerivedUpperShriekBaseChangeMap A qv).app K =
      (sourceLocality A N v g).hom.app K ≫ (excCongr A w).hom.app K ≫
      (sourceLocality A N j f).inv.app K ≫
      (Etale.rightDerivedUpperShriekBaseChangeMap A qj).app K := by
  let H := finiteExceptionalComposition A r i ≪≫
    Functor.isoWhiskerRight (rho A N i) (Etale.rightDerivedUpperShriek A r)
  have hj : (Etale.rightDerivedUpperShriekBaseChangeMap A qj).app K ≫
      (Etale.rightDerivedUpperShriek A r).map
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) i).hom.app K) =
      (sourceLocality A N j f).hom.app K ≫
        (excCongr A qj.w).hom.app K ≫ H.hom.app K := by
    rw [rawExchange_exact A qj, exact_locality_exchange A N qj]
    simp only [sourceLocality, H, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc]
  have hv : (Etale.rightDerivedUpperShriekBaseChangeMap A qv).app K ≫
      (Etale.rightDerivedUpperShriek A r).map
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) i).hom.app K) =
      (sourceLocality A N v g).hom.app K ≫
        (excCongr A qv.w).hom.app K ≫ H.hom.app K := by
    rw [rawExchange_exact A qv, exact_locality_exchange A N qv]
    simp only [sourceLocality, H, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc]
  have hc : (excCongr A w).hom.app K ≫ (excCongr A qj.w).hom.app K =
      (excCongr A qv.w).hom.app K := by
    exact (congrArg (fun e ↦ e.hom.app K) (excCongr_trans A w qj.w)).symm
  apply (cancel_mono ((Etale.rightDerivedUpperShriek A r).map
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} A) i).hom.app K))).mp
  simp only [Category.assoc]
  rw [hj, hv]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hc]


private theorem unit_inv (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] : (OrientationCounit.unitChange P f).inv = 𝟙 _ := by
  unfold OrientationCounit.unitChange
  simp only [Functor.mapIso_inv, Iso.symm_inv]
  have hu : (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) Y).hom =
      𝟙 _ := by
    apply (cancel_mono
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) Y).inv).mp
    rw [Iso.hom_inv_id, Etale.singleFunctorObjUnitIso_inv]
    exact (Category.id_comp _).symm
  erw [hu, CategoryTheory.Functor.map_id]
  rfl


private theorem unit_hom (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] : (OrientationCounit.unitChange P f).hom = 𝟙 _ := by
  apply (cancel_mono (OrientationCounit.unitChange P f).inv).mp
  rw [Iso.hom_inv_id, unit_inv, Category.id_comp]
  rfl

private theorem excCongr_app (P : PurityFiniteSetting.{u})
    {Z S : Scheme.{u}} {f g : Z ⟶ S}
    [HasCompactification f] [HasCompactification g] (w : f = g) :
    (excCongr P.Coefficient w).app
        (𝟙_ (Etale.DerivedCategoryModule P.Coefficient S)) =
      P.diagonalDualizingCongr w := by
  subst g
  rfl

/-- Locality for two Cartesian presentations with the same target-open restriction.
Source: orientation-charts Step 3, horizontal double-counit normalization.

Proof in words: form the chosen Cartesian squares qj and qv from their canonical
pullback identifications. Apply etaleHorizontalDoubleCounit and its compositor
formula to each, with the same normalized compact-support datum N. Their single
counit equations identify B_j with source locality followed by the target-open
exceptional composition H, and B_v with source locality, equality comparison w,
and the same H. Naturality at the fixed unit isomorphism gives the
coefficient-unit equations. Solve the first equation for H using the source-locality isomorphism,
then substitute it into the second. This gives
B_v=L_v congr(w) L_j^{-1} B_j. No integration or affine counit occurs, and no
evaluation counit is cancelled. The argument includes empty schemes.
(blueprint: new-lem-pur-etale-locality-cartesian-exchange). -/
theorem etaleLocality_cartesian_exchange (P : PurityFiniteSetting.{u})
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    {X Y Z S T : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [IsNoetherian S] [IsNoetherian T]
    (f : X ⟶ S) (g : Y ⟶ S) (i : T ⟶ S) (r : Z ⟶ T)
    (j : Z ⟶ X) (v : Z ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsOpenImmersion i] [QuasiCompact i]
    [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [QuasiCompact r] [HasCompactification f] [HasCompactification g]
    [HasCompactification r] [HasCompactification (j ≫ f)]
    [HasCompactification (v ≫ g)]
    (qj : IsPullback j r f i) (qv : IsPullback v r g i)
    (w : v ≫ g = j ≫ f) :
    P.ordinaryCoefficientDualizingExchange qv =
      (P.diagonalEtaleLocality N v g).hom ≫ (P.diagonalDualizingCongr w).hom ≫
      (P.diagonalEtaleLocality N j f).inv ≫
      P.ordinaryCoefficientDualizingExchange qj := by
  letI : LocallyOfFiniteType r :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) qj inferInstance
  letI : IsSeparated r :=
    MorphismProperty.of_isPullback (P := @IsSeparated) qj inferInstance
  letI : HasCompactification i := inferInstance
  letI : HasCompactification j := inferInstance
  letI : HasCompactification v := inferInstance
  letI : HasCompactification (r ≫ i) := inferInstance
  have h := raw_exchange_compare P.Coefficient N qj qv w
    (𝟙_ (Etale.DerivedCategoryModule P.Coefficient S))
  have hraw := congrArg (fun z ↦ z ≫ (Etale.rightDerivedUpperShriek P.Coefficient r).map
    (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) i).hom) h
  have hj : (sourceLocality P.Coefficient N j f).app
      (𝟙_ (Etale.DerivedCategoryModule P.Coefficient S)) =
      P.diagonalEtaleLocality N j f := by rfl
  have hv : (sourceLocality P.Coefficient N v g).app
      (𝟙_ (Etale.DerivedCategoryModule P.Coefficient S)) =
      P.diagonalEtaleLocality N v g := by rfl
  have hw : (excCongr P.Coefficient w).app
      (𝟙_ (Etale.DerivedCategoryModule P.Coefficient S)) =
      P.diagonalDualizingCongr w := excCongr_app P w
  simp only [← Iso.app_hom, ← Iso.app_inv, hj, hv, hw] at hraw
  simpa only [ordinaryCoefficientDualizingExchange, unit_inv, unit_hom,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Etale.dualizingComplexBaseChangeMap, Category.assoc] using hraw

end WeilConjectures.PurityFiniteSetting
