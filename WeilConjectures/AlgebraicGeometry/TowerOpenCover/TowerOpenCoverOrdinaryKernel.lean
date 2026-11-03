/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverOrdinarySequence
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenComparison
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import all WeilConjectures.Algebra.Homology.SubterminalLocal.SubterminalModuleLocalCalculus
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.ProEtaleRingedOpenCoverReflectsIso

/-! The overlap kernel for a covering pair of geometric opens.
Source: current blueprint, tower-geometric Gluing and Levels paragraphs.
(blueprint: lem-dla1-tower-open-cover-ordinary-kernel).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.TowerOpenCover

private theorem support_comparison
    {C D D' : Type*} [Category* C] [Category* D] [Category* D']
    {L : D ⥤ C} {R : C ⥤ D} {L' : D' ⥤ C} {R' : C ⥤ D'}
    (a : L ⊣ R) (a' : L' ⊣ R') (e : D ≌ D') (d : R ⋙ e.functor ≅ R') :
    ∃ p : R ⋙ L ≅ R' ⋙ L', ∀ M,
      p.hom.app M ≫ a'.counit.app M = a.counit.app M := by
  let aTransport : e.inverse ⋙ L ⊣ R' := (e.symm.toAdjunction.comp a).ofNatIsoRight d
  let i := aTransport.leftAdjointUniq a'
  let p : R ⋙ L ≅ R' ⋙ L' :=
    Functor.isoWhiskerLeft R ((Functor.leftUnitor L).symm ≪≫
      Functor.isoWhiskerRight e.unitIso L ≪≫ Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight d (e.inverse ⋙ L) ≪≫
      Functor.isoWhiskerLeft R' i
  refine ⟨p, fun M ↦ ?_⟩
  have hi := aTransport.leftAdjointUniq_hom_app_counit a' M
  dsimp only [p, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.associator_hom_app]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  rw [hi]
  have hc : aTransport.counit.app M =
      L.map (e.inverse.map (d.inv.app M)) ≫
        L.map (e.unitIso.inv.app (R.obj M)) ≫ a.counit.app M := by
    simp only [aTransport, Adjunction.ofNatIsoRight_counit,
      Adjunction.comp_counit_app, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.comp_map]
    rfl
  rw [hc]
  simp only [Functor.comp_map]
  rw [← L.map_comp_assoc (e.inverse.map (d.hom.app M))
    (e.inverse.map (d.inv.app M))]
  simp only [← e.inverse.map_comp, Iso.hom_inv_id_app, e.inverse.map_id,
    L.map_id, Category.id_comp]
  rw [← L.map_comp_assoc, Iso.hom_inv_id_app, L.map_id, Category.id_comp]

private theorem finite_support_comparison {U X : Scheme.{u}}
    (A : Type u) [CommRing A] [Finite A] (j : U ⟶ X) [IsOpenImmersion j]
    (a : sfIntrinsicExtensionByZero j A ⊣ proEtaleConstantRingPullback A j) :
    ∃ p : proEtaleConstantRingPullback A j ⋙ sfIntrinsicExtensionByZero j A ≅
        SheafOfModules.SubterminalLocal.jstar.{u + 1, u, u + 1}
          (proEtaleConstantRing X A) (ProEt.mk j) ⋙
          SheafOfModules.SubterminalLocal.jbang.{u + 1, u, u + 1}
            (proEtaleConstantRing X A) (ProEt.mk j),
      ∀ M, p.hom.app M ≫
        (SheafOfModules.SubterminalLocal.adj.{u + 1, u, u + 1}
          (proEtaleConstantRing X A) (ProEt.mk j)).counit.app M = a.counit.app M := by
  let R := proEtaleConstantRing X A
  let R' := proEtaleConstantRing U A
  let c := proEtaleConstantRingComparison j A
  let Z := ProEt.mk j
  have : IsOpenImmersion Z.hom := inferInstanceAs (IsOpenImmersion j)
  obtain ⟨q, ⟨hq⟩⟩ := proEtale_ringed_open_comparison Z R
  let e := proEtaleScalarEquivalence U ((sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)
  obtain ⟨theta, _, _, htheta⟩ :=
    SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, u + 1} c
  let p : proEtaleConstantRingPullback A j ≅
      proEtaleModuleInverseImage j R ⋙ e.inverse := by
    unfold proEtaleConstantRingPullback proEtaleRingModulePullback
    exact NatIso.ofComponents (fun M ↦ theta ((proEtaleModuleInverseImage j R).obj M))
      (fun f ↦ htheta _ _ ((proEtaleModuleInverseImage j R).map f))
  let pR : proEtaleConstantRingPullback A j ⋙ e.functor ≅
      proEtaleModuleInverseImage j R :=
    Functor.isoWhiskerRight p e.functor ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ e.counitIso ≪≫ Functor.rightUnitor _
  let d : proEtaleConstantRingPullback A j ⋙ (e.trans q).functor ≅
      SheafOfModules.SubterminalLocal.jstar.{u + 1, u, u + 1} R Z :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight pR q.functor ≪≫ hq
  exact support_comparison a (SheafOfModules.SubterminalLocal.adj.{u + 1, u, u + 1} R Z)
    (e.trans q) d

private theorem ordinary_support_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)
    (M : SpTowerShriek.S l E X) :
    ∃ p : (SpTowerShriek.ev l E X n).obj ((ordinarySupport l E b o j).obj M) ≅
        (SheafOfModules.SubterminalLocal.jstar.{u + 1, u, u + 1}
          (proEtaleConstantRing X (SpTowerShriek.R l E n)) (ProEt.mk j) ⋙
          SheafOfModules.SubterminalLocal.jbang.{u + 1, u, u + 1}
            (proEtaleConstantRing X (SpTowerShriek.R l E n)) (ProEt.mk j)).obj
              ((SpTowerShriek.ev l E X n).obj M),
      p.hom ≫ (SheafOfModules.SubterminalLocal.adj.{u + 1, u, u + 1}
          (proEtaleConstantRing X (SpTowerShriek.R l E n)) (ProEt.mk j)).counit.app
            ((SpTowerShriek.ev l E X n).obj M) =
        (SpTowerShriek.ev l E X n).map ((o.openOp j).ordinaryAdjunction.counit.app M) := by
  let : Finite (SpTowerShriek.R l E n) := b.finite n
  obtain ⟨p, hp⟩ := finite_support_comparison (SpTowerShriek.R l E n) j
    (SpTowerShriek.finiteOpenAdjunction l E b j n)
  let pu := ((o.openOp j).evaluation n).app ((o.geometry j).pull.obj M)
  let pr := (sfIntrinsicExtensionByZero j (SpTowerShriek.R l E n)).mapIso
    (((o.openOp j).ordinaryPullEvaluation n).app M)
  let q := pu ≪≫ pr ≪≫ p.app ((SpTowerShriek.ev l E X n).obj M)
  refine ⟨q, ?_⟩
  dsimp only [q, Iso.trans_hom, Iso.app_hom]
  simp only [Category.assoc]
  rw [hp]
  apply (cancel_epi pu.inv).1
  rw [Iso.inv_hom_id_assoc]
  simpa only [pu, pr, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv] using
    ((o.openOp j).counit_evaluation n M).symm

private theorem signed_lift_comparison
    {C : Type*} [Category* C] [Abelian C]
    {W U V W' U' V' : C} (pW : W ≅ W') (pU : U ≅ U') (pV : V ≅ V')
    (x : W ⟶ U) (y : W ⟶ V) (x' : W' ⟶ U') (y' : W' ⟶ V')
    (hx : x ≫ pU.hom = pW.hom ≫ x') (hy : y ≫ pV.hom = pW.hom ≫ y') :
    pW.hom ≫ biprod.lift x' (-y') =
      biprod.lift x (-y) ≫ (biprod.mapIso pU pV).hom := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.mapIso_hom, biprod.map_fst,
      biprod.lift_fst, biprod.lift_fst_assoc]
    exact hx.symm
  · simp only [Category.assoc, biprod.mapIso_hom, biprod.map_snd,
      biprod.lift_snd, biprod.lift_snd_assoc, Preadditive.comp_neg, Preadditive.neg_comp]
    exact congrArg Neg.neg hy.symm


open SheafOfModules.SubterminalLocal

private def siteSequence {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {U V W : X.ProEt} (f : W ⟶ U) (g : W ⟶ V)
    (M : SheafOfModules.SubterminalLocal.Modules.{u + 1, u, u + 1} R) :
    ShortComplex (SheafOfModules.SubterminalLocal.Modules.{u + 1, u, u + 1} R) :=
  ShortComplex.mk (biprod.lift (nested.{u + 1, u, u + 1} R f M)
    (-nested.{u + 1, u, u + 1} R g M))
    (biprod.desc ((adj.{u + 1, u, u + 1} R U).counit.app M)
      ((adj.{u + 1, u, u + 1} R V).counit.app M)) (by
        simp only [biprod.lift_desc, Preadditive.neg_comp, nested_counit, add_neg_cancel])

private theorem site_supported_ext {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {U W : X.ProEt} (f : W ⟶ U) [Mono (terminal.from U)]
    (M D : SheafOfModules.SubterminalLocal.Modules.{u + 1, u, u + 1} R)
    (p : D ≅ (jbang.{u + 1, u, u + 1} R W).obj
      ((jstar.{u + 1, u, u + 1} R W).obj M))
    (t v : D ⟶ (jbang.{u + 1, u, u + 1} R U).obj
      ((jstar.{u + 1, u, u + 1} R U).obj M))
    (h : t ≫ (adj.{u + 1, u, u + 1} R U).counit.app M =
      v ≫ (adj.{u + 1, u, u + 1} R U).counit.app M) : t = v := by
  have hi := site_restricted_counit_isIso R f M
  let := hi
  apply (cancel_epi p.inv).mp
  apply ((adj.{u + 1, u, u + 1} R W).homEquiv _ _).injective
  apply (cancel_mono ((jstar.{u + 1, u, u + 1} R W).map
    ((adj.{u + 1, u, u + 1} R U).counit.app M))).mp
  have hp : (p.inv ≫ t) ≫ (adj.{u + 1, u, u + 1} R U).counit.app M =
      (p.inv ≫ v) ≫ (adj.{u + 1, u, u + 1} R U).counit.app M := by
    simpa only [Category.assoc] using congrArg (fun k ↦ p.inv ≫ k) h
  simpa only [Adjunction.homEquiv_naturality_right] using
    congrArg ((adj.{u + 1, u, u + 1} R W).homEquiv _ _) hp

private theorem open_subterminal {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Mono (terminal.from (ProEt.mk j)) := by
  constructor
  intro T a b _
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono j).1
  exact a.w.trans b.w.symm

private def open_intersection_product {W U V X : Scheme.{u}}
    (aU : W ⟶ U) (aV : W ⟶ V) (jU : U ⟶ X) (jV : V ⟶ X) (jW : W ⟶ X)
    [IsOpenImmersion aU] [IsOpenImmersion aV]
    [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion jW]
    (sq : IsPullback aU aV jU jV) (wU : aU ≫ jU = jW) (wV : aV ≫ jV = jW) :
    IsLimit (BinaryFan.mk (MorphismProperty.Over.homMk aU wU : ProEt.mk jW ⟶ ProEt.mk jU)
      (MorphismProperty.Over.homMk aV wV : ProEt.mk jW ⟶ ProEt.mk jV)) := by
  let lift (s : BinaryFan (ProEt.mk jU) (ProEt.mk jV)) : s.pt ⟶ ProEt.mk jW :=
    MorphismProperty.Over.homMk
      (sq.lift s.fst.left s.snd.left (s.fst.w.trans s.snd.w.symm)) (by
        change sq.lift s.fst.left s.snd.left _ ≫ jW = s.pt.hom
        rw [← wU, ← Category.assoc, sq.lift_fst]
        exact s.fst.w)
  refine BinaryFan.isLimitMk lift ?_ ?_ ?_
  · intro s
    apply MorphismProperty.Over.Hom.ext
    exact sq.lift_fst _ _ _
  · intro s
    apply MorphismProperty.Over.Hom.ext
    exact sq.lift_snd _ _ _
  · intro s m hm hn
    apply MorphismProperty.Over.Hom.ext
    apply sq.hom_ext
    · exact (congrArg (fun f ↦ f.left) hm).trans (sq.lift_fst _ _ _).symm
    · exact (congrArg (fun f ↦ f.left) hn).trans (sq.lift_snd _ _ _).symm

private theorem open_pair_cover {U V X : Scheme.{u}}
    (jU : U ⟶ X) (jV : V ⟶ X) [IsOpenImmersion jU] [IsOpenImmersion jV]
    (cover : Set.range jU ∪ Set.range jV = Set.univ) :
    Sieve.ofArrows (fun b : Bool ↦ if b then ProEt.mk jU else ProEt.mk jV)
      (fun b ↦ terminal.from (if b then ProEt.mk jU else ProEt.mk jV)) ∈
        (ProEt.topology X) (⊤_ X.ProEt) := by
  let Z : ULift.{u + 1} Bool → Scheme.{u} := fun i ↦ Bool.rec V U i.down
  let j : ∀ i, Z i ⟶ X := fun i ↦ by
    rcases i with ⟨i⟩
    cases i
    · exact jV
    · exact jU
  have (i : ULift.{u + 1} Bool) : IsOpenImmersion (j i) := by
    rcases i with ⟨i⟩
    cases i <;> dsimp [j, Z] <;> infer_instance
  have hc : ∀ x : X, ∃ (i : ULift.{u + 1} Bool) (v : Z i), (j i).base v = x := by
    intro x
    have hx : x ∈ Set.range jU ∪ Set.range jV := by rw [cover]; trivial
    rcases hx with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact ⟨⟨true⟩, v, hv⟩
    · exact ⟨⟨false⟩, v, hv⟩
  have ht := Scheme.RingedRestrictionExchange.opens_coverTop Z j hc
  have hb : (ProEt.topology X).CoversTop
      (fun b : Bool ↦ if b then ProEt.mk jU else ProEt.mk jV) := by
    intro T
    apply (ProEt.topology X).superset_covering _ (ht T)
    rintro Y f ⟨⟨i⟩, ⟨g⟩⟩
    cases i
    · exact ⟨false, ⟨g⟩⟩
    · exact ⟨true, ⟨g⟩⟩
  rw [Sieve.ofArrows_eq_ofObjects terminalIsTerminal]
  exact hb _

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem evaluation_jointly_faithful {X : Scheme.{u}}
    {M N : SpTowerShriek.S l E X} {a b : M ⟶ N}
    (hn : ∀ n : ℕ, (SpTowerShriek.ev l E X n).map a =
      (SpTowerShriek.ev l E X n).map b) : a = b := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  ext x
  exact congrArg (fun f ↦ f.val.app (op Z.unop.2) x) (hn Z.unop.1)

private theorem evaluation_jointly_isZero {X : Scheme.{u}} (M : SpTowerShriek.S l E X)
    (hn : ∀ n : ℕ, IsZero ((SpTowerShriek.ev l E X n).obj M)) : IsZero M := by
  apply (IsZero.iff_id_eq_zero M).mpr
  apply evaluation_jointly_faithful l E
  intro n
  let F := SpTowerShriek.ev l E X n
  calc
    F.map (𝟙 M) = 𝟙 (F.obj M) := F.map_id M
    _ = 0 := (hn n).eq_of_src (𝟙 _) 0
    _ = F.map (0 : M ⟶ M) := (F.map_zero M M).symm

private theorem evaluation_jointly_shortExact {X : Scheme.{u}}
    (S : ShortComplex (SpTowerShriek.S l E X))
    (hn : ∀ n : ℕ, (S.map (SpTowerShriek.ev l E X n)).ShortExact) : S.ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply S.exact_iff_isZero_homology.mpr
    apply evaluation_jointly_isZero l E
    intro n
    exact (((S.map (SpTowerShriek.ev l E X n)).exact_iff_isZero_homology.mp
      (hn n).exact).of_iso (S.mapHomologyIso (SpTowerShriek.ev l E X n)).symm)
  · constructor
    intro T a b hab
    apply evaluation_jointly_faithful l E
    intro n
    let := (hn n).mono_f
    apply (cancel_mono ((S.map (SpTowerShriek.ev l E X n)).f)).mp
    simpa only [ShortComplex.map_f, ShortComplex.map_g, Functor.map_comp] using
      congrArg (SpTowerShriek.ev l E X n).map hab
  · constructor
    intro T a b hab
    apply evaluation_jointly_faithful l E
    intro n
    let := (hn n).epi_g
    apply (cancel_epi ((S.map (SpTowerShriek.ev l E X n)).g)).mp
    simpa only [ShortComplex.map_f, ShortComplex.map_g, Functor.map_comp] using
      congrArg (SpTowerShriek.ev l E X n).map hab

variable (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)

/-- Local split exactness transported to the geometric strict-tower operations. -/
private theorem ordinarySequence_shortExact {W U V X : Scheme.{u}}
    (aU : W ⟶ U) (aV : W ⟶ V) (jU : U ⟶ X) (jV : V ⟶ X) (jW : W ⟶ X)
    [IsOpenImmersion aU] [IsOpenImmersion aV]
    [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion jW]
    (intersection : IsPullback aU aV jU jV)
    (wU : aU ≫ jU = jW) (wV : aV ≫ jV = jW)
    (cover : Set.range jU ∪ Set.range jV = Set.univ) (M : SpTowerShriek.S l E X) :
    (ordinarySequence l E b o aU aV jU jV jW wU wV M).ShortExact := by
  apply evaluation_jointly_shortExact l E
  intro n
  let F := SpTowerShriek.ev l E X n
  let R := proEtaleConstantRing X (SpTowerShriek.R l E n)
  obtain ⟨pU, hpU⟩ := ordinary_support_comparison l E b o jU n M
  obtain ⟨pV, hpV⟩ := ordinary_support_comparison l E b o jV n M
  obtain ⟨pW, hpW⟩ := ordinary_support_comparison l E b o jW n M
  let f : ProEt.mk jW ⟶ ProEt.mk jU := MorphismProperty.Over.homMk aU wU
  let g : ProEt.mk jW ⟶ ProEt.mk jV := MorphismProperty.Over.homMk aV wV
  let : Mono (terminal.from (ProEt.mk jU)) := open_subterminal jU
  let : Mono (terminal.from (ProEt.mk jV)) := open_subterminal jV
  let : Mono (terminal.from (ProEt.mk jW)) := open_subterminal jW
  let T := siteSequence R f g (F.obj M)
  have ht : T.ShortExact := site_cover_shortExact R f g
    (open_intersection_product aU aV jU jV jW intersection wU wV)
    (open_pair_cover jU jV cover) (F.obj M)
  have hu : F.map ((ordinaryAlpha l E b o aU jU jW wU).app M) ≫ pU.hom =
      pW.hom ≫ nested.{u + 1, u, u + 1} R f (F.obj M) := by
    apply site_supported_ext R f (F.obj M) _ pW
    rw [Category.assoc, hpU, ← F.map_comp, ordinaryAlpha_counit,
      Category.assoc, nested_counit, hpW]
  have hv : F.map ((ordinaryAlpha l E b o aV jV jW wV).app M) ≫ pV.hom =
      pW.hom ≫ nested.{u + 1, u, u + 1} R g (F.obj M) := by
    apply site_supported_ext R g (F.obj M) _ pW
    rw [Category.assoc, hpV, ← F.map_comp, ordinaryAlpha_counit,
      Category.assoc, nested_counit, hpW]
  have (A B : SpTowerShriek.S l E X) : PreservesBinaryBiproduct A B F :=
    preservesBinaryBiproduct_of_preservesBinaryProduct F
  let B := F.mapBiprod ((ordinarySupport l E b o jU).obj M)
    ((ordinarySupport l E b o jV).obj M)
  let q := B ≪≫ biprod.mapIso pU pV
  let S := ordinarySequence l E b o aU aV jU jV jW wU wV M
  have hb₁ : F.map S.f ≫ B.hom =
      biprod.lift (F.map ((ordinaryAlpha l E b o aU jU jW wU).app M))
        (-F.map ((ordinaryAlpha l E b o aV jV jW wV).app M)) := by
    simpa only [S, ordinarySequence, F.map_neg] using
      biprod.map_lift_mapBiprod F _ _
        ((ordinaryAlpha l E b o aU jU jW wU).app M)
        (-((ordinaryAlpha l E b o aV jV jW wV).app M))
  have hb₂ : B.inv ≫ F.map S.g =
      biprod.desc (F.map ((o.openOp jU).ordinaryAdjunction.counit.app M))
        (F.map ((o.openOp jV).ordinaryAdjunction.counit.app M)) := by
    exact biprod.mapBiprod_inv_map_desc F _ _ _ _
  have e : S.map F ≅ T := by
    refine ShortComplex.isoMk pW q (Iso.refl _) ?_ ?_
    · change pW.hom ≫ T.f = F.map S.f ≫ B.hom ≫ (biprod.mapIso pU pV).hom
      rw [← Category.assoc, hb₁]
      exact signed_lift_comparison pW pU pV
        (F.map ((ordinaryAlpha l E b o aU jU jW wU).app M))
        (F.map ((ordinaryAlpha l E b o aV jV jW wV).app M))
        (nested.{u + 1, u, u + 1} R f (F.obj M))
        (nested.{u + 1, u, u + 1} R g (F.obj M)) hu hv
    · change B.hom ≫ (biprod.mapIso pU pV).hom ≫ T.g = F.map S.g ≫ 𝟙 _
      simp only [Category.comp_id]
      apply (cancel_epi B.inv).mp
      rw [Iso.inv_hom_id_assoc, hb₂]
      apply biprod.hom_ext'
      · simpa only [T, siteSequence, biprod.mapIso_hom, Category.assoc,
          biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc] using hpU
      · simpa only [T, siteSequence, biprod.mapIso_hom, Category.assoc,
          biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc] using hpV
  exact ShortComplex.shortExact_of_iso e.symm ht

/-- The signed overlap is the kernel of the sum of counits for a covering pair.

Source: current blueprint, tower-geometric Gluing and Levels paragraphs;
Stacks Project, Tags 03DI--03DJ.
(blueprint: lem-dla1-tower-open-cover-ordinary-kernel).

Proof: Identify each finite geometric restriction with restriction to its open
subterminal on the ambient pro-etale site. Uniqueness of left adjoints identifies
support functors with the site extensions, with equality of the specified counits.
The actual scheme pullback gives the binary product cone, and the range-covering
hypothesis gives a binary covering sieve. On U the V component of the signed
intersection arrow and the U counit are invertible; on V the other two components
are invertible. Explicit biproduct retractions and sections split the restricted
short complexes. Joint detection on the cover reflects their exactness and the
mono and epi conditions. To compare nested arrows, restrict the U counit to W,
where it is invertible. The W adjunction then shows that maps from W-supported
objects to U-support are determined by their counit composites. The identity
ordinaryAlpha_counit therefore supplies the required comparison without any
extra compositor evaluation assumption. Coefficient evaluation is exact and jointly
faithful on strict towers, hence reflects zero homology, monos and epis. Thus the
ordinary sequence is short exact; take its exactness and monicity assertions.
All calculations allow empty, disjoint and repeated opens and the zero tower. -/
theorem ordinarySequence_kernel {W U V X : Scheme.{u}}
    (aU : W ⟶ U) (aV : W ⟶ V) (jU : U ⟶ X) (jV : V ⟶ X) (jW : W ⟶ X)
    [IsOpenImmersion aU] [IsOpenImmersion aV]
    [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion jW]
    (intersection : IsPullback aU aV jU jV)
    (wU : aU ≫ jU = jW) (wV : aV ≫ jV = jW)
    (cover : Set.range jU ∪ Set.range jV = Set.univ) (M : SpTowerShriek.S l E X) :
    (ordinarySequence l E b o aU aV jU jV jW wU wV M).Exact ∧
      Mono (ordinarySequence l E b o aU aV jU jV jW wU wV M).f := by
  have h := ordinarySequence_shortExact l E b o aU aV jU jV jW
    intersection wU wV cover M
  exact ⟨h.exact, h.mono_f⟩

end AlgebraicGeometry.ProEtale.TowerOpenCover
