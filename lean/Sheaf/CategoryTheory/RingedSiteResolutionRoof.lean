/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
import Sheaf.CategoryTheory.Sites.DirectImageInjectiveEvaluationAcyclic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Mathlib.Algebra.Homology.ModelCategory.Injective
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import Mathlib.Algebra.Homology.Embedding.HomEquiv

/-! # Resolved direct-image cohomology roofs

Source: Stacks 01FD, 03AX, 03FC and 08J6.
(blueprint: lem-weil-pbc-ringed-site-resolution-roof)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

attribute [local instance] Functor.additive_of_preserves_binary_products

private theorem roof_lift
    {A : Type*} [Category* A] [Abelian A]
    {P Q I : CochainComplex A ℕ} (a : P ⟶ Q) [QuasiIso a]
    (ha : ∀ n, Mono (a.f n)) (hi : ∀ n, Injective (I.X n)) (g : P ⟶ I) :
    ∃ b : Q ⟶ I, a ≫ b = g := by
  classical
  let e := ComplexShape.embeddingUpNat
  let P' : CochainComplex.Plus A := ⟨P.extend e, 0, inferInstance⟩
  let Q' : CochainComplex.Plus A := ⟨Q.extend e, 0, inferInstance⟩
  let I' : CochainComplex.Plus A := ⟨I.extend e, 0, inferInstance⟩
  let a' : P' ⟶ Q' := ObjectProperty.homMk (HomologicalComplex.extendMap a e)
  let g' : P' ⟶ I' := ObjectProperty.homMk (HomologicalComplex.extendMap g e)
  let : ∀ n, Mono (a.f n) := ha
  let : Mono a := HomologicalComplex.mono_of_mono_f a ha
  have : Mono a' := by
    apply (CochainComplex.Plus.mono_iff a').2
    apply HomologicalComplex.mono_of_mono_f
    intro n
    by_cases hn : ∃ k : ℕ, e.f k = n
    · obtain ⟨k, rfl⟩ := hn
      change Mono ((HomologicalComplex.extendMap a e).f (e.f k))
      rw [HomologicalComplex.extendMap_f a e rfl]
      infer_instance
    · exact (P.isZero_extend_X e n (by simpa using hn)).mono _
  open scoped CochainComplex.Plus.modelCategoryQuillen in
  have : HomotopicalAlgebra.WeakEquivalence a' := by
    apply (CochainComplex.Plus.modelCategoryQuillen.weakEquivalence_iff a').2
    exact (HomologicalComplex.quasiIso_extendMap_iff a e).2 inferInstance
  let : ∀ n, Injective (I.X n) := hi
  open scoped CochainComplex.Plus.modelCategoryQuillen in
  have : HomotopicalAlgebra.IsFibrant I' :=
    (CochainComplex.Plus.modelCategoryQuillen.isFibrant_iff I').2 (fun _ ↦ inferInstance)
  let sq : CommSq g' a' (terminal.from I') (terminal.from Q') := ⟨by simp⟩
  open scoped CochainComplex.Plus.modelCategoryQuillen in
  have : sq.HasLift := by infer_instance
  let b := (e.extendFunctor A).preimage sq.lift.hom
  refine ⟨b, ?_⟩
  apply (e.extendFunctor A).map_injective
  rw [Functor.map_comp, Functor.map_preimage]
  exact congrArg (fun f ↦ f.hom) sq.fac_left

private theorem roof_homotopy
    {A : Type*} [Category* A] [Abelian A]
    {P Q I : CochainComplex A ℕ} (a : P ⟶ Q) [QuasiIso a]
    (hi : ∀ n, Injective (I.X n)) (f g : Q ⟶ I) (w : a ≫ f = a ≫ g) :
    Nonempty (Homotopy f g) := by
  let e := ComplexShape.embeddingUpNat
  let : ∀ n, Injective (I.X n) := hi
  have : QuasiIso (HomologicalComplex.extendMap a e) :=
    (HomologicalComplex.quasiIso_extendMap_iff a e).2 inferInstance
  obtain ⟨ht⟩ := CochainComplex.homotopy_of_comp_quasiIso_of_injective
    (I := I.extend e)
    ⟨0, fun n hn ↦ (CochainComplex.isStrictlyGE_iff (I.extend e) 0).1
      inferInstance n hn⟩
    (HomologicalComplex.extendMap a e)
    (HomologicalComplex.extendMap f e) (HomologicalComplex.extendMap g e)
    ⟨Homotopy.ofEq (by simp only [← HomologicalComplex.extendMap_comp, w])⟩
  exact ⟨ht.ofExtend⟩

private theorem roof_replacement
    {A : Type*} [Category* A] [Abelian A] [EnoughInjectives A]
    (P : CochainComplex A ℕ) :
    ∃ (I : CochainComplex A ℕ) (a : P ⟶ I),
      (∀ n, Injective (I.X n)) ∧ (∀ n, Mono (a.f n)) ∧ QuasiIso a := by
  classical
  let e := ComplexShape.embeddingUpNat
  obtain ⟨I, a, hzero, hi, hm, hq⟩ :=
    CochainComplex.exists_mono_quasiIso_injective_boundedBelow A 0 (P.extend e)
      (fun n hn ↦ (CochainComplex.isStrictlyGE_iff (P.extend e) 0).1
        inferInstance n hn)
  let L := I.restriction e
  have hlift : e.HasLift (𝟙 L) := by
    intro j hj i' hij
    have hn : i' < 0 := by
      by_contra hn
      exact hj.notMem hij i'.toNat (by
        simpa [e] using Int.toNat_of_nonneg (by omega : 0 ≤ i'))
    exact (hzero i' hn).eq_of_src _ _
  let c : I ⟶ L.extend e := e.liftExtend (𝟙 L) hlift
  have hc' (n : ℤ) : IsIso (c.f n) := by
    by_cases hn : ∃ k : ℕ, (k : ℤ) = n
    · obtain ⟨k, rfl⟩ := hn
      dsimp [c]
      rw [e.liftExtend_f _ _ (show e.f k = (k : ℤ) from rfl)]
      infer_instance
    · have hn' : n < 0 := by
        by_contra hn'
        exact hn ⟨n.toNat, Int.toNat_of_nonneg (by omega)⟩
      exact IsZero.isIso (hzero n hn')
        (L.isZero_extend_X e n (by simpa [e] using hn)) _
  let : ∀ n, IsIso (c.f n) := hc'
  have hc : IsIso c := HomologicalComplex.Hom.isIso_of_components c
  let b := (e.extendFunctor A).preimage (a ≫ c)
  have hb : HomologicalComplex.extendMap b e = a ≫ c :=
    (e.extendFunctor A).map_preimage _
  have hbmono (n : ℕ) : Mono (b.f n) := by
    have hcmono : Mono ((a ≫ c).f (n : ℤ)) := by
      have := hm (n : ℤ)
      have : IsIso (c.f (n : ℤ)) := by infer_instance
      simp only [HomologicalComplex.comp_f]
      infer_instance
    rw [← hb] at hcmono
    change Mono ((HomologicalComplex.extendMap b e).f (e.f n)) at hcmono
    rw [HomologicalComplex.extendMap_f b e rfl] at hcmono
    simpa only [Category.assoc, mono_comp_iff_of_isIso,
      mono_comp_iff_of_mono] using hcmono
  have : QuasiIso (HomologicalComplex.extendMap b e) := by
    rw [hb]
    let := hq
    infer_instance
  exact ⟨L, b, fun n ↦ hi (n : ℤ), hbmono,
    (HomologicalComplex.quasiIso_extendMap_iff b e).1 this⟩

private theorem roof_abstract
    {A B T : Type*} [Category* A] [Category* B] [Category* T]
    [Abelian A] [Abelian B] [Abelian T] [EnoughInjectives A] [EnoughInjectives B]
    (E : B ⥤ A) [E.Additive] (F : A ⥤ T) [F.Additive] [PreservesFiniteLimits F]
    (hacyc : ∀ (I : B) [Injective I], F.rightAcyclic (E.obj I))
    (M : A) (N : B) (h : M ⟶ E.obj N) (q : ℕ) :
    ∃ hH : (F.rightDerived q).obj M ⟶ ((E ⋙ F).rightDerived q).obj N,
      (∀ (IM : InjectiveResolution M) (IN : InjectiveResolution N),
        ∃ (L : CochainComplex A ℕ)
          (lam : (E.mapHomologicalComplex (.up ℕ)).obj IN.cocomplex ⟶ L)
          (b : IM.cocomplex ⟶ L),
          (∀ n, Injective (L.X n)) ∧ (∀ n, Mono (lam.f n)) ∧ QuasiIso lam ∧
          IM.ι.f 0 ≫ b.f 0 = h ≫ E.map (IN.ι.f 0) ≫ lam.f 0) ∧
      (∀ (IM : InjectiveResolution M) (IN : InjectiveResolution N)
        (L : CochainComplex A ℕ)
        (lam : (E.mapHomologicalComplex (.up ℕ)).obj IN.cocomplex ⟶ L)
        (b : IM.cocomplex ⟶ L),
        (∀ n, Injective (L.X n)) → (∀ n, Mono (lam.f n)) → QuasiIso lam →
        IM.ι.f 0 ≫ b.f 0 = h ≫ E.map (IN.ι.f 0) ≫ lam.f 0 →
        IsIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map lam) q) ∧
        hH ≫ (IN.isoRightDerivedObj (E ⋙ F) q).hom ≫
            HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map lam) q =
          (IM.isoRightDerivedObj F q).hom ≫
            HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map b) q) := by
  classical
  let EC := E.mapHomologicalComplex (.up ℕ)
  let FC := F.mapHomologicalComplex (.up ℕ)
  let H := FC ⋙ HomologicalComplex.homologyFunctor T (.up ℕ) q
  have hex (IM : InjectiveResolution M) (IN : InjectiveResolution N) :
      ∃ (L : CochainComplex A ℕ) (lam : EC.obj IN.cocomplex ⟶ L)
        (b : IM.cocomplex ⟶ L),
        (∀ n, Injective (L.X n)) ∧ (∀ n, Mono (lam.f n)) ∧ QuasiIso lam ∧
        IM.ι.f 0 ≫ b.f 0 = h ≫ E.map (IN.ι.f 0) ≫ lam.f 0 := by
    obtain ⟨L, lam, hi, hm, hq⟩ := roof_replacement (EC.obj IN.cocomplex)
    let g : (CochainComplex.single₀ A).obj M ⟶ L :=
      (CochainComplex.single₀ A).map h ≫
        (HomologicalComplex.singleMapHomologicalComplex E _ 0).inv.app N ≫
        EC.map IN.ι ≫ lam
    obtain ⟨b, hb⟩ := roof_lift IM.ι (fun _ ↦ inferInstance) hi g
    refine ⟨L, lam, b, hi, hm, hq, ?_⟩
    have hw := congrArg (fun f ↦ f.f 0) hb
    simpa [g, EC] using hw
  have hiso (IN : InjectiveResolution N) (L : CochainComplex A ℕ)
      (lam : EC.obj IN.cocomplex ⟶ L) (hi : ∀ n, Injective (L.X n))
      (hq : QuasiIso lam) : IsIso (H.map lam) := by
    let := hq
    let : ∀ n, Injective (L.X n) := hi
    have := F.quasiIso_map_of_rightAcyclic_nat lam
      (fun n ↦ hacyc (IN.cocomplex.X n))
      (fun n ↦ Functor.rightAcyclic_of_injective (L.X n))
    change IsIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map lam) q)
    infer_instance
  let IM₀ := injectiveResolution M
  let IN₀ := injectiveResolution N
  obtain ⟨L₀, lam₀, b₀, hi₀, hm₀, hq₀, hw₀⟩ := hex IM₀ IN₀
  let := hiso IN₀ L₀ lam₀ hi₀ hq₀
  let hH := (IM₀.isoRightDerivedObj F q).hom ≫ H.map b₀ ≫ inv (H.map lam₀) ≫
    (IN₀.isoRightDerivedObj (E ⋙ F) q).inv
  refine ⟨hH, hex, ?_⟩
  intro IM IN L lam b hi hm hq hw
  let := hiso IN L lam hi hq
  refine ⟨hiso IN L lam hi hq, ?_⟩
  let a := InjectiveResolution.desc (𝟙 N) IN₀ IN
  let s := InjectiveResolution.desc (𝟙 M) IM₀ IM
  let := hq
  obtain ⟨d, hd⟩ := roof_lift lam hm hi₀ (EC.map a ≫ lam₀)
  have hw' : IM.ι ≫ (b ≫ d) = IM.ι ≫ (s ≫ b₀) := by
    ext
    have hd₀ := congrArg (fun f ↦ f.f 0) hd
    have ha₀ := InjectiveResolution.desc_commutes_zero (𝟙 N) IN₀ IN
    have hs₀ := InjectiveResolution.desc_commutes_zero (𝟙 M) IM₀ IM
    change lam.f 0 ≫ d.f 0 = E.map (a.f 0) ≫ lam₀.f 0 at hd₀
    change IM.ι.f 0 ≫ (b.f 0 ≫ d.f 0) = IM.ι.f 0 ≫ (s.f 0 ≫ b₀.f 0)
    have ha₀' : IN.ι.f 0 ≫ a.f 0 = IN₀.ι.f 0 := by simp [a]
    have hs₀' : IM.ι.f 0 ≫ s.f 0 = IM₀.ι.f 0 := by simp [s]
    calc
      _ = (h ≫ E.map (IN.ι.f 0) ≫ lam.f 0) ≫ d.f 0 := by
        rw [← hw, Category.assoc]
      _ = h ≫ E.map (IN.ι.f 0 ≫ a.f 0) ≫ lam₀.f 0 := by
        rw [E.map_comp]
        simp only [Category.assoc, hd₀]
      _ = IM₀.ι.f 0 ≫ b₀.f 0 := by rw [ha₀', ← hw₀]
      _ = _ := by rw [← hs₀', Category.assoc]
  obtain ⟨ht⟩ := roof_homotopy IM.ι hi₀ (b ≫ d) (s ≫ b₀) hw'
  have heq : H.map b ≫ H.map d = H.map s ≫ H.map b₀ := by
    simpa only [H, Functor.comp_map, Functor.map_comp,
      HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap_comp]
      using (F.mapHomotopy ht).homologyMap_eq q
  have hdH : H.map lam ≫ H.map d = H.map (EC.map a) ≫ H.map lam₀ := by
    rw [← H.map_comp, hd, H.map_comp]
  have hs := InjectiveResolution.isoRightDerivedObj_hom_naturality
    (𝟙 M) IM IM₀ s (by simp [s]) F q
  have ha := InjectiveResolution.isoRightDerivedObj_hom_naturality
    (𝟙 N) IN IN₀ a (by simp [a]) (E ⋙ F) q
  simp only [Functor.map_id, Category.id_comp] at hs ha
  have ha' : (IN₀.isoRightDerivedObj (E ⋙ F) q).hom =
      (IN.isoRightDerivedObj (E ⋙ F) q).hom ≫ H.map (EC.map a) := ha
  have hs' : (IM₀.isoRightDerivedObj F q).hom =
      (IM.isoRightDerivedObj F q).hom ≫ H.map s := hs
  have hdIso : IsIso (H.map d) := by
    have : IsIso (H.map (EC.map a)) := by
      have : IsIso ((IN.isoRightDerivedObj (E ⋙ F) q).hom ≫ H.map (EC.map a)) := by
        rw [← ha']
        infer_instance
      exact IsIso.of_isIso_comp_left (IN.isoRightDerivedObj (E ⋙ F) q).hom _
    have : IsIso (H.map lam ≫ H.map d) := by rw [hdH]; infer_instance
    exact IsIso.of_isIso_comp_left (H.map lam) (H.map d)
  apply (cancel_mono (H.map d)).1
  change (hH ≫ (IN.isoRightDerivedObj (E ⋙ F) q).hom ≫ H.map lam) ≫ H.map d =
    ((IM.isoRightDerivedObj F q).hom ≫ H.map b) ≫ H.map d
  simp only [Category.assoc]
  rw [hdH, ← Category.assoc (IN.isoRightDerivedObj (E ⋙ F) q).hom,
    ← ha']
  simp only [hH, Category.assoc, Iso.inv_hom_id_assoc,
    IsIso.inv_hom_id, Category.comp_id]
  rw [heq, ← Category.assoc _ (H.map s) (H.map b₀), ← hs']

/-- The resolved-direct-image map exists with its normalization for every replacement.

Source: Stacks 013K, 013P, 013S and 08J6; steps 2, 4 and 8 of the refinement proof
(blueprint: lem-weil-pbc-ringed-site-resolution-roof).

Proof: Embed the termwise direct image of the target resolution into a nonnegative
injective complex by a monic quasi-isomorphism. Lift the source augmentation strictly
into this complex. Direct images of injectives are acyclic for evaluation, so Leray
acyclicity makes the replacement invertible after evaluation. Define the map by this
roof. For another replacement, lift its map along the first monic quasi-isomorphism;
the two source lifts are homotopic since they agree on the augmentation. Evaluation
preserves that homotopy, giving equality of the roofs. Source and target resolution
comparisons give the same equation by their canonical derived-functor isomorphisms.
This proves the asserted equation for every pair of resolutions and every replacement.
-/
theorem ringedSite_resolution_roof
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (u : C ⥤ D) [PreservesFiniteLimits u]
    (hcover : ∀ (Y : C) (S : Presieve Y), S ∈ J Y → S.map u ∈ K (u.obj Y))
    [u.IsContinuous J.toGrothendieck K.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    (R : Sheaf J.toGrothendieck RingCat.{u}) (R' : Sheaf K.toGrothendieck RingCat.{u})
    (ρ : R ⟶ (u.sheafPushforwardContinuous RingCat.{u}
      J.toGrothendieck K.toGrothendieck).obj R')
    [EnoughInjectives (ringedSiteModules.{u} R)]
    [EnoughInjectives (ringedSiteModules.{u} R')]
    (M : ringedSiteModules.{u} R) (N : ringedSiteModules.{u} R')
    (h : M ⟶ (SheafOfModules.pushforward.{u} ρ).obj N)
    {X : C} (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    (q : ℕ) :
    ∃ hH : (((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation
              Cᵒᵖ AddCommGrpCat.{u}).obj (op X)).rightDerived q).obj M ⟶ (((SheafOfModules.forget R'
              ⋙ PresheafOfModules.toPresheaf R'.obj) ⋙ (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op
              (u.obj X))).rightDerived q).obj N,
              (∀ (IM : InjectiveResolution M) (IN : InjectiveResolution N),
                ∃ (L : CochainComplex (ringedSiteModules.{u} R) ℕ)
                  (lam : ((SheafOfModules.pushforward.{u} ρ).mapHomologicalComplex (ComplexShape.up
                    ℕ)).obj IN.cocomplex ⟶ L)
                  (b : IM.cocomplex ⟶ L),
                  (∀ n : ℕ, Injective (L.X n)) ∧
                  (∀ n : ℕ, Mono (lam.f n)) ∧ QuasiIso lam ∧
                  IM.ι.f 0 ≫ b.f 0 = h ≫ (SheafOfModules.pushforward.{u} ρ).map (IN.ι.f 0) ≫ lam.f
                    0) ∧
              (∀ (IM : InjectiveResolution M) (IN : InjectiveResolution N)
                (L : CochainComplex (ringedSiteModules.{u} R) ℕ)
                (lam : ((SheafOfModules.pushforward.{u} ρ).mapHomologicalComplex (ComplexShape.up
                  ℕ)).obj IN.cocomplex ⟶ L)
                (b : IM.cocomplex ⟶ L),
                (∀ n : ℕ, Injective (L.X n)) →
                (∀ n : ℕ, Mono (lam.f n)) → QuasiIso lam →
                IM.ι.f 0 ≫ b.f 0 = h ≫ (SheafOfModules.pushforward.{u} ρ).map (IN.ι.f 0) ≫ lam.f 0 →
                IsIso (HomologicalComplex.homologyMap ((((SheafOfModules.forget R ⋙
                  PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
                  X)).mapHomologicalComplex (ComplexShape.up ℕ)).map lam) q) ∧
                hH ≫ (IN.isoRightDerivedObj ((SheafOfModules.forget R' ⋙
                  PresheafOfModules.toPresheaf R'.obj) ⋙ (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op
                  (u.obj X))) q).hom ≫
                  HomologicalComplex.homologyMap ((((SheafOfModules.forget R ⋙
                    PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
                    X)).mapHomologicalComplex (ComplexShape.up ℕ)).map lam) q =
                (IM.isoRightDerivedObj ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf
                  R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)) q).hom ≫
                  HomologicalComplex.homologyMap ((((SheafOfModules.forget R ⋙
                    PresheafOfModules.toPresheaf R.obj) ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op
                    X)).mapHomologicalComplex (ComplexShape.up ℕ)).map b) q) := by
  have _ := hX
  have _ := huX
  let E := SheafOfModules.pushforward.{u} ρ
  have : E.Additive := { map_add := rfl }
  let F := (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)
  have hacyc (I : ringedSiteModules.{u} R') [Injective I] :
      F.rightAcyclic (E.obj I) := by
    intro n
    exact ringedSite_directImage_injective_evaluation_isZero J K u hcover
      (fun _ _ _ _ _ _ _ _ ↦ inferInstance) R R' ρ I X (n + 1) (by omega)
  exact roof_abstract E F hacyc M N h q

end CategoryTheory
