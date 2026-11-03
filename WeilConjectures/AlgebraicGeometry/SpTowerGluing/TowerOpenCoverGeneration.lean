/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverTriangle
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import all WeilConjectures.SixFunctors.Supporting.PullbackTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Finite-open-cover generation of constructible coefficient towers

Source: latest blueprint, tower-geometric Gluing paragraph.
(blueprint: lem-dla1-tower-finite-open-cover-generation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

/-- Pullback of an arbitrary finite constant coefficient ring preserves bounded
constructibility and the specified Tor interval. In particular it applies directly
to ell-power quotients, without changing the coefficient presentation.

Source: blueprint latest, sec-proetale-coefficients/sk-cor-pe-finite-tor-comparison/
lem-sf-pullback-tor-amplitude.proof.md; Stacks Tags 03D2, 0735 and 08FZ.
(blueprint: lem-sf-pullback-tor-amplitude).

Proof: descend the bounded constructible pro-etale complex through the finite-ring
intrinsic derived comparison. Exact etale inverse image preserves bounded
constructibility. The constant-ring comparison square identifies its realization
with the specified derived constant-ring pullback. Reflect the given Tor interval
through the comparison, pull a flat model back termwise, and reflect the same
interval back on X. Transport both conclusions along the comparison isomorphism.
The input finite-Tor witness is not used: the specified interval supplies one.
-/
private theorem finite_constant_pullback_bounds
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (A : Type u) [CommRing A] [Finite A] (f : X ⟶ Y)
    (K : proEtaleDerivedCategory Y A) (hK : spFiniteConstructibleTor Y A K)
    (a b : ℤ) (hTor : HasProEtaleTorAmplitude Y A K a b) :
    spFiniteConstructibleTor X A ((proEtaleConstantRingDerivedPullback A f).obj K) ∧
      HasProEtaleTorAmplitude X A ((proEtaleConstantRingDerivedPullback A f).obj K)
        a b := by
  classical
  let B := ULift.{u + 1, u} A
  let F := proEtaleConstantRingDerivedPullback A f
  obtain ⟨c, d, hcd, hvan⟩ := hK.1
  obtain ⟨L, ⟨eL⟩⟩ := ((finiteRing_constructibleDerived_origin Y A).2.2.1 K).mpr
    ⟨hK.2.1, c, d, hcd, hvan⟩
  have hbc := (etaleBounded_iff Y B L.obj).mp L.property
  let P := (Etale.upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.obj L.obj
  have hbcP : Etale.DerivedCategory.isBoundedConstructible B X P :=
    (etaleBounded_iff X B P).mpr (hbc.mapDerivedCategory_upperStar f)
  have hplus : DerivedCategory.TStructure.t.plus L.obj := hbc.1.1
  have hplusP : DerivedCategory.TStructure.t.plus P :=
    ((etaleBounded_iff X B P).mp hbcP).1.1
  have htL : Etale.DerivedCategory.hasTorAmplitudeIn B Y a b L.obj :=
    (comparison_tor_iff Y A a b hTor.1 L.obj hplus).mpr
      (torAmplitude_of_iso Y A eL.symm a b hTor)
  have htP : Etale.DerivedCategory.hasTorAmplitudeIn B X a b P := by
    apply Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
    exact (Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} B) X a b).prop_of_iso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} B) f).app L.obj)
      (Etale.torAmplitudeIn_leftDerivedUpperStar (ModuleCat.{u + 1} B) f a b
        (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp htL))
  let eP : (ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj P ≅
      F.obj K :=
    ((intrinsicDerivedComparisonPullbackIso f A).app L.obj).symm ≪≫ F.mapIso eL
  have himage := ((finiteRing_constructibleDerived_origin X A).2.2.1 (F.obj K)).mp
    ⟨⟨P, hbcP⟩, ⟨eP⟩⟩
  have ht : HasProEtaleTorAmplitude X A (F.obj K) a b :=
    torAmplitude_of_iso X A eP a b
      ((comparison_tor_iff X A a b hTor.1 P hplusP).mp htP)
  exact ⟨⟨himage.2, himage.1, a, b, ht⟩, ht⟩

private theorem finite_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L)
    (h : spFiniteConstructibleTor T A K) : spFiniteConstructibleTor T A L := by
  obtain ⟨⟨a, b, hab, hv⟩, hc, s, t, ht⟩ := h
  refine ⟨⟨a, b, hab, ?_⟩, ?_, s, t, torAmplitude_of_iso T A e s t ht⟩
  · intro i hi
    exact (hv i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm
  · intro i
    have hcons := hc i
    rw [proEtaleModuleRestriction_constructible_iff] at hcons ⊢
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction T A).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e)) hcons

private theorem finite_union_induction {ι Ω : Type*}
    [DistribLattice Ω] [OrderTop Ω] [OrderBot Ω]
    (Q : Ω → Prop) (hzero : Q ⊥)
    (hglue : ∀ V W, Q V → Q W → Q (V ⊓ W) → Q (V ⊔ W))
    (s : Finset ι) (U : ι → Ω)
    (h : ∀ t ⊆ s, t.Nonempty → Q (t.inf U)) : Q (s.sup U) := by
  classical
  induction s using Finset.induction_on generalizing U with
  | empty => simpa using hzero
  | @insert i s hi ih =>
    rw [Finset.sup_insert]
    apply hglue
    · simpa using h {i} (by simp) (Finset.singleton_nonempty i)
    · exact ih U (fun t ht hn ↦ h t (ht.trans (Finset.subset_insert _ _)) hn)
    · rw [Finset.sup_inf_distrib_left]
      apply ih (fun j ↦ U i ⊓ U j)
      intro t ht hn
      have h' := h (insert i t) (Finset.insert_subset_insert i ht)
        (Finset.insert_nonempty i t)
      have he : t.inf (fun j ↦ U i ⊓ U j) = U i ⊓ t.inf U := by
        change t.inf ((fun _ ↦ U i) ⊓ U) = _
        rw [Finset.inf_inf, Finset.inf_const hn]
      rw [he]
      simpa only [Finset.inf_insert] using h'

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

private theorem tower_pullback_ctf {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) (M : SpTowerCalculus.C l E b q Y) :
    spConstructibleTorTowers l E X (q.abelian X)
      ((SpTowerCalculus.etalePullback l E b o q f).obj M.obj) := by
  let := (q.abelian X).hasDerived
  let := (q.abelian Y).hasDerived
  let := b.realizationAdditive X
  let := b.realizationAdditive Y
  let RX := SpTowerCalculus.realization l E b X (q.abelian X)
  let RY := SpTowerCalculus.realization l E b Y (q.abelian Y)
  let F := SpTowerCalculus.etalePullback l E b o q f
  have ev_pull (n : ℕ) :
      (spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj (F.obj M.obj) ≅
        (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) f).obj
          ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj M.obj) :=
    ((SpTowerCalculus.levelComparison l E b q X n).app (F.obj M.obj)).symm ≪≫
      (SpTowerShriek.Ev l E X n).mapIso
        (RX.counitIso.app ((SpTowerShriek.pull l E b (o.geometry f)).obj
          (RY.functor.obj M.obj))) ≪≫
      ((o.geometry f).pullEvaluation n).app (RY.functor.obj M.obj) ≪≫
      (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) f).mapIso
        ((SpTowerCalculus.levelComparison l E b q Y n).app M.obj)
  obtain ⟨hfinite, a, d, s, t, had, hst, hbounds⟩ := M.property
  have hp (n : ℕ) := finite_constant_pullback_bounds (SpTowerShriek.R l E n) f
    ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj M.obj)
    (hfinite n) s t (hbounds n).2
  refine ⟨fun n ↦ finite_of_iso X _ (ev_pull n).symm (hp n).1,
    a, d, s, t, had, hst, ?_⟩
  intro n
  refine ⟨?_, torAmplitude_of_iso X _ (ev_pull n).symm s t (hp n).2⟩
  intro i hi
  let G := proEtaleConstantRingPullback (SpTowerShriek.R l E n) f
  have hz := G.map_isZero ((hbounds n).1 i hi)
  exact hz.of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso (ev_pull n) ≪≫
      ((G.mapDerivedCategoryHomologyFunctorIso i).app _).symm)

open CategoryTheory.Pretriangulated

private theorem two_open_generation {W U V X : Scheme.{u}}
    (aU : W ⟶ U) (aV : W ⟶ V) (jU : U ⟶ X) (jV : V ⟶ X) (jW : W ⟶ X)
    [IsOpenImmersion aU] [IsOpenImmersion aV]
    [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion jW]
    (intersection : IsPullback aU aV jU jV)
    (wU : aU ≫ jU = jW) (wV : aV ≫ jV = jW)
    (cover : Set.range jU ∪ Set.range jV = Set.univ)
    (P : ObjectProperty (SpTowerShriek.D l E X))
    [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
    (M : SpTowerShriek.D l E X)
    (hW : P ((TowerOpenCover.support l E b o jW).obj M))
    (hU : P ((TowerOpenCover.support l E b o jU).obj M))
    (hV : P ((TowerOpenCover.support l E b o jV).obj M)) : P M := by
  obtain ⟨δ, hδ, _⟩ := TowerOpenCover.tower_open_cover_triangle l E b o
    aU aV jU jV jW intersection wU wV cover
  have hsum : P (((TowerOpenCover.support l E b o jU).obj M) ⊞
      ((TowerOpenCover.support l E b o jV).obj M)) :=
    P.prop_of_iso (biprod.isoProd _ _).symm (P.prop_prod _ _ hU hV)
  exact P.ext_of_isTriangulatedClosed₃ _ (hδ M) hW hsum

private def extension_support_iso {A Z X : Scheme.{u}}
    (j : A ⟶ Z) (k : Z ⟶ X) (i : A ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion i]
    (w : j ≫ k = i)
    (M : spDerivedCoefficientTowers l E Z (q.abelian Z)) :
    (SpTowerCalculus.openExtension l E b o q i).obj
        ((SpTowerCalculus.etalePullback l E b o q j).obj M) ≅
      ((SpTowerShriek.openD l E b (o.openOp k)) ⋙
        (SpTowerCalculus.realization l E b X (q.abelian X)).inverse).obj
          ((TowerOpenCover.support l E b o j).obj
            ((SpTowerCalculus.realization l E b Z (q.abelian Z)).functor.obj M)) := by
  let RA := SpTowerCalculus.realization l E b A (q.abelian A)
  let RZ := SpTowerCalculus.realization l E b Z (q.abelian Z)
  let RX := SpTowerCalculus.realization l E b X (q.abelian X)
  let N := (SpTowerShriek.pull l E b (o.geometry j)).obj (RZ.functor.obj M)
  let e : SpTowerShriek.openD l E b (o.openOp j) ⋙
      SpTowerShriek.openD l E b (o.openOp k) ≅
        SpTowerShriek.openD l E b (o.openOp i) :=
    SpTowerCalculus.sequenceOpenComposition l E b o j k ≪≫
      eqToIso (by subst i; rfl)
  exact ((SpTowerShriek.openD l E b (o.openOp i)) ⋙ RX.inverse).mapIso
    (RA.counitIso.app N) ≪≫ RX.inverse.mapIso (e.symm.app N)

private theorem ordinary_zero_of_empty (X : Scheme.{u}) [IsEmpty X]
    (M : SpTowerShriek.S l E X) : IsZero M := by
  apply (IsZero.iff_id_eq_zero M).mpr
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  ext x
  let n := Z.unop.1
  let N := (SpTowerShriek.ev l E X n).obj M
  let R := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (proEtaleConstantRing X (SpTowerShriek.R l E n))
  let F := SheafOfModules.toSheaf.{u + 1} R
  have hN : IsZero (F.obj N) :=
    (Sheaf.isTerminalOfEqTop (Scheme.ProEt.topology_eq_top_of_isEmpty X) (F.obj N)).isZero
  have hzero : IsZero N := by
    apply (IsZero.iff_id_eq_zero N).mpr
    apply F.map_injective
    simpa only [F.map_id, F.map_zero] using hN.eq_of_src (𝟙 (F.obj N)) 0
  exact congrArg (fun f ↦ f.val.app (op Z.unop.2) x)
    (hzero.eq_of_src (𝟙 N) 0)

private theorem derived_zero_of_empty (X : Scheme.{u}) [IsEmpty X]
    (M : SpTowerShriek.D l E X) : IsZero M := by
  exact (DerivedCategory.isZero_iff M).2
    (fun i ↦ ordinary_zero_of_empty l E X ((DerivedCategory.homologyFunctor _ i).obj M))

private theorem open_union_generation (X : Scheme.{u}) [IsNoetherian X]
    (P : ObjectProperty (spDerivedCoefficientTowers l E X (q.abelian X)))
    [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
    (U V : X.Opens)
    (hU : ∀ M : SpTowerCalculus.C l E b q U.toScheme,
      P ((SpTowerCalculus.openExtension l E b o q U.ι).obj M.obj))
    (hV : ∀ M : SpTowerCalculus.C l E b q V.toScheme,
      P ((SpTowerCalculus.openExtension l E b o q V.ι).obj M.obj))
    (hW : ∀ M : SpTowerCalculus.C l E b q (U ⊓ V).toScheme,
      P ((SpTowerCalculus.openExtension l E b o q (U ⊓ V).ι).obj M.obj))
    (M : SpTowerCalculus.C l E b q (U ⊔ V).toScheme) :
    P ((SpTowerCalculus.openExtension l E b o q (U ⊔ V).ι).obj M.obj) := by
  let Z := U ⊔ V
  let := (q.abelian X).hasDerived
  let := b.realizationAdditive X
  let RZ := SpTowerCalculus.realization l E b Z.toScheme (q.abelian Z.toScheme)
  let RX := SpTowerCalculus.realization l E b X (q.abelian X)
  let jU := X.homOfLE (show U ≤ Z from le_sup_left)
  let jV := X.homOfLE (show V ≤ Z from le_sup_right)
  let jW := X.homOfLE (show U ⊓ V ≤ Z from inf_le_left.trans le_sup_left)
  let aU := X.homOfLE (show U ⊓ V ≤ U from inf_le_left)
  let aV := X.homOfLE (show U ⊓ V ≤ V from inf_le_right)
  let F := SpTowerShriek.openD l E b (o.openOp Z.ι) ⋙ RX.inverse
  let _ : F.CommShift ℤ := by
    change ((o.openOp Z.ι).extension.mapDerivedCategory ⋙
      (b.realization X).inverse.mapDerivedCategory).CommShift ℤ
    infer_instance
  have : F.IsTriangulated := by
    change ((o.openOp Z.ι).extension.mapDerivedCategory ⋙
      (b.realization X).inverse.mapDerivedCategory).IsTriangulated
    infer_instance
  let Q := P.inverseImage F
  have hlocal (A : X.Opens) (hA : A ≤ Z)
      (ha : ∀ N : SpTowerCalculus.C l E b q A.toScheme,
        P ((SpTowerCalculus.openExtension l E b o q A.ι).obj N.obj)) :
      Q ((TowerOpenCover.support l E b o (X.homOfLE hA)).obj (RZ.functor.obj M.obj)) := by
    let j := X.homOfLE hA
    let N : SpTowerCalculus.C l E b q A.toScheme :=
      ⟨(SpTowerCalculus.etalePullback l E b o q j).obj M.obj,
        tower_pullback_ctf l E b o q j M⟩
    exact P.prop_of_iso (extension_support_iso l E b o q j Z.ι A.ι
      (by simp [j]) M.obj) (ha N)
  have hc : Set.range jU ∪ Set.range jV = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    have hx : x.1 ∈ U ∨ x.1 ∈ V := x.2
    rcases hx with hx | hx
    · exact Or.inl ⟨⟨x.1, hx⟩, by apply Subtype.ext; simp [jU]⟩
    · exact Or.inr ⟨⟨x.1, hx⟩, by apply Subtype.ext; simp [jV]⟩
  exact two_open_generation l E b o aU aV jU jV jW
    (isPullback_opens_inf_le le_sup_left le_sup_right)
    (by simp [aU, jU, jW]) (by simp [aV, jV, jW]) hc Q (RZ.functor.obj M.obj)
    (hlocal (U ⊓ V) _ hW) (hlocal U _ hU) (hlocal V _ hV)

/-- A finite cover generates each uniformly constructible finite-Tor tower from
extensions by zero of constructible tests on its nonempty indexed intersections.
The triangulated subcategory is arbitrary: no representing pair or counit occurs.

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric/
`sk-prop-sp-tower-geometric-gluing.proof.md`, Gluing paragraph.
(blueprint: lem-dla1-tower-finite-open-cover-generation).

Proof: restriction to an open preserves the cohomological and Tor intervals and
constructibility levelwise. For a two-open cover the distinguished open-cover
triangle expresses a test tower as an extension of the sum of the two extended
restrictions by the shifted extended restriction to the intersection. A
triangulated subcategory contains this sum and the third vertex. Induct on the
number of opens, applying the same argument inside the union of the preceding
opens and its intersection with the last open. Successive extensions by zero
compose by their adjunction comparison; restriction along composite opens
composes by the inverse-image comparison. Consequently all resulting pieces
are extensions from the original indexed intersections. For an empty cover X
is empty. Its sheaf modules and derived towers are zero, which every strictly
full triangulated subcategory contains. This includes empty intersections,
repeated opens and zero test towers. -/
theorem tower_finite_open_cover_generation
    (X : Scheme.{u}) [IsNoetherian X] (a : ℕ) (U : Fin a → X.Opens) (hcover : iSup U = ⊤)
    (P : ObjectProperty (spDerivedCoefficientTowers l E X (q.abelian X)))
    [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
    (hlocal : ∀ (s : Finset (Fin a)), s.Nonempty →
      ∀ M : SpTowerCalculus.C l E b q (s.inf U).toScheme,
        P ((SpTowerCalculus.openExtension l E b o q (s.inf U).ι).obj M.obj))
    (M : SpTowerCalculus.C l E b q X) : P M.obj := by
  classical
  let := (q.abelian X).hasDerived
  let := b.realizationAdditive X
  let RX := SpTowerCalculus.realization l E b X (q.abelian X)
  let Q : X.Opens → Prop := fun V ↦
    ∀ N : SpTowerCalculus.C l E b q V.toScheme,
      P ((SpTowerCalculus.openExtension l E b o q V.ι).obj N.obj)
  have hbot : Q ⊥ := by
    intro N
    let V : X.Opens := ⊥
    let : IsEmpty V.toScheme := ⟨fun x ↦ x.2⟩
    let RV := SpTowerCalculus.realization l E b V.toScheme (q.abelian V.toScheme)
    let F := SpTowerShriek.openD l E b (o.openOp V.ι) ⋙ RX.inverse
    exact P.prop_of_isZero (F.map_isZero
      (derived_zero_of_empty l E V.toScheme (RV.functor.obj N.obj)))
  have hsup : Q (Finset.univ.sup U) :=
    finite_union_induction Q hbot
      (fun V W hV hW hVW N ↦ open_union_generation l E b o q X P V W hV hW hVW N)
      Finset.univ U (fun s _ hs ↦ hlocal s hs)
  have htop : Q ⊤ := by
    have hu : Finset.univ.sup U = ⊤ := by simpa [Finset.sup_eq_iSup] using hcover
    simpa only [hu] using hsup
  let V : X.Opens := ⊤
  let j := V.ι
  let RV := SpTowerCalculus.realization l E b V.toScheme (q.abelian V.toScheme)
  let N : SpTowerCalculus.C l E b q V.toScheme :=
    ⟨(SpTowerCalculus.etalePullback l E b o q j).obj M.obj,
      tower_pullback_ctf l E b o q j M⟩
  let K := (SpTowerShriek.pull l E b (o.geometry j)).obj (RX.functor.obj M.obj)
  let e : (SpTowerCalculus.openExtension l E b o q j).obj N.obj ≅
      RX.inverse.obj ((TowerOpenCover.support l E b o j).obj (RX.functor.obj M.obj)) :=
    (SpTowerShriek.openD l E b (o.openOp j) ⋙ RX.inverse).mapIso (RV.counitIso.app K)
  let _ : RX.inverse.CommShift ℤ := by
    change (b.realization X).inverse.mapDerivedCategory.CommShift ℤ
    infer_instance
  have : RX.inverse.IsTriangulated := by
    change (b.realization X).inverse.mapDerivedCategory.IsTriangulated
    infer_instance
  let P' := P.inverseImage RX.inverse
  have hj : P' ((TowerOpenCover.support l E b o j).obj (RX.functor.obj M.obj)) :=
    P.prop_of_iso e (htop N)
  have hM : P' (RX.functor.obj M.obj) :=
    two_open_generation l E b o (𝟙 _) (𝟙 _) j j j
      (IsPullback.of_horiz_isIso_mono ⟨by simp⟩) (by simp) (by simp)
      (by simp [j, V, Scheme.Opens.range_ι]) P' (RX.functor.obj M.obj) hj hj hj
  exact P.prop_of_iso (RX.unitIso.app M.obj).symm hM

end AlgebraicGeometry.ProEtale.SpTowerGluing
