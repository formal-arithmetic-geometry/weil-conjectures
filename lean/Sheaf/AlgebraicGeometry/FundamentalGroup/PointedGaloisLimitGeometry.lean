/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q141
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverConstruction
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import Mathlib.CategoryTheory.Limits.Final
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.OpenSubgroups

/-! # Geometry of the pointed Galois inverse limit

Source: Stacks Project 0BND, 0BN2, 01YX, 01YW, 01Z2, 01Z4, 097I and 097N
(blueprint: lem-sfb-pointed-galois-limit-geometry).

The scheme, its point and its projections are the published `UniversalCover` construction.
An equivalence with open normal subgroups chooses the indicated pointed covers without
introducing another limit. The affine rings and their structure map below are actual
section-ring diagrams and colimit maps.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite PreGaloisCategory

namespace AlgebraicGeometry.Scheme.UniversalCover

/-- The filtered diagram `N ↦ Γ(Y_N, p_N⁻¹ U)` on an affine base open, with the
transition pullbacks already constructed in `AffineOverLimit.diagram`.
Source: Stacks 01YX, 01YW
(blueprint: lem-sfb-pointed-galois-limit-geometry). -/
noncomputable abbrev normalSectionDiagram {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (G : ProfiniteGrp.{u}) (E : OpenNormalSubgroup G ≌ Index x)
    (U : X.AffineZariskiSite) : (OpenNormalSubgroup G)ᵒᵖ ⥤ CommRingCat.{u} :=
  E.functor.op ⋙ AffineOverLimit.diagram (diagram x) (p x) (map_p x) ⋙
    (CategoryTheory.evaluation _ _).obj (op U)

/-- The canonical map from the base ring to the displayed colimit: pull sections
back to the stage indexed by the whole group, then use its colimit inclusion.
Source: Stacks 01YX, 01YW, 097I
(blueprint: lem-sfb-pointed-galois-limit-geometry). -/
noncomputable def normalSectionAlgebraMap {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (G : ProfiniteGrp.{u}) (E : OpenNormalSubgroup G ≌ Index x)
    (U : X.AffineZariskiSite) : Γ(X, U.toOpens) ⟶ colimit (normalSectionDiagram x G E U) :=
  (p x (E.functor.obj ⟨⟨⊤, isOpen_univ⟩, inferInstance⟩)).app U.toOpens ≫
    colimit.ι (normalSectionDiagram x G E U) (op ⟨⟨⊤, isOpen_univ⟩, inferInstance⟩)

section Labels

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
  (G : ProfiniteGrp.{u})
  [∀ Y : X.FiniteEtale, MulAction G ((FiniteEtale.fiber x).obj Y)]
  [IsFundamentalGroup (FiniteEtale.fiber x) G]

attribute [local instance] FiniteEtale.fiberFunctor

private lemma normal_stabilizer (P : X.FiniteEtale) [IsGalois P]
    (a : (FiniteEtale.fiber x).obj P) : (MulAction.stabilizer G a).Normal where
  conj_mem n hn g := by
    rw [MulAction.mem_stabilizer_iff] at hn ⊢
    simp only [mul_smul]
    obtain ⟨φ, hφ⟩ := evaluation_aut_surjective_of_isGalois (FiniteEtale.fiber x) P a
      (g⁻¹ • a)
    calc
      g • n • (g⁻¹ • a) = g • n • ((FiniteEtale.fiber x).map φ.hom a) :=
        congrArg (fun b ↦ g • n • b) hφ.symm
      _ = g • ((FiniteEtale.fiber x).map φ.hom (n • a)) :=
        congrArg (g • ·) (IsNaturalSMul.naturality n φ.hom a).symm
      _ = g • ((FiniteEtale.fiber x).map φ.hom a) :=
        congrArg (fun b ↦ g • ((FiniteEtale.fiber x).map φ.hom b)) hn
      _ = g • (g⁻¹ • a) := congrArg (g • ·) hφ
      _ = a := smul_inv_smul g a

private lemma galois_of_normal_stabilizer (P : X.FiniteEtale) [IsConnected P]
    (a : (FiniteEtale.fiber x).obj P) (h : (MulAction.stabilizer G a).Normal) :
    IsGalois P := by
  apply (isGalois_iff_pretransitive (FiniteEtale.fiber x) P).mpr
  have hs (b : (FiniteEtale.fiber x).obj P) :
      MulAction.stabilizer G a = MulAction.stabilizer G b := by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G a b
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    let := h
    exact (Subgroup.Normal.map_conj_eq (MulAction.stabilizer G a) g).symm
  refine ⟨fun b c ↦ ?_⟩
  obtain ⟨e, he⟩ := (FiniteEtale.exists_iso_fiber_map_eq_iff x G P P b c).mpr
    ((hs b).symm.trans (hs c))
  exact ⟨e, he⟩

private noncomputable def stageSubgroup (j : Index x) : OpenNormalSubgroup G :=
  ⟨FiniteEtale.stabilizerOpenSubgroup x G ((obj x).obj j) (point x j),
    normal_stabilizer x G _ _⟩

private lemma subgroup_map_le {i j : Index x} (f : i ⟶ j) :
    stageSubgroup x G i ≤ stageSubgroup x G j := by
  intro g hg
  change g • point x j = point x j
  rw [← map_point x f, ← IsNaturalSMul.naturality]
  exact congrArg ((FiniteEtale.fiber x).map ((obj x).map f)) hg

private noncomputable def subgroupFunctor : Index x ⥤ OpenNormalSubgroup G where
  obj := stageSubgroup x G
  map f := homOfLE (subgroup_map_le x G f)

private lemma index_hom_subsingleton (i j : Index x) : Subsingleton (i ⟶ j) := by
  refine ⟨fun f g ↦ (indexEquiv x).fullyFaithfulInverse.map_injective ?_⟩
  apply PointedGaloisObject.hom_ext
  apply evaluation_injective_of_isConnected (FiniteEtale.fiber x)
    ((obj x).obj i) ((obj x).obj j) (point x i)
  exact (map_point x f).trans (map_point x g).symm

private lemma quotient_label (P : X.FiniteEtale) [IsConnected P]
    (a : (FiniteEtale.fiber x).obj P) (N : OpenNormalSubgroup G)
    (ha : MulAction.stabilizer G a = N.toSubgroup) :
    ∃ e : (FiniteEtale.fiber x).obj P ≃ G ⧸ N.toSubgroup,
      e a = QuotientGroup.mk (1 : G) ∧
      ∀ (g : G) b, e (g • b) = QuotientGroup.mk g * e b := by
  obtain ⟨e, he, hs⟩ := FiniteEtale.exists_equiv_of_stabilizer_eq G a
    (QuotientGroup.mk (1 : G) : G ⧸ N.toSubgroup)
    (ha.trans (MulAction.stabilizer_quotient N.toSubgroup).symm)
  refine ⟨e, he, fun g b ↦ ?_⟩
  rw [hs]
  induction e b using QuotientGroup.induction_on with | H k
  rfl

private lemma lift_equivariant {P Q : X.FiniteEtale}
    (f : (FiniteEtale.fiber x).obj P → (FiniteEtale.fiber x).obj Q)
    (hf : ∀ (g : G) a, f (g • a) = g • f a) :
    ∃ φ : P ⟶ Q, ∀ a, (FiniteEtale.fiber x).map φ a = f a := by
  let A := FiniteEtale.equivalenceContAction x G
  let ψ : (A.functor.obj P).obj ⟶ (A.functor.obj Q).obj :=
    { hom := FintypeCat.homMk f
      comm g := by
        ext a
        change f (((A.functor.obj P).obj.ρ g).hom a) =
          ((A.functor.obj Q).obj.ρ g).hom (f a)
        rw [FiniteEtale.equivalenceContAction_functor_obj_obj_ρ_apply,
          FiniteEtale.equivalenceContAction_functor_obj_obj_ρ_apply]
        exact hf g a }
  let φ := A.functor.preimage ((ObjectProperty.fullyFaithfulι _).preimage ψ)
  refine ⟨φ, fun a ↦ ?_⟩
  have hφ : (A.functor.map φ).hom.hom = (FiniteEtale.fiber x).map φ :=
    FiniteEtale.equivalenceContAction_functor_map_hom_hom x G φ
  rw [← hφ]
  change ((A.functor.map (A.functor.preimage _)).hom.hom) a = f a
  simp only [Functor.map_preimage]
  rfl

private lemma index_hom_of_le {i j : Index x}
    (h : stageSubgroup x G i ≤ stageSubgroup x G j) : Nonempty (i ⟶ j) := by
  classical
  let M := stageSubgroup x G i
  let N := stageSubgroup x G j
  obtain ⟨ei, hei, hsi⟩ := quotient_label x G ((obj x).obj i) (point x i) M rfl
  obtain ⟨ej, hej, hsj⟩ := quotient_label x G ((obj x).obj j) (point x j) N rfl
  let m := QuotientGroup.map M.toSubgroup N.toSubgroup (MonoidHom.id G) h
  let f := fun a ↦ ej.symm (m (ei a))
  have hf (g : G) a : f (g • a) = g • f a := by
    apply ej.injective
    simp only [f, Equiv.apply_symm_apply, hsi, map_mul, hsj]
    rfl
  obtain ⟨φ, hφ⟩ := lift_equivariant x G f hf
  have hp : (FiniteEtale.fiber x).map φ (point x i) = point x j := by
    rw [hφ]
    apply ej.injective
    dsimp only [f]
    rw [Equiv.apply_symm_apply]
    rw [hei, hej]
    rfl
  exact ⟨(indexEquiv x).inverse.preimage (PointedGaloisObject.Hom.mk φ hp)⟩

private lemma subgroupFunctor_equivalence : (subgroupFunctor x G).IsEquivalence := by
  classical
  let S := subgroupFunctor x G
  have : S.Faithful := ⟨fun {i j} f g _ ↦ (index_hom_subsingleton x i j).elim f g⟩
  have : S.Full := ⟨fun {i j} f ↦ by
    obtain ⟨φ⟩ := index_hom_of_le x G (leOfHom f)
    exact ⟨φ, Subsingleton.elim _ _⟩⟩
  have : S.EssSurj := ⟨fun N ↦ by
    obtain ⟨P, a, hP, ha⟩ := FiniteEtale.exists_isConnected_stabilizer_eq x G
      N.toOpenSubgroup
    let := hP
    have hnormal : (MulAction.stabilizer G a).Normal := by rw [ha]; infer_instance
    let := galois_of_normal_stabilizer x G P a hnormal
    let A : PointedGaloisObject (FiniteEtale.fiber x) := ⟨P, a, inferInstance⟩
    let i := (indexEquiv x).functor.obj A
    let e := (PointedGaloisObject.incl (FiniteEtale.fiber x)).mapIso
      ((indexEquiv x).unitIso.app A)
    have he : (FiniteEtale.fiber x).map e.hom a = point x i :=
      ((indexEquiv x).unitIso.hom.app A).comp
    have hs : MulAction.stabilizer G a = MulAction.stabilizer G (point x i) :=
      (FiniteEtale.exists_iso_fiber_map_eq_iff x G P ((obj x).obj i) a
        (point x i)).mp ⟨e, he⟩
    have hi : S.obj i = N := by
      apply SetLike.ext
      intro g
      change g ∈ MulAction.stabilizer G (point x i) ↔ g ∈ N.toSubgroup
      rw [← hs, ha]
    exact ⟨i, ⟨eqToIso hi⟩⟩⟩
  exact { }

private lemma exists_labels :
    ∃ E : OpenNormalSubgroup G ≌ Index x,
    ∃ q : ∀ N : OpenNormalSubgroup G,
      (FiniteEtale.fiber x).obj ((obj x).obj (E.functor.obj N)) ≃ G ⧸ N.toSubgroup,
      (∀ N, q N (point x (E.functor.obj N)) = QuotientGroup.mk (1 : G)) ∧
      (∀ (N : OpenNormalSubgroup G) (g : G)
        (s : (FiniteEtale.fiber x).obj ((obj x).obj (E.functor.obj N))),
        q N (g • s) = QuotientGroup.mk g * q N s) := by
  classical
  let := subgroupFunctor_equivalence x G
  let S := (subgroupFunctor x G).asEquivalence
  have hN (N : OpenNormalSubgroup G) : stageSubgroup x G (S.inverse.obj N) = N :=
    le_antisymm (leOfHom (S.counitIso.app N).hom) (leOfHom (S.counitIso.app N).inv)
  have hs (N : OpenNormalSubgroup G) :
      MulAction.stabilizer G (point x (S.inverse.obj N)) = N.toSubgroup :=
    congrArg (fun N : OpenNormalSubgroup G ↦ N.toSubgroup) (hN N)
  choose q hq hqs using fun N ↦ quotient_label x G _ (point x (S.inverse.obj N)) N (hs N)
  exact ⟨S.symm, q, hq, hqs⟩

private lemma transition_finite {i j : Index x} (f : i ⟶ j) :
    IsFinite ((diagram x).map f) := by
  have : IsFinite ((diagram x).map f ≫ p x j) := by rw [map_p]; infer_instance
  exact IsFinite.of_comp _ (p x j)

private lemma transition_etale {i j : Index x} (f : i ⟶ j) :
    Etale ((diagram x).map f) := by
  have : Etale ((diagram x).map f ≫ p x j) := by rw [map_p]; infer_instance
  exact Etale.of_comp _ (p x j)

private lemma transition_surjective {i j : Index x} (f : i ⟶ j) :
    Surjective ((diagram x).map f) := by
  have := transition_finite x f
  have := transition_etale x f
  have : ConnectedSpace ((diagram x).obj j) :=
    FiniteEtale.connectedSpace_of_isConnected ((obj x).obj j)
  have : Nonempty ((diagram x).obj i) :=
    ⟨(point x i).left (IsLocalRing.closedPoint Ω)⟩
  have hr : Set.range ((diagram x).map f) = Set.univ :=
    (show IsClopen (Set.range ((diagram x).map f)) from
      ⟨((diagram x).map f).isClosedMap.isClosed_range,
        ((diagram x).map f).isOpenMap.isOpen_range⟩).eq_univ (Set.range_nonempty _)
  exact ⟨Set.range_eq_univ.mp hr⟩

private lemma projection_surjective (j : Index x) :
    Surjective (limit.π (diagram x) j) := by
  let D := Over.forget j ⋙ diagram x
  let p' : ∀ i : Over j, D.obj i ⟶ (diagram x).obj j :=
    fun i ↦ (diagram x).map i.hom
  have hp' {i k : Over j} (f : i ⟶ k) : D.map f ≫ p' k = p' i := by
    dsimp [D, p']
    rw [← Functor.map_comp, Over.w f]
  have hq (i : Over j) :
      ((limit.cone (diagram x)).whisker (Over.forget j)).π.app i ≫ p' i =
        limit.π (diagram x) j := limit.w _ _
  have (i : Over j) : IsAffineHom (p' i) := by dsimp [p']; infer_instance
  exact ⟨surjective_of_isLimit D
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget j) _).symm (limit.isLimit _))
    p' hp' (limit.π (diagram x) j) hq fun i ↦ (transition_surjective x i.hom).surj⟩

end Labels

section Charts

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
  (G : ProfiniteGrp.{u}) (E : OpenNormalSubgroup G ≌ Index x)

private lemma section_etale (U : X.AffineZariskiSite) (N : OpenNormalSubgroup G) :
    ((p x (E.functor.obj N)).app U.toOpens).hom.Etale := by
  simpa only [Scheme.Hom.app_eq_appLE] using
    HasRingHomProperty.appLE (P := @Etale) (p x (E.functor.obj N)) inferInstance
      U ⟨_, U.2.preimage (p x (E.functor.obj N))⟩ le_rfl

private lemma section_map_compatible (U : X.AffineZariskiSite)
    {M N : (OpenNormalSubgroup G)ᵒᵖ} (f : M ⟶ N) :
    (p x (E.functor.obj M.unop)).app U.toOpens ≫
      (normalSectionDiagram x G E U).map f = (p x (E.functor.obj N.unop)).app U.toOpens := by
  exact congrArg (fun η ↦ η.app (op U))
    (AffineOverLimit.sectionsι_comp_diagram_map (diagram x) (p x) (map_p x)
      (E.functor.op.map f))

private lemma section_map_colimit (U : X.AffineZariskiSite) (N : OpenNormalSubgroup G) :
    (p x (E.functor.obj N)).app U.toOpens ≫
      colimit.ι (normalSectionDiagram x G E U) (op N) =
        normalSectionAlgebraMap x G E U := by
  have : IsCofiltered (OpenNormalSubgroup G) := IsCofiltered.of_equivalence E.symm
  have : CategoryTheory.IsConnected ((OpenNormalSubgroup G)ᵒᵖ) :=
    IsFiltered.isConnected _
  exact constant_of_preserves_morphisms
    (fun i ↦ (p x (E.functor.obj i.unop)).app U.toOpens ≫
      colimit.ι (normalSectionDiagram x G E U) i)
    (fun i j f ↦ by
      rw [← section_map_compatible x G E U f, Category.assoc, colimit.w]) (op N) _

private lemma section_indEtale (U : X.AffineZariskiSite) :
    RingHom.IndEtaleAcrossUniverses (normalSectionAlgebraMap x G E U).hom := by
  have : IsCofiltered (OpenNormalSubgroup G) := IsCofiltered.of_equivalence E.symm
  let D := normalSectionDiagram x G E U
  let t : (Functor.const _).obj Γ(X, U.toOpens) ⟶ D :=
    { app N := (p x (E.functor.obj N.unop)).app U.toOpens
      naturality M N f := by
        change 𝟙 _ ≫ _ = _ ≫ _
        rw [Category.id_comp]
        exact (section_map_compatible x G E U f).symm }
  have h : (normalSectionAlgebraMap x G E U).hom.IndEtale :=
    (RingHom.IndEtale.iff_exists _).mpr
      ⟨_, inferInstance, inferInstance, D, t, (colimit.cocone D).ι, colimit.isColimit D,
        fun N ↦ ⟨section_etale x G E U N.unop, section_map_colimit x G E U N.unop⟩⟩
  have hP := RingHom.IndEtale.isStableUnderBaseChange.localizationPreserves.away.respectsIso
  exact hP.1 _ ULift.ringEquiv.symm (hP.2 _ ULift.ringEquiv h)

private lemma section_chart (U : X.AffineZariskiSite) :
    ∃ e : (proj x ⁻¹ᵁ U.toOpens).toScheme ≅ Spec (colimit (normalSectionDiagram x G E U)),
      e.hom ≫ Spec.map (normalSectionAlgebraMap x G E U) ≫ U.2.fromSpec =
        (proj x ⁻¹ᵁ U.toOpens).ι ≫ proj x ∧
      ∀ N : OpenNormalSubgroup G,
        e.hom ≫ Spec.map (colimit.ι (normalSectionDiagram x G E U) (op N)) ≫
          AffineOverLimit.chart (diagram x) (p x) (E.functor.obj N) U =
            (proj x ⁻¹ᵁ U.toOpens).ι ≫ limit.π (diagram x) (E.functor.obj N) := by
  have : IsCofiltered (OpenNormalSubgroup G) := IsCofiltered.of_equivalence E.symm
  let D := E.functor ⋙ diagram x
  let p' : ∀ N, D.obj N ⟶ X := fun N ↦ p x (E.functor.obj N)
  have hp' {M N : OpenNormalSubgroup G} (f : M ⟶ N) : D.map f ≫ p' N = p' M :=
    map_p x (E.functor.map f)
  have (N : OpenNormalSubgroup G) : IsAffineHom (p' N) := by dsimp [p']; infer_instance
  let A := AffineOverLimit.diagram D p' hp'
  let ev := (CategoryTheory.evaluation X.AffineZariskiSiteᵒᵖ CommRingCat.{u}).obj (op U)
  let r : (colimit A).obj (op U) ≅ colimit (normalSectionDiagram x G E U) :=
    preservesColimitIso ev A
  let c := (limit.cone (diagram x)).whisker E.functor
  let h : IsLimit c :=
    (Functor.Initial.isLimitWhiskerEquiv E.functor _).symm (limit.isLimit _)
  let e₀ : cover x ≅ AffineOverLimit.limitScheme D p' hp' :=
    h.conePointUniqueUpToIso (AffineOverLimit.isLimitLimitCone D p' hp')
  let d := AffineOverLimit.gluingData D p' hp'
  let k : Spec (colimit (normalSectionDiagram x G E U)) ⟶ cover x :=
    Spec.map r.hom ≫ colimit.ι d.functor U ≫ e₀.inv
  have hk (N : OpenNormalSubgroup G) :
      k ≫ limit.π (diagram x) (E.functor.obj N) =
        Spec.map (colimit.ι (normalSectionDiagram x G E U) (op N)) ≫
          AffineOverLimit.chart (diagram x) (p x) (E.functor.obj N) U := by
    change Spec.map r.hom ≫ colimit.ι d.functor U ≫ e₀.inv ≫ c.π.app N = _
    rw [IsLimit.conePointUniqueUpToIso_inv_comp]
    change Spec.map r.hom ≫ colimit.ι (AffineOverLimit.gluingData D p' hp').functor U ≫
      AffineOverLimit.π D p' hp' N = _
    rw [AffineOverLimit.ι_π]
    rw [← Spec.map_comp_assoc]
    congr 2
    exact ι_preservesColimitIso_hom ev A (op N)
  have hbase : k ≫ proj x =
      Spec.map (normalSectionAlgebraMap x G E U) ≫ U.2.fromSpec := by
    let N : OpenNormalSubgroup G := ⟨⟨⊤, isOpen_univ⟩, inferInstance⟩
    rw [← π_p x (E.functor.obj N), ← Category.assoc, hk, Category.assoc,
      AffineOverLimit.chart_comp_p, ← Spec.map_comp_assoc]
    rfl
  have hglobal : e₀.hom ≫ AffineOverLimit.limitHom D p' hp' = proj x := by
    let N : OpenNormalSubgroup G := ⟨⟨⊤, isOpen_univ⟩, inferInstance⟩
    have heN : e₀.hom ≫ AffineOverLimit.π D p' hp' N = c.π.app N :=
      h.conePointUniqueUpToIso_hom_comp (AffineOverLimit.isLimitLimitCone D p' hp') N
    rw [← AffineOverLimit.π_p D p' hp' N, ← Category.assoc, heN]
    exact π_p x _
  have : IsOpenImmersion k := by dsimp [k, d]; infer_instance
  have hrange : Set.range k = (proj x ⁻¹ᵁ U.toOpens : Set (cover x)) := by
    have hg : e₀.inv ≫ proj x = AffineOverLimit.limitHom D p' hp' := by
      rw [← hglobal, Iso.inv_hom_id_assoc]
    have hd := d.toBase_preimage_eq_opensRange_ι U
    have hι : Set.range (colimit.ι d.functor U) =
        (AffineOverLimit.limitHom D p' hp' ⁻¹ᵁ U.toOpens : Set _) := by
      simpa only [Scheme.Hom.coe_opensRange, AffineZariskiSite.directedCover,
        Scheme.Opens.opensRange_ι] using congrArg SetLike.coe hd.symm
    have hpre : Set.range (colimit.ι d.functor U ≫ e₀.inv) =
        (proj x ⁻¹ᵁ U.toOpens : Set (cover x)) := by
      ext z
      constructor
      · rintro ⟨a, rfl⟩
        change proj x (e₀.inv (colimit.ι d.functor U a)) ∈ U.toOpens
        rw [← Scheme.Hom.comp_apply, hg]
        have hz := Set.mem_range_self (f := colimit.ι d.functor U) a
        rw [hι] at hz
        exact hz
      · intro hz
        have hez : e₀.hom z ∈ Set.range (colimit.ι d.functor U) := by
          rw [hι]
          change AffineOverLimit.limitHom D p' hp' (e₀.hom z) ∈ U.toOpens
          rw [← Scheme.Hom.comp_apply, hglobal]
          exact hz
        obtain ⟨a, ha⟩ := hez
        refine ⟨a, ?_⟩
        change e₀.inv (colimit.ι d.functor U a) = z
        rw [ha, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
        rfl
    change Set.range (Spec.map r.hom ≫ (colimit.ι d.functor U ≫ e₀.inv)) = _
    change Set.range ((colimit.ι d.functor U ≫ e₀.inv) ∘ Spec.map r.hom) = _
    have hs : Function.Surjective (Spec.map r.hom) := (Spec.map r.hom).homeomorph.surjective
    rw [Set.range_comp, Set.range_eq_univ.mpr hs, Set.image_univ]
    exact hpre
  let e := IsOpenImmersion.isoOfRangeEq (proj x ⁻¹ᵁ U.toOpens).ι k
    ((Scheme.Opens.range_ι _).trans hrange.symm)
  have he : e.hom ≫ k = (proj x ⁻¹ᵁ U.toOpens).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  refine ⟨e, ?_, fun N ↦ ?_⟩
  · rw [← hbase, ← Category.assoc, he]
  · rw [← hk, ← Category.assoc, he]

end Charts

/-- Geometry of the pointed Galois inverse limit, with every normal-subgroup label fixed.
Source: Stacks 0BND, 0BN2, 01YX, 01YW, 01Z2, 01Z4, 097I and 097N
(blueprint: lem-sfb-pointed-galois-limit-geometry).

Proof: (1) The fundamental Galois equivalence `thm-galois-fundamental` and
`cor-galois-open-subgroups` represent each pointed left coset set (G/N,N).
Automorphisms are right translations for normal N; conversely transitivity of
N_G(U)/U on G/U forces U normal.
(2) An equivariant pointed map sends aM to aN, exists exactly for M ≤ N, and is
unique. Full faithfulness gives the equivalence E and the transition equations.
Intersections give common refinements; the whole group is an index.
(3) A cone on a cofinal system extends to any object by choosing a refining object.
Common refinements and uniqueness of pointed arrows make this independent of choices.
Restriction and extension are inverse, proving the canonical limit comparisons,
also in schemes over X.
(4) Finite maps are affine and separated. The affine and qcqs permanence lemmas
make the stages qcqs. `lem-weil-pbc-limit-affine-transition` gives the existing
limit and affine projections; composition gives an affine structure map and qcqs limit.
(5) The finite étale degree of every pointed connected cover and transition is
positive, by `lem-weil-pbc-finite-etale-trace-degree`, so all these maps are surjective.
(6) Pass to the tail below N and base change to a residue field. By
`lem-weil-pbc-limit-fibre-products` this fibre is the limit of the nonempty affine
stage fibres. `lem-weil-pbc-limit-nonempty` makes it nonempty. Hence every projection,
and consequently the structure map, is surjective.
(7) The compatible marked points give the map pt by the limit universal property.
Its composites are the marked stage points and x; Spec Ω is nonempty.
(8) Base change to an affine open V. Each stage is finite étale affine over V.
Fibre products commute with the limit; the affine limit formula is Spec of the
filtered colimit of their section rings. The affine étale criterion identifies
the terms as étale finitely presented algebras, hence the colimit is ind-étale.
The chart equations characterize this identification by every colimit inclusion.
(9) `det-pe-morphisms-etale-comparison` makes v weakly étale on these charts,
hence globally; in particular v is flat. The single affine preimage of each affine
open covers that open, giving the pro-étale singleton covering condition.
(10) Descend a clopen and its compact complement to a common stage using
`pqf-lem-limit-qc-open-descends`. Surjectivity of the projection makes the descended
opens complementary. Stage connectedness makes them trivial. Together with the
marked point this proves connectedness of the limit. -/
theorem exists_pointedGaloisLimitGeometry {X : Scheme.{u}} [ConnectedSpace X]
    [CompactSpace X] [QuasiSeparatedSpace X] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u})
    [∀ Y : X.FiniteEtale, MulAction G ((FiniteEtale.fiber x).obj Y)]
    [IsFundamentalGroup (FiniteEtale.fiber x) G] :
    ∃ E : OpenNormalSubgroup G ≌ Index x,
    ∃ q : ∀ N : OpenNormalSubgroup G,
      (FiniteEtale.fiber x).obj ((obj x).obj (E.functor.obj N)) ≃ G ⧸ N.toSubgroup,
      (∀ N, q N (point x (E.functor.obj N)) = QuotientGroup.mk (1 : G)) ∧
      (∀ (N : OpenNormalSubgroup G) (g : G)
        (s : (FiniteEtale.fiber x).obj ((obj x).obj (E.functor.obj N))),
        q N (g • s) = QuotientGroup.mk g * q N s) ∧
      (∀ {M N : OpenNormalSubgroup G} (f : M ⟶ N)
        (s : (FiniteEtale.fiber x).obj ((obj x).obj (E.functor.obj M))),
        q N ((FiniteEtale.fiber x).map ((obj x).map (E.functor.map f)) s) =
          QuotientGroup.map M.toSubgroup N.toSubgroup (MonoidHom.id G) (leOfHom f) (q M s)) ∧
      (∀ M N : OpenNormalSubgroup G,
        Subsingleton (E.functor.obj M ⟶ E.functor.obj N)) ∧
      (∀ M N : OpenNormalSubgroup G,
        Nonempty (E.functor.obj M ⟶ E.functor.obj N) ↔ M ≤ N) ∧
      (∀ (N : OpenNormalSubgroup G)
        (s t : (FiniteEtale.fiber x).obj ((obj x).obj (E.functor.obj N))),
        ∃! a : Aut ((obj x).obj (E.functor.obj N)), (FiniteEtale.fiber x).map a.hom s = t) ∧
      Nonempty (IsLimit ((limit.cone (diagram x)).whisker E.functor)) ∧
      Nonempty (IsLimit (Over.liftCone (diagram x) (pNatTrans x)
        (limit.cone (diagram x)) (proj x) (π_p x))) ∧
      (∀ (J : Type u) [SmallCategory J] (F : J ⥤ Index x) [Functor.Initial F],
        Nonempty (IsLimit ((limit.cone (diagram x)).whisker F)) ∧
        Nonempty (IsLimit ((Over.liftCone (diagram x) (pNatTrans x)
          (limit.cone (diagram x)) (proj x) (π_p x)).whisker F))) ∧
      (∀ N : OpenNormalSubgroup G,
        ConnectedSpace ((diagram x).obj (E.functor.obj N)) ∧
        CompactSpace ((diagram x).obj (E.functor.obj N)) ∧
        QuasiSeparatedSpace ((diagram x).obj (E.functor.obj N)) ∧
        IsFinite (p x (E.functor.obj N)) ∧ Etale (p x (E.functor.obj N)) ∧
        Surjective (p x (E.functor.obj N)) ∧
        IsAffineHom (limit.π (diagram x) (E.functor.obj N)) ∧
        Surjective (limit.π (diagram x) (E.functor.obj N))) ∧
      (∀ {M N : OpenNormalSubgroup G} (f : M ⟶ N),
        IsFinite ((diagram x).map (E.functor.map f)) ∧
        Etale ((diagram x).map (E.functor.map f)) ∧
        Surjective ((diagram x).map (E.functor.map f))) ∧
      (∀ N : OpenNormalSubgroup G,
        pt x ≫ limit.π (diagram x) (E.functor.obj N) = (point x (E.functor.obj N)).left) ∧
      pt x ≫ proj x = x ∧
      ConnectedSpace (cover x) ∧ CompactSpace (cover x) ∧ QuasiSeparatedSpace (cover x) ∧
      IsAffineHom (proj x) ∧ Flat (proj x) ∧ Surjective (proj x) ∧ WeaklyEtale (proj x) ∧
      (∀ U : X.AffineZariskiSite,
        (∀ N : OpenNormalSubgroup G,
          ((p x (E.functor.obj N)).app U.toOpens).hom.Etale) ∧
        RingHom.IndEtaleAcrossUniverses (normalSectionAlgebraMap x G E U).hom ∧
        (∀ N : OpenNormalSubgroup G,
          (p x (E.functor.obj N)).app U.toOpens ≫
            colimit.ι (normalSectionDiagram x G E U) (op N) = normalSectionAlgebraMap x G E U) ∧
        ∃ e : (proj x ⁻¹ᵁ U.toOpens).toScheme ≅ Spec (colimit (normalSectionDiagram x G E U)),
          e.hom ≫ Spec.map (normalSectionAlgebraMap x G E U) ≫ U.2.fromSpec =
            (proj x ⁻¹ᵁ U.toOpens).ι ≫ proj x ∧
          ∀ N : OpenNormalSubgroup G,
            e.hom ≫ Spec.map (colimit.ι (normalSectionDiagram x G E U) (op N)) ≫
              AffineOverLimit.chart (diagram x) (p x) (E.functor.obj N) U =
                (proj x ⁻¹ᵁ U.toOpens).ι ≫ limit.π (diagram x) (E.functor.obj N)) ∧
      Presieve.singleton (proj x) ∈ proetalePrecoverage X  := by
  classical
  obtain ⟨E, q, hq, hqs⟩ := exists_labels x G
  have : Surjective (proj x) := ⟨surjective_proj x⟩
  have : Nonempty (Index x) := IsCofiltered.nonempty
  refine ⟨E, q, hq, hqs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, pt_proj x,
    inferInstance, ?_, ?_, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro M N f s
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G (point x (E.functor.obj M)) s
    rw [IsNaturalSMul.naturality, map_point, hqs, hqs, hq, hq]
    simp only [← QuotientGroup.mk_mul, mul_one, QuotientGroup.map_mk, MonoidHom.id_apply]
  · intro M N
    exact index_hom_subsingleton x _ _
  · intro M N
    constructor
    · rintro ⟨f⟩
      exact leOfHom (E.functor.preimage f)
    · intro h
      exact ⟨E.functor.map (homOfLE h)⟩
  · intro N s t
    exact (evaluation_aut_bijective_of_isGalois (FiniteEtale.fiber x) _ s).existsUnique t
  · exact ⟨(Functor.Initial.isLimitWhiskerEquiv E.functor _).symm (limit.isLimit _)⟩
  · exact ⟨Over.isLimitLiftCone _ _ _ _ _ (limit.isLimit _)⟩
  · intro J _ F _
    constructor
    · exact ⟨(Functor.Initial.isLimitWhiskerEquiv F _).symm (limit.isLimit _)⟩
    · exact ⟨(Functor.Initial.isLimitWhiskerEquiv F _).symm
        (Over.isLimitLiftCone _ _ _ _ _ (limit.isLimit _))⟩
  · intro N
    refine ⟨FiniteEtale.connectedSpace_of_isConnected _, inferInstance, inferInstance,
      inferInstance, inferInstance, ?_, ?_, projection_surjective x _⟩
    · exact FiniteEtale.surjective_of_nonempty_fiber x _ ⟨point x _⟩
    · exact isAffineHom_π_app (diagram x) (limit.cone _) (limit.isLimit _) _
  · intro M N f
    exact ⟨transition_finite x _, transition_etale x _, transition_surjective x _⟩
  · exact fun N ↦ pt_π x _
  · exact QuasiCompact.compactSpace_of_compactSpace (proj x)
  · exact quasiSeparatedSpace_of_quasiSeparated (proj x)
  · intro U
    exact ⟨section_etale x G E U, section_indEtale x G E U,
      section_map_colimit x G E U, section_chart x G E U⟩
  · exact Scheme.Hom.singleton_mem_propQCPrecoverage (inferInstance : WeaklyEtale (proj x))

end AlgebraicGeometry.Scheme.UniversalCover
