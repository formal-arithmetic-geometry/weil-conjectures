/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension
import WeilConjectures.RepresentationTheory.FiniteMatrixWitness
import WeilConjectures.Mathlib.RepresentationTheory.Irreducible
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.OpenSubgroups
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GeometricFiber
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Instances.Matrix

/-! # A finite cover detecting irreducibility of pro-etale local systems

This is the finite-cover part of the curve-testing argument, without choosing a curve.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory Limits
open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

private theorem exists_openNormal_irreducibility_detector
    {K G V : Type*} [Field K] [IsAlgClosed K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (hρ : ρ.IsIrreducible)
    (hc : ∀ (φ : Module.Dual K V) (v : V), Continuous fun g ↦ φ (ρ g v)) :
    ∃ N : OpenNormalSubgroup G, ∀ H : Subgroup G,
      (∀ g : G, ∃ h ∈ H, g⁻¹ * h ∈ N) → Representation.IsIrreducible (ρ.comp H.subtype) := by
  classical
  have := hρ
  have := hρ.nontrivial
  let b := Module.finBasis K V
  let I := Fin (Module.finrank K V) × Fin (Module.finrank K V)
  obtain ⟨s, hs⟩ := b.exists_det_ne_zero_of_span_range_eq_top ρ
    (Representation.span_range_eq_top_of_isIrreducible ρ)
  let D (a : I → G) : K :=
    (Matrix.of fun j p ↦ LinearMap.toMatrix b b (ρ (s j * a j)) p.1 p.2).det
  have hD : Continuous D := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro j
    apply continuous_pi
    intro p
    apply Continuous.congr ((hc (b.coord p.1) (b p.2)).comp
      (show Continuous (fun a : I → G ↦ s j * a j) from
        continuous_const.mul (continuous_apply j)))
    intro a
    simp only [Function.comp_apply, Matrix.of_apply, LinearMap.toMatrix_apply,
      Module.Basis.coord_apply]
  have hD1 : D 1 ≠ 0 := by simpa [D] using hs
  have hn : {a : I → G | D a ≠ 0} ∈ nhds 1 :=
    (isOpen_ne.preimage hD).mem_nhds hD1
  rw [nhds_pi, Filter.mem_pi] at hn
  obtain ⟨J, -, U, hU, hJU⟩ := hn
  have hN (j : I) : ∃ N : OpenNormalSubgroup G, (N : Set G) ⊆ U j := by
    obtain ⟨W, hWU, hW, h1W⟩ := mem_nhds_iff.mp (hU j)
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW h1W
    exact ⟨N, hN.trans hWU⟩
  choose N hN using hN
  let N₀ : OpenNormalSubgroup G :=
    { toSubgroup := ⨅ j, (N j).toSubgroup
      isOpen' := by
        change IsOpen (↑(⨅ j, (N j).toSubgroup) : Set G)
        rw [Subgroup.coe_iInf]
        exact isOpen_iInter_of_finite (fun j ↦ (N j).isOpen)
      isNormal' := Subgroup.normal_iInf_normal (fun j ↦ inferInstance) }
  refine ⟨N₀, fun H hH ↦ ?_⟩
  choose a ha hsa using fun j : I ↦ hH (s j)
  have hsmall : D (fun j ↦ (s j)⁻¹ * a j) ≠ 0 := by
    apply hJU
    intro j hj
    apply hN j
    exact (Subgroup.mem_iInf.mp (hsa j)) j
  have hdet : (Matrix.of fun j p ↦ LinearMap.toMatrix b b (ρ (a j)) p.1 p.2).det ≠ 0 := by
    simpa only [D, mul_inv_cancel_left] using hsmall
  apply Representation.isIrreducible_of_span_range_eq_top
  rw [eq_top_iff, ← b.span_range_eq_top_of_det_ne_zero (fun j ↦ ρ (a j)) hdet]
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨⟨a j, ha j⟩, rfl⟩

open Scheme.FiniteEtale LisseMonodromy in
private theorem isZero_of_subsingleton_stalk
    {l : ℕ} [Fact l.Prime] {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    {M : LisseMonodromy l X Ω} {t : Spec (.of (AlgebraicClosure Ω)) ⟶ X}
    (hM : M.IsEquivalenceAt t) (F : LisseSheaf l X)
    [Subsingleton (StalkSpace t F)] : IsZero F.obj := by
  have h : (𝟙 F : F ⟶ F) = 0 := hM.faithful _ _ (by
    apply (WeilCoefficients.toModuleCat l).map_injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    exact Subsingleton.elim _ _)
  apply (IsZero.iff_id_eq_zero _).mpr
  exact congrArg (fun f : F ⟶ F ↦ f.hom) h

open Scheme.FiniteEtale LisseMonodromy in
private theorem monodromy_irreducible_iff
    {l : ℕ} [Fact l.Prime] {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsRegular X] [ConnectedSpace X] {Ω : Type u} [Field Ω]
    {M : LisseMonodromy l X Ω} {t : Spec (.of (AlgebraicClosure Ω)) ⟶ X}
    (hM : M.IsEquivalenceAt t) (F : LisseSheaf l X) :
    (M.rep t F).IsIrreducible ↔ IsIrreducibleAdicLocalSystem F.obj := by
  classical
  have : IrreducibleSpace X := IsRegular.irreducibleSpace X
  let S : AdicSheaf l X ⥤ ModuleCat.{u + 1} (PadicAlgCl l) :=
    AdicSheaf.forget X ⋙ stalkFunctor l t ⋙ WeilCoefficients.toModuleCat.{u} l
  constructor
  · intro hρ
    have hn := hρ.nontrivial
    refine ⟨F.property, ?_, fun A i hi hA ↦ ?_⟩
    · intro hz
      have hz' : IsZero (S.obj F.obj) := S.map_isZero hz
      have hs : Subsingleton (StalkSpace t F) := ModuleCat.isZero_iff_subsingleton.mp hz'
      exact not_nontrivial_iff_subsingleton.mpr hs hn
    · let A' : LisseSheaf l X := ⟨A, hA⟩
      let i' : A' ⟶ F := ObjectProperty.homMk i
      let a := ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map i')).hom
      have ha : Function.Injective a := (ModuleCat.mono_iff_injective _).mp (S.map_mono i)
      have hr := (Representation.isIrreducible_iff.mp hρ).2 (LinearMap.range a) (by
        rintro g _ ⟨v, rfl⟩
        exact ⟨M.rep t A' g v, M.rep_naturality t i' g v⟩)
      rcases hr with hr | hr
      · left
        have hs : Subsingleton (StalkSpace t A') := ⟨fun v w ↦ ha (by
          have hv := LinearMap.mem_range_self a v
          have hw := LinearMap.mem_range_self a w
          rw [hr, Submodule.mem_bot] at hv hw
          exact hv.trans hw.symm)⟩
        exact isZero_of_subsingleton_stalk hM A'
      · right
        have : IsIso i' := hM.isIso_of_bijective i'
          ⟨ha, LinearMap.range_eq_top.mp hr⟩
        exact (ObjectProperty.ι _).map_isIso i'
  · intro hF
    have hn : Nontrivial (StalkSpace t F) := by
      by_contra hn
      have := not_nontrivial_iff_subsingleton.mp hn
      exact hF.2.1 (isZero_of_subsingleton_stalk hM F)
    apply Representation.isIrreducible_iff.mpr
    refine ⟨hn, fun W hW ↦ ?_⟩
    let σ := (M.rep t F).subrepresentation W hW
    obtain ⟨A, e, he⟩ := hM.essSurj W σ (by
      intro φ w
      obtain ⟨φ', hφ'⟩ := LinearMap.exists_extend (K := PadicAlgCl l) (p := W) φ
      have h (g : Aut (fiber t)) : φ (σ g w) = φ' (M.rep t F g w) := by
        rw [← hφ']; rfl
      simp_rw [h]
      exact hM.continuous_rep F φ' w)
    let a : StalkSpace t A →ₗ[PadicAlgCl l] StalkSpace t F := W.subtype ∘ₗ e.toLinearMap
    obtain ⟨i, hi⟩ := hM.full a (fun g v ↦ by
      change (e (M.rep t A g v) : StalkSpace t F) = _
      rw [he]
      rfl)
    have hai : Function.Injective a := Subtype.val_injective.comp e.injective
    have hK := (isAdicLisseSheaf_kernel_cokernel_of_irreducibleSpace
      A.property F.property i.hom).1
    let K : LisseSheaf l X := ⟨kernel i.hom, hK⟩
    have hsK : Subsingleton (StalkSpace t K) := by
      let b := (S.map (kernel.ι i.hom)).hom
      have hb : Function.Injective b := (ModuleCat.mono_iff_injective _).mp
        (S.map_mono (kernel.ι i.hom))
      have hzero (v : StalkSpace t K) : b v = 0 := by
        apply hai
        change a (b v) = a 0
        rw [map_zero, ← hi]
        have h := congrArg (fun f ↦ f.hom v) (congrArg S.map (kernel.condition i.hom))
        change (S.map i.hom).hom ((S.map (kernel.ι i.hom)).hom v) = 0
        simpa only [Functor.map_comp, Functor.map_zero, ModuleCat.hom_comp,
          LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h
      exact ⟨fun v w ↦ hb ((hzero v).trans (hzero w).symm)⟩
    have hK0 := isZero_of_subsingleton_stalk hM K
    have : Mono i.hom := Abelian.mono_of_kernel_ι_eq_zero i.hom (hK0.eq_of_src _ _)
    rcases hF.2.2 A.obj i.hom inferInstance A.property with hz | hi'
    · left
      have hs : Subsingleton (StalkSpace t A) :=
        ModuleCat.isZero_iff_subsingleton.mp (S.map_isZero hz)
      apply le_bot_iff.mp
      intro v hv
      obtain ⟨w, hw⟩ := e.surjective ⟨v, hv⟩
      have hw0 : w = 0 := Subsingleton.elim _ _
      rw [hw0, map_zero] at hw
      exact congrArg Subtype.val hw.symm
    · right
      have hs : Function.Surjective a := by
        rw [← hi]
        change Function.Surjective (S.map i.hom).hom
        exact (ConcreteCategory.bijective_of_isIso (S.map i.hom)).2
      apply top_unique
      intro v hv
      obtain ⟨w, rfl⟩ := hs v
      exact (e w).property

open CategoryTheory.PreGaloisCategory Scheme in
private theorem finite_quotient_cover
    {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber x) G]
    (Q : Type u) [Group Q] [Finite Q] (q : G →* Q)
    (hq : @Continuous G Q inferInstance ⊥ q) (hs : Function.Surjective q) :
    ∃ T : X.FiniteEtale, ConnectedSpace T.obj.left ∧
      ∃ e : ((FiniteEtale.fiber x).obj T) ≃ Q,
        ∀ (g : G) (t : (FiniteEtale.fiber x).obj T), e (g • t) = q g * e t := by
  let : TopologicalSpace Q := ⊥
  have : DiscreteTopology Q := ⟨rfl⟩
  let : MulAction G Q := MulAction.compHom Q q
  have hopen (a : Q) : IsOpen {g : G | g • a = a} := by
    change IsOpen {g : G | q g * a = a}
    have he : {g : G | q g * a = a} = q ⁻¹' {1} := by ext g; simp
    rw [he]
    exact (isOpen_discrete _).preimage hq
  obtain ⟨T, e, he⟩ := FiniteEtale.exists_fiber_equiv x G hopen
  have : Nonempty ((FiniteEtale.fiber x).obj T) := ⟨e.symm 1⟩
  have : MulAction.IsPretransitive G ((FiniteEtale.fiber x).obj T) := ⟨by
    intro a b
    obtain ⟨g, hg⟩ := hs (e b * (e a)⁻¹)
    refine ⟨g, e.injective ?_⟩
    rw [he]
    change q g * e a = e b
    rw [hg, inv_mul_cancel_right]⟩
  have : IsConnected T := FiniteEtale.isConnected_of_isPretransitive x G T
  exact ⟨T, FiniteEtale.connectedSpace_of_isConnected T, e, he⟩

/-- A finite family of irreducible local systems admits one connected finite etale cover
whose connected pullback to a smooth connected affine curve detects irreducibility.
Source: current blueprint, sec-deligne-laumon-general/sk-i-dl-general-real,
lem-zl-curve-testing-irreducibility, finite matrix witnesses and common quotient cover
(blueprint: lem-zl-proetale-irreducibility-detector).

Proof: fix a geometric point of the nonempty connected smooth affine scheme X. The
pro-etale lisse monodromy equivalence identifies each F j with an irreducible continuous
finite-dimensional representation. Burnside gives finitely many group elements whose
matrices form a basis of the endomorphism space. Continuity of their nonzero determinant
gives an open normal subgroup such that every subgroup surjecting onto its quotient
still contains a matrix basis and acts irreducibly. Intersect these open normal subgroups
for the finitely many representations and realize the
regular action of the quotient as a connected finite etale cover T of X. For a connected
curve C, connectedness of T times_X C says that the image of pi_1(C) acts transitively on
that regular quotient. Its orbit of the identity is its image, so it surjects. The matrix
witnesses imply irreducibility of every restricted representation. Compatibility of
pro-etale lisse monodromy with pullback transports this to the asserted local systems.
For an empty family the intersection is the whole group and its quotient cover is
of degree one; no individual representation must be chosen. The argument requires neither
semisimplicity nor a Weil structure. -/
theorem exists_connected_finiteEtale_irreducibility_detector
    {k : Type u} [Field k] [IsAlgClosed k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsAffine X] [ConnectedSpace X] {d : ℕ} [SmoothOfRelativeDimension d f]
    {r : ℕ} (F : Fin r → AdicSheaf l X)
    (hF : ∀ j, IsIrreducibleAdicLocalSystem (F j)) :
    ∃ (T : Scheme.{u}) (π : T ⟶ X), IsFinite π ∧ Etale π ∧ ConnectedSpace T ∧
      ∀ (C : Scheme.{u}) (i : C ⟶ X) [IsAffine C]
        [SmoothOfRelativeDimension 1 (i ≫ f)] [ConnectedSpace C],
        ConnectedSpace ↑(pullback π i) →
          ∀ j, IsIrreducibleAdicLocalSystem ((i)^*ᵃ[l].obj (F j)) := by
  classical
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular X := IsRegular.of_smooth f
  obtain ⟨x, -⟩ := f.exists_comp_eq_id_of_isAlgClosed
  let t₀ : Spec (.of (AlgebraicClosure k)) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) ≫ x
  let M := universalLisseMonodromy l X k
  have hM := universalLisseMonodromy_isEquivalenceAt l X k
  let L (j : Fin r) : LisseSheaf l X := ⟨F j, (hF j).1⟩
  obtain ⟨G, _, _⟩ := Scheme.FiniteEtale.exists_isFundamentalGroup t₀
  let ρ (j : Fin r) : Representation (PadicAlgCl l) G
      (LisseMonodromy.StalkSpace t₀ (L j)) := (M.rep t₀ (L j)).comp
    (CategoryTheory.PreGaloisCategory.toAut (Scheme.FiniteEtale.fiber t₀) G)
  have hirr (j : Fin r) : (ρ j).IsIrreducible :=
    ((monodromy_irreducible_iff (hM t₀) (L j)).mpr (hF j)).comp
      (CategoryTheory.PreGaloisCategory.toAut_bijective _ G).2
  have hcont (j : Fin r) (φ : Module.Dual (PadicAlgCl l) (LisseMonodromy.StalkSpace t₀ (L j)))
      (v : LisseMonodromy.StalkSpace t₀ (L j)) : Continuous fun g : G ↦ φ (ρ j g v) :=
    ((hM t₀).continuous_rep (L j) φ v).comp
      (CategoryTheory.PreGaloisCategory.toAut_continuous _ G)
  choose N hN using fun j ↦ exists_openNormal_irreducibility_detector (ρ j) (hirr j) (hcont j)
  let N₀ : OpenNormalSubgroup G :=
    { toSubgroup := ⨅ j, (N j).toSubgroup
      isOpen' := by
        change IsOpen (↑(⨅ j, (N j).toSubgroup) : Set G)
        rw [Subgroup.coe_iInf]
        exact isOpen_iInter_of_finite (fun j ↦ (N j).isOpen)
      isNormal' := Subgroup.normal_iInf_normal (fun j ↦ inferInstance) }
  let S : Subgroup G := N₀.toSubgroup
  have : S.Normal := N₀.isNormal'
  have hopen : IsOpen (S : Set G) := N₀.isOpen
  have : Finite (G ⧸ S) := S.quotient_finite_of_isOpen hopen
  let q : G →* (G ⧸ S) := QuotientGroup.mk' S
  have hq : @Continuous G (G ⧸ S) inferInstance ⊥ q := by
    have : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hopen
    convert (QuotientGroup.continuous_mk (N := S)) using 1
    · exact DiscreteTopology.eq_bot.symm
    · rfl
  obtain ⟨T, hT, e, he⟩ := finite_quotient_cover t₀ G _ q hq
    (QuotientGroup.mk'_surjective S)
  have : IsFinite T.obj.hom := T.property
  have : Etale T.obj.hom := T.obj.prop
  refine ⟨T.obj.left, T.obj.hom, inferInstance, inferInstance, hT, ?_⟩
  intro C i _ _ _ hTC
  have : Smooth (i ≫ f) := SmoothOfRelativeDimension.smooth 1 (i ≫ f)
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (i ≫ f)
  have : IsRegular C := IsRegular.of_smooth (i ≫ f)
  obtain ⟨c, -⟩ := (i ≫ f).exists_comp_eq_id_of_isAlgClosed
  let t : Spec (.of (AlgebraicClosure k)) ⟶ C :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) ≫ c
  let M' := universalLisseMonodromy l C k
  have hM' := universalLisseMonodromy_isEquivalenceAt l C k t
  have hcomp := isCompatible_universalLisseMonodromy l k i
  obtain ⟨τ⟩ := CategoryTheory.PreGaloisCategory.nonempty_iso_of_fiberFunctor
    (Scheme.FiniteEtale.fiber t₀) (Scheme.FiniteEtale.fiber (t ≫ i))
  let β := Scheme.FiniteEtale.pullbackFiberIso i t ≪≫ τ.symm
  obtain ⟨GC, _, _⟩ := Scheme.FiniteEtale.exists_isFundamentalGroup t
  let p := Scheme.FiniteEtale.fundamentalGroupMap β GC G
  have hpath (σ : GC) :
      CategoryTheory.PreGaloisCategory.toAut (Scheme.FiniteEtale.fiber t₀) G (p σ) ≪≫ τ =
        τ ≪≫ Scheme.FiniteEtale.pullbackPathHom i t
          (CategoryTheory.PreGaloisCategory.toAut _ GC σ) := by
    ext P z
    change τ.hom.app P (p σ • z) =
      (Scheme.FiniteEtale.pullbackFiberIso i t).hom.app P
        (σ • (show (Scheme.FiniteEtale.fiber t).obj
          ((Scheme.FiniteEtale.pullback i).obj P) from
            (Scheme.FiniteEtale.pullbackFiberIso i t).inv.app P (τ.hom.app P z)))
    have h := Scheme.FiniteEtale.fundamentalGroupMap_smul β GC G σ P (β.inv.app P z)
    have hz : β.hom.app P (β.inv.app P z) = z :=
      ConcreteCategory.congr_hom (β.inv_hom_id_app P) z
    rw [hz] at h
    have h' := congrArg (τ.hom.app P) h
    have hτ (w : (Scheme.FiniteEtale.fiber (t ≫ i)).obj P) :
        τ.hom.app P (τ.inv.app P w) = w :=
      ConcreteCategory.congr_hom (τ.inv_hom_id_app P) w
    simpa only [β, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      NatTrans.comp_app, ConcreteCategory.comp_apply, hτ] using h'
  have hpq : Function.Surjective (q.comp p) := by
    let TC := (Scheme.FiniteEtale.pullback i).obj T
    have : ConnectedSpace TC.obj.left := hTC
    have : CategoryTheory.PreGaloisCategory.IsConnected TC :=
      Scheme.FiniteEtale.isConnected_of_connectedSpace TC
    let eC : ((Scheme.FiniteEtale.fiber t).obj TC) ≃ (G ⧸ S) :=
      (Equiv.ofBijective (β.hom.app T) (ConcreteCategory.bijective_of_isIso _)).trans e
    have heC (σ : GC)
        (z : (Scheme.FiniteEtale.fiber t).obj TC) :
        eC (σ • z) = q (p σ) * eC z := by
      change e (β.hom.app T (σ • z)) = q (p σ) * e (β.hom.app T z)
      rw [← Scheme.FiniteEtale.fundamentalGroupMap_smul β
        GC G, he]
    intro a
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq
      GC (eC.symm 1) (eC.symm a)
    refine ⟨σ, ?_⟩
    have h := congrArg eC hσ
    change q (p σ) = a
    simpa only [heC, Equiv.apply_symm_apply, mul_one] using h
  have hrange (j : Fin r) : Representation.IsIrreducible ((ρ j).comp p) := by
    have hmeet (g : G) : ∃ h ∈ p.range, g⁻¹ * h ∈ N j := by
      obtain ⟨σ, hσ⟩ := hpq (q g)
      refine ⟨p σ, ⟨σ, rfl⟩, ?_⟩
      have hs : g⁻¹ * p σ ∈ S := (QuotientGroup.eq_one_iff _).mp (by
        change q (g⁻¹ * p σ) = 1
        rw [map_mul, map_inv]
        change (q g)⁻¹ * (q.comp p) σ = 1
        rw [hσ, inv_mul_cancel])
      exact (Subgroup.mem_iInf.mp hs) j
    have hdet := hN j p.range hmeet
    exact hdet.comp (f := p.rangeRestrict) p.rangeRestrict_surjective
  intro j
  let a : LisseMonodromy.StalkSpace t₀ (L j) ≃ₗ[PadicAlgCl l]
      LisseMonodromy.StalkSpace (t ≫ i) (L j) :=
    WeilCoefficients.linearEquivOfIso ((M.mono τ).app (L j))
  let b := LisseMonodromy.upperStarStalkLinearEquiv i t (L j)
  let er : Representation.Equiv ((ρ j).comp p)
      ((M'.rep t ((L j).upperStar l i)).comp
        (CategoryTheory.PreGaloisCategory.toAut _ GC)) :=
    .mk (a.trans b) (by
      intro σ
      apply LinearMap.ext
      intro v
      have ha : a (ρ j (p σ) v) =
          M.rep (t ≫ i) (L j) (Scheme.FiniteEtale.pullbackPathHom i t
            (CategoryTheory.PreGaloisCategory.toAut _ GC σ)) (a v) := by
        change M.monoLinear τ (L j)
          (M.monoLinear (CategoryTheory.PreGaloisCategory.toAut _ G (p σ)) (L j) v) =
            M.monoLinear (Scheme.FiniteEtale.pullbackPathHom i t
              (CategoryTheory.PreGaloisCategory.toAut _ GC σ)) (L j)
              (M.monoLinear τ (L j) v)
        rw [← M.monoLinear_trans, ← M.monoLinear_trans, hpath]
      change b (a (ρ j (p σ) v)) = _
      rw [ha]
      exact hcomp.rep_apply (CategoryTheory.PreGaloisCategory.toAut _ GC σ) (L j) (a v))
  apply (monodromy_irreducible_iff hM' ((L j).upperStar l i)).mp
  have hi := er.isIrreducible_iff.mp (hrange j)
  rw [Representation.isIrreducible_iff] at hi ⊢
  exact ⟨hi.1, fun W hW ↦ hi.2 W (fun g v hv ↦ hW _ v hv)⟩

end AlgebraicGeometry.ProEtale
