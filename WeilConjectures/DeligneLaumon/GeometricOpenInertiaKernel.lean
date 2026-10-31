/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.HenselianBoundaryLocalData
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.HomotopyExactSequence
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Extension
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineIrreducible
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Spreading
import WeilConjectures.TraceFormula.HenselizationPrimeIndEtale
import WeilConjectures.RingTheory.EtaleColimitNormalLocalDomain
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DecompositionGroup
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleStalkNeighbourhoodSpreading
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.HenselianInertiaFiniteEtaleModel
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.HenselianFiniteEtaleStalkModel

/-! # Geometric henselian inertia generates the kernel for filling infinity

Source: Stacks 0BSM, 0BTD and 0BSW; proof step 2 of
lem-dl-a1-condensed-lisse-extension-inertia.
(blueprint: lem-dl-a1-geometric-open-inertia-kernel).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme.FiniteEtale
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia


open CategoryTheory.PreGaloisCategory

private theorem baseChangedOpen_data
    {k₀ k : Type u} [Field k₀] [Field k] (f : Spec (.of k) ⟶ Spec (.of k₀))
    (W : (ProjectiveLine (Spec (.of k₀))).Opens) (X : Scheme.{u})
    (e : X ≅ pullback (W.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)) f) :
    ∃ i : X ⟶ ProjectiveLine (Spec (.of k)), IsOpenImmersion i ∧
      i ≫ ProjectiveSpace.map (ULift.{u} (Fin 2)) f =
        e.hom ≫ pullback.fst _ _ ≫ W.ι ∧
      i ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) = e.hom ≫ pullback.snd _ _ := by
  have h : IsPullback (e.hom ≫ pullback.fst _ _) (e.hom ≫ pullback.snd _ _)
      (W.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)) f :=
    IsPullback.of_iso_pullback ⟨by
      simpa only [Category.assoc] using
        congrArg (fun t ↦ e.hom ≫ t) (pullback.condition (f :=
          W.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)) (g := f))⟩ e rfl rfl
  let i := ProjectiveSpace.liftBaseChange (e.hom ≫ pullback.snd _ _)
    ((e.hom ≫ pullback.fst _ _) ≫ W.ι) (by simpa [Category.assoc] using h.w.symm)
  have hi : IsPullback (e.hom ≫ pullback.fst _ _) i W.ι
      (ProjectiveSpace.map (ULift.{u} (Fin 2)) f) :=
    ProjectiveSpace.isPullback_liftBaseChange (e.hom ≫ pullback.snd _ _) h _
  have : IsOpenImmersion i := MorphismProperty.of_isPullback hi inferInstance
  exact ⟨i, inferInstance, by simp [i, Category.assoc], by simp [i]⟩

private theorem geometry_integral_normal
    {k : Type u} [Field k] {C : Scheme.{u}} [Nonempty C]
    (i : C ⟶ ProjectiveLine (Spec (.of k))) [IsOpenImmersion i] :
    IsIntegral C ∧ IsNoetherian C ∧
      ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x) := by
  have : IsIntegral C := isIntegral_of_isOpenImmersion i
  have : Smooth (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) :=
    SmoothOfRelativeDimension.smooth 1 _
  have : IsLocallyNoetherian (ProjectiveLine (Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have : CompactSpace (ProjectiveLine (Spec (.of k))) :=
    QuasiCompact.compactSpace_of_compactSpace
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace i
  have : Smooth (i ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) := inferInstance
  have : IsLocallyNoetherian C :=
    LocallyOfFiniteType.isLocallyNoetherian (i ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have : IsRegular C :=
    IsRegular.of_smooth (i ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have : IsNoetherian C := ⟨⟩
  exact ⟨inferInstance, inferInstance, fun x ↦ IsRegular.isIntegrallyClosed_stalk x⟩

private theorem over_pullback_map_sq
    {S T : Scheme.{u}} (f : T ⟶ S) {X Y : Over S} (g : X ⟶ Y) :
    IsPullback ((Over.pullback f).map g).left (pullback.fst X.hom f)
      (pullback.fst Y.hom f) g.left := by
  have h : IsPullback (pullback.snd X.hom f) (pullback.fst X.hom f)
      f (g.left ≫ Y.hom) := by
    simpa only [Over.w] using (IsPullback.of_hasPullback X.hom f).flip
  have hout : IsPullback
      (((Over.pullback f).map g).left ≫ pullback.snd Y.hom f)
      (pullback.fst X.hom f) f (g.left ≫ Y.hom) := by
    simpa only [Over.pullback_map_left, pullback.lift_snd] using h
  exact hout.of_right (by simp) (IsPullback.of_hasPullback Y.hom f).flip

private theorem range_conjugate_map
    {S T : Scheme.{u}} (f : T ⟶ S) {X Y : Over S} (g : X ⟶ Y)
    {X' Y' : Scheme.{u}} (eX : X' ≅ pullback X.hom f)
    (eY : Y' ≅ pullback Y.hom f) :
    Set.range (eX.hom ≫ ((Over.pullback f).map g).left ≫ eY.inv) =
      (fun y ↦ pullback.fst Y.hom f (eY.hom y)) ⁻¹' Set.range g.left := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨pullback.fst X.hom f (eX.hom x), ?_⟩
    simp only [← Scheme.Hom.comp_apply, Category.assoc, Iso.inv_hom_id_assoc]
    simp
  · intro hy
    obtain ⟨x, hx⟩ := hy
    obtain ⟨z, hz, hz'⟩ := Scheme.exists_preimage_of_isPullback
      (over_pullback_map_sq f g) (eY.hom y) x hx.symm
    refine ⟨eX.inv z, ?_⟩
    change eY.inv (((Over.pullback f).map g).left (eX.hom (eX.inv z))) = y
    rw [show eX.hom (eX.inv z) = z by
      exact congrArg (fun t : pullback X.hom f ⟶ pullback X.hom f ↦ t z) eX.inv_hom_id]
    rw [hz]
    exact congrArg (fun t : Y' ⟶ Y' ↦ t y) eY.hom_inv_id

private theorem baseChangedOpen_complement_subsingleton
    {k₀ k : Type u} [Field k₀] [Field k]
    (f : Spec (.of k) ⟶ Spec (.of k₀))
    (U₀ C₀ : (ProjectiveLine (Spec (.of k₀))).Opens)
    (hC : (C₀ : Set (ProjectiveLine (Spec (.of k₀)))) =
      (U₀ : Set (ProjectiveLine (Spec (.of k₀)))) ∪
        Set.range (ProjectiveLine.infinity (Spec (.of k₀))))
    (hUC : U₀ ≤ C₀) {U C : Scheme.{u}}
    (eU : U ≅ pullback (U₀.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)) f)
    (eC : C ≅ pullback (C₀.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)) f)
    (j₀ : Over.mk (U₀.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)) ⟶
      Over.mk (C₀.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)))
    (hj₀ : j₀.left = (ProjectiveLine (Spec (.of k₀))).homOfLE hUC)
    (j : U ⟶ C)
    (hj : j = eU.hom ≫ ((Over.pullback f).map j₀).left ≫ eC.inv) :
    Set.Subsingleton (Set.range j)ᶜ := by
  obtain ⟨i, hi, himap, _⟩ := baseChangedOpen_data f C₀ C eC
  have : IsOpenImmersion i := hi
  have hrange := range_conjugate_map f j₀ eU eC
  rw [← hj, hj₀] at hrange
  have hinf (y : C) (hy : y ∉ Set.range j) :
      i y = ProjectiveLine.infinity (Spec (.of k)) (IsLocalRing.closedPoint k) := by
    have hynot : ((pullback.fst (C₀.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)) f)
        (eC.hom y)).1 ∉ U₀ := by
      intro h
      apply hy
      rw [hrange]
      refine ⟨⟨_, h⟩, ?_⟩
      apply Subtype.ext
      exact Scheme.homOfLE_apply hUC _
    have hyC : ((pullback.fst (C₀.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)) f)
        (eC.hom y)).1 ∈ C₀ :=
      ((pullback.fst (C₀.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)) f)
        (eC.hom y)).property
    have hyUnion := Eq.mp (congrArg
      (fun S : Set (ProjectiveLine (Spec (.of k₀))) ↦
        ((pullback.fst (C₀.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)) f)
          (eC.hom y)).1 ∈ S) hC) hyC
    have hout : ((pullback.fst (C₀.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)) f)
        (eC.hom y)).1 ∉
        (ProjectiveLine.affineChart (Spec (.of k₀))).opensRange := by
      exact (ProjectiveLine.range_infinity (Spec (.of k₀))).le
        (hyUnion.resolve_left hynot)
    have hmap : ProjectiveSpace.map (ULift.{u} (Fin 2)) f (i y) =
        ((pullback.fst (C₀.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)) f)
        (eC.hom y)).1 := by
      exact congrArg (fun t : C ⟶ ProjectiveLine (Spec (.of k₀)) ↦ t y) himap
    have hpre : ProjectiveSpace.map (ULift.{u} (Fin 2)) f ⁻¹ᵁ
        (ProjectiveLine.affineChart (Spec (.of k₀))).opensRange =
        (ProjectiveLine.affineChart (Spec (.of k))).opensRange := by
      simp only [ProjectiveLine.opensRange_affineChart,
        ProjectiveSpace.map_preimage_standardOpen]
    have hiy : i y ∉ (ProjectiveLine.affineChart (Spec (.of k))).opensRange := by
      rw [← hpre]
      change ProjectiveSpace.map (ULift.{u} (Fin 2)) f (i y) ∉
        (ProjectiveLine.affineChart (Spec (.of k₀))).opensRange
      rwa [hmap]
    have hs := ProjectiveLine.compl_opensRange_affineChart_eq_singleton k
    have his : i y ∈
        ((ProjectiveLine.affineChart (Spec (.of k))).opensRange : Set _)ᶜ := hiy
    rw [hs] at his
    exact his
  intro y hy z hz
  apply i.isOpenEmbedding.injective
  exact (hinf y hy).trans (hinf z hz).symm

private theorem geometric_open_data
    {k₀ k : Type u} [Field k₀] [Field k]
    (f : Spec (.of k) ⟶ Spec (.of k₀))
    (U₀ C₀ : (ProjectiveLine (Spec (.of k₀))).Opens)
    (hC : (C₀ : Set (ProjectiveLine (Spec (.of k₀)))) =
      (U₀ : Set (ProjectiveLine (Spec (.of k₀)))) ∪
        Set.range (ProjectiveLine.infinity (Spec (.of k₀))))
    (hUC : U₀ ≤ C₀) {U C : Scheme.{u}} [Nonempty U]
    (eU : U ≅ pullback (U₀.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)) f)
    (eC : C ≅ pullback (C₀.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)) f)
    (j₀ : Over.mk (U₀.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)) ⟶
      Over.mk (C₀.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)))
    (hj₀ : j₀.left = (ProjectiveLine (Spec (.of k₀))).homOfLE hUC)
    (j : U ⟶ C)
    (hj : j = eU.hom ≫ ((Over.pullback f).map j₀).left ≫ eC.inv)
    (x : C)
    (hx : (pullback.fst (C₀.ι ≫ ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)) f) (eC.hom x) ∉
      Set.range ((ProjectiveLine (Spec (.of k₀))).homOfLE hUC)) :
    IsOpenImmersion j ∧ IsIntegral U ∧ IsIntegral C ∧ IsNoetherian C ∧
      (∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y)) ∧ (Set.range j)ᶜ = {x} := by
  have : Nonempty C := ⟨x⟩
  have : IsOpenImmersion j₀.left := by rw [hj₀]; infer_instance
  have : IsOpenImmersion ((Over.pullback f).map j₀).left :=
    MorphismProperty.of_isPullback (over_pullback_map_sq f j₀).flip inferInstance
  have hjopen : IsOpenImmersion j := by rw [hj]; infer_instance
  obtain ⟨iU, hiU, _, _⟩ := baseChangedOpen_data f U₀ U eU
  obtain ⟨iC, hiC, _, _⟩ := baseChangedOpen_data f C₀ C eC
  have : IsOpenImmersion iU := hiU
  have : IsOpenImmersion iC := hiC
  obtain ⟨hUintegral, _, _⟩ := geometry_integral_normal iU
  obtain ⟨hCintegral, hCnoeth, hCnormal⟩ := geometry_integral_normal iC
  refine ⟨hjopen, hUintegral, hCintegral, hCnoeth, hCnormal, ?_⟩
  have hrange := range_conjugate_map f j₀ eU eC
  rw [← hj, hj₀] at hrange
  have hxj : x ∉ Set.range j := by rwa [hrange]
  have hs := baseChangedOpen_complement_subsingleton f U₀ C₀ hC hUC eU eC j₀ hj₀ j hj
  ext y
  constructor
  · exact fun hy ↦ hs hy hxj
  · rintro rfl
    exact hxj

private theorem henselization_normal
    (A H : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing H] [HenselianLocalRing H] [Algebra A H]
    [Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H]
    [IsScalarTower A (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H]
    (hH : Algebra.IsHenselizationAtPrime' A (IsLocalRing.maximalIdeal A) H) :
    IsIntegrallyClosed H := by
  have hind := RingHom.henselization_prime_indEtale A (IsLocalRing.maximalIdeal A) H hH
  rw [← IsScalarTower.algebraMap_eq A
    (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H] at hind
  have : Algebra.IndEtale A H := (RingHom.IndEtale.algebraMap_iff A H).mp hind
  obtain ⟨I, hI, hfilter, P, hP⟩ :=
    Algebra.IndEtale.exists_colimitPresentation (R := A) (S := H)
  let : SmallCategory I := hI
  let : IsFiltered I := hfilter
  let e := (colimit.isColimit P.diag).coconePointUniqueUpToIso P.isColimit
  let er : ↥(colimit P.diag) ≃+* H := (CommAlgCat.algEquivOfIso e).toRingEquiv
  have : IsLocalRing ↥(colimit P.diag) := er.symm.isLocalRing
  obtain ⟨⟨hdomain, hclosed⟩, _⟩ :=
    CommAlgCat.isDomain_isIntegrallyClosed_injective_of_etale_colimit A
      (fun p _ ↦ ⟨inferInstance,
        isIntegrallyClosed_of_isLocalization _ p.primeCompl
          p.primeCompl_le_nonZeroDivisors⟩) P.diag hP
  have := hclosed
  exact IsIntegrallyClosed.of_equiv er

private theorem kernel_mem_iff_fixed
    {U C : Scheme.{u}} (j : U ⟶ C)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (g : Aut (fiber b)) :
    g ∈ (pullbackPathHom j b).ker ↔
      ∀ (P : C.FiniteEtale) (z : (fiber b).obj ((Scheme.FiniteEtale.pullback j).obj P)),
        g.hom.app _ z = z := by
  constructor
  · intro hg P z
    have h := congrArg
      (fun a : Aut (fiber (b ≫ j)) ↦ a.hom.app P ((pullbackFiberIso j b).hom.app P z)) hg
    change (pullbackFiberIso j b).hom.app P (g.hom.app _
      ((pullbackFiberIso j b).inv.app P ((pullbackFiberIso j b).hom.app P z))) =
        (pullbackFiberIso j b).hom.app P z at h
    have he : (pullbackFiberIso j b).inv.app P
        ((pullbackFiberIso j b).hom.app P z) = z :=
      ConcreteCategory.congr_hom ((pullbackFiberIso j b).hom_inv_id_app P) z
    rw [he] at h
    exact (ConcreteCategory.bijective_of_isIso ((pullbackFiberIso j b).hom.app P)).1 h
  · intro hg
    apply Iso.ext
    apply NatTrans.ext
    funext P
    apply FintypeCat.hom_ext
    intro z
    change (pullbackFiberIso j b).hom.app P
      (g.hom.app _ ((pullbackFiberIso j b).inv.app P z)) = z
    rw [hg]
    exact ConcreteCategory.congr_hom ((pullbackFiberIso j b).inv_hom_id_app P) z

private theorem local_model_of_extension
    {U C : Scheme.{u}} (j : U ⟶ C)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (x : C) (B : HenselianBoundaryLocalData j b x) (P : U.FiniteEtale)
    (hext : ∃ Q : C.FiniteEtale,
      Nonempty ((Scheme.FiniteEtale.pullback j).obj Q ≅ P)) :
    ∃ Q : (Spec (.of B.H)).FiniteEtale,
      Nonempty ((Scheme.FiniteEtale.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap B.H B.K)))).obj Q ≅
          (Scheme.FiniteEtale.pullback B.localGenericPoint).obj P) := by
  obtain ⟨Q, ⟨e⟩⟩ := hext
  let h : Spec (.of B.H) ⟶ C :=
    Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x) B.H)) ≫ C.fromSpecStalk x
  let k : Spec (.of B.K) ⟶ Spec (.of B.H) :=
    Spec.map (CommRingCat.ofHom (algebraMap B.H B.K))
  have hk : k ≫ h = B.localGenericPoint ≫ j := by
    rw [B.localGenericPoint_spec]
    dsimp [k, h]
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq _ _ _).symm
  refine ⟨(Scheme.FiniteEtale.pullback h).obj Q, ⟨?_⟩⟩
  exact (pullbackCompIso k h Q).symm ≪≫
    eqToIso (congrArg (fun f ↦ (Scheme.FiniteEtale.pullback f).obj Q) hk) ≪≫
    pullbackCompIso B.localGenericPoint j Q ≪≫
    (Scheme.FiniteEtale.pullback B.localGenericPoint).mapIso e

private theorem kernel_eq_normalClosure_of_extension
    {U C : Scheme.{u}} [ConnectedSpace U] (j : U ⟶ C)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (G : ProfiniteGrp.{u}) (eG : G ≃ₜ* Aut (fiber b)) (S : Subgroup G)
    (hext : ∀ P : U.FiniteEtale,
      (∃ Q : C.FiniteEtale,
        Nonempty ((Scheme.FiniteEtale.pullback j).obj Q ≅ P)) ↔
        ∀ g ∈ S, ∀ z : (fiber b).obj P, (eG g).hom.app P z = z) :
    ((pullbackPathHom j b).comp eG.toMonoidHom).ker =
      (Subgroup.normalClosure (S : Set G)).topologicalClosure := by
  classical
  let (P : U.FiniteEtale) : MulAction G ((fiber b).obj P) :=
    MulAction.compHom _ eG.toMonoidHom
  have hsmul (g : G) (P : U.FiniteEtale) (z : (fiber b).obj P) :
      g • z = (eG g).hom.app P z := rfl
  let : IsFundamentalGroup (fiber b) G :=
    { naturality g P Q f z := by
        simp only [hsmul]
        exact IsNaturalSMul.naturality (eG g) f z
      transitive_of_isGalois P _ := by
        refine ⟨fun z w ↦ ?_⟩
        obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (Aut (fiber b)) z w
        change a.hom.app P z = w at ha
        exact ⟨eG.symm a, by
          simpa only [hsmul, eG.apply_symm_apply] using ha⟩
      continuous_smul P := by
        refine ⟨?_⟩
        change Continuous (fun p : G × (fiber b).obj P ↦ eG p.1 • p.2)
        exact continuous_smul.comp
          ((eG.continuous.comp continuous_fst).prodMk continuous_snd)
      non_trivial' g hg := by
        apply eG.injective
        rw [map_one]
        exact IsFundamentalGroup.non_trivial (F := fiber b) (eG g) (fun P z ↦ hg P z) }
  let q := (pullbackPathHom j b).comp eG.toMonoidHom
  have hker (g : G) : g ∈ q.ker ↔
      ∀ (Q : C.FiniteEtale)
        (z : (fiber b).obj ((Scheme.FiniteEtale.pullback j).obj Q)), g • z = z :=
    kernel_mem_iff_fixed j b (eG g)
  have hS : S ≤ q.ker := by
    intro g hg
    exact (hker g).mpr (fun Q z ↦ (hext _).mp ⟨Q, ⟨Iso.refl _⟩⟩ g hg z)
  have hc : IsClosed (q.ker : Set G) :=
    isClosed_singleton.preimage ((continuous_pullbackPathHom j b).comp eG.continuous)
  apply le_antisymm
  · intro g hg
    let N := (Subgroup.normalClosure (S : Set G)).topologicalClosure
    have : N.Normal := Subgroup.is_normal_topologicalClosure _
    apply mem_of_forall_smul_eq_self b G N (Subgroup.isClosed_topologicalClosure _) g
    intro P z hz
    obtain ⟨Z, i, w, rfl, hZ, hi⟩ := fiber_in_connected_component (fiber b) P z
    have hinj : Function.Injective ((fiber b).map i) :=
      ConcreteCategory.injective_of_mono_of_preservesPullback ((fiber b).map i)
    have hw (k : G) (hk : k ∈ N) : k • w = w := by
      apply hinj
      rw [IsNaturalSMul.naturality, hz k hk]
    have hZfixed (k : G) (hk : k ∈ N) (v : (fiber b).obj Z) : k • v = v := by
      obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq G w v
      have hconj : a⁻¹ * k * a ∈ N := by
        simpa using (inferInstance : N.Normal).conj_mem k hk a⁻¹
      rw [← mul_smul, show k * a = a * (a⁻¹ * k * a) by group, mul_smul, hw _ hconj]
    obtain ⟨Q, ⟨e⟩⟩ := (hext Z).mpr (fun k hk v ↦
      hZfixed k (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hk)) v)
    rw [← IsNaturalSMul.naturality, smul_eq_self_of_iso b G e ((hker g).mp hg Q)]
  · exact Subgroup.topologicalClosure_minimal _
      (Subgroup.normalClosure_le_normal hS) hc

private theorem local_inertia_fixes
    {U C : Scheme.{u}} (j : U ⟶ C)
    {Ωb : Type u} [Field Ωb] [IsAlgClosed Ωb] (b : Spec (.of Ωb) ⟶ U)
    (x : C) (B : HenselianBoundaryLocalData j b x)
    {σ : B.Ω ≃ₐ[B.K] B.Ω} (hσ : σ ∈ B.residueAction.ker)
    (Q : (Spec (.of B.H)).FiniteEtale)
    (t : (fiber (pointOfAlgebra B.Ω
      (Spec.map (CommRingCat.ofHom (algebraMap B.H B.K)) ≫ 𝟙 _))).obj Q) :
    (galoisToAut _ σ).hom.app Q t = t := by
  let R := integralClosure B.H B.Ω
  let κ := IsLocalRing.ResidueField R
  have : IsAlgClosed κ := IsAlgClosure.isAlgClosed (IsLocalRing.ResidueField B.H)
  let ap := integralClosurePoint B.Ω (𝟙 (Spec (.of B.H)))
  have h := pointOfAlgebra_integralClosurePoint
    (K := B.K) (Ω := B.Ω) (𝟙 (Spec (.of B.H)))
  let t' : (fiber (pointOfAlgebra B.Ω ap)).obj Q := Over.homMk t.left (by
    change t.left ≫ Q.obj.hom = _
    rw [fiber_left_comp, h]
    rfl)
  have heΩ : (specMapIso σ.toRingEquiv).hom ≫ pointOfAlgebra B.Ω ap =
      pointOfAlgebra B.Ω ap := by
    rw [h]
    exact specMapIso_hom_comp_pointOfAlgebra _ σ
  have heκ : (specMapIso (RingEquiv.refl κ)).hom ≫ pointOfAlgebra κ ap =
      pointOfAlgebra κ ap := by
    change Spec.map (𝟙 _) ≫ _ = _
    rw [Spec.map_id, Category.id_comp]
  have heB : (B.integralAction σ).toRingEquiv =
      galoisIntegralClosure (R := B.H) σ := by
    ext z
    exact B.integralAction_spec σ z
  have hres (z : R) : IsLocalRing.residue R (B.integralAction σ z) =
      IsLocalRing.residue R z := by
    rw [← B.residueAction_spec]
    change B.residueAction σ (IsLocalRing.residue R z) = _
    rw [show B.residueAction σ = 1 from hσ]
    rfl
  have key := specialization_app_fiberPrecompIso ap
    (B.integralAction σ).toRingEquiv σ.toRingEquiv (RingEquiv.refl κ)
    (by rw [heB]; exact specMap_galoisIntegralClosure_comp _ σ)
    (by ext z; exact B.integralAction_spec σ z)
    (by ext z; exact hres z) heΩ heκ Q t'
  have hrefl :
      (fiberPrecompIso _ (specMapIso (RingEquiv.refl κ)) heκ).hom.app Q
        ((specialization B.Ω κ ap).app Q t') = (specialization B.Ω κ ap).app Q t' := by
    apply fiber_ext
    rw [fiberPrecompIso_hom_app_left]
    change Spec.map (𝟙 _) ≫ _ = _
    rw [Spec.map_id, Category.id_comp]
  rw [hrefl] at key
  have hinj : Function.Injective ((specialization B.Ω κ ap).app Q) :=
    (ConcreteCategory.bijective_of_isIso _).1
  have hp := congrArg Over.Hom.left (hinj key)
  apply fiber_ext
  rw [galoisToAut_hom_app_left]
  rw [fiberPrecompIso_hom_app_left] at hp
  -- Rewriting `t'.left` explicitly avoids a slow kernel unfolding of `Over.homMk`.
  have ht : t'.left = t.left := Over.homMk_left _ _
  rw [ht] at hp
  exact hp

private theorem decomposition_app_path
    {U C : Scheme.{u}} (j : U ⟶ C)
    {Ωb : Type u} [Field Ωb] [IsAlgClosed Ωb] (b : Spec (.of Ωb) ⟶ U)
    (x : C) (B : HenselianBoundaryLocalData j b x)
    (σ : B.Ω ≃ₐ[B.K] B.Ω) (P : U.FiniteEtale)
    (z : (fiber (pointOfAlgebra B.Ω B.localGenericPoint)).obj P) :
    (B.decomposition σ).hom.app P (B.path.hom.app P z) =
      B.path.hom.app P ((galoisToAut B.localGenericPoint σ).hom.app P z) := by
  apply (ConcreteCategory.bijective_of_isIso (B.path.inv.app P)).1
  have hc : B.path.inv.app P (B.path.hom.app P
      ((galoisToAut B.localGenericPoint σ).hom.app P z)) =
        (galoisToAut B.localGenericPoint σ).hom.app P z :=
    ConcreteCategory.congr_hom (B.path.hom_inv_id_app P) _
  rw [hc]
  apply fiber_ext
  exact B.decomposition_spec σ P z

private theorem decomposition_fixed_of_galois_fixed
    {U C : Scheme.{u}} (j : U ⟶ C)
    {Ωb : Type u} [Field Ωb] [IsAlgClosed Ωb] (b : Spec (.of Ωb) ⟶ U)
    (x : C) (B : HenselianBoundaryLocalData j b x)
    (σ : B.Ω ≃ₐ[B.K] B.Ω) (P : U.FiniteEtale)
    (hfix : ∀ z : (fiber (pointOfAlgebra B.Ω B.localGenericPoint)).obj P,
      (galoisToAut B.localGenericPoint σ).hom.app P z = z)
    (z : (fiber b).obj P) : (B.decomposition σ).hom.app P z = z := by
  obtain ⟨w, rfl⟩ := (ConcreteCategory.bijective_of_isIso (B.path.hom.app P)).2 z
  rw [decomposition_app_path, hfix]

private theorem inertia_fixed_of_local_model
    {U C : Scheme.{u}} (j : U ⟶ C)
    {Ωb : Type u} [Field Ωb] [IsAlgClosed Ωb] (b : Spec (.of Ωb) ⟶ U)
    (x : C) (B : HenselianBoundaryLocalData j b x) (P : U.FiniteEtale)
    (hmodel : ∃ Q : (Spec (.of B.H)).FiniteEtale,
      Nonempty ((Scheme.FiniteEtale.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap B.H B.K)))).obj Q ≅
          (Scheme.FiniteEtale.pullback B.localGenericPoint).obj P)) :
    ∀ σ ∈ B.residueAction.ker, ∀ z : (fiber b).obj P,
      (B.decomposition σ).hom.app P z = z := by
  obtain ⟨Q, ⟨e⟩⟩ := hmodel
  intro σ hσ
  apply decomposition_fixed_of_galois_fixed j b x B σ P
  intro z
  let a := Spec.map (CommRingCat.ofHom (algebraMap B.K B.Ω))
  let k := Spec.map (CommRingCat.ofHom (algebraMap B.H B.K))
  let s := Spec.map (CommRingCat.ofHom σ.toRingHom)
  have hak : a ≫ k = Spec.map (CommRingCat.ofHom (algebraMap B.H B.Ω)) := by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq _ _ _).symm
  let zk := pullback.lift z.left a (fiber_left_comp _ z)
  let w := zk ≫ e.inv.hom.left
  have hw : w ≫ pullback.snd Q.obj.hom k = a := by
    dsimp [w]
    have hew : e.inv.hom.left ≫ pullback.snd Q.obj.hom k =
        pullback.snd P.obj.hom B.localGenericPoint := hom_left_comp e.inv
    rw [Category.assoc, hew, pullback.lift_snd]
  let tq : (fiber (pointOfAlgebra B.Ω (k ≫ 𝟙 _))).obj Q :=
    Over.homMk (w ≫ pullback.fst Q.obj.hom k) (by
      change (w ≫ pullback.fst Q.obj.hom k) ≫ Q.obj.hom = _
      rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
      simp only [pointOfAlgebra]
      rfl)
  have hq : s ≫ (w ≫ pullback.fst Q.obj.hom k) = w ≫ pullback.fst Q.obj.hom k :=
    congrArg Over.Hom.left (local_inertia_fixes j b x B hσ Q tq)
  have ha : s ≫ a = a := by
    dsimp [s, a]
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact σ.commutes r
  have hww : s ≫ w = w := by
    apply pullback.hom_ext
    · simpa only [Category.assoc] using hq
    · rw [Category.assoc, hw, ha]
  have hzk : s ≫ zk = zk := by
    apply (cancel_mono e.inv.hom.left).mp
    simpa only [w, Category.assoc] using hww
  apply fiber_ext
  rw [galoisToAut_hom_app_left]
  change s ≫ z.left = z.left
  have hz := congrArg (· ≫ pullback.fst P.obj.hom B.localGenericPoint) hzk
  simpa only [zk, Category.assoc, pullback.lift_fst] using hz

private theorem generic_inertia_fixed_of_decomposition_fixed
    {U C : Scheme.{u}} (j : U ⟶ C)
    {Ωb : Type u} [Field Ωb] [IsAlgClosed Ωb] (b : Spec (.of Ωb) ⟶ U)
    (x : C) (B : HenselianBoundaryLocalData j b x) (P : U.FiniteEtale)
    (hfixed : ∀ σ ∈ B.residueAction.ker, ∀ z : (fiber b).obj P,
      (B.decomposition σ).hom.app P z = z) :
    ∀ σ ∈ B.residueAction.ker,
      ∀ z : (fiber (Spec.map (CommRingCat.ofHom (algebraMap B.K B.Ω)))).obj
        ((Scheme.FiniteEtale.pullback B.localGenericPoint).obj P),
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ z.left = z.left := by
  intro σ hσ z
  let a := Spec.map (CommRingCat.ofHom (algebraMap B.K B.Ω))
  let s := Spec.map (CommRingCat.ofHom σ.toRingHom)
  have hz : z.left ≫ pullback.snd P.obj.hom B.localGenericPoint = a :=
    fiber_left_comp _ z
  let w : (fiber (pointOfAlgebra B.Ω B.localGenericPoint)).obj P :=
    Over.homMk (z.left ≫ pullback.fst P.obj.hom B.localGenericPoint) (by
      change (z.left ≫ pullback.fst P.obj.hom B.localGenericPoint) ≫ P.obj.hom = _
      rw [Category.assoc, pullback.condition, ← Category.assoc, hz]
      rfl)
  have hw : (galoisToAut B.localGenericPoint σ).hom.app P w = w := by
    apply (ConcreteCategory.bijective_of_isIso (B.path.hom.app P)).1
    rw [← decomposition_app_path, hfixed σ hσ]
  have hw' : s ≫ (z.left ≫ pullback.fst P.obj.hom B.localGenericPoint) =
      z.left ≫ pullback.fst P.obj.hom B.localGenericPoint :=
    congrArg Over.Hom.left hw
  have ha : s ≫ a = a := by
    dsimp [s, a]
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact σ.commutes r
  apply pullback.hom_ext
  · simpa only [Category.assoc] using hw'
  · rw [Category.assoc, hz]
    exact ha

private theorem inertia_fixed_iff
    {U C : Scheme.{u}} (j : U ⟶ C)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (x : C) (B : HenselianBoundaryLocalData j b x)
    (G : ProfiniteGrp.{u}) (eG : G ≃ₜ* Aut (fiber b)) (P : U.FiniteEtale) :
    (∀ g ∈ (B.residueAction.ker.map B.decomposition).comap eG.toMonoidHom,
      ∀ z : (fiber b).obj P, (eG g).hom.app P z = z) ↔
      ∀ σ ∈ B.residueAction.ker, ∀ z : (fiber b).obj P,
        (B.decomposition σ).hom.app P z = z := by
  constructor
  · intro h σ hσ z
    have hm : eG.symm (B.decomposition σ) ∈
        (B.residueAction.ker.map B.decomposition).comap eG.toMonoidHom := by
      change eG (eG.symm (B.decomposition σ)) ∈
        B.residueAction.ker.map B.decomposition
      rw [eG.apply_symm_apply]
      exact ⟨σ, hσ, rfl⟩
    simpa only [eG.apply_symm_apply] using h _ hm z
  · intro h g hg z
    obtain ⟨σ, hσ, heq⟩ := hg
    change B.decomposition σ = eG g at heq
    rw [← heq]
    exact h σ hσ z

private theorem extension_of_stalk_model
    {C : Scheme.{u}} [IsNoetherian C] [QuasiSeparatedSpace C]
    (V : C.Opens) (P : ((𝟙 C) ⁻¹ᵁ V).toScheme.FiniteEtale) (x : C)
    (hboundary : (((𝟙 C) ⁻¹ᵁ V : C.Opens) : Set C)ᶜ = {x})
    (Q : (pullback (𝟙 C) (C.fromSpecStalk x)).FiniteEtale)
    (e : Nonempty ((Scheme.FiniteEtale.pullback
      (pullback.fst ((𝟙 C) ⁻¹ᵁ V).ι (pullback.fst (𝟙 C) (C.fromSpecStalk x)))).obj P ≅
      (Scheme.FiniteEtale.pullback
      (pullback.snd ((𝟙 C) ⁻¹ᵁ V).ι (pullback.fst (𝟙 C) (C.fromSpecStalk x)))).obj Q)) :
    ∃ R : C.FiniteEtale,
      Nonempty ((Scheme.FiniteEtale.pullback ((𝟙 C) ⁻¹ᵁ V).ι).obj R ≅ P) := by
  obtain ⟨W, hxW, R, ⟨a⟩⟩ :=
    Scheme.FiniteEtale.exists_neighbourhood_model_of_stalk (𝟙 C) V P x Q e
  apply exists_pullback_iso_of_isPullback
    (C.homOfLE (inf_le_left : ((𝟙 C) ⁻¹ᵁ V) ⊓ ((𝟙 C) ⁻¹ᵁ W) ≤ _))
    (C.homOfLE (inf_le_right : ((𝟙 C) ⁻¹ᵁ V) ⊓ ((𝟙 C) ⁻¹ᵁ W) ≤ _))
    ((𝟙 C) ⁻¹ᵁ V).ι ((𝟙 C) ⁻¹ᵁ W).ι (isPullback_opens_inf _ _) _ P R a
  intro y
  by_cases hy : y ∈ (𝟙 C) ⁻¹ᵁ V
  · exact Or.inl ⟨⟨y, hy⟩, rfl⟩
  · have hyx : y = x := by
      have hm : y ∈ ((((𝟙 C) ⁻¹ᵁ V : C.Opens) : Set C)ᶜ) := hy
      rwa [hboundary] at hm
    subst y
    exact Or.inr ⟨⟨x, hxW⟩, rfl⟩

private theorem extension_of_openRange_stalk_model
    {C U : Scheme.{u}} [IsNoetherian C] [QuasiSeparatedSpace C]
    (j : U ⟶ C) [IsOpenImmersion j] (P : U.FiniteEtale) (x : C)
    (hboundary : (Set.range j)ᶜ = {x})
    (Q : (pullback (𝟙 C) (C.fromSpecStalk x)).FiniteEtale)
    (e : Nonempty ((Scheme.FiniteEtale.pullback
      (pullback.fst ((𝟙 C) ⁻¹ᵁ j.opensRange).ι
        (pullback.fst (𝟙 C) (C.fromSpecStalk x)))).obj
          ((Scheme.FiniteEtale.pullback j.isoOpensRange.inv).obj P) ≅
      (Scheme.FiniteEtale.pullback
      (pullback.snd ((𝟙 C) ⁻¹ᵁ j.opensRange).ι
        (pullback.fst (𝟙 C) (C.fromSpecStalk x)))).obj Q)) :
    ∃ R : C.FiniteEtale, Nonempty ((Scheme.FiniteEtale.pullback j).obj R ≅ P) := by
  obtain ⟨R, ⟨a⟩⟩ := extension_of_stalk_model j.opensRange
    ((Scheme.FiniteEtale.pullback j.isoOpensRange.inv).obj P) x hboundary Q e
  refine ⟨R, ⟨?_⟩⟩
  have hj : j.isoOpensRange.hom ≫ ((𝟙 C) ⁻¹ᵁ j.opensRange).ι = j :=
    Scheme.Hom.isoOpensRange_hom_ι j
  have hid : j.isoOpensRange.hom ≫ j.isoOpensRange.inv = 𝟙 U :=
    j.isoOpensRange.hom_inv_id
  exact eqToIso (congrArg (fun f ↦ (Scheme.FiniteEtale.pullback f).obj R) hj.symm) ≪≫
    pullbackCompIso _ _ R ≪≫
    (Scheme.FiniteEtale.pullback j.isoOpensRange.hom).mapIso a ≪≫
    (pullbackCompIso _ _ P).symm ≪≫
    eqToIso (congrArg (fun f ↦ (Scheme.FiniteEtale.pullback f).obj P) hid) ≪≫
    pullbackIdIso P

open CategoryTheory AlgebraicGeometry in
private theorem residue_algClosed_at_complement
    {k : Type u} [Field k] [IsAlgClosed k]
    {U C : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j]
    (i : C ⟶ ProjectiveLine (Spec (.of k))) [IsOpenImmersion i]
    (x : C) (hboundary : (Set.range j)ᶜ = {x}) :
    IsAlgClosed (C.residueField x) := by
  let p := i ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)
  have : LocallyOfFiniteType p := inferInstance
  have hx : IsClosed ({x} : Set C) := by
    rw [← hboundary]
    exact j.isOpenEmbedding.isOpen_range.isClosed_compl
  let := (p.residueFieldAlgebraMap x).toAlgebra
  have : Module.Finite k (C.residueField x) := p.finite_residueField_of_isClosed x hx
  exact IsAlgClosed.of_ringEquiv k _
    (RingEquiv.ofBijective (algebraMap k (C.residueField x))
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)))

set_option maxHeartbeats 0 in
-- Elaborating the geometric pullback and fibre comparisons exceeds the default budget.
/-- On the geometric open curve, filling infinity kills the closed normal subgroup
generated by the recorded geometric henselian inertia, with the actual fibre-functor map.

Source: Stacks 0BTD and 0BSW; rem-dl-a1-conventions, inertia equivalence.
(blueprint: lem-dl-a1-geometric-open-inertia-kernel).

Proof:
1. Use the cartesian projective-line base-change squares to realize U and C as
nonempty opens of P1 over the geometric field. Smoothness gives regularity and
normal stalks, and the Noetherian projective line makes C Noetherian. The range
of infinity is a singleton after base change, so the complement of j is exactly
{x}. The ordinary henselization B.H is normal by its ind-etale presentation.
2. Test the kernel on finite etale covers: an automorphism is in the kernel
precisely when it fixes every fibre of a cover pulled back from C. If S is the
recorded inertia image and N its closed normal closure, membership in N is
likewise detected by finite fibres. Given an N-fixed point, pass to its connected
component. Normality and transitivity imply that N fixes that entire component.
If covers fixed by S extend to C, the component therefore extends, and the kernel
fixes the original point. The reverse inclusion follows from the kernel being
closed and normal. This proves the group-theoretic reduction without a generic
absolute Galois presentation of C or U.
3. A cover pulled back from C has an actual finite etale B.H-model, by pullback
associativity and B.localGenericPoint_spec. Specialize its generic fibre through
the integral closure of B.H in B.Omega. B.integralAction_spec and
B.residueAction_spec make specialization equivariant, and an element of the
residue kernel acts identically on the closed fibre. Specialization is an
isomorphism, so it fixes the generic fibre. Transport through the given model
isomorphism and B.path; B.decomposition_spec gives exactly the recorded action.
4. Conversely, explicitly transport the fixed-point hypothesis through B.path
and through the pullback projections. The closed boundary point has algebraically
closed residue field, so apply the geometric henselian inertia model theorem to
this finite etale B.K-cover. Descend its finite etale henselian model to the
ordinary stalk by the stalk-model theorem, retaining the comparison over the
punctured local overlap. Spread this stalk model and comparison to a neighbourhood
W of x, using finite presentation. The opens U and W cover C, since only x is
missing from U. Glue the finite etale covers by their overlap isomorphism.
5. Apply step 2, with the subgroup transported through eG. All comparisons use
the specified fibre map and path. The statement and every public signature are
unchanged; no representation, coefficient system or Frobenius is involved.
-/
theorem geometric_open_inertia_kernel
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (U₀ C₀ : (ProjectiveLine (Spec (.of D.k₀))).Opens)
    (_hU : U₀ ≤ (ProjectiveLine.affineChart (Spec (.of D.k₀))).opensRange)
    (_hdense : Dense (U₀ : Set (ProjectiveLine (Spec (.of D.k₀)))))
    (_hC : (C₀ : Set (ProjectiveLine (Spec (.of D.k₀)))) =
      (U₀ : Set (ProjectiveLine (Spec (.of D.k₀)))) ∪
        Set.range (ProjectiveLine.infinity (Spec (.of D.k₀))))
    (hUC : U₀ ≤ C₀) (U C : Scheme.{u})
    (eU : U ≅ pullback (U₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (eC : C ≅ pullback (C₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (j₀ : Over.mk (U₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀)) ⟶
      Over.mk (C₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀)))
    (_hj₀ : j₀.left = (ProjectiveLine (Spec (.of D.k₀))).homOfLE hUC)
    (j : U ⟶ C)
    (_hj : j = eU.hom ≫ ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left ≫ eC.inv)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (_hb : IsGenericPoint (b (IsLocalRing.closedPoint Ω)) Set.univ)
    (x : C)
    (_hx : (pullback.fst
      (C₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) (eC.hom x) ∉
      Set.range ((ProjectiveLine (Spec (.of D.k₀))).homOfLE hUC))
    (B : HenselianBoundaryLocalData j b x)
    (G : ProfiniteGrp.{u}) (eG : G ≃ₜ* Aut (fiber b)) :
    ((pullbackPathHom j b).comp eG.toMonoidHom).ker =
      (Subgroup.normalClosure
        (((B.residueAction.ker.map B.decomposition).comap eG.toMonoidHom : Subgroup G) :
          Set G)).topologicalClosure := by
  have : Nonempty U := ⟨b (IsLocalRing.closedPoint Ω)⟩
  obtain ⟨hjopen, hUint, hCint, hCnoeth, hCnormal, hboundary⟩ :=
    geometric_open_data (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
      U₀ C₀ _hC hUC eU eC j₀ _hj₀ j _hj x _hx
  have : IsOpenImmersion j := hjopen
  have : IsIntegral U := hUint
  have : IsIntegral C := hCint
  have : IsNoetherian C := hCnoeth
  have : IsIntegrallyClosed (C.presheaf.stalk x) := hCnormal x
  have : IsIntegrallyClosed B.H :=
    henselization_normal (C.presheaf.stalk x) B.H B.isHenselization
  obtain ⟨i, hi, _, _⟩ := baseChangedOpen_data
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) C₀ C eC
  have : IsOpenImmersion i := hi
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : IsAlgClosed (C.residueField x) :=
    residue_algClosed_at_complement j i x hboundary
  apply kernel_eq_normalClosure_of_extension j b G eG
    ((B.residueAction.ker.map B.decomposition).comap eG.toMonoidHom)
  intro P
  rw [inertia_fixed_iff j b x B G eG P]
  constructor
  · intro hext
    exact inertia_fixed_of_local_model j b x B P (local_model_of_extension j b x B P hext)
  · intro hfixed
    obtain ⟨Q, e⟩ := stalk_model_of_henselian_model j b x B hCnormal P
      (henselian_model_of_inertia_fixed j b x B
        ((Scheme.FiniteEtale.pullback B.localGenericPoint).obj P)
        (generic_inertia_fixed_of_decomposition_fixed j b x B P hfixed))
    exact extension_of_openRange_stalk_model j P x hboundary Q e

end AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia
