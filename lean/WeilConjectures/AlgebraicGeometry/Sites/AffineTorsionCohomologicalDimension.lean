/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Curve.TorsionCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension
import WeilConjectures.SixFunctors.OpenClosed.Supported
import WeilConjectures.AlgebraicGeometry.Sites.LerayVanishing
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import Sheaf.AlgebraicGeometry.Sites.AffineLineProjectionStalkBound
import Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula
import Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModel
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import Sheaf.CategoryTheory.Abelian.ExactFunctorHigherDerivedVanishing

/-!
# The affine Artin vanishing bound

Let `K` be a field with `cd_tor(K) ≤ c` and `X` an affine `K`-scheme of finite type. Then
`cd_tor(X) ≤ dim X + c` (`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine`,
blueprint `thm-sc-affine-torsion-cd`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

private theorem isTorsion_lowerStar_finite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : F.IsTorsion) : ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj F).IsTorsion := by
  have : LocallySmall.{u + 1} Y.Etale := locallySmall_max.{u + 1, u}
  apply Sheaf.IsTorsion.of_isAddTorsion_sheafFiber
    (isConservativeFamilyOfPoints_ulift_pointSmallEtale Y)
  rintro ⟨_, ⟨y⟩⟩
  let s := Y.algClosurePoint y
  let G (t : Scheme.Hom.GeometricFiber f s) : AddCommGrpCat.{u + 1} :=
    (pointSmallEtale t.1).sheafFiber.obj F
  have : Finite (Scheme.Hom.GeometricFiber f s) := inferInstance
  have : Small.{u + 1} (Discrete (Scheme.Hom.GeometricFiber f s)) := small_succ _
  have : HasLimitsOfShape (Discrete (Scheme.Hom.GeometricFiber f s))
      AddCommGrpCat.{u + 1} := AddCommGrpCat.hasLimitsOfShape
  have hG (t : Scheme.Hom.GeometricFiber f s) : IsAddTorsion (G t) :=
    (isTorsion_iff_isAddTorsion_sheafFiber F).mp hF _ t.1
  have : PreservesLimit (Discrete.functor G) (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    inferInstance
  have hprod : IsAddTorsion (∏ᶜ G : AddCommGrpCat.{u + 1}) := by
    intro z
    have hz : IsOfFinAddOrder (fun t ↦ (Pi.π G t) z) :=
      IsOfFinAddOrder.pi fun t ↦ hG t _
    obtain ⟨n, hn, hz⟩ := hz.exists_nsmul_eq_zero
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, ?_⟩
    apply Concrete.limit_ext (Discrete.functor G)
    rintro ⟨t⟩
    change (Pi.π G t) (n • z) = (Pi.π G t) 0
    simpa using congrFun hz t
  let e := Etale.stalkIsoPi AddCommGrpCat.{u + 1} f s F
  have hs : IsAddTorsion ((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1}) |>.obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj F)) :=
    IsAddTorsion.of_surjective (f := e.inv.hom)
      (ConcreteCategory.bijective_of_isIso e.inv).2 hprod
  exact IsAddTorsion.of_surjective
    (f := (((pointSmallEtale s).uliftSheafFiberIso AddCommGrpCat.{u + 1}).app
      ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj F)).inv.hom)
    (ConcreteCategory.bijective_of_isIso _).2 hs

private theorem torsionCd_of_finite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    {n : ℕ} (hY : Y.HasTorsionCohomologicalDimensionLE n) :
    X.HasTorsionCohomologicalDimensionLE n := by
  intro F hF q hq
  have := hY _ (isTorsion_lowerStar_finite f hF) q hq
  exact (Etale.bijective_edgeMap_of_isFinite f F q).2.subsingleton

private theorem torsionCd_spec_of_polynomial (K : Type u) [Field K] (d : ℕ)
    (hpoly : ∀ n : ℕ, n ≤ d →
      (Spec (.of (MvPolynomial (Fin n) K))).HasTorsionCohomologicalDimensionLE n)
    (R : CommRingCat.{u}) [Algebra K R] [Algebra.FiniteType K R]
    (hR : ringKrullDim R ≤ (d : WithBot ℕ∞)) :
    (Spec R).HasTorsionCohomologicalDimensionLE d := by
  cases subsingleton_or_nontrivial R with
  | inl h =>
      let g : MvPolynomial (Fin 0) K →ₐ[K] R := MvPolynomial.aeval Fin.elim0
      have hg : g.Finite := by
        algebraize [g.toRingHom]
        change Module.Finite (MvPolynomial (Fin 0) K) R
        infer_instance
      have : IsFinite (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
        (IsFinite.SpecMap_iff _).mpr hg
      exact (torsionCd_of_finite (Spec.map (CommRingCat.ofHom g.toRingHom))
        (hpoly 0 (Nat.zero_le d))).mono (Nat.zero_le d)
  | inr h =>
      obtain ⟨n, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg K R
      have hnd : n ≤ d := by
        have := (ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial g hginj hgfin).symm.le.trans hR
        exact_mod_cast this
      have : IsFinite (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
        (IsFinite.SpecMap_iff _).mpr hgfin
      exact (torsionCd_of_finite (Spec.map (CommRingCat.ofHom g.toRingHom))
        (hpoly n hnd)).mono hnd

private theorem torsionCd_affine_of_polynomial (K : Type u) [Field K] (d : ℕ)
    (hpoly : ∀ n : ℕ, n ≤ d →
      (Spec (.of (MvPolynomial (Fin n) K))).HasTorsionCohomologicalDimensionLE n)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [IsAffine X]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    X.HasTorsionCohomologicalDimensionLE d := by
  let R := Γ(X, ⊤)
  let φ : K →+* R := (a.appLE ⊤ ⊤ (by simp)).hom.comp (ΓSpecIso (.of K)).inv.hom
  let : Algebra K R := φ.toAlgebra
  have : Algebra.FiniteType K R := (isAffineOpen_top X).algebra_finiteType_of_field a
  have hR : ringKrullDim R ≤ (d : WithBot ℕ∞) := by
    have he : topologicalKrullDim X = ringKrullDim R := by
      rw [IsHomeomorph.topologicalKrullDim_eq _ X.isoSpec.hom.homeomorph.isHomeomorph]
      exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R
    exact he ▸ hX
  exact (torsionCd_spec_of_polynomial K d hpoly R hR).of_isUniversalHomeomorphism
    X.isoSpec.inv

private theorem torsionCd_affine_of_geometric_polynomial (d : ℕ)
    (hpoly : ∀ (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ), n ≤ d →
      (Spec (.of (MvPolynomial (Fin n) K))).HasTorsionCohomologicalDimensionLE n)
    {K : Type u} [Field K] {c : ℕ}
    (hK : (Spec (.of K)).HasTorsionCohomologicalDimensionLE c) {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [IsAffine X]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    X.HasTorsionCohomologicalDimensionLE (d + c) := by
  let L := AlgebraicClosure K
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have hdim : topologicalKrullDim (pullback a g : Scheme.{u}) ≤ (d : WithBot ℕ∞) :=
    (topologicalKrullDim_pullback_le_of_field a g).trans hX
  have hgeom := torsionCd_affine_of_polynomial L d (hpoly L) (pullback.snd a g) hdim
  simpa only [Nat.add_comm c d] using
    hasTorsionCohomologicalDimensionLE_add_of_isAlgClosure L a hK hgeom

private theorem torsionCd_polynomial_zero (K : Type u) [Field K] [IsAlgClosed K] :
    (Spec (.of (MvPolynomial (Fin 0) K))).HasTorsionCohomologicalDimensionLE 0 := by
  let e := (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).toRingEquiv
  exact (hasTorsionCohomologicalDimensionLE_zero_of_isSepClosed K).of_isUniversalHomeomorphism
    (Spec.map (CommRingCat.ofHom e.toRingHom))

private theorem torsionCd_polynomial_one (K : Type u) [Field K] [IsAlgClosed K] :
    (Spec (.of (MvPolynomial (Fin 1) K))).HasTorsionCohomologicalDimensionLE 1 := by
  let a : Spec (.of (MvPolynomial (Fin 1) K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 1) K)))
  have : LocallyOfFiniteType a := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have : IsCurve a :=
    { krullDim_le_one := by
        change topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin 1) K)) ≤ 1
        rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
          MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
        simp }
  exact (IsCurve.hasTorsionCohomologicalDimensionLE a).2 inferInstance

private theorem isTorsion_of_mono {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : F ⟶ G) [Mono φ] (hG : G.IsTorsion) : F.IsTorsion := by
  intro U s
  obtain ⟨R, hR, hs⟩ := hG (φ.hom.app U s)
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨n, hn, hns⟩ := (hs hf).exists_nsmul_eq_zero
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, ?_⟩
  apply Etale.injective_app_of_mono φ V
  rw [map_nsmul, map_zero, NatTrans.naturality_apply]
  exact hns

private theorem dim_union_le {X : Type u} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    (S T : Set X) (hS : IsClosed S) (hT : IsClosed T) (a : WithBot ℕ∞)
    (hSa : topologicalKrullDim S ≤ a) (hTa : topologicalKrullDim T ≤ a) :
    topologicalKrullDim (S ∪ T : Set X) ≤ a := by
  have : QuasiSober (S ∪ T : Set X) := (hS.union hT).isClosedEmbedding_subtypeVal.quasiSober
  have hpoint (C : Set X) (hC : IsClosed C) (hCa : topologicalKrullDim C ≤ a)
      (z : (S ∪ T : Set X)) (hz : z.val ∈ C) :
      topologicalKrullDim (closure ({z} : Set (S ∪ T : Set X))) ≤ a := by
    have hc : closure ({z} : Set (S ∪ T : Set X)) ⊆ Subtype.val ⁻¹' C :=
      closure_minimal (Set.singleton_subset_iff.mpr hz) (hC.preimage continuous_subtype_val)
    let f : closure ({z} : Set (S ∪ T : Set X)) → C := fun x ↦ ⟨x.val.val, hc x.property⟩
    have hf : Topology.IsInducing f := by
      apply (Topology.IsInducing.subtypeVal :
        Topology.IsInducing (Subtype.val : C → X)).of_comp_iff.mp
      change Topology.IsInducing (fun x : closure ({z} : Set (S ∪ T : Set X)) ↦ x.val.val)
      exact Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
    exact hf.topologicalKrullDim_le.trans hCa
  let := specializationOrder (S ∪ T : Set X)
  rw [topologicalKrullDim_eq_krullDim_specializationOrder, Order.krullDim_eq_iSup_height]
  refine iSup_le fun z ↦ ?_
  rw [← topologicalKrullDim_closure_singleton]
  rcases z.property with hz | hz
  · exact hpoint S hS hSa z hz
  · exact hpoint T hT hTa z hz

private theorem exists_closedComplement {B : Scheme.{u}} (U : B.Opens) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ B), IsClosedImmersion i ∧
      Set.range i.base = ((U : Set B)ᶜ : Set B) := by
  let I := IdealSheafData.vanishingIdeal ⟨(U : Set B)ᶜ, U.isOpen.isClosed_compl⟩
  refine ⟨I.subscheme, I.subschemeι, inferInstance, ?_⟩
  rw [IdealSheafData.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]
  rfl

private theorem supportedInι_mono {B : Scheme.{u}}
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : B.Opens) :
    Mono (Etale.supportedInι N U) := by
  unfold Etale.supportedInι
  infer_instance

private theorem supportKernel_H {K : Type u} [Field K] {B : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) [LocallyOfFiniteType b] [IsAffine B]
    (a : ℕ)
    (hbound : ∀ {Z : Scheme.{u}} (z : Z ⟶ Spec (.of K))
      [LocallyOfFiniteType z] [IsAffine Z],
      topologicalKrullDim Z ≤ (a : WithBot ℕ∞) → Z.HasTorsionCohomologicalDimensionLE a)
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) (hN : N.IsTorsion)
    (U : B.Opens) (hU : topologicalKrullDim ((U : Set B)ᶜ : Set B) ≤ a)
    (q : ℕ) (hq : a < q) : Subsingleton (Sheaf.H (Etale.supportedIn N U) q) := by
  obtain ⟨Z, i, hiClosed, hiRange⟩ := exists_closedComplement U
  have := hiClosed
  have : IsAffine Z := isAffine_of_isAffineHom i
  have hi : Set.range i.base = (Set.range U.ι.base)ᶜ := by
    simpa only [Scheme.Opens.range_ι] using hiRange
  have : Mono (Etale.supportedInι N U) := supportedInι_mono N U
  let A := Etale.supportedIn N U
  let adj := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι
  have hiso : IsIso ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).map (adj.unit.app N)) := by
    have : IsIso ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).map (adj.unit.app N) ≫
        adj.counit.app ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj N)) := by
      have ht : (Etale.upperStar AddCommGrpCat.{u + 1} U.ι).map (adj.unit.app N) ≫
          adj.counit.app ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj N) = 𝟙 _ :=
        adj.left_triangle_components N
      exact ht.symm ▸ IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
  have : Mono ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).map (adj.unit.app N)) :=
    @IsIso.mono_of_iso _ _ _ _ _ hiso
  have hz : IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj A) :=
    (isZero_kernel_of_mono ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).map
      (adj.unit.app N))).of_iso (PreservesKernel.iso _ _)
  obtain ⟨G, ⟨e⟩⟩ := Etale.mem_essImage_lowerStar_of_isZero_upperStar i (j := U.ι) hi hz
  have hA : A.IsTorsion := isTorsion_of_mono (Etale.supportedInι N U) hN
  have hpush : ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj G).IsTorsion :=
    isTorsion_of_mono e.hom hA
  have hG : G.IsTorsion := by
    have h' := Etale.isTorsion_upperStar i hpush
    exact isTorsion_of_mono
      (asIso ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).counit.app G)).inv h'
  have hdim : topologicalKrullDim Z ≤ (a : WithBot ℕ∞) := by
    rw [i.isClosedEmbedding.isEmbedding.topologicalKrullDim_eq_range, hiRange]
    exact hU
  have hZ := hbound (i ≫ b) hdim
  have : Subsingleton (Sheaf.H ((𝟭 _).obj G) q) := hZ G hG q hq
  have : Subsingleton (Sheaf.H ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj G) q) :=
    (Etale.bijective_edgeMap_of_isFinite i G q).injective.subsingleton
  have : Subsingleton ((Sheaf.functorH.{u + 1} B.smallEtaleTopology q).obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj G)) := ‹_›
  exact (ConcreteCategory.bijective_of_isIso
    ((Sheaf.functorH.{u + 1} B.smallEtaleTopology q).map e.inv)).injective.subsingleton

private theorem supportedIn_transition_condition {B : Scheme.{u}}
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) {U V : B.Opens} (h : V ≤ U) :
    Etale.supportedInι N U ≫
      (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} V.ι).unit.app N = 0 := by
  have ht := Etale.unit_app_comp_unitComparison (Scheme.homOfLE B h)
    U.ι V.ι (Scheme.homOfLE_ι B h).symm N
  change kernel.ι _ ≫ _ = 0
  rw [← ht, kernel.condition_assoc, zero_comp]

private noncomputable def supportedIn_transition {B : Scheme.{u}}
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) {U V : B.Opens} (h : V ≤ U) :
    Etale.supportedIn N U ⟶ Etale.supportedIn N V :=
  kernel.lift _ (Etale.supportedInι N U) (supportedIn_transition_condition N h)

private theorem supportedIn_transition_ι {B : Scheme.{u}}
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) {U V : B.Opens} (h : V ≤ U) :
    supportedIn_transition N h ≫ Etale.supportedInι N V = Etale.supportedInι N U :=
  kernel.lift_ι _ _ _

private theorem support_dimension_H {K : Type u} [Field K] {B : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) [LocallyOfFiniteType b] [IsAffine B]
    (a : ℕ)
    (hbound : ∀ {Z : Scheme.{u}} (z : Z ⟶ Spec (.of K))
      [LocallyOfFiniteType z] [IsAffine Z],
      topologicalKrullDim Z ≤ (a : WithBot ℕ∞) → Z.HasTorsionCohomologicalDimensionLE a)
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) (hN : N.IsTorsion)
    (hstalk : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ B),
      (a : Cardinal.{u}) < residueFieldTrdeg b (s (IsLocalRing.closedPoint Ω)) →
        IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj N))
    (q : ℕ) (hq : a < q) : Subsingleton (Sheaf.H N q) := by
  let (U : B.Opens) : Mono (Etale.supportedInι N U) := supportedInι_mono N U
  let J := { U : B.Opens // topologicalKrullDim ((U : Set B)ᶜ : Set B) ≤ a }ᵒᵈ
  have : Nonempty J := by
    have : IsEmpty (TopologicalSpace.IrreducibleCloseds
        (((⊤ : B.Opens) : Set B)ᶜ : Set B)) :=
      ⟨fun C ↦ (C.isIrreducible.nonempty.choose).property (by trivial)⟩
    refine ⟨⟨(⊤ : B.Opens), ?_⟩⟩
    rw [topologicalKrullDim, Order.krullDim_eq_bot]
    exact bot_le
  have : IsDirectedOrder J := ⟨fun U V ↦ by
    refine ⟨⟨(U.val ⊓ V.val : B.Opens), ?_⟩, ?_, ?_⟩
    · rw [TopologicalSpace.Opens.coe_inf, Set.compl_inter]
      exact dim_union_le _ _ (U.val : B.Opens).isOpen.isClosed_compl
        (V.val : B.Opens).isOpen.isClosed_compl _ U.property V.property
    · change U.val ⊓ V.val ≤ U.val
      exact inf_le_left
    · change U.val ⊓ V.val ≤ V.val
      exact inf_le_right⟩
  let D : J ⥤ Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    { obj U := Etale.supportedIn N U.val
      map {U V} f := supportedIn_transition N (show V.val ≤ U.val from leOfHom f)
      map_id U := by
        apply (cancel_mono (Etale.supportedInι N U.val)).1
        rw [supportedIn_transition_ι, Category.id_comp]
      map_comp {U V W} f g := by
        apply (cancel_mono (Etale.supportedInι N W.val)).1
        rw [supportedIn_transition_ι, Category.assoc,
          supportedIn_transition_ι, supportedIn_transition_ι] }
  let c : Cocone D :=
    { pt := N
      ι := { app U := Etale.supportedInι N U.val
             naturality U V f := (supportedIn_transition_ι N
               (show V.val ≤ U.val from leOfHom f)).trans
               (Category.comp_id _).symm } }
  have : ∀ U, Mono (c.ι.app U) := by
    intro U
    change Mono (Etale.supportedInι N U.val)
    infer_instance
  have hc : IsColimit c := Etale.isColimitOfMonoOfLocallySurjective c fun V s ↦ by
    obtain ⟨R, hR, hRs⟩ := Etale.exists_covering_supportedIn b a N hN hstalk V s
    refine ⟨R, hR, fun W g hg ↦ ?_⟩
    obtain ⟨U, hU, t, ht⟩ := hRs g hg
    exact ⟨⟨U, hU⟩, t, ht⟩
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨U, y, rfl⟩ := (H_map_isColimit_of_isFiltered B hc q).1 x
  have : Subsingleton (Sheaf.H (D.obj U) q) :=
    supportKernel_H b a hbound N hN U.val U.property q hq
  exact (congrArg (Sheaf.H.map (c.ι.app U) q) (Subsingleton.elim y 0)).trans
    (map_zero _)

private theorem subsingleton_H_of_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (h : ∀ p q : ℕ, p + q = n →
      Subsingleton (Sheaf.H (((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj F) p)) :
    Subsingleton (Sheaf.H F n) := by
  rw [Etale.subsingleton_H_iff_isZero_rightDerived_Γ]
  have : ((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Opposite.op (⊤_ Y.Etale))).Additive :=
    { map_add := rfl }
  have : ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Opposite.op (⊤_ X.Etale))).Additive :=
    { map_add := rfl }
  have hFG := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).isAcyclicComposablePair
    (Sheaf.sectionsFunctorAt Y.smallEtaleTopology
      (⊤_ Y.Etale) : Sheaf _ AddCommGrpCat.{u + 1} ⥤ _)
  refine IsZero.of_iso (Functor.isZero_rightDerived_comp_of_isZero _ _ hFG F n
    (fun p q hpq ↦ (Etale.subsingleton_H_iff_isZero_rightDerived_Γ _ p).1 (h p q hpq)))
    ((NatIso.rightDerived
      (Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f) n).app F).symm

private theorem torsionCd_polynomial_of_projection_bound
    (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ)
    (hbase :
      (Spec (.of (MvPolynomial (Fin (n + 1)) K))).HasTorsionCohomologicalDimensionLE (n + 1))
    (hsmall : ∀ a : ℕ, a < n + 2 → ∀ {Z : Scheme.{u}} (z : Z ⟶ Spec (.of K))
      [LocallyOfFiniteType z] [IsAffine Z],
      topologicalKrullDim Z ≤ (a : WithBot ℕ∞) → Z.HasTorsionCohomologicalDimensionLE a)
    (hR : ∀ (M : Sheaf (Spec (.of (MvPolynomial (Fin (n + 2)) K))).smallEtaleTopology
        AddCommGrpCat.{u + 1}) (N : ℕ), 0 < N → N • 𝟙 M = 0 → ∀ q : ℕ, 2 ≤ q →
      let f : Spec (.of (MvPolynomial (Fin (n + 2)) K)) ⟶
          Spec (.of (MvPolynomial (Fin (n + 1)) K)) :=
        Spec.map (CommRingCat.ofHom (MvPolynomial.rename
          (Fin.castSucc : Fin (n + 1) → Fin (n + 2))).toRingHom)
      let b := Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin (n + 1)) K)))
      (n + 2 < q → IsZero (((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj M)) ∧
        (q ≤ n + 2 → ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
          (s : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin (n + 1)) K))),
          ((n + 2 - q : ℕ) : Cardinal.{u}) <
              residueFieldTrdeg b (s (IsLocalRing.closedPoint Ω)) →
            IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj
              (((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj M)))) :
    (Spec (.of (MvPolynomial (Fin (n + 2)) K))).HasTorsionCohomologicalDimensionLE (n + 2) := by
  let f : Spec (.of (MvPolynomial (Fin (n + 2)) K)) ⟶
      Spec (.of (MvPolynomial (Fin (n + 1)) K)) :=
    Spec.map (CommRingCat.ofHom (MvPolynomial.rename
      (Fin.castSucc : Fin (n + 1) → Fin (n + 2))).toRingHom)
  let b := Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin (n + 1)) K)))
  have : LocallyOfFiniteType b := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  intro F hF r hr
  apply Etale.subsingleton_H_of_isTorsion hF r
  intro M N hN hM
  apply subsingleton_H_of_diagonal f M r
  intro p q hpq
  have hRq : N • 𝟙 (((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj M) = 0 := by
    have hmap := congrArg
      ((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).map hM
    simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] using hmap
  have htorsion := isTorsion_of_nsmul_id_eq_zero hN hRq
  by_cases hq : 2 ≤ q
  · by_cases hqd : q ≤ n + 2
    · apply support_dimension_H b (n + 2 - q) (hsmall _ (by omega)) _ htorsion
        ((hR M N hN hM q hq).2 hqd) p
      omega
    · exact (Etale.subsingleton_H_iff_isZero_rightDerived_Γ _ p).2
        (((Sheaf.sectionsFunctorAt _ (⊤_ _)).rightDerived p).map_isZero
          ((hR M N hN hM q hq).1 (by omega)))
  · exact hbase _ htorsion p (by omega)

private theorem isUnit_aeval_away_of_mem_maximalIdeal
    (F R : Type u) [Field F] [CommRing R] [IsLocalRing R] [Algebra F R]
    (h : R) (hh : h ∈ IsLocalRing.maximalIdeal R)
    (p : Polynomial F) (hp : p ≠ 0) :
    IsUnit (Polynomial.aeval (algebraMap R (Localization.Away h) h) p) := by
  obtain ⟨Q, hQ, hQ0⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp 0
  simp only [map_zero, sub_zero] at hQ hQ0
  have hcoeff : Q.coeff 0 ≠ 0 := fun hc ↦ hQ0 (Polynomial.X_dvd_iff.mpr hc)
  have hres : IsLocalRing.residue R (Polynomial.aeval h Q) ≠ 0 := by
    have hz : IsLocalRing.residue R h = 0 := (IsLocalRing.residue_eq_zero_iff h).mpr hh
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hz, Polynomial.eval₂_at_zero]
    simpa only [map_zero] using
      ((IsLocalRing.residue R).comp (algebraMap F R)).injective.ne hcoeff
  have hunit : IsUnit (Polynomial.aeval h Q) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres
  rw [hQ, map_mul, map_pow, Polynomial.aeval_X]
  refine ((IsLocalization.Away.algebraMap_isUnit h).pow _).mul ?_
  have heval : Polynomial.aeval (algebraMap R (Localization.Away h) h) Q =
      algebraMap R (Localization.Away h) (Polynomial.aeval h Q) := by
    exact (Polynomial.aeval_algHom_apply
      (IsScalarTower.toAlgHom F R (Localization.Away h)) h Q)
  rw [heval]
  exact hunit.map (algebraMap R (Localization.Away h))

private theorem torsionCd_domain_of_trdeg
    (K : Type u) [Field K] (c m : ℕ)
    (hbound : ∀ {X : Scheme.{u}} (a : X ⟶ Spec (.of K))
      [LocallyOfFiniteType a] [IsAffine X],
      topologicalKrullDim X ≤ (m : WithBot ℕ∞) →
        X.HasTorsionCohomologicalDimensionLE (m + c))
    (A : Type u) [CommRing A] [IsDomain A] [Algebra K A]
    (hA : Algebra.trdeg K A ≤ (m : Cardinal.{u})) :
    (Spec (.of A)).HasTorsionCohomologicalDimensionLE (m + c) := by
  let I := {S : Subalgebra K A // S.FG}
  let D : Iᵒᵖ ⥤ Scheme.{u} := (CommRingCat.fgSubalgebraDiagramOf K A).op ⋙ Scheme.Spec
  let cone : Cone D := Scheme.Spec.mapCone (CommRingCat.fgSubalgebraCoconeOf K A).op
  have hc : IsLimit cone :=
    isLimitOfPreserves Scheme.Spec (CommRingCat.isColimitFGSubalgebraCocone K A).op
  have hD {i j : Iᵒᵖ} (g : i ⟶ j) : IsAffineHom (D.map g) := by
    change IsAffineHom (Spec.map ((CommRingCat.fgSubalgebraDiagramOf K A).map g.unop))
    infer_instance
  have hcompact (i : Iᵒᵖ) : CompactSpace (D.obj i) := by
    change CompactSpace (Spec (.of i.unop.val))
    infer_instance
  have hsep (i : Iᵒᵖ) : QuasiSeparatedSpace (D.obj i) := by
    change QuasiSeparatedSpace (Spec (.of i.unop.val))
    infer_instance
  apply HasTorsionCohomologicalDimensionLE.of_isLimit D cone hc
  intro i
  let S := i.unop.val
  have : Algebra.FiniteType K S := (Subalgebra.fg_iff_finiteType S).mp i.unop.property
  let b := Spec.map (CommRingCat.ofHom (algebraMap K S))
  have : LocallyOfFiniteType b := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  apply hbound b
  change topologicalKrullDim (PrimeSpectrum S) ≤ _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  obtain ⟨r, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K S
  have hdim := (ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial g hinj hfin).symm
  have htrdeg := (Algebra.trdeg_eq_of_ringKrullDim_eq K S hdim.symm).symm.le.trans
    ((trdeg_le_of_injective S.val Subtype.val_injective).trans hA)
  have hrm : r ≤ m := by exact_mod_cast htrdeg
  exact hdim ▸ (by exact_mod_cast hrm)

private theorem trdeg_away_le_fractionRing
    (F R : Type u) [Field F] [CommRing R] [IsDomain R] [Algebra F R]
    (h : R) (hh0 : h ≠ 0) :
    Algebra.trdeg F (Localization.Away h) ≤ Algebra.trdeg F (FractionRing R) := by
  have hu : IsUnit (algebraMap R (FractionRing R) h) := by
    apply isUnit_iff_ne_zero.mpr
    simpa only [map_zero] using (IsFractionRing.injective R (FractionRing R)).ne hh0
  let ψ : Localization.Away h →ₐ[F] FractionRing R :=
    IsLocalization.Away.liftAlgHom h
      (f := IsScalarTower.toAlgHom F R (FractionRing R)) hu
  have hψ (x : R) : ψ (algebraMap R (Localization.Away h) x) =
      algebraMap R (FractionRing R) x := IsLocalization.Away.lift_eq h hu x
  have hinj : Function.Injective ψ := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers h)
      ψ.toRingHom).mpr
    intro x y
    change algebraMap R (Localization.Away h) x = algebraMap R (Localization.Away h) y ↔
      ψ (algebraMap R (Localization.Away h) x) = ψ (algebraMap R (Localization.Away h) y)
    rw [hψ, hψ,
      (IsLocalization.injective (Localization.Away h)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hh0)).eq_iff,
      (IsFractionRing.injective R (FractionRing R)).eq_iff]
  exact trdeg_le_of_injective ψ hinj

private theorem torsionCd_principalOpen_of_trdeg
    (F R : Type u) [Field F] [IsSepClosed F] [CommRing R] [IsLocalRing R] [IsDomain R]
    [Algebra F R] (h : R) (hh : h ∈ IsLocalRing.maximalIdeal R) (hh0 : h ≠ 0)
    (m : ℕ)
    (hbound : ∀ {X : Scheme.{u}} (a : X ⟶ Spec (.of (RatFunc F)))
      [LocallyOfFiniteType a] [IsAffine X],
      topologicalKrullDim X ≤ (m : WithBot ℕ∞) →
        X.HasTorsionCohomologicalDimensionLE (m + 1))
    (htrdeg : Algebra.trdeg F (FractionRing R) ≤ ((m + 1 : ℕ) : Cardinal.{u})) :
    (Spec (.of (Localization.Away h))).HasTorsionCohomologicalDimensionLE (m + 1) := by
  let A := Localization.Away h
  have : IsDomain A :=
    IsLocalization.isDomain_of_le_nonZeroDivisors
      (M := Submonoid.powers h) (S := A) (powers_le_nonZeroDivisors_of_noZeroDivisors hh0)
  let e : Polynomial F →+* A := (Polynomial.aeval (algebraMap R A h)).toRingHom
  have he (p : nonZeroDivisors (Polynomial F)) : IsUnit (e p) :=
    isUnit_aeval_away_of_mem_maximalIdeal F R h hh p (nonZeroDivisors.ne_zero p.property)
  let φ : RatFunc F →+* A := IsLocalization.lift he
  have hφ (x : F) : φ (algebraMap F (RatFunc F) x) = algebraMap F A x := by
    change φ (algebraMap (Polynomial F) (RatFunc F) (Polynomial.C x)) = _
    exact (IsLocalization.lift_eq he (Polynomial.C x)).trans (Polynomial.aeval_C _ _)
  let : Algebra (RatFunc F) A := φ.toAlgebra
  have : IsScalarTower F (RatFunc F) A := .of_algebraMap_eq fun x ↦ (hφ x).symm
  have : Algebra.IsAlgebraic (Polynomial F) (RatFunc F) :=
    IsLocalization.isAlgebraic (RatFunc F) (nonZeroDivisors (Polynomial F))
  have hrat : Algebra.trdeg F (RatFunc F) = 1 := by
    have ht := trdeg_add_eq (R := F) (S := Polynomial F) (A := RatFunc F)
    rw [trdeg_eq_zero (R := Polynomial F), add_zero, Polynomial.trdeg_of_isDomain] at ht
    exact ht.symm
  have ht := trdeg_add_eq (R := F) (S := RatFunc F) (A := A)
  have hm : Algebra.trdeg (RatFunc F) A ≤ (m : Cardinal.{u}) := by
    apply Cardinal.add_one_le_add_one_iff.mp
    calc
      Algebra.trdeg (RatFunc F) A + 1 = Algebra.trdeg F A := by
        simpa only [hrat, add_comm] using ht
      _ ≤ (m : Cardinal.{u}) + 1 := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (trdeg_away_le_fractionRing F R h hh0).trans htrdeg
  exact torsionCd_domain_of_trdeg (RatFunc F) 1 m hbound A hm

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
private theorem strictLocal_principalOpen_bound
    (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ)
    (hlocal : ∀ (F R : Type u) [Field F] [IsSepClosed F] [CommRing R]
        [IsLocalRing R] [IsDomain R] [Algebra F R]
        (h : R), h ∈ IsLocalRing.maximalIdeal R → h ≠ 0 →
        ∀ (m : ℕ), m < n + 2 →
          Algebra.trdeg F (FractionRing R) ≤ ((m + 1 : ℕ) : Cardinal.{u}) →
          (Spec (.of (Localization.Away h))).HasTorsionCohomologicalDimensionLE (m + 1)) :
    ∀ (Y : Scheme.{u}) [IsIntegral Y]
        (f : Y ⟶ Spec (.of K)) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f]
        (a : ℕ), a < n + 2 → topologicalKrullDim Y = ((n + 2 : ℕ) : WithBot ℕ∞) →
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
          (y : Y), s (IsLocalRing.closedPoint Ω) = y →
        ∀ [Algebra K (Y.residueField y)],
          Spec.map (CommRingCat.ofHom (algebraMap K (Y.residueField y))) =
            Y.fromSpecResidueField y ≫ f →
        ∀ [Algebra (Y.residueField y) Ω],
          Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫
            Y.fromSpecResidueField y = s →
          Algebra.trdeg K (Y.residueField y) = (a : Cardinal.{u}) →
        ∀ [Algebra K (strictHenselizationRing s)],
          Spec.map (CommRingCat.ofHom (algebraMap K (strictHenselizationRing s))) =
            strictHenselizationStructuralMap s ≫ f →
        ∀ (h : strictHenselizationRing s), h ∈ IsLocalRing.maximalIdeal _ → h ≠ 0 →
          (Spec (.of (Localization.Away h))).HasTorsionCohomologicalDimensionLE (n + 2 - a) := by
  intro Y _ f _ _ _ a ha hd Ω _ _ s y hy _ hκ _ hΩ htrdeg _ hK h hh hh0
  obtain ⟨_, hl, hdom, hm⟩ :=
    smooth_strict_local_field_model K Y f (n + 2) a hd Ω s y hy hκ hΩ htrdeg hK
  let := hl
  let := hdom
  obtain ⟨_, e, he, i, hi, halg, F, hField, hAlg, j, hsep, hj, htrK, htrF⟩ := hm
  let := hField
  let := hAlg
  let := hsep
  let : Algebra F (strictHenselizationRing s) := j.toRingHom.toAlgebra
  have ht : Algebra.trdeg F (FractionRing (strictHenselizationRing s)) =
      ((n + 2 - a : ℕ) : Cardinal.{u}) := htrF
  have heq : n + 2 - a - 1 + 1 = n + 2 - a := by omega
  have hb := hlocal F (strictHenselizationRing s) h hh hh0 (n + 2 - a - 1)
    (by omega) (by rw [heq]; exact ht.le)
  simpa only [heq] using hb
-/

private theorem isZero_of_forall_isZero_pointPullback {B : Scheme.{u}}
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ B),
      IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj N)) : IsZero N := by
  have : LocallySmall.{u + 1} B.Etale := locallySmall_max.{u + 1, u}
  rw [IsZero.iff_id_eq_zero]
  apply sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro y
  let Ω := AlgebraicClosure (B.residueField y)
  let s := B.algClosurePoint y
  have : LocallySmall.{u + 1} (Spec (.of Ω)).Etale := locallySmall_max.{u + 1, u}
  have : ((pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber
      (A := AddCommGrpCat.{u + 1})).Additive :=
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber_additive
  have e := (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} s (𝟙 _)).app N
  rw [Category.id_comp] at e
  have hz : IsZero ((pointSmallEtale s).sheafFiber.obj N) :=
    IsZero.of_iso (((pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber
      (A := AddCommGrpCat.{u + 1})).map_isZero (h Ω s)) e.symm
  exact hz.eq_of_src _ _

private theorem projectiveLine_rightDerived_module_isZero
    (Λ : Type (u + 1)) [CommRing Λ] (S : Scheme.{u})
    (F : Sheaf (AlgebraicGeometry.ProjectiveLine S).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) [IsTorsionModuleSheaf F]
    (q : ℕ) (hq : 2 < q) :
    IsZero (((Etale.lowerStar (ModuleCat.{u + 1} Λ)
      (AlgebraicGeometry.ProjectiveLine S ↘ S)).rightDerived q).obj F) := by
  have : LocallySmall.{u + 1} S.Etale := locallySmall_max.{u + 1, u}
  rw [IsZero.iff_id_eq_zero]
  apply sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro y
  let Ω := AlgebraicClosure (S.residueField y)
  let s := S.algClosurePoint y
  let p := AlgebraicGeometry.ProjectiveLine S ↘ S
  have sq : IsPullback (𝟙 (AlgebraicGeometry.ProjectiveLine S)) p p (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨e, _, _⟩ :=
    Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine Λ sq s s
      (𝟙 _) (by simp)
      ⟨y, CommRingCat.ofHom (algebraMap (S.residueField y) Ω),
        Algebra.IsIntegral.isIntegral (R := S.residueField y), rfl⟩
      ⟨y, CommRingCat.ofHom (algebraMap (S.residueField y) Ω),
        Algebra.IsIntegral.isIntegral (R := S.residueField y), rfl⟩ F q
  let P := (Etale.upperStar (ModuleCat.{u + 1} Λ) (ProjectiveSpace.map _ s)).obj F
  have hP : ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj P).IsTorsion :=
    (isTorsionModuleSheaf_iff_isTorsion P).mp inferInstance
  have hz := (AlgebraicGeometry.IsCurve.hasTorsionCohomologicalDimensionLE_of_isSepClosed
    (AlgebraicGeometry.ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω))).1 _ hP q hq
  have hs : Subsingleton
      (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
        ((Etale.baseChangeSourceFunctor Λ (𝟙 S) p q).obj F)) :=
    e.injective.subsingleton
  obtain ⟨e₁⟩ := (show Nonempty _ from ⟨
    (Etale.baseChangeSourceFunctorIso Λ (𝟙 S) p q).app F⟩)
  obtain ⟨e₃⟩ := (show Nonempty _ from ⟨
    Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) p) F q⟩)
  obtain ⟨E⟩ := (show Nonempty _ from ⟨
    ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).mapIso
    (e₁ ≪≫ (Etale.upperStarId (ModuleCat.{u + 1} Λ) S).app _ ≪≫ e₃)⟩)
  have hzSource : IsZero (((pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj
        ((Etale.baseChangeSourceFunctor Λ (𝟙 S) p q).obj F)) :=
    ModuleCat.isZero_of_subsingleton _
  exact (IsZero.of_iso hzSource E.symm).eq_of_src _ _

private theorem isZero_rightDerived_of_exact_square
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasInjectiveResolutions C] [HasInjectiveResolutions C']
    (F : C ⥤ D) (G : C' ⥤ D') (E : C ⥤ C') (H : D ⥤ D')
    [F.Additive] [G.Additive] [E.Additive] [H.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] [PreservesFiniteLimits G]
    (eComp : F ⋙ H ≅ E ⋙ G)
    (hE : ∀ (I : C) [Injective I], G.rightAcyclic (E.obj I))
    (X : C) (Y : C') (e : E.obj X ≅ Y) (q : ℕ)
    (hz : IsZero ((F.rightDerived q).obj X)) :
    IsZero ((G.rightDerived q).obj Y) := by
  obtain ⟨e₁⟩ := (show Nonempty _ from ⟨Functor.rightDerivedCompObjIso F H q X⟩)
  obtain ⟨e₂⟩ := (show Nonempty _ from ⟨Functor.rightDerivedObjIsoOfIso eComp q X⟩)
  obtain ⟨e₃⟩ := (show Nonempty _ from ⟨Functor.compRightDerivedObjIso E G hE q X⟩)
  obtain ⟨e₄⟩ := (show Nonempty _ from ⟨(G.rightDerived q).mapIso e⟩)
  exact IsZero.of_iso (H.map_isZero hz) ((e₁.symm ≪≫ e₂ ≪≫ e₃ ≪≫ e₄).symm)

private theorem projectiveLine_rightDerived_isZero (S : Scheme.{u})
    (M : Sheaf (AlgebraicGeometry.ProjectiveLine S).smallEtaleTopology
      AddCommGrpCat.{u + 1}) (hM : M.IsTorsion) (q : ℕ) (hq : 2 < q) :
    IsZero (((Etale.lowerStar AddCommGrpCat.{u + 1}
      (AlgebraicGeometry.ProjectiveLine S ↘ S)).rightDerived q).obj M) := by
  let Φ (X : Scheme.{u}) := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  obtain ⟨F, ⟨e⟩⟩ :=
    Functor.EssSurj.mem_essImage (Φ (AlgebraicGeometry.ProjectiveLine S)) M
  have : IsTorsionModuleSheaf F :=
    (isTorsionModuleSheaf_iff_isTorsion F).mpr (isTorsion_of_mono e.hom hM)
  let p := AlgebraicGeometry.ProjectiveLine S ↘ S
  have hz := projectiveLine_rightDerived_module_isZero (ULift.{u + 1} ℤ) S F q hq
  exact isZero_rightDerived_of_exact_square
    (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) p)
    (Etale.lowerStar AddCommGrpCat.{u + 1} p)
    (Φ (AlgebraicGeometry.ProjectiveLine S)) (Φ S)
    (Etale.lowerStarCompForget₂Iso (ULift.{u + 1} ℤ) p)
    (fun I _ ↦ Functor.rightAcyclic_of_injective _) F M e q hz

private theorem rightDerived_id_isZero {C : Type*} [Category* C] [Abelian C]
    [EnoughInjectives C] (F : C) (q : ℕ) (hq : 0 < q) :
    IsZero (((𝟭 C).rightDerived q).obj F) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  exact Functor.isZero_rightDerived_obj_of_exact (𝟭 C) F r

private theorem rightDerived_closedSection_isZero
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (g : Y ⟶ Z) (hi : i ≫ g = 𝟙 Z)
    (N : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (hq : 0 < q) :
    IsZero (((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived q).obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj N)) := by
  have : LocallySmall.{u + 1} Y.Etale := locallySmall_max.{u + 1, u}
  obtain ⟨e⟩ := (show Nonempty _ from ⟨
    Etale.lowerStarComp AddCommGrpCat.{u + 1} i g (𝟙 Z) hi.symm ≪≫
    Etale.lowerStarId AddCommGrpCat.{u + 1} Z⟩)
  obtain ⟨e₁⟩ := (show Nonempty _ from ⟨
    Functor.compRightDerivedObjIso
    (Etale.lowerStar AddCommGrpCat.{u + 1} i)
    (Etale.lowerStar AddCommGrpCat.{u + 1} g)
    (fun I hI ↦ by
      have := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).map_injective I hI
      exact Functor.rightAcyclic_of_injective _) q N⟩)
  obtain ⟨e₂⟩ := (show Nonempty _ from ⟨
    Functor.rightDerivedObjIsoOfIso e q N⟩)
  exact IsZero.of_iso (rightDerived_id_isZero N q hq) (e₁.symm ≪≫ e₂)

private theorem rightDerived_openImmersion_supported
    {U Z Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (i : Z ⟶ Y) [IsClosedImmersion i]
    (hi : Set.range i.base = (Set.range j.base)ᶜ)
    (M : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (hq : 0 < q) :
    (Etale.lowerStar AddCommGrpCat.{u + 1} i).essImage
      (((Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerived q).obj M) := by
  apply Etale.mem_essImage_lowerStar_of_isZero_upperStar i hi
  obtain ⟨e₁⟩ := (show Nonempty _ from ⟨
    Functor.rightDerivedCompObjIso
    (Etale.lowerStar AddCommGrpCat.{u + 1} j)
    (Etale.upperStar AddCommGrpCat.{u + 1} j) q M⟩)
  obtain ⟨e₂⟩ := (show Nonempty _ from ⟨
    Functor.rightDerivedObjIsoOfIso
    (asIso (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).counit) q M⟩)
  exact IsZero.of_iso (rightDerived_id_isZero M q hq) (e₁.symm ≪≫ e₂)

private theorem rightDerived_openImmersion_boundary_acyclic
    {U Z Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (i : Z ⟶ Y) [IsClosedImmersion i] (g : Y ⟶ Z)
    (hi : Set.range i.base = (Set.range j.base)ᶜ) (hig : i ≫ g = 𝟙 Z)
    (M : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    IsZero (((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived p).obj
      (((Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerived q).obj M)) := by
  obtain ⟨N, ⟨e⟩⟩ := rightDerived_openImmersion_supported j i hi M q hq
  exact IsZero.of_iso (rightDerived_closedSection_isZero i g hig N p hp)
    (((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived p).mapIso e).symm

private theorem isZero_derivedCohomology_single_of_subsingleton_H {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (hF : Subsingleton (Sheaf.H F q)) :
    IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} X q).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  have : ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Opposite.op (⊤_ X.Etale))).Additive :=
    { map_add := rfl }
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  obtain ⟨e₁⟩ := (show Nonempty _ from ⟨
    Functor.homologyRightDerivedFunctorObjSingleFunctorIso Γ F q⟩)
  obtain ⟨e₂⟩ := (show Nonempty _ from ⟨
    (NatIso.rightDerived
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal) q).app F⟩)
  exact IsZero.of_iso ((Etale.subsingleton_H_iff_isZero_rightDerived_Γ F q).mp hF)
    (e₁ ≪≫ e₂)

private theorem isZero_stalk_rightDerived_of_strictLocal_H
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (h : Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1}
      (pullback.fst f (strictHenselizationStructuralMap s))).obj F) q)) :
    IsZero ((pointSmallEtale s).sheafFiber.obj
      (((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj F)) := by
  obtain ⟨r, hr, hiso⟩ := (Etale.strictHenselizationStalkFormula f s F hF q).1
  have := hiso
  have hz := IsZero.of_iso
    (isZero_derivedCohomology_single_of_subsingleton_H _ q h)
    (asIso (r ≫ Etale.strictHenselizationCohomologyComparison s f F q))
  obtain ⟨e⟩ := (show Nonempty _ from ⟨
    (pointSmallEtale s).sheafFiber.mapIso
    (Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso
      (Etale.lowerStar AddCommGrpCat.{u + 1} f) F q)⟩)
  exact IsZero.of_iso hz e.symm

private theorem isZero_pullback_rightDerived_comp_of_diagonal
    {X Y S T : Scheme.{u}} (j : X ⟶ Y) (g : Y ⟶ S) (s : T ⟶ S)
    (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (r : ℕ)
    (h : ∀ p q : ℕ, p + q = r →
      IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj
        (((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived p).obj
          (((Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerived q).obj M)))) :
    IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj
      (((Etale.lowerStar AddCommGrpCat.{u + 1} (j ≫ g)).rightDerived r).obj M)) := by
  let F := Etale.lowerStar AddCommGrpCat.{u + 1} j
  let G := Etale.lowerStar AddCommGrpCat.{u + 1} g
  let H := Etale.upperStar AddCommGrpCat.{u + 1} s
  have hFG :=
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).isAcyclicComposablePair (G ⋙ H)
  have hz : IsZero (((F ⋙ (G ⋙ H)).rightDerived r).obj M) := by
    apply Functor.isZero_rightDerived_comp_of_isZero F (G ⋙ H) hFG M r
    intro p q hpq
    exact IsZero.of_iso (h p q hpq)
      (Functor.rightDerivedCompObjIso G H p ((F.rightDerived q).obj M))
  obtain ⟨e₁⟩ := (show Nonempty _ from ⟨
    Functor.rightDerivedObjIsoOfIso (Functor.associator F G H).symm r M⟩)
  obtain ⟨e₂⟩ := (show Nonempty _ from ⟨
    Functor.rightDerivedCompObjIso (F ⋙ G) H r M⟩)
  obtain ⟨e₃⟩ := (show Nonempty _ from ⟨
    H.mapIso (Functor.rightDerivedObjIsoOfIso
    (Etale.lowerStarComp AddCommGrpCat.{u + 1} j g (j ≫ g) rfl) r M)⟩)
  exact IsZero.of_iso hz (e₁ ≪≫ e₂ ≪≫ e₃).symm

private noncomputable def lastVariableRingEquiv (K : Type u) [CommRing K] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) K ≃+*
      MvPolynomial PUnit.{u + 1} (MvPolynomial (Fin n) K) :=
  ((MvPolynomial.renameEquiv K (finRotate (n + 1))).toRingEquiv.trans
    (MvPolynomial.finSuccEquiv K n).toRingEquiv).trans
      (MvPolynomial.uniqueAlgEquiv (MvPolynomial (Fin n) K) PUnit.{u + 1}).symm.toRingEquiv

private theorem lastVariableRingEquiv_rename (K : Type u) [CommRing K] (n : ℕ) :
    (lastVariableRingEquiv K n).toRingHom.comp
      (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1))).toRingHom =
      MvPolynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro x
    simp [lastVariableRingEquiv, MvPolynomial.finSuccEquiv_apply]
  · intro i
    have hi : finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
    simp [lastVariableRingEquiv, hi, MvPolynomial.finSuccEquiv_X_succ]

private theorem exists_affineSpace_line_iso (K : Type u) [CommRing K] (n : ℕ) :
    let B := Spec (.of (MvPolynomial (Fin n) K))
    let f := Spec.map (CommRingCat.ofHom (MvPolynomial.rename
      (Fin.castSucc : Fin n → Fin (n + 1))).toRingHom)
    ∃ e : Spec (.of (MvPolynomial (Fin (n + 1)) K)) ≅ AffineSpace PUnit.{u + 1} B,
      e.hom ≫ AffineSpace PUnit.{u + 1} B ↘ B = f := by
  let R := MvPolynomial (Fin n) K
  obtain ⟨e, heC⟩ : ∃ e : MvPolynomial (Fin (n + 1)) K ≃+*
      MvPolynomial PUnit.{u + 1} R,
      e.toRingHom.comp
        (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1))).toRingHom =
        MvPolynomial.C := ⟨lastVariableRingEquiv K n, lastVariableRingEquiv_rename K n⟩
  let k := Scheme.Spec.mapIso e.symm.toCommRingCatIso.op
  have he : e.symm.toRingHom.comp MvPolynomial.C =
      (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1))).toRingHom := by
    apply RingHom.ext
    intro p
    apply e.injective
    change e (e.symm (MvPolynomial.C p)) = e (MvPolynomial.rename Fin.castSucc p)
    rw [e.apply_symm_apply]
    exact (congrArg (fun φ ↦ φ p) heC).symm
  refine ⟨k ≪≫ (AffineSpace.SpecIso PUnit.{u + 1} (.of R)).symm, ?_⟩
  change (k.hom ≫ (AffineSpace.SpecIso PUnit.{u + 1} (.of R)).inv) ≫ _ = _
  rw [Category.assoc, AffineSpace.SpecIso_inv_over]
  change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom MvPolynomial.C) = _
  rw [← Spec.map_comp]
  exact congrArg Spec.map (congrArg CommRingCat.ofHom he)

private theorem torsionCd_affine_of_projection_bounds
    {K : Type u} [Field K] {c d : ℕ}
    (hK : (Spec (.of K)).HasTorsionCohomologicalDimensionLE c) {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [IsAffine X]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    X.HasTorsionCohomologicalDimensionLE (d + c) := by
  sorry

/-- Blueprint `thm-sc-affine-torsion-cd`: The affine torsion cohomological dimension bound.

Let `K` be a field with `cd_tor(K) ≤ c`, and let `X` be an affine `K`-scheme of finite type
(structure morphism `a`) of dimension at most `d`. Then `cd_tor(X) ≤ d + c`:
`Hᵠ(X_ét, F) = 0` for every torsion abelian étale sheaf `F` on `X` and every `q > d + c`.

The proof is by induction on `d`, over all ground fields at once; it reduces to algebraically
closed `K` (`lem-sc-cd-ground-field`) and, by Noether normalisation, to affine space, where the
Leray spectral sequence of `𝔸ᵈ ⟶ ℙ¹ × 𝔸ᵈ⁻¹ ⟶ 𝔸ᵈ⁻¹` and a computation of the stalks of the
higher direct images (`lem-sc-one-variable-field-cd`, `lem-sc-cd-affine-limit`) conclude. -/
theorem hasTorsionCohomologicalDimensionLE_of_isAffine {K : Type u} [Field K] {c d : ℕ}
    (hK : (Spec (.of K)).HasTorsionCohomologicalDimensionLE c) {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [IsAffine X]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    X.HasTorsionCohomologicalDimensionLE (d + c) := by
  exact torsionCd_affine_of_projection_bounds hK a hX

end AlgebraicGeometry.Scheme
