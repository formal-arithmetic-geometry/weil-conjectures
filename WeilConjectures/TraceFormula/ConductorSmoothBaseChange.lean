/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.ReducedNormalization
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Mathlib.Algebra.Field.ULift
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.NormalizedBlowupCalculus
import WeilConjectures.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange
import WeilConjectures.RingTheory.AnnihilatorFiniteFlatBaseChange
import WeilConjectures.AlgebraicGeometry.SchemeTheoreticSupport
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.CanonicalStructureBaseChangeIsIso
import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Conductor and smooth base change

Source: Stacks Project, Algebra, Tag 07T8; Morphisms, Tags 035P, 035S, 0H7D;
ILO Exposé VIII, Lemma 2.2.9 (blueprint: lem-trf-conductor-smooth-base-change).
-/



universe u

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- The cokernel of the canonical structure-sheaf map into the pushforward of the
componentwise normalization.
Source: Stacks Project, Algebra, Tag 07T8 (blueprint: lem-trf-conductor-smooth-base-change). -/
noncomputable def conductorCokernel (S : Scheme.{u}) : S.Modules :=
  cokernel (SheafOfModules.unitToPushforwardObjUnit
    (Scheme.fromReducedNormalization S).toRingCatSheafHom)

/-- The ideal sheaf obtained affine-locally as the annihilator of the normalization
cokernel.
Source: Stacks Project, Algebra, Tag 07T8 (blueprint: lem-trf-conductor-smooth-base-change). -/
noncomputable def conductorIdeal (S : Scheme.{u}) : S.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals (fun U ↦
    Module.annihilator (Γ(S, U)) (Γ(conductorCokernel S, U)))

private theorem coherent_unit (S : Scheme.{u}) [IsLocallyNoetherian S] :
    RingedSpace.IsCoherent S.toRingedSpace (SheafOfModules.unit S.ringCatSheaf) :=
  Scheme.Modules.isCoherent_unit_of_finite_to_locallyNoetherian (𝟙 S)

private theorem coherent_structure_cokernel {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] [IsLocallyNoetherian S] :
    RingedSpace.IsCoherent S.toRingedSpace
      (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) := by
  have hX := Scheme.Modules.isCoherent_unit_of_finite_to_locallyNoetherian f
  have hpush := (Scheme.Modules.isCoherent_pushforward_of_isFinite f _ hX).1
  exact ((RingedSpace.coherent_kernel_cokernel_sum S.toRingedSpace).1 _ _
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
    (coherent_unit S) hpush).2

private theorem coherent_ideal (S : Scheme.{u}) [IsLocallyNoetherian S]
    (I : S.IdealSheafData) :
    RingedSpace.IsCoherent S.toRingedSpace I.toModules := by
  have hZ := Scheme.Modules.isCoherent_unit_of_finite_to_locallyNoetherian I.subschemeι
  have hpush := (Scheme.Modules.isCoherent_pushforward_of_isFinite I.subschemeι _ hZ).1
  exact ((RingedSpace.coherent_kernel_cokernel_sum S.toRingedSpace).1 _ _
    I.toPushforwardSubscheme (coherent_unit S) hpush).1

private theorem conductor_ideal_affine (S : Scheme.{u}) [IsLocallyNoetherian S]
    (hC : RingedSpace.IsCoherent S.toRingedSpace (conductorCokernel S))
    (U : S.affineOpens) :
    (conductorIdeal S).ideal U = Module.annihilator Γ(S, U.1) Γ(conductorCokernel S, U.1) := by
  obtain ⟨hq, ht⟩ :=
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType S _).mp hC
  let := hq
  let := ht
  obtain ⟨I, hI, _⟩ := Scheme.schemeTheoreticSupport S (conductorCokernel S)
  have heq : conductorIdeal S = I := by
    unfold conductorIdeal
    rw [show (fun U : S.affineOpens ↦
      Module.annihilator Γ(S, U.1) Γ(conductorCokernel S, U.1)) = I.ideal from
      funext fun U ↦ (hI U).symm, Scheme.IdealSheafData.ofIdeals_ideal]
  rw [heq, hI]

private theorem structure_cokernel_sections (X S : Scheme.{u}) (f : X ⟶ S)
    [IsFinite f] [IsLocallyNoetherian S] [IsSchemeTheoreticallyDominant f]
    (U : S.affineOpens) :
    Subsingleton Γ(cokernel
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom), U.1) ↔
      IsIso (f ∣_ U.1) := by
  let φ := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have hpush := (Scheme.Modules.isCoherent_pushforward_of_isFinite f _
    (Scheme.Modules.isCoherent_unit_of_finite_to_locallyNoetherian f)).1
  have : ((SheafOfModules.pushforward f.toRingCatSheafHom).obj
      (SheafOfModules.unit X.ringCatSheaf)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType S _).mp hpush).1
  have := SheafOfModules.isQuasicoherent_unit (R := S.ringCatSheaf)
  obtain ⟨_, _, _, _, _, _, _, _, h⟩ := Scheme.Modules.quasiCoherent_cokernel_image φ
  obtain ⟨_, hsurj, hker, _⟩ := h U
  rw [isIso_morphismRestrict_iff_isIso_app f U.2, ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro hs
    let := hs
    refine ⟨f.app_injective U.1, fun y ↦ ?_⟩
    have hy : y ∈ LinearMap.ker ((cokernel.π φ).val.app (Opposite.op U.1)).hom :=
      hs.elim _ _
    rw [hker] at hy
    exact hy
  · intro hb
    refine ⟨fun a b ↦ ?_⟩
    have hz (a : Γ(cokernel φ, U.1)) : a = 0 := by
      obtain ⟨y, rfl⟩ := hsurj a
      obtain ⟨x, rfl⟩ := hb.2 y
      have hh := congrArg (fun t : SheafOfModules.unit S.ringCatSheaf ⟶ cokernel φ ↦
        t.val.app (Opposite.op U.1)) (cokernel.condition φ)
      exact ConcreteCategory.congr_hom hh x
    exact (hz a).trans (hz b).symm

private theorem normal_of_iso_open (S : Scheme.{u}) (U : S.Opens)
    [IsIso (S.fromReducedNormalization ∣_ U)] (x : S) (hx : x ∈ U) :
    IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x) := by
  let f := inv (S.fromReducedNormalization ∣_ U) ≫
    (S.fromReducedNormalization ⁻¹ᵁ U).ι
  let y : U.toScheme := ⟨x, hx⟩
  let e := (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  have := (AlgebraicGeometry.normal_normalization S (f y)).1
  have := (AlgebraicGeometry.normal_normalization S (f y)).2
  have hd : IsDomain (U.toScheme.presheaf.stalk y) := e.symm.toMulEquiv.isDomain
  have hc : IsIntegrallyClosed (U.toScheme.presheaf.stalk y) :=
    IsIntegrallyClosed.of_equiv e
  let a := (U.stalkIso y).commRingCatIsoToRingEquiv
  exact ⟨a.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv a⟩

private theorem conductor_support_normal (S : Scheme.{u}) [IsReduced S]
    (q : S ⟶ Spec (.of (ULift ℚ))) [LocallyOfFiniteType q] [QuasiCompact q]
    [IsFinite S.fromReducedNormalization]
    [IsSchemeTheoreticallyDominant S.fromReducedNormalization]
    [IsLocallyNoetherian S]
    (N : S.Opens) (hN : ∀ x : S, x ∈ N ↔
      IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x))
    (hNi : IsIso (S.fromReducedNormalization ∣_ N)) :
    ∀ x : S, x ∈ ((conductorIdeal S).support : Set S) ↔
      ¬ (IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x)) := by
  have hC := coherent_structure_cokernel S.fromReducedNormalization
  have hc (U : S.affineOpens) := structure_cokernel_sections _ _
    S.fromReducedNormalization U
  intro x
  apply not_iff_not.mp
  rw [not_not]
  constructor
  · intro hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUS⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open hx
        (conductorIdeal S).support.isClosed.isOpen_compl
    have hdis : Disjoint (U : Set S) ((conductorIdeal S).support : Set S) :=
      Set.disjoint_left.mpr fun y hy hs ↦ hUS hy hs
    have ht := (conductorIdeal S).ideal_eq_top_of_disjoint_support (U := ⟨U, hU⟩) hdis
    rw [conductor_ideal_affine S hC] at ht
    have hs := Module.annihilator_eq_top_iff.mp ht
    have := (hc ⟨U, hU⟩).mp hs
    exact normal_of_iso_open S U x hxU
  · intro hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUN⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open ((hN x).mpr hx) N.isOpen
    have := S.fromReducedNormalization.isIso_restrict_of_le hUN hNi
    have ht := (Module.annihilator_eq_top_iff (R := Γ(S, U))
      (M := Γ(conductorCokernel S, U))).mpr ((hc ⟨U, hU⟩).mpr inferInstance)
    intro hs
    change x ∈ (conductorIdeal S).support at hs
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU,
      conductor_ideal_affine S hC, ht] at hs
    have h1 := (Scheme.mem_zeroLocus_iff _ _ _).mp hs 1 Submodule.mem_top
    rw [Scheme.basicOpen_one] at h1
    exact h1 hxU

private theorem smooth_normalization_square (S T : Scheme.{u}) [IsReduced S]
    (q : S ⟶ Spec (.of (ULift ℚ))) [LocallyOfFiniteType q] [QuasiCompact q]
    (h : T ⟶ S) [Smooth h] [QuasiCompact h] :
    IsReduced T ∧ ∃ n : T.reducedNormalization ⟶ S.reducedNormalization,
      IsPullback n T.fromReducedNormalization S.fromReducedNormalization h := by
  have hfg (U : S.affineOpens) : ((⊤ : S.IdealSheafData).ideal U).FG := by
    simpa using (Ideal.fg_top Γ(S, U.1) : (⊤ : Ideal Γ(S, U.1)).FG)
  have hd : Dense ((⊤ : S.IdealSheafData).support.compl : Set S) := by
    simp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs, _⟩ :=
    Scheme.IdealSheafData.normalizedBlowup_calculus S q ⊤ hfg hd
  obtain ⟨ht, _, ⟨n, hn, _⟩, hp, _⟩ := hs T h
  exact ⟨ht, n, hp n hn⟩

open Scheme.Modules in
private theorem structure_cokernel_base_change {X Y X' Y' : Scheme.{u}}
    (p : X ⟶ Y) (q : X' ⟶ Y') (g : Y' ⟶ Y) (k : X' ⟶ X)
    (sq : IsPullback k q p g) [IsAffineHom p] :
    Nonempty ((Scheme.Modules.pullback g).obj
        (cokernel (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom)) ≅
      cokernel (SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom)) := by
  let β := ((pullbackPushforwardAdjunction g).homEquiv _ _).symm
    ((pushforward p).map (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom) ≫
      (pushforwardComp k p).hom.app (unit X') ≫
      (pushforwardCongr sq.w).hom.app (unit X') ≫
      (pushforwardComp q g).inv.app (unit X'))
  have hβ : IsIso β := Scheme.Modules.canonical_structure_baseChange_isIso p q g k sq
  let α := Scheme.Modules.pullbackObjUnitIso g
  have comm : (Scheme.Modules.pullback g).map
      (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom) ≫ β =
      α.hom ≫ SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom := by
    apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right]
    dsimp only [β]
    erw [Equiv.apply_symm_apply]
    rw [show (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _ α.hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom from
        SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _]
    apply Scheme.Modules.hom_ext
    intro U
    ext r
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
      Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardComp_inv_app_app,
      Scheme.Modules.pushforwardCongr_hom_app_app, ConcreteCategory.comp_apply]
    change X'.presheaf.map
      (eqToHom (congrArg (fun f : X' ⟶ Y ↦ f ⁻¹ᵁ U) sq.w.symm)).op
        ((k.app (p ⁻¹ᵁ U)).hom ((p.app U).hom r)) =
      (q.app (g ⁻¹ᵁ U)).hom ((g.app U).hom r)
    have hw := Scheme.Hom.congr_app sq.w.symm U
    have hw' := congrArg (fun t ↦ t.hom r) hw
    simp only [Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply,
      CommRingCat.Hom.hom] at hw'
    convert! hw'.symm using 1
  exact ⟨PreservesCokernel.iso (Scheme.Modules.pullback g) _ ≪≫
    cokernel.mapIso _ _ α (asIso β) comm⟩

private theorem conductor_ideal_base_change (S T : Scheme.{u})
    [IsLocallyNoetherian S] [IsLocallyNoetherian T] (h : T ⟶ S) [Flat h]
    (hS : RingedSpace.IsCoherent S.toRingedSpace (conductorCokernel S))
    (hT : RingedSpace.IsCoherent T.toRingedSpace (conductorCokernel T))
    (e : (Scheme.Modules.pullback h).obj (conductorCokernel S) ≅ conductorCokernel T) :
    conductorIdeal T = (conductorIdeal S).comap h := by
  have : (conductorCokernel S).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType S _).mp hS).1
  have : (conductorCokernel S).IsFiniteType := hS.1
  let ι := Σ' (U : S.affineOpens) (V : T.affineOpens), V.1 ≤ h ⁻¹ᵁ U.1
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := ι) (fun i ↦ i.2.1)
  · rw [eq_top_iff]
    intro x _
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (h x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open (a := x) hxU (h ⁻¹ᵁ U).2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, ⟨V, hV⟩, hVU⟩, hxV⟩
  · rintro ⟨U, V, hVU⟩
    rw [Scheme.IdealSheafData.ideal_comap_appLE _ h U V hVU,
      conductor_ideal_affine S hS, conductor_ideal_affine T hT]
    let := (h.appLE U.1 V.1 hVU).hom.toAlgebra
    have : Module.Finite Γ(S, U.1) Γ(conductorCokernel S, U.1) :=
      Scheme.Modules.finite_sections_of_finiteType _ U.2
    obtain ⟨a, _⟩ := Scheme.Modules.exists_linearEquiv_pullback_sections
      h (conductorCokernel S) U.2 V.2 hVU
    let b : Γ((Scheme.Modules.pullback h).obj (conductorCokernel S), V.1) ≃ₗ[Γ(T, V.1)]
        Γ(conductorCokernel T, V.1) :=
      { toFun := e.hom.app V.1
        invFun := e.inv.app V.1
        map_add' := map_add _
        map_smul' := fun r m ↦ Scheme.Modules.Hom.app_smul e.hom r m
        left_inv := fun m ↦ congrArg (fun t ↦ t.app V.1 m) e.hom_inv_id
        right_inv := fun m ↦ congrArg (fun t ↦ t.app V.1 m) e.inv_hom_id }
    rw [← (a.trans b).annihilator_eq]
    exact Module.annihilator_tensorProduct_flat_base_change
      (IsScalarTower.toAlgHom Γ(S, U.1) Γ(S, U.1) Γ(T, V.1))
      (h.flat_appLE U.2 V.2 hVU)

/-- For a reduced finite-type scheme over `ℚ`, the conductor ideal of componentwise
normalization is coherent, cuts out exactly the nonnormal locus, and commutes with
quasi-compact smooth pullback. The conductor ideal `D_S` itself is stated coherent as an
`𝒪_S`-module through its ideal sheaf `(conductorIdeal S).toModules`.
Source: Stacks Project, Algebra, Tag 07T8; Morphisms, Tags 035P, 035S, 0H7D;
ILO Exposé VIII, Lemma 2.2.9 (blueprint: lem-trf-conductor-smooth-base-change).
Proof: use finiteness and injectivity of componentwise normalization, coherence of its
pushforward and cokernel, the affine annihilator/support calculation, and the smooth
normalization comparison. Apply finite flat annihilator base change on affine smooth
charts; the local equalities glue and are compatible with identity and composition.
-/
theorem conductor_smooth_base_change
    (S : Scheme.{u}) [AlgebraicGeometry.IsReduced S]
    (q : S ⟶ Spec (.of (ULift ℚ))) [LocallyOfFiniteType q] [QuasiCompact q]
    : IsFinite (Scheme.fromReducedNormalization S) ∧
      (∀ U : S.Opens, Function.Injective
        ((Scheme.fromReducedNormalization S).app U).hom) ∧
      RingedSpace.IsCoherent S.toRingedSpace (conductorCokernel S) ∧
      RingedSpace.IsCoherent S.toRingedSpace (conductorIdeal S).toModules ∧
      (∀ x : S, x ∈ ((conductorIdeal S).support : Set S) ↔
        ¬ (IsDomain (S.presheaf.stalk x).carrier ∧
          IsIntegrallyClosed (S.presheaf.stalk x).carrier)) ∧
      IsNowhereDense
        ((conductorIdeal S).support : Set S) ∧
      ((conductorIdeal S = ⊤) ↔
        ∀ x : S, IsDomain (S.presheaf.stalk x).carrier ∧
          IsIntegrallyClosed (S.presheaf.stalk x).carrier) ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ S), QuasiCompact h → Smooth h →
        conductorIdeal T = (conductorIdeal S).comap h) ∧
      ((conductorIdeal S).comap (𝟙 S) = conductorIdeal S) ∧
      (∀ (T U : Scheme.{u}) (h : T ⟶ S) (g : U ⟶ T),
        (conductorIdeal S).comap (g ≫ h) =
          ((conductorIdeal S).comap h).comap g)
    := by
  obtain ⟨hfin, hsurj, ⟨N, hN, hNd, hNi⟩, _⟩ :=
    reduced_algebraic_normalization_field_change (k := ULift ℚ) S q
  let := hfin
  let := hsurj
  have : IsDominant S.fromReducedNormalization := inferInstance
  have : IsSchemeTheoreticallyDominant S.fromReducedNormalization :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian q
  have hs := conductor_support_normal S q N hN hNi
  have hcompl : ((conductorIdeal S).support : Set S)ᶜ = (N : Set S) := by
    ext x
    simp only [Set.mem_compl_iff, hs, not_not, SetLike.mem_coe]
    exact (hN x).symm
  refine ⟨hfin, S.fromReducedNormalization.app_injective,
    coherent_structure_cokernel _, coherent_ideal S _, hs, ?_, ?_, ?_,
    (conductorIdeal S).comap_id, fun T U h g ↦ (conductorIdeal S).comap_comp g h⟩
  · apply ((conductorIdeal S).support.isClosed.isNowhereDense_iff).mpr
    apply interior_eq_empty_iff_dense_compl.mpr
    rw [hcompl]
    exact hNd
  · constructor
    · intro ht x
      by_contra hx
      have hm := (hs x).mpr hx
      simp [ht] at hm
    · intro hn
      apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
      apply TopologicalSpace.Closeds.ext
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact ((hs x).mp hx) (hn x)
  · intro T h hh hsmooth
    let := hh
    let := hsmooth
    obtain ⟨ht, n, hn⟩ := smooth_normalization_square S T q h
    let := ht
    have : LocallyOfFiniteType (h ≫ q) := inferInstance
    have : QuasiCompact (h ≫ q) := inferInstance
    have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (h ≫ q)
    have := (reduced_algebraic_normalization_field_change
      (k := ULift ℚ) T (h ≫ q)).1
    obtain ⟨e⟩ := structure_cokernel_base_change S.fromReducedNormalization
      T.fromReducedNormalization h n hn
    exact conductor_ideal_base_change S T h (coherent_structure_cokernel _)
      (coherent_structure_cokernel _) e

end AlgebraicGeometry

end
