/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q149
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.Depth
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.FittingIdealSheaf
public import Sheaf.AlgebraicGeometry.DthFittingSmoothLocus
import all WeilConjectures.AlgebraicGeometry.FibreCohenMacaulayLocus
import WeilConjectures.AlgebraicGeometry.CohenMacaulayFibreDimensionDecomposition
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import Sheaf.AlgebraicGeometry.FittingIdealGenerateLocally
import Sheaf.RingTheory.PresentationFittingIdeal
import Sheaf.AlgebraicGeometry.SmoothAtPointDifferentialCriterion
import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineSections
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Kaehler.TensorProduct

/-! # Detecting a smooth generic fibre from a finite jet

Source: Stacks Project, examples-defos.tex, Tag 0E7T, lemma-criterion-smoothing.
(blueprint: lem-sfb-finite-jet-smooth-generic-fibre)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
private theorem local_dimension_iso {X Z : Scheme.{u}} (e : X ≅ Z) (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (e.hom x) := by
  have hle {X Z : Scheme.{u}} (e : X ≅ Z) (x : X) :
      topologicalKrullDimAt x ≤ topologicalKrullDimAt (e.hom x) := by
    refine le_iInf₂ fun U hx ↦ (iInf₂_le (e.hom ⁻¹ᵁ U) hx).trans ?_
    let h : ↥(e.hom ⁻¹ᵁ U) ≃ₜ ↥U := e.hom.homeomorph.subtype (fun _ ↦ Iff.rfl)
    exact (IsHomeomorph.topologicalKrullDim_eq h h.isHomeomorph).le
  refine le_antisymm (hle e x) ?_
  simpa using hle e.symm (e.hom x)

set_option backward.isDefEq.respectTransparency.types false in
private theorem open_eq_top_of_special_fibre {k : Type u} [Field k]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of (PowerSeries k))) [IsProper f]
    (U : Y.Opens)
    (hU : ∀ x : ↥(pullback f (Spec.map (CommRingCat.ofHom
      (PowerSeries.constantCoeff (R := k))))), pullback.fst f _ x ∈ U) : U = ⊤ := by
  let i := Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))
  have hi : i (IsLocalRing.closedPoint k) =
      IsLocalRing.closedPoint (PowerSeries k) := by
    change PrimeSpectrum.comap (PowerSeries.constantCoeff (R := k)) _ = _
    apply PrimeSpectrum.ext
    change Ideal.comap (PowerSeries.constantCoeff (R := k)) (IsLocalRing.maximalIdeal k) = _
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact PowerSeries.ker_coeff_eq_max_ideal
  apply eq_top_iff.mpr
  intro y _
  by_contra hy
  have hclosed := f.isClosedMap (U : Set Y)ᶜ U.isOpen.isClosed_compl
  have hs : IsLocalRing.closedPoint (PowerSeries k) ∈ f '' (U : Set Y)ᶜ :=
    (IsLocalRing.specializes_closedPoint (f y)).mem_closed hclosed ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hzs⟩ := hs
  obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := i)
    z (IsLocalRing.closedPoint k)
    (hzs.trans hi.symm)
  exact hz (hw ▸ hU w)

set_option backward.isDefEq.respectTransparency.types false in
private theorem special_fibre_iso {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of (PowerSeries k))) :
    ∃ e : pullback f (Spec.map (CommRingCat.ofHom
        (PowerSeries.constantCoeff (R := k)))) ≅
      f.fiber (IsLocalRing.closedPoint (PowerSeries k)),
      e.hom ≫ f.fiberι _ = pullback.fst _ _ := by
  let S := Spec (.of (PowerSeries k))
  let i := Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))
  have : IsClosedImmersion i :=
    IsClosedImmersion.spec_of_surjective _ PowerSeries.constantCoeff_surj
  let s := i (IsLocalRing.closedPoint k)
  let a := S.descResidueField (Scheme.stalkClosedPointTo i)
  have ha : IsIso a := by
    apply (ConcreteCategory.isIso_iff_bijective a).mpr
    refine ⟨a.hom.injective, ?_⟩
    intro b
    obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso
      (stalkClosedPointIso (.of k)).hom).2 b
    obtain ⟨d, hd⟩ := i.stalkMap_surjective (IsLocalRing.closedPoint k) c
    refine ⟨S.residue s d, ?_⟩
    change (S.residue s ≫ a) d = b
    rw [Scheme.residue_descResidueField]
    exact (congrArg (stalkClosedPointIso (.of k)).hom hd).trans hc
  have hfac : Spec.map a ≫ S.fromSpecResidueField s = i :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k S i
  have hs : s = IsLocalRing.closedPoint (PowerSeries k) := by
    apply PrimeSpectrum.ext
    change Ideal.comap (PowerSeries.constantCoeff (R := k)) (IsLocalRing.maximalIdeal k) = _
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact PowerSeries.ker_coeff_eq_max_ideal
  let q := pullback.map f i f (S.fromSpecResidueField s)
    (𝟙 _) (Spec.map a) (𝟙 _) (by simp) (by simpa using hfac.symm)
  have : IsIso q := inferInstance
  refine ⟨asIso q ≪≫ eqToIso (congrArg f.fiber hs), ?_⟩
  have heq (t t' : Spec (.of (PowerSeries k))) (h : t = t') :
      eqToHom (congrArg f.fiber h) ≫ f.fiberι t' = f.fiberι t := by
    subst t'
    simp
  change (q ≫ eqToHom (congrArg f.fiber hs)) ≫ f.fiberι _ = _
  rw [Category.assoc, heq _ _ hs]
  change q ≫ pullback.fst f (S.fromSpecResidueField s) = _
  exact pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency.types false in
private theorem special_fibre_point_iso {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of (PowerSeries k)))
    (x : ↥(pullback f (Spec.map (CommRingCat.ofHom
      (PowerSeries.constantCoeff (R := k)))))) :
    ∃ e : pullback f (Spec.map (CommRingCat.ofHom
        (PowerSeries.constantCoeff (R := k)))) ≅ f.fiber (f (pullback.fst f _ x)),
      e.hom x = f.asFiber (pullback.fst f _ x) := by
  obtain ⟨e, he⟩ := special_fibre_iso f
  let y := pullback.fst f (Spec.map (CommRingCat.ofHom
    (PowerSeries.constantCoeff (R := k)))) x
  have hy : f y = IsLocalRing.closedPoint (PowerSeries k) := by
    change f (pullback.fst f _ x) = _
    rw [← he, Scheme.Hom.comp_apply]
    rw [← Scheme.Hom.comp_apply, f.fiber_fac, Scheme.Hom.comp_apply,
      f.fiberToSpecResidueField_apply]
    simp
  let e' := e ≪≫ eqToIso (congrArg f.fiber hy.symm)
  refine ⟨e', ?_⟩
  apply (f.fiberι _).isEmbedding.injective
  have heq (t t' : Spec (.of (PowerSeries k))) (h : t = t') :
      eqToHom (congrArg f.fiber h) ≫ f.fiberι t' = f.fiberι t := by
    subst t'
    simp
  change f.fiberι _ (e'.hom x) = _
  change (e'.hom ≫ f.fiberι (f y)) x = _
  have hf : e'.hom ≫ f.fiberι (f y) = pullback.fst f _ := by
    change (e.hom ≫ eqToHom (congrArg f.fiber hy.symm)) ≫ f.fiberι (f y) = _
    rw [Category.assoc, heq _ _ hy.symm, he]
  rw [hf, Scheme.Hom.fiberι_asFiber]

set_option backward.isDefEq.respectTransparency.types false in
private theorem presentation_fitting_comp_equiv {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) {n : ℕ} (π : (Fin n → R) →ₗ[R] M) (d : ℕ) :
    (e.toLinearMap.comp π).presentationFittingIdeal d = π.presentationFittingIdeal d := by
  simp only [LinearMap.presentationFittingIdeal, LinearMap.comp_apply,
    LinearEquiv.coe_coe, EmbeddingLike.map_eq_zero_iff]

open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency.types false in
private theorem fitting_affine_baseChange {X S T P : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (p : P ⟶ X) (q : P ⟶ T)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation q]
    (U : X.affineOpens) (V : P.affineOpens)
    (A : S.affineOpens) (B : T.affineOpens)
    (hf : U.1 ≤ f ⁻¹ᵁ A.1) (hg : B.1 ≤ g ⁻¹ᵁ A.1)
    (hp : V.1 ≤ p ⁻¹ᵁ U.1) (hq : V.1 ≤ q ⁻¹ᵁ B.1)
    (H : IsPushout (f.appLE A.1 U.1 hf) (g.appLE A.1 B.1 hg)
      (p.appLE U.1 V.1 hp) (q.appLE B.1 V.1 hq)) (d : ℕ) :
    (Scheme.Modules.fittingIdealSheaf q.relativeDifferentials d).ideal V =
      ((Scheme.Modules.fittingIdealSheaf f.relativeDifferentials d).ideal U).map
        (p.appLE U.1 V.1 hp).hom := by
  let R := Γ(S, A.1)
  let R' := Γ(T, B.1)
  let C := Γ(X, U.1)
  let C' := Γ(P, V.1)
  let a := f.appLE A.1 U.1 hf
  let b := g.appLE A.1 B.1 hg
  let c := p.appLE U.1 V.1 hp
  let e := q.appLE B.1 V.1 hq
  let : Algebra R C := a.hom.toAlgebra
  let : Algebra R R' := b.hom.toAlgebra
  let : Algebra C C' := c.hom.toAlgebra
  let : Algebra R' C' := e.hom.toAlgebra
  let : Algebra R C' := (e.hom.comp b.hom).toAlgebra
  have : IsScalarTower R R' C' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R C C' := IsScalarTower.of_algebraMap_eq fun r ↦ by
    exact congr($(H.w).hom r).symm
  have : Algebra.IsPushout R R' C C' :=
    CommRingCat.isPushout_iff_isPushout.mp H.flip
  obtain ⟨e₁, _⟩ := relativeDifferentials_affine_sections f U A hf
  obtain ⟨e₂, _⟩ := relativeDifferentials_affine_sections q V B hq
  let e₃ : C' ⊗[C] Γ(f.relativeDifferentials, U.1) ≃ₗ[C']
      Γ(q.relativeDifferentials, V.1) :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C' C') e₁.symm) ≪≫ₗ
      (KaehlerDifferential.tensorKaehlerEquiv R R' C C') ≪≫ₗ e₂
  have : Module.Finite C Γ(f.relativeDifferentials, U.1) :=
    Scheme.Modules.finite_sections_of_finiteType f.relativeDifferentials U.2
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' C Γ(f.relativeDifferentials, U.1)
  have hbase := (π.presentationFittingIdeal_independence_baseChange d hπ).2.1 C'
  rw [(Scheme.Modules.fitting_ideal_generate_locally _ _ d).1 V n
    (e₃.toLinearMap.comp (π.baseChangePresentation C'))
      (e₃.surjective.comp hbase.1), presentation_fitting_comp_equiv,
    hbase.2, (Scheme.Modules.fitting_ideal_generate_locally _ _ d).1 U n π hπ]
  rfl

/-- The canonical closed thickening `Spec (k[[t]]/(t^n)) → Spec k[[t]]`.
Source: Stacks Project, examples-defos.tex, Tag 0E7T, lemma-criterion-smoothing;
its `k[t]/(t^n)` is canonically this quotient for positive `n`.
(blueprint: lem-sfb-finite-jet-smooth-generic-fibre) -/
noncomputable def Scheme.powerSeriesJetBaseMap (k : Type u) [Field k] (n : ℕ) :
    Spec (.of ((PowerSeries k) ⧸
      Ideal.span {(PowerSeries.X : PowerSeries k) ^ n})) ⟶ Spec (.of (PowerSeries k)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    (Ideal.span {(PowerSeries.X : PowerSeries k) ^ n})))

set_option backward.isDefEq.respectTransparency.types false in
private theorem spec_ker {R S : CommRingCat.{u}} (a : R ⟶ S) :
    (Spec.map a).ker = Scheme.IdealSheafData.ofIdealTop
      ((RingHom.ker a.hom).map (Scheme.ΓSpecIso R).inv.hom) := by
  rw [Scheme.ker_of_isAffine]
  congr 1
  ext z
  obtain ⟨w, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).2 z
  have hnat : (Spec.map a).appTop ((Scheme.ΓSpecIso R).inv w) =
      (Scheme.ΓSpecIso S).inv (a w) :=
    congr($(Scheme.ΓSpecIso_inv_naturality a) w).symm
  rw [RingHom.mem_ker, hnat, Ideal.mem_map_iff_of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).2]
  constructor
  · intro hw
    refine ⟨w, ?_, rfl⟩
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).inv).1
      (hw.trans (map_zero _).symm)
  · rintro ⟨w', hw', he⟩
    have hw := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).1 he
    subst w'
    rw [show a w = 0 from hw', map_zero]

set_option backward.isDefEq.respectTransparency.types false in
private theorem jet_base_ker (k : Type u) [Field k] (n : ℕ) :
    (Scheme.powerSeriesJetBaseMap k n).ker = Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {((Scheme.ΓSpecIso (.of (PowerSeries k))).inv
        (PowerSeries.X : PowerSeries k)) ^ n}) := by
  rw [Scheme.powerSeriesJetBaseMap, spec_ker]
  simp only [CommRingCat.hom_ofHom, Ideal.mk_ker, Ideal.map_span,
    Set.image_singleton, map_pow]

set_option backward.isDefEq.respectTransparency.types false in
private theorem restrict_ideal_mem {X : Scheme.{u}} (I : X.IdealSheafData)
    {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (ha : a ∈ I.idealOfOpens U) :
    X.presheaf.map (homOfLE h).op a ∈ I.idealOfOpens V := by
  change I.subschemeι.app V (X.presheaf.map (homOfLE h).op a) = 0
  rw [← CommRingCat.comp_apply, I.subschemeι.naturality, CommRingCat.comp_apply]
  change I.subscheme.presheaf.map _ (I.subschemeι.app U a) = 0
  rw [show I.subschemeι.app U a = 0 from ha, map_zero]

set_option backward.isDefEq.respectTransparency.types false in
private theorem jet_fitting_local_relation (k : Type u) [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of (PowerSeries k))) [LocallyOfFinitePresentation f]
    (d n : ℕ)
    (hjet : (pullback.snd f (Scheme.powerSeriesJetBaseMap k n)).appTop
        ((Scheme.ΓSpecIso (.of ((PowerSeries k) ⧸
          Ideal.span {(PowerSeries.X : PowerSeries k) ^ n}))).inv
          (Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ (n - 1)))) ∈
      (Scheme.Modules.fittingIdealSheaf
        (pullback.snd f (Scheme.powerSeriesJetBaseMap k n)).relativeDifferentials
          d).idealOfOpens ⊤)
    (U : Y.affineOpens) :
    let t := f.appLE ⊤ U.1 le_top
      ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv (PowerSeries.X : PowerSeries k))
    ∃ b ∈ (Scheme.Modules.fittingIdealSheaf f.relativeDifferentials d).ideal U,
      ∃ a : Γ(Y, U.1), t ^ (n - 1) = b + t ^ n * a := by
  let j := Scheme.powerSeriesJetBaseMap k n
  let p := pullback.fst f j
  let q := pullback.snd f j
  have : IsClosedImmersion j :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion p := MorphismProperty.pullback_fst _ _ inferInstance
  have : LocallyOfFinitePresentation q := MorphismProperty.pullback_snd _ _ inferInstance
  let V : (pullback f j).affineOpens := ⟨p ⁻¹ᵁ U.1, U.2.preimage p⟩
  let A : (Spec (.of (PowerSeries k))).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let B : (Spec (.of ((PowerSeries k) ⧸
    Ideal.span {(PowerSeries.X : PowerSeries k) ^ n}))).affineOpens :=
    ⟨⊤, isAffineOpen_top _⟩
  have hinf : V.1 = p ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ B.1 := by simp [V, B]
  have H := (isIso_pushoutSection_iff (IsPullback.of_hasPullback f j)
      (show B.1 ≤ j ⁻¹ᵁ A.1 by simp [A, B])
      (show U.1 ≤ f ⁻¹ᵁ A.1 by simp [A]) hinf).mp
    (isIso_pushoutSection_of_isAffineOpen (IsPullback.of_hasPullback f j)
      (show B.1 ≤ j ⁻¹ᵁ A.1 by simp [A, B])
      (show U.1 ≤ f ⁻¹ᵁ A.1 by simp [A]) hinf A.2 B.2 U.2)
  have hfit := fitting_affine_baseChange f j p q U V A B
    (by simp [A]) (by simp [A, B]) le_rfl (by simp [B]) H d
  let t := f.appLE ⊤ U.1 le_top
    ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv (PowerSeries.X : PowerSeries k))
  have hc : p.appLE U.1 V.1 le_rfl = p.app U.1 := by
    rw [Scheme.Hom.app_eq_appLE]
  rw [hc] at hfit
  have hmem : (p.app U.1) (t ^ (n - 1)) ∈
      (Scheme.Modules.fittingIdealSheaf q.relativeDifferentials d).ideal V := by
    have h := restrict_ideal_mem
      (Scheme.Modules.fittingIdealSheaf q.relativeDifferentials d) (V := V.1) le_top _ hjet
    rw [Scheme.IdealSheafData.idealOfOpens_eq_ideal _ V] at h
    convert h using 1
    change (p.app U.1) ((f.appLE ⊤ U.1 le_top
      ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv
        (PowerSeries.X : PowerSeries k))) ^ (n - 1)) = _
    rw [map_pow, ← CommRingCat.comp_apply, ← hc,
      Scheme.Hom.appLE_comp_appLE, pullback.condition]
    rw [← Scheme.Hom.appLE_comp_appLE q j ⊤ ⊤ V.1 le_top (by simp),
      CommRingCat.comp_apply]
    have hj : j.appLE ⊤ ⊤ le_top = j.appTop := by
      simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    rw [hj]
    have hn := congr($(Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {(PowerSeries.X : PowerSeries k) ^ n}))))
      (PowerSeries.X : PowerSeries k))
    change (Scheme.ΓSpecIso (.of ((PowerSeries k) ⧸
      Ideal.span {(PowerSeries.X : PowerSeries k) ^ n}))).inv
        (Ideal.Quotient.mk _ PowerSeries.X) =
      j.appTop ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv PowerSeries.X) at hn
    change q.appLE ⊤ V.1 _ (j.appTop
      ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv PowerSeries.X)) ^ (n - 1) = _
    rw [← hn, ← map_pow, ← map_pow]
    simp [q, Scheme.Hom.appLE, Scheme.Hom.appTop, j]
  rw [hfit] at hmem
  obtain ⟨b, hb, he⟩ := (Ideal.mem_map_iff_of_surjective (p.app U.1).hom
    (p.app_surjective U.1 U.2)).mp hmem
  have hker : RingHom.ker (p.app U.1).hom = Ideal.span {t ^ n} := by
    rw [← Scheme.Hom.ker_apply p U]
    change ((pullback.fst f j).ker).ideal U = _
    rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, jet_base_ker,
      Scheme.IdealSheafData.ideal_comap_appLE _ f A U (by simp [A])]
    simp only [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span,
      Set.image_singleton, map_pow]
    congr 2
  have hdiff : t ^ (n - 1) - b ∈ Ideal.span {t ^ n} := by
    rw [← hker, RingHom.mem_ker, map_sub, he, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hdiff
  exact ⟨b, hb, a, by linear_combination ha⟩

/-- A proper flat finitely presented family over `k[[t]]` with pure Cohen--Macaulay
special fibre has smooth Laurent-series generic fibre if some finite jet has the
specified Fitting-ideal section. `idealOfOpens ⊤` means membership as a global section,
not merely membership in the support or in one affine chart.
Source: Stacks Project, examples-defos.tex, Tag 0E7T, lemma-criterion-smoothing.
(blueprint: lem-sfb-finite-jet-smooth-generic-fibre)

Proof:
1. Properness makes every open containing the special fibre equal to the whole source:
   the closed image of its complement must contain the closed point of the local base
   if it is nonempty. Identify the special fibre with the fibre over that closed point.
2. Apply openness of the fibre Cohen--Macaulay locus, then the relative-dimension open
   partition. Pure dimension of the special fibre identifies its local dimension as d.
   The d-piece contains the special fibre, so properness makes it the whole source.
3. On affine charts identify differential sections with Kähler differentials. Tensor
   base change and presentation independence give base change of their Fitting ideals.
   The jet bound therefore gives t^(n-1) = b + t^n a with b in the original Fitting ideal.
4. The basic opens D(1-ta) contain the special fibre, so together cover the source by
   properness. On the generic fibre t is invertible, hence the equation makes b a unit
   on these opens. Every generic-fibre point is outside the Fitting support.
5. The Fitting generator criterion and the dimension from step 2 imply smoothness on
   a neighbourhood of each such point. Restrict these neighbourhoods to the generic
   fibre, cancel its open immersion into the base, and use Zariski source locality.
   For n=1 the same unit equation applies; for an empty fibre the cover is empty.
-/
theorem smooth_genericFibre_of_finiteJet_fitting
    (k : Type u) [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of (PowerSeries k)))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] (d : ℕ)
    (hCM : ∀ x : ↥(pullback f (Spec.map (CommRingCat.ofHom
        (PowerSeries.constantCoeff (R := k))))),
      (IsLocalRing.depth
        (R := (pullback f (Spec.map (CommRingCat.ofHom
          (PowerSeries.constantCoeff (R := k))))).presheaf.stalk x)
        ((pullback f (Spec.map (CommRingCat.ofHom
          (PowerSeries.constantCoeff (R := k))))).presheaf.stalk x) : WithBot ℕ∞) =
      ringKrullDim ((pullback f (Spec.map (CommRingCat.ofHom
        (PowerSeries.constantCoeff (R := k))))).presheaf.stalk x))
    (hpure : (pullback f (Spec.map (CommRingCat.ofHom
      (PowerSeries.constantCoeff (R := k))))).IsPureDimension d)
    (hjet : ∃ n : ℕ, 1 ≤ n ∧
      (pullback.snd f (Scheme.powerSeriesJetBaseMap k n)).appTop
        ((Scheme.ΓSpecIso (.of ((PowerSeries k) ⧸
          Ideal.span {(PowerSeries.X : PowerSeries k) ^ n}))).inv
          (Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ (n - 1)))) ∈
      (Scheme.Modules.fittingIdealSheaf
        (pullback.snd f (Scheme.powerSeriesJetBaseMap k n)).relativeDifferentials
          d).idealOfOpens ⊤) :
    Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom
      (algebraMap (PowerSeries k) (LaurentSeries k))))) := by
  let i := Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))
  have hspecial (x : ↥(pullback f i)) :
      (IsLocalRing.depth
        (R := (f.fiber (f (pullback.fst f i x))).presheaf.stalk
          (f.asFiber (pullback.fst f i x)))
        ((f.fiber (f (pullback.fst f i x))).presheaf.stalk
          (f.asFiber (pullback.fst f i x))) : WithBot ℕ∞) =
        ringKrullDim ((f.fiber (f (pullback.fst f i x))).presheaf.stalk
          (f.asFiber (pullback.fst f i x))) := by
    obtain ⟨e, he⟩ := special_fibre_point_iso f x
    let r := ((f.fiber (f (pullback.fst f i x))).presheaf.stalkCongr
      (.of_eq he.symm) ≪≫ asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv
    -- Reuse the depth transport from FibreCohenMacaulayLocus via its `import all`.
    rw [depth_eq_of_ringEquiv r, ringKrullDim_eq_of_ringEquiv r]
    exact hCM x
  let W : Y.Opens := ⟨_, isOpen_fibre_depth_eq_ringKrullDim f⟩
  have hW : W = ⊤ := open_eq_top_of_special_fibre f W hspecial
  have hcm (y : Y) :
      (IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
        ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) := by
    exact hW.ge (Set.mem_univ y)
  obtain ⟨V, hcover, hdisj, hdim⟩ :=
    exists_fibre_dimension_open_partition_of_depth_eq_ringKrullDim f ⊤ ⊤
      (fun y _ ↦ ⟨trivial, hcm y⟩)
  have hdspecial (x : ↥(pullback f i)) :
      topologicalKrullDimAt (f.asFiber (pullback.fst f i x)) = (d : WithBot ℕ∞) := by
    obtain ⟨e, he⟩ := special_fibre_point_iso f x
    rw [← he, ← local_dimension_iso e]
    have : LocallyOfFiniteType (pullback.snd f i) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    have ht : ∀ C ∈ irreducibleComponents ↥(⊤ : (pullback f i).Opens),
        topologicalKrullDim C = (d : WithBot ℕ∞) := by
      intro C hC
      let e : ↥(⊤ : (pullback f i).Opens) ≃ₜ ↥(pullback f i) :=
        Homeomorph.Set.univ _
      have himage : e '' C ∈ irreducibleComponents ↥(pullback f i) :=
        image_mem_irreducibleComponents_of_isPreirreducible_fiber e e.continuous
          e.isOpenMap (fun y ↦ (Set.subsingleton_singleton.preimage e.injective).isPreirreducible)
          e.surjective hC
      exact (IsHomeomorph.topologicalKrullDim_eq (e.image C)
        (e.image C).isHomeomorph).trans (hpure _ himage)
    exact topologicalKrullDimAt_eq_of_equidimensional_open (pullback.snd f i)
      ⊤ d ht x trivial
  have hdimall (y : Y) : topologicalKrullDimAt (f.asFiber y) = (d : WithBot ℕ∞) := by
    have hv : V d = ⊤ := by
      apply open_eq_top_of_special_fibre f
      intro x
      obtain ⟨n, hn⟩ := TopologicalSpace.Opens.mem_iSup.mp
        (hcover.ge (Set.mem_univ (pullback.fst f i x)))
      have hn' := (hdim n _ hn).symm.trans (hdspecial x)
      have : n = d := by exact_mod_cast hn'
      simpa [this] using hn
    exact hdim d y (hv.ge (Set.mem_univ y))
  obtain ⟨n, hn, hjet⟩ := hjet
  let t (U : Y.affineOpens) := f.appLE ⊤ U.1 le_top
    ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv (PowerSeries.X : PowerSeries k))
  choose b hb a he using jet_fitting_local_relation k f d n hjet
  let G (U : Y.affineOpens) : Y.Opens := Y.basicOpen (1 - t U * a U)
  have hG : (⨆ U, G U) = ⊤ := by
    apply open_eq_top_of_special_fibre f
    intro x
    let y := pullback.fst f i x
    obtain ⟨U₀, hU₀, hyU, -⟩ := exists_isAffineOpen_mem_and_subset
      (TopologicalSpace.Opens.mem_top y)
    let U : Y.affineOpens := ⟨U₀, hU₀⟩
    have ht : y ∉ Y.basicOpen (t U) := by
      rw [Scheme.basicOpen_appLE]
      intro h
      have hz : f y ∈ PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries k) := by
        have h' := h.2
        change f y ∈ (Spec (.of (PowerSeries k))).basicOpen
          ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv PowerSeries.X) at h'
        rwa [basicOpen_eq_of_affine] at h'
      have hfi : f y = i (pullback.snd f i x) :=
        congr($(pullback.condition (f := f) (g := i)) x)
      rw [hfi] at hz
      change PowerSeries.constantCoeff PowerSeries.X ∉
        (pullback.snd f i x).asIdeal at hz
      exact hz (by simp)
    have htu : ¬ IsUnit (Y.presheaf.germ U.1 y hyU (t U)) :=
      fun h ↦ ht ((Y.mem_basicOpen _ y hyU).mpr h)
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨U, (Y.mem_basicOpen _ y hyU).mpr ?_⟩
    rw [map_sub, map_one, map_mul]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      (fun h ↦ htu (isUnit_of_mul_isUnit_left h))
  let j := Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))
  let p := pullback.fst f j
  let q := pullback.snd f j
  have hj : IsOpenImmersion j := IsOpenImmersion.of_isLocalization
    (PowerSeries.X : PowerSeries k)
  have hp : IsOpenImmersion p := MorphismProperty.pullback_fst _ _ inferInstance
  have hq : LocallyOfFinitePresentation q := MorphismProperty.pullback_snd _ _ inferInstance
  have htgen (z : ↥(pullback f j)) (U : Y.affineOpens) (hzU : p z ∈ U.1) :
      p z ∈ Y.basicOpen (t U) := by
    rw [Scheme.basicOpen_appLE]
    refine ⟨hzU, ?_⟩
    rw [basicOpen_eq_of_affine]
    have hf : f (p z) = j (q z) :=
      congr($(pullback.condition (f := f) (g := j)) z)
    change f (p z) ∈ PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries k)
    rw [hf]
    change algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X ∉ (q z).asIdeal
    exact (q z).asIdeal.notMem_of_isUnit (IsLocalization.map_units (LaurentSeries k)
      (⟨PowerSeries.X, Submonoid.mem_powers _⟩ : Submonoid.powers
        (PowerSeries.X : PowerSeries k)))
  have hsmooth (z : ↥(pullback f j)) :
      ∃ U : Y.Opens, p z ∈ U ∧ Smooth (U.ι ≫ f) := by
    obtain ⟨U, hzG⟩ := TopologicalSpace.Opens.mem_iSup.mp (hG.ge (Set.mem_univ (p z)))
    have hzU : p z ∈ U.1 := Y.basicOpen_le _ hzG
    have hunit := (Y.mem_basicOpen _ (p z) hzU).mp (htgen z U hzU)
    have hgunit := (Y.mem_basicOpen _ (p z) hzU).mp hzG
    have hbunit : IsUnit (Y.presheaf.germ U.1 (p z) hzU (b U)) := by
      have heq : (1 - t U * a U) * t U ^ (n - 1) = b U := by
        have h := he U
        change t U ^ (n - 1) = b U + t U ^ n * a U at h
        rw [show t U ^ n = t U ^ (n - 1) * t U by
          rw [← pow_succ]; congr 1; omega] at h
        linear_combination h
      rw [← heq, map_mul, map_pow]
      exact hgunit.mul (hunit.pow _)
    have hoff : p z ∉ (Scheme.Modules.fittingIdealSheaf f.relativeDifferentials d).support := by
      intro h
      have hz := (Scheme.IdealSheafData.mem_support_iff_of_mem hzU).mp h
      exact (Y.mem_zeroLocus_iff _ _).mp hz (b U) (hb U)
        ((Y.mem_basicOpen _ _ hzU).mpr hbunit)
    obtain ⟨v, hv⟩ := ((Scheme.Modules.fitting_ideal_generate_locally Y
      f.relativeDifferentials d).2.2 (p z)).2.2.mp hoff
    apply (Scheme.Hom.smoothAtPoint_iff_flat_stalkMap_and_differentials_generators f
      (p z)).mpr
    exact ⟨Flat.stalkMap f _, d, v, (hdimall _).ge, hv⟩
  choose O hzO hO using hsmooth
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (fun z : ↥(pullback f j) ↦ p ⁻¹ᵁ O z) ?_ ?_
  · apply eq_top_iff.mpr
    intro z _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hzO z⟩
  · intro z
    have : Smooth ((p ⁻¹ᵁ O z).ι ≫ q ≫ j) := by
      rw [← pullback.condition]
      change Smooth ((p ⁻¹ᵁ O z).ι ≫ p ≫ f)
      rw [← morphismRestrict_ι_assoc]
      have : Smooth ((O z).ι ≫ f) := hO z
      infer_instance
    exact MorphismProperty.of_postcomp @Smooth
      (W' := MorphismProperty.monomorphisms Scheme) ((p ⁻¹ᵁ O z).ι ≫ q) j
        (show Mono j from inferInstance)
        (by simpa only [Category.assoc] using this)

end AlgebraicGeometry
