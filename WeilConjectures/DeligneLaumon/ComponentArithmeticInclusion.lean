/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedGenericWeilData
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ArithmeticLiftFibrePath
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! # The canonical arithmetic inclusion of a geometric component

Source: Weil II (1.1.10), and the homotopy exact sequence over the finite constant field.
(blueprint: lem-dl-a1-component-arithmetic-exactness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FiniteEtale
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.ProEtale.CondensedGenericWeil

/-- Finite étale covers of the geometric base embed in arithmetic pullbacks.
This is finite-field descent followed by the monomorphism into the larger fibre product. -/
private theorem geometric_covers_embed (D : WeilConjectures.FiniteFieldDatum.{u})
    (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom] (Q : (D.geometricFiber U₀).left.FiniteEtale) :
    ∃ (R : U₀.left.FiniteEtale)
      (φ : Q ⟶ (FiniteEtale.pullback (projection D U₀)).obj R), Mono φ.hom.left := by
  classical
  obtain ⟨E, hE, Q_E, ⟨e⟩⟩ := (FiniteEtale.finiteEtale_fieldLimit_descent
    (L := D.k) U₀).1 Q
  let := hE
  let R := FiniteEtale.arithmeticModelCover U₀ E Q_E
  let f := FiniteEtale.fieldExtensionBaseMap U₀ E.val
  let p := projection D U₀
  let φ : (FiniteEtale.pullback f).obj Q_E ⟶ (FiniteEtale.pullback p).obj R :=
    ObjectProperty.homMk (MorphismProperty.Over.homMk
      (pullback.lift (pullback.fst Q_E.obj.hom f) (pullback.snd Q_E.obj.hom f) (by
        change pullback.fst Q_E.obj.hom f ≫
            (Q_E.obj.hom ≫ FiniteEtale.arithmeticBaseProjection (L := E) U₀) =
          pullback.snd Q_E.obj.hom f ≫ p
        rw [← Category.assoc, pullback.condition, Category.assoc]
        congr 1
        simp [f, p, projection, FiniteEtale.fieldExtensionBaseMap,
          FiniteEtale.arithmeticBaseProjection]))
      (pullback.lift_snd _ _ _))
  have hφ : Mono φ.hom.left := ⟨by
    intro T a b hab
    apply pullback.hom_ext
    · have h := congrArg (fun z ↦ z ≫ pullback.fst R.obj.hom p) hab
      dsimp only [φ, ObjectProperty.homMk, MorphismProperty.Over.homMk,
        CategoryTheory.Over.homMk, CostructuredArrow.homMk] at h
      simpa only [Category.assoc, pullback.lift_fst] using h
    · have h := congrArg (fun z ↦ z ≫ pullback.snd R.obj.hom p) hab
      dsimp only [φ, ObjectProperty.homMk, MorphismProperty.Over.homMk,
        CategoryTheory.Over.homMk, CostructuredArrow.homMk] at h
      simpa only [Category.assoc, pullback.lift_snd] using h⟩
  refine ⟨R, e.inv ≫ φ, ?_⟩
  change Mono (e.inv.hom.left ≫ φ.hom.left)
  infer_instance

private theorem integral_closed_range {L Ω : Type u} [Field L] [IsAlgClosed L]
    [Field Ω] [Algebra L Ω] {z : Ω} (hz : _root_.IsIntegral L z) :
    ∃ a : L, algebraMap L Ω a = z := by
  refine ⟨-(minpoly L z).coeff 0, ?_⟩
  have hq : (minpoly L z).leadingCoeff = 1 := minpoly.monic hz
  have h : (minpoly L z).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible hz)
  have he : Polynomial.aeval z (minpoly L z) = 0 := minpoly.aeval L z
  rw [Polynomial.eq_X_add_C_of_degree_eq_one h, hq, Polynomial.C_1, one_mul,
    Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C,
    add_eq_zero_iff_eq_neg] at he
  exact (map_neg (algebraMap L Ω) ((minpoly L z).coeff 0)).symm ▸ he.symm

private theorem finite_algebra_factor {K L Ω A : Type u}
    [Field K] [Field L] [IsAlgClosed L] [Field Ω] [CommRing A]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [Algebra K A] [Module.Finite K A] (f : A →ₐ[K] Ω) :
    ∃ τ : A →ₐ[K] L, (IsScalarTower.toAlgHom K L Ω).comp τ = f := by
  let i := IsScalarTower.toAlgHom K L Ω
  have hi : Function.Injective i := (algebraMap L Ω).injective
  have hf : ∀ a, f a ∈ i.range := by
    intro a
    obtain ⟨b, hb⟩ := integral_closed_range (L := L)
      (((Algebra.IsIntegral.isIntegral (R := K) a).map f).tower_top (A := L))
    exact ⟨b, hb⟩
  let τ := (AlgEquiv.ofInjective i hi).symm.toAlgHom.comp (f.codRestrict i.range hf)
  refine ⟨τ, ?_⟩
  ext a
  exact congrArg Subtype.val ((AlgEquiv.ofInjective i hi).apply_symm_apply
    (f.codRestrict i.range hf a))

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [ConnectedSpace U₀.left]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (t : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left)
  (G : ProfiniteGrp.{u})
  [∀ Q, MulAction G ((FiniteEtale.fiber (t ≫ projection D U₀)).obj Q)]
  [PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber (t ≫ projection D U₀)) G]
  (C : RealCondensedFibre.Context.{u})
  (j : C.X ⟶ (D.geometricFiber U₀).left) (x : Spec (.of Ω) ⟶ C.X)
  (hx : x ≫ j = t) (P : ProfiniteGrp.{u})
  [∀ Q, MulAction P ((FiniteEtale.fiber x).obj Q)]
  [PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber x) P]

/-- Pullback of finite arithmetic covers, with the basepoint fixed by hx.
Source: Weil II (1.1.10), finite-cover normalization
(blueprint: lem-dl-a1-component-arithmetic-exactness). -/
def componentArithmeticInclusion : P →* G :=
  FiniteEtale.fundamentalGroupMap
    (FiniteEtale.pullbackFiberIso (j ≫ projection D U₀) x ≪≫
      eqToIso (congrArg FiniteEtale.fiber
        ((Category.assoc x j (projection D U₀)).symm.trans
          (congrArg (fun z ↦ z ≫ projection D U₀) hx)))) P G

omit [ConnectedSpace U₀.left] in
/-- Covers of a clopen geometric component embed in arithmetic pullbacks. -/
private theorem component_covers_embed [IsSeparated U₀.hom]
    (hj : IsOpenImmersion j) (hclosed : IsClosed (Set.range j))
    (Q : C.X.FiniteEtale) :
    ∃ (R : U₀.left.FiniteEtale)
      (φ : Q ⟶ (FiniteEtale.pullback (j ≫ projection D U₀)).obj R),
      Mono φ.hom.left := by
  let := hj
  have : IsClosedImmersion j := IsClosedImmersion.of_isPreimmersion j hclosed
  have : Etale Q.obj.hom := Q.obj.prop
  have : IsFinite Q.obj.hom := Q.property
  let B : (D.geometricFiber U₀).left.FiniteEtale :=
    ⟨MorphismProperty.Over.mk ⊤ (Q.obj.hom ≫ j) inferInstance,
      inferInstanceAs (IsFinite (Q.obj.hom ≫ j))⟩
  obtain ⟨R, φ, hφ⟩ := geometric_covers_embed D U₀ B
  let r := projection D U₀
  let l := φ.hom.left ≫ pullback.fst R.obj.hom r
  have hw : l ≫ R.obj.hom = Q.obj.hom ≫ (j ≫ r) := by
    have h := FiniteEtale.hom_left_comp φ
    change φ.hom.left ≫ pullback.snd R.obj.hom r = Q.obj.hom ≫ j at h
    dsimp only [l]
    rw [Category.assoc, pullback.condition, ← Category.assoc, h, Category.assoc]
  let ψ : Q ⟶ (FiniteEtale.pullback (j ≫ r)).obj R :=
    ObjectProperty.homMk (MorphismProperty.Over.homMk
      (pullback.lift l Q.obj.hom hw) (pullback.lift_snd _ _ _))
  refine ⟨R, ψ, ⟨?_⟩⟩
  intro T a b hab
  apply (cancel_mono φ.hom.left).mp
  apply pullback.hom_ext
  · have h := congrArg (fun z ↦ z ≫ pullback.fst R.obj.hom (j ≫ r)) hab
    dsimp only [ψ, ObjectProperty.homMk, MorphismProperty.Over.homMk,
      CategoryTheory.Over.homMk, CostructuredArrow.homMk] at h
    simpa only [Category.assoc, pullback.lift_fst] using h
  · have h := congrArg (fun z ↦ z ≫ pullback.snd R.obj.hom (j ≫ r)) hab
    change a ≫ pullback.lift l Q.obj.hom hw ≫ _ =
      b ≫ pullback.lift l Q.obj.hom hw ≫ _ at h
    simp only [pullback.lift_snd] at h
    have h' := congrArg (fun z ↦ z ≫ j) h
    have hwφ := FiniteEtale.hom_left_comp φ
    change φ.hom.left ≫ pullback.snd R.obj.hom r = Q.obj.hom ≫ j at hwφ
    change a ≫ (φ.hom.left ≫ pullback.snd R.obj.hom r) =
      b ≫ (φ.hom.left ≫ pullback.snd R.obj.hom r)
    rw [hwφ]
    exact h'

/-- Injectivity of the concrete arithmetic map follows already from finite cover descent.
Source: Stacks Project, Tags 0BTV and 0BTX, finite-model argument.
(blueprint: lem-dl-a1-component-arithmetic-exactness). -/
theorem componentArithmeticInclusion_injective [IsSeparated U₀.hom]
    (hj : IsOpenImmersion j)
    (himage : Set.range j = connectedComponent (t (IsLocalRing.closedPoint Ω))) :
    Function.Injective (componentArithmeticInclusion D U₀ t G C j x hx P) := by
  refine (injective_iff_map_eq_one _).2 fun a ha ↦ ?_
  apply PreGaloisCategory.IsFundamentalGroup.non_trivial (F := FiniteEtale.fiber x) a
  intro Q y
  have hclosed : IsClosed (Set.range j) := by
    rw [himage]
    exact isClosed_connectedComponent
  obtain ⟨R, φ, hφ⟩ := component_covers_embed D U₀ C j hj hclosed Q
  have htriv (z : (FiniteEtale.fiber x).obj
      ((FiniteEtale.pullback (j ≫ projection D U₀)).obj R)) : a • z = z := by
    have h := FiniteEtale.fundamentalGroupMap_smul
      (FiniteEtale.pullbackFiberIso (j ≫ projection D U₀) x ≪≫
        eqToIso (congrArg FiniteEtale.fiber
          ((Category.assoc x j (projection D U₀)).symm.trans
            (congrArg (fun z ↦ z ≫ projection D U₀) hx)))) P G a R z
    change componentArithmeticInclusion D U₀ t G C j x hx P a • _ = _ at h
    rw [ha, one_smul] at h
    exact ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1 h.symm
  have hinj : Function.Injective ((FiniteEtale.fiber x).map φ) := by
    intro z w h
    apply FiniteEtale.fiber_ext x
    apply hφ.right_cancellation
    exact congrArg (fun z ↦ z.left) h
  apply hinj
  rw [PreGaloisCategory.IsNaturalSMul.naturality, htriv]

/-- The map is continuous in the existing profinite topologies.
Source: functoriality of finite-etale fundamental groups
(blueprint: lem-dl-a1-component-arithmetic-exactness). -/
theorem componentArithmeticInclusion_continuous :
    Continuous (componentArithmeticInclusion D U₀ t G C j x hx P) := by
  have : ∀ Q, ContinuousSMul P ((FiniteEtale.fiber x).obj Q) :=
    fun Q ↦ PreGaloisCategory.IsFundamentalGroup.continuous_smul Q
  exact FiniteEtale.continuous_fundamentalGroupMap _ P G

/-- On finite covers this is exactly conjugated geometric pullback transport.
Source: Weil II (1.1.10), finite-cover normalization
(blueprint: lem-dl-a1-component-arithmetic-exactness). -/
theorem componentArithmeticInclusion_normalized (a : P) :
    PreGaloisCategory.toAut (FiniteEtale.fiber (t ≫ projection D U₀)) G
        (componentArithmeticInclusion D U₀ t G C j x hx P a) =
      (eqToIso (congrArg FiniteEtale.fiber
        ((Category.assoc x j (projection D U₀)).symm.trans
          (congrArg (fun z ↦ z ≫ projection D U₀) hx)))).symm ≪≫
        FiniteEtale.pullbackPathIso (j ≫ projection D U₀)
          (PreGaloisCategory.toAut (FiniteEtale.fiber x) P a) ≪≫
        eqToIso (congrArg FiniteEtale.fiber
          ((Category.assoc x j (projection D U₀)).symm.trans
            (congrArg (fun z ↦ z ≫ projection D U₀) hx))) := by
  unfold componentArithmeticInclusion FiniteEtale.fundamentalGroupMap
  change (PreGaloisCategory.toAutMulEquiv _ G)
    ((PreGaloisCategory.toAutMulEquiv _ G).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  ext Q z
  rfl

private def componentConstantSection (A : FiniteEtaleAlgebra D.k₀)
    (τ : A.1 →ₐ[D.k₀] D.k) :
    C.X ⟶ ((FiniteEtale.pullback (j ≫ projection D U₀)).obj
      (FiniteEtale.constantCover U₀.hom A)).obj.left := by
  let p := j ≫ projection D U₀
  let ℓ := j ≫ pullback.snd U₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  have hw : p ≫ U₀.hom =
      (ℓ ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)) ≫ A.specHom := by
    change p ≫ U₀.hom = ℓ ≫
      (Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap D.k₀ A.1)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hτ : τ.toRingHom.comp (algebraMap D.k₀ A.1) = algebraMap D.k₀ D.k := by
      ext a
      exact τ.commutes a
    rw [hτ]
    dsimp only [p, ℓ, projection]
    rw [Category.assoc, pullback.condition, Category.assoc]
  exact pullback.lift (pullback.lift p
    (ℓ ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)) hw) (𝟙 _) (by simp [p])

omit [ConnectedSpace U₀.left] in
private theorem componentConstantSection_snd (A : FiniteEtaleAlgebra D.k₀)
    (τ : A.1 →ₐ[D.k₀] D.k) :
    componentConstantSection D U₀ C j A τ ≫
      ((FiniteEtale.pullback (j ≫ projection D U₀)).obj
        (FiniteEtale.constantCover U₀.hom A)).obj.hom = 𝟙 _ := by
  unfold componentConstantSection
  exact pullback.lift_snd _ _ _

omit [ConnectedSpace U₀.left] in
private theorem componentConstantSection_label (A : FiniteEtaleAlgebra D.k₀)
    (τ : A.1 →ₐ[D.k₀] D.k) :
    componentConstantSection D U₀ C j A τ ≫
      pullback.fst (FiniteEtale.constantCover U₀.hom A).obj.hom (j ≫ projection D U₀) ≫
        pullback.snd U₀.hom A.specHom =
      (j ≫ pullback.snd U₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ≫
          Spec.map (CommRingCat.ofHom τ.toRingHom) := by
  unfold componentConstantSection
  simp only [pullback.lift_fst_assoc, pullback.lift_snd]

omit [ConnectedSpace U₀.left] in
private theorem component_constant_point_section (A : FiniteEtaleAlgebra D.k₀)
    (z : (fiber x).obj ((FiniteEtale.pullback (j ≫ projection D U₀)).obj
      (constantCover U₀.hom A))) :
    ∃ τ : A.1 →ₐ[D.k₀] D.k,
      z.left = x ≫ componentConstantSection D U₀ C j A τ := by
  let ℓ := j ≫ pullback.snd U₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  let α : D.k →+* Ω := (Spec.preimage (x ≫ ℓ)).hom
  let : Algebra D.k Ω := α.toAlgebra
  let : Algebra D.k₀ Ω := (α.comp (algebraMap D.k₀ D.k)).toAlgebra
  let : IsScalarTower D.k₀ D.k Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let p := j ≫ projection D U₀
  let z₀ := (pullbackFiberIso p x).hom.app (constantCover U₀.hom A) z
  have hb : baseRingHom U₀.hom (x ≫ p) = algebraMap D.k₀ Ω := by
    suffices h : CommRingCat.ofHom (baseRingHom U₀.hom (x ≫ p)) =
        CommRingCat.ofHom (algebraMap D.k₀ Ω) from congrArg CommRingCat.Hom.hom h
    apply Spec.map_injective
    rw [spec_map_baseRingHom]
    change (x ≫ p) ≫ U₀.hom =
      Spec.map (CommRingCat.ofHom (α.comp (algebraMap D.k₀ D.k)))
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    change (x ≫ p) ≫ U₀.hom =
      Spec.map (Spec.preimage (x ≫ ℓ)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
    rw [Spec.map_preimage]
    dsimp only [p, ℓ, projection]
    simp only [Category.assoc, pullback.condition]
  let f : A.1 →ₐ[D.k₀] Ω :=
    { (fiberConstantCoverEquiv U₀.hom (x ≫ p) A z₀).val with
      commutes' a := DFunLike.congr_fun
        ((fiberConstantCoverEquiv U₀.hom (x ≫ p) A z₀).property.trans hb) a }
  obtain ⟨τ, hτ⟩ := finite_algebra_factor (L := D.k) f
  refine ⟨τ, ?_⟩
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [componentConstantSection, Category.assoc, pullback.lift_fst]
      change z.left ≫
        (pullback.fst (constantCover U₀.hom A).obj.hom p ≫
          (constantCover U₀.hom A).obj.hom) = x ≫ p
      rw [pullback.condition, ← Category.assoc]
      exact congrArg (fun a ↦ a ≫ p) (fiber_left_comp x z)
    · have hh :
          (fiberConstantCoverEquiv U₀.hom (x ≫ p) A z₀).val =
            α.comp τ.toRingHom := congrArg AlgHom.toRingHom hτ.symm
      rw [fiberConstantCoverEquiv_apply] at hh
      have hm := congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) hh
      change Spec.map (Spec.preimage (z₀.left ≫ pullback.snd U₀.hom A.specHom)) =
        Spec.map (CommRingCat.ofHom (α.comp τ.toRingHom)) at hm
      rw [Spec.map_preimage, CommRingCat.ofHom_comp, Spec.map_comp] at hm
      dsimp only [z₀] at hm
      rw [pullbackFiberIso_hom_app_left] at hm
      have hl := componentConstantSection_label D U₀ C j A τ
      change componentConstantSection D U₀ C j A τ ≫
        pullback.fst (constantCover U₀.hom A).obj.hom p ≫
          pullback.snd U₀.hom A.specHom = ℓ ≫ _ at hl
      change _ = x ≫ (componentConstantSection D U₀ C j A τ ≫
        pullback.fst (constantCover U₀.hom A).obj.hom p ≫
          pullback.snd U₀.hom A.specHom)
      rw [hl]
      change _ = Spec.map (Spec.preimage (x ≫ ℓ)) ≫ _ at hm
      rw [Spec.map_preimage] at hm
      simpa only [Category.assoc] using hm
  · have hs := componentConstantSection_snd D U₀ C j A τ
    change componentConstantSection D U₀ C j A τ ≫
      pullback.snd (constantCover U₀.hom A).obj.hom p = 𝟙 _ at hs
    change z.left ≫ pullback.snd (constantCover U₀.hom A).obj.hom p =
      x ≫ (componentConstantSection D U₀ C j A τ ≫
        pullback.snd (constantCover U₀.hom A).obj.hom p)
    rw [hs, Category.comp_id]
    exact fiber_left_comp x z

private theorem componentArithmeticInclusion_constant (a : P)
    (A : FiniteEtaleAlgebra D.k₀)
    (z : (fiber (t ≫ projection D U₀)).obj (constantCover U₀.hom A)) :
    componentArithmeticInclusion D U₀ t G C j x hx P a • z = z := by
  let e := pullbackFiberIso (j ≫ projection D U₀) x ≪≫
    eqToIso (congrArg fiber
      ((Category.assoc x j (projection D U₀)).symm.trans
        (congrArg (fun z ↦ z ≫ projection D U₀) hx)))
  let z' : (fiber x).obj ((FiniteEtale.pullback (j ≫ projection D U₀)).obj
      (constantCover U₀.hom A)) := e.inv.app (constantCover U₀.hom A) z
  obtain ⟨τ, hτ⟩ := component_constant_point_section D U₀ C j x A z'
  have hfix : a • z' = z' := by
    apply fiber_ext x
    rw [← PreGaloisCategory.toAut_hom_app_apply]
    exact (path_section (PreGaloisCategory.toAut (fiber x) P a) _
      (componentConstantSection D U₀ C j A τ)
      (componentConstantSection_snd D U₀ C j A τ) z' hτ).trans hτ.symm
  have hz : e.hom.app (constantCover U₀.hom A) z' = z :=
    ConcreteCategory.congr_hom (e.inv_hom_id_app _) z
  have h := fundamentalGroupMap_smul e P G a (constantCover U₀.hom A) z'
  change componentArithmeticInclusion D U₀ t G C j x hx P a • _ = _ at h
  rw [hz, hfix, hz] at h
  exact h

/-- Geometric pullback transport fixes every point of every arithmetic constant cover.
Source: Stacks Project, Tag 0BTX, and Weil II (1.1.10).
(blueprint: lem-dl-a1-component-arithmetic-exactness).

Proof: each finite constant-cover fibre point factors through the algebraically closed
constant field. It thus lies on a section over the component. Naturality fixes such a
section point, and the canonical fibre comparison transports this equality to G. -/
theorem componentArithmeticInclusion_range_le :
    (componentArithmeticInclusion D U₀ t G C j x hx P).range ≤
      (constantCoverAction U₀.hom (t ≫ projection D U₀) G).ker := by
  rintro _ ⟨a, rfl⟩
  change constantCoverAction U₀.hom (t ≫ projection D U₀) G
    (componentArithmeticInclusion D U₀ t G C j x hx P a) = 1
  funext A
  apply Equiv.ext
  intro z
  exact componentArithmeticInclusion_constant D U₀ t G C j x hx P a A z


/-- Every element acting trivially on constant covers comes from the geometric component.
Only the profinite arithmetic inclusion is asserted here, not any Weil representation.

Source: Weil II (1.1.10), generic-fibre proof step 3; homotopy exact sequence over
its finite constant field.
(blueprint: lem-dl-a1-component-arithmetic-exactness).

Proof: normality and connectedness make U0 integral. Apply the normal constant-field
component theorem to its algebraic constant field L. The component selected by t is the
geometric base change of U0 over L. Its canonical map to the specified C is the unique
isomorphism over the geometric fibre, since both are open immersions with the same image.
The arithmetic exact sequence for U0 over L identifies its geometric fundamental group
with the kernel of the action on finite L-constant covers. Transport this sequence along
the component isomorphism and the given geometric point. On finite constant covers the
map to Gal(k/k0) is the composite of the map to Gal(k/L) and its injective restriction
inclusion: both send an embedding to its composite with the same field automorphism.
Thus their kernels agree. The finite-cover fibre comparison is exactly the one in
componentArithmeticInclusion, by pullback functoriality and the equality hx. Fundamental
groups are identified by their actions on every finite cover, so the transported map is
this actual map, proving the claimed range equation. Injectivity has already been proved
independently by embedding geometric finite covers in arithmetic pullbacks. -/
theorem component_arithmetic_kernel_le [IsSeparated U₀.hom]
    (hj : IsOpenImmersion j)
    (himage : Set.range j = connectedComponent (t (IsLocalRing.closedPoint Ω)))
    (hNormal : ∀ z : U₀.left, IsDomain (U₀.left.presheaf.stalk z) ∧
      IsIntegrallyClosed (U₀.left.presheaf.stalk z))
    (hGeneric : ∃ Z ∈ irreducibleComponents (D.geometricFiber U₀).left,
      IsGenericPoint (t (IsLocalRing.closedPoint Ω)) Z) :
    (FiniteEtale.constantCoverAction U₀.hom (t ≫ projection D U₀) G).ker ≤
      (componentArithmeticInclusion D U₀ t G C j x hx P).range := by
  sorry

/-- The two inclusions identify the concrete image with the constant-cover kernel.
Source: Weil II (1.1.10), generic-fibre proof step 3.
(blueprint: lem-dl-a1-component-arithmetic-exactness).

Proof: the section argument gives one inclusion. The exact-sequence argument over the
finite constant field gives the reverse inclusion. -/
theorem component_arithmetic_range [IsSeparated U₀.hom]
    (hj : IsOpenImmersion j)
    (himage : Set.range j = connectedComponent (t (IsLocalRing.closedPoint Ω)))
    (hNormal : ∀ z : U₀.left, IsDomain (U₀.left.presheaf.stalk z) ∧
      IsIntegrallyClosed (U₀.left.presheaf.stalk z))
    (hGeneric : ∃ Z ∈ irreducibleComponents (D.geometricFiber U₀).left,
      IsGenericPoint (t (IsLocalRing.closedPoint Ω)) Z) :
    (componentArithmeticInclusion D U₀ t G C j x hx P).range =
      (FiniteEtale.constantCoverAction U₀.hom (t ≫ projection D U₀) G).ker := by
  exact le_antisymm (componentArithmeticInclusion_range_le D U₀ t G C j x hx P)
    (component_arithmetic_kernel_le D U₀ t G C j x hx P hj himage hNormal hGeneric)

/-- The proved injection together with the image calculation gives arithmetic exactness.
Source: Weil II (1.1.10), generic-fibre proof step 3.
(blueprint: lem-dl-a1-component-arithmetic-exactness).

Proof: combine injectivity from finite-model embeddings with the constant-field image
calculation. Both statements use the same pullback-induced homomorphism. -/
theorem component_arithmetic_exactness [IsSeparated U₀.hom]
    (hj : IsOpenImmersion j)
    (himage : Set.range j = connectedComponent (t (IsLocalRing.closedPoint Ω)))
    (hNormal : ∀ z : U₀.left, IsDomain (U₀.left.presheaf.stalk z) ∧
      IsIntegrallyClosed (U₀.left.presheaf.stalk z))
    (hGeneric : ∃ Z ∈ irreducibleComponents (D.geometricFiber U₀).left,
      IsGenericPoint (t (IsLocalRing.closedPoint Ω)) Z) :
    Function.Injective (componentArithmeticInclusion D U₀ t G C j x hx P) ∧
      (componentArithmeticInclusion D U₀ t G C j x hx P).range =
        (FiniteEtale.constantCoverAction U₀.hom (t ≫ projection D U₀) G).ker := by
  exact ⟨componentArithmeticInclusion_injective D U₀ t G C j x hx P hj himage,
    component_arithmetic_range D U₀ t G C j x hx P hj himage hNormal hGeneric⟩

end AlgebraicGeometry.ProEtale.CondensedGenericWeil
