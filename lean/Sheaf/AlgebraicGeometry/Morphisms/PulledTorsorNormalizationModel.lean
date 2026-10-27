/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q152
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Algebra.Pi

import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleTorsorSectionTrivialization
import Mathlib.AlgebraicGeometry.EffectiveEpi
import Mathlib.Algebra.Group.Shrink
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.Morphisms.FieldTorsorGaloisComponents
import WeilConjectures.RingTheory.EtaleNormalRing
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.Integral

/-! # The finite normalization of an actual pulled-back torsor

Source: ILO, Travaux de Gabber, IX Proposition 2.1(ii), pp.133-134;
Stacks Project, Tags 032L, 033C, 034M, 0307 and 01I4.
(blueprint: lem-sfb-pulled-torsor-normalization-model)

`A` and `A'` are presentations of the principal localizations of `R` and `B`;
`K` and `E` are their fraction fields. All algebra structures are required to commute.
`S` is an affine coordinate presentation of the given torsor, with its structure map.
The conclusion produces this presentation using finiteness of the torsor.

Tensor factors are written with the scalar-extension ring first: `A' ⊗[A] S`,
`E ⊗[A'] (A' ⊗[A] S)`, and `E ⊗[K] L j`. Thus their default algebra structures
are exactly the right-hand scalar structures in the usual opposite tensor order.
The pure-tensor formulas specify the comparisons, and the last equivalence expresses
literal equality of the images of `T` and `C[1/f]` inside the same generic product.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

/-- Transport the geometric action and its uniqueness clause through an actual pullback. -/
private theorem action_pullback
    {X Y Z : Scheme.{u}} (G : Type v) [Group G]
    (π : Z ⟶ X) (a : G → (Z ⟶ Z))
    (ha : ∀ g, a g ≫ π = π) (h1 : a 1 = 𝟙 Z)
    (hm : ∀ g h, a (g * h) = a h ≫ a g)
    (ht : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x y : Spec (.of Ω) ⟶ Z), x ≫ π = y ≫ π → ∃! g : G, x ≫ a g = y)
    (j : Y ⟶ X) :
    ∃ b : G → (pullback π j ⟶ pullback π j),
      (∀ g, b g ≫ pullback.fst π j = pullback.fst π j ≫ a g) ∧
      (∀ g, b g ≫ pullback.snd π j = pullback.snd π j) ∧
      b 1 = 𝟙 _ ∧ (∀ g h, b (g * h) = b h ≫ b g) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x y : Spec (.of Ω) ⟶ pullback π j),
        x ≫ pullback.snd π j = y ≫ pullback.snd π j → ∃! g : G, x ≫ b g = y) := by
  let b : G → (pullback π j ⟶ pullback π j) := fun g ↦
    pullback.lift (pullback.fst π j ≫ a g) (pullback.snd π j)
      (by simp [ha, pullback.condition])
  have hb₁ (g : G) : b g ≫ pullback.fst π j = pullback.fst π j ≫ a g := by
    simp [b]
  have hb₂ (g : G) : b g ≫ pullback.snd π j = pullback.snd π j := by simp [b]
  refine ⟨b, hb₁, hb₂, ?_, ?_, ?_⟩
  · apply pullback.hom_ext <;> simp [hb₁, hb₂, h1]
  · intro g h
    apply pullback.hom_ext
    · simp only [Category.assoc, hb₁, hm]
      rw [← Category.assoc (b h), hb₁, Category.assoc]
    · simp [hb₂]
  · intro Ω _ _ x y hxy
    obtain ⟨g, hg, hu⟩ := ht Ω (x ≫ pullback.fst π j) (y ≫ pullback.fst π j)
      (by rw [Category.assoc, pullback.condition, ← Category.assoc, hxy,
        Category.assoc, ← pullback.condition, ← Category.assoc])
    refine ⟨g, ?_, ?_⟩
    · apply pullback.hom_ext
      · simpa only [Category.assoc, hb₁] using hg
      · simpa only [Category.assoc, hb₂] using hxy
    · intro h hh
      apply hu
      simpa only [Category.assoc, hb₁] using congrArg (fun k ↦ k ≫ pullback.fst π j) hh

/-- The diagonal section identifies the self-pullback with the coproduct of translates. -/
private theorem action_comparison
    {X Z : Scheme.{u}} (G : Type v) [Group G] [Finite G]
    (π : Z ⟶ X) [IsFinite π] [Etale π]
    (a : G → (Z ⟶ Z))
    (ha : ∀ g, a g ≫ π = π) (h1 : a 1 = 𝟙 Z)
    (hm : ∀ g h, a (g * h) = a h ≫ a g)
    (ht : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x y : Spec (.of Ω) ⟶ Z), x ≫ π = y ≫ π → ∃! g : G, x ≫ a g = y) :
    IsIso (Sigma.desc fun g : G ↦
      pullback.lift (f := π) (g := π) (a g) (𝟙 Z) (by simp [ha])) := by
  obtain ⟨b, hb₁, hb₂, hb1, hbm, hbt⟩ := action_pullback G π a ha h1 hm ht π
  obtain ⟨Q, e, hQ, he, hei, hdisj, hcov, θ, hθ, hθπ, rest⟩ :=
    finite_etale_torsor_section_trivialization G (pullback.snd π π) b hb₂ hb1 hbm hbt
      (pullback.diagonal π) (by simp)
  have heq : θ.hom = Sigma.desc (fun g : G ↦
      pullback.lift (f := π) (g := π) (a g) (𝟙 Z) (by simp [ha])) := by
    rw [hθ]
    apply Sigma.hom_ext
    intro g
    simp only [Sigma.ι_desc]
    apply pullback.hom_ext <;> simp [hb₁, hb₂]
  rw [← heq]
  infer_instance

/-- Affine faithfully flat descent supplies the invariant-map quotient property. -/
private theorem action_quotient
    {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z]
    (G : Type v) [Group G] [Finite G]
    (π : Z ⟶ X) [IsFinite π] [Etale π] [Surjective π]
    (a : G → (Z ⟶ Z))
    (ha : ∀ g, a g ≫ π = π) (h1 : a 1 = 𝟙 Z)
    (hm : ∀ g h, a (g * h) = a h ≫ a g)
    (ht : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x y : Spec (.of Ω) ⟶ Z), x ≫ π = y ≫ π → ∃! g : G, x ≫ a g = y)
    (T : Scheme.{u}) (k : Z ⟶ T) (hk : ∀ g, a g ≫ k = k) :
    ∃! q : X ⟶ T, π ≫ q = k := by
  let d := Sigma.desc fun g : G ↦
    pullback.lift (f := π) (g := π) (a g) (𝟙 Z) (by simp [ha])
  have : IsIso d := action_comparison G π a ha h1 hm ht
  have : IsRegularEpi π := isRegularEpi_of_flat_of_surjective_of_isAffine π
  have h : pullback.fst π π ≫ k = pullback.snd π π ≫ k := by
    rw [← cancel_epi d]
    apply Sigma.hom_ext
    intro g
    simp only [d, colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt,
      Cofan.mk_ι_app, limit.lift_π_assoc, PullbackCone.mk_π_app, cospan_left, cospan_right,
      hk]
    exact (Category.id_comp k).symm
  obtain ⟨q, hq⟩ := IsRegularEpi.exists_of_isKernelPair π (.of_hasPullback π) k h
  exact ⟨q, hq, fun r hr ↦ (cancel_epi π).mp (hr.trans hq.symm)⟩

/-- Build the pulled torsor without changing the given action convention. -/
private theorem action_base_change
    {X Y : Scheme.{u}} [IsAffine Y] (G : Type v) [Group G] [Finite G]
    (P : GaloisCoverAction G X) (j : Y ⟶ X) :
    ∃ (W : GaloisCoverAction G Y) (ι : W.Z ≅ pullback P.π j),
      ι.hom ≫ pullback.snd P.π j = W.π ∧
      ∀ g, W.smul g ≫ ι.hom ≫ pullback.fst P.π j =
        ι.hom ≫ pullback.fst P.π j ≫ P.smul g := by
  have : IsFinite P.π := P.isFinite
  have : Etale P.π := P.etale
  have : Surjective P.π := P.surjective
  obtain ⟨b, hb₁, hb₂, hb1, hbm, hbt⟩ :=
    action_pullback G P.π P.smul P.smul_π P.one_smul P.mul_smul P.simply_transitive j
  have : IsAffine (pullback P.π j) := isAffine_of_isAffineHom (pullback.snd P.π j)
  let W : GaloisCoverAction G Y :=
    { Z := pullback P.π j
      π := pullback.snd P.π j
      isFinite := inferInstance
      etale := inferInstance
      surjective := inferInstance
      smul := b
      smul_π := hb₂
      one_smul := hb1
      mul_smul := hbm
      simply_transitive := hbt
      quotient := action_quotient G (pullback.snd P.π j) b hb₂ hb1 hbm hbt }
  exact ⟨W, Iso.refl _, Category.id_comp _, fun g ↦ by simpa [W] using hb₁ g⟩

/-- The generic algebra is the total fraction ring of a finite etale normal algebra. -/
private theorem finite_etale_generic_normal
    (A E T : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field E] [Algebra A E] [IsFractionRing A E]
    [CommRing T] [Algebra A T] [Module.Finite A T] [Algebra.Etale A T] :
    Function.Injective
      (Algebra.TensorProduct.includeRight : T →ₐ[A] E ⊗[A] T) ∧
    @IsLocalization T _ (nonZeroDivisors T) (E ⊗[A] T) _
      Algebra.TensorProduct.rightAlgebra ∧
    (∀ (p : Ideal T) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ∧
    @IsIntegrallyClosedIn T (E ⊗[A] T) _ _ Algebra.TensorProduct.rightAlgebra := by
  let D := E ⊗[A] T
  let : Algebra T D := Algebra.TensorProduct.rightAlgebra
  let M := Algebra.algebraMapSubmonoid T (nonZeroDivisors A)
  have : IsLocalization M D := inferInstance
  have hM : M ≤ nonZeroDivisors T := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    apply (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := T) ha)
    simpa only [Algebra.smul_def, mul_zero, zero_mul, mul_comm] using hx
  have hinj : Function.Injective (algebraMap T D) := IsLocalization.injective D hM
  have : Module.Finite E D := inferInstance
  have : IsArtinianRing D := isArtinian_of_tower E inferInstance
  have hfrac : IsFractionRing T D := IsLocalization.of_le M (nonZeroDivisors T) hM
    (fun t ht ↦ IsArtinianRing.isUnit_of_mem_nonZeroDivisors
      (IsLocalization.nonZeroDivisors_le_comap M D ht))
  have hn : ∀ (p : Ideal T) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) :=
    (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale A T)).isNormalRing (fun p _ ↦
      ⟨inferInstance, isIntegrallyClosed_of_isLocalization (Localization.AtPrime p) p.primeCompl
        p.primeCompl_le_nonZeroDivisors⟩)
  have hc : IsIntegrallyClosedIn T (FractionRing T) :=
    isIntegrallyClosedIn_iff.mpr ⟨IsFractionRing.injective T _,
      fun hx ↦ integral_totalFraction_mem_range_of_normal T hn _ hx⟩
  have : IsIntegrallyClosed T :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn (FractionRing T)).mpr hc
  exact ⟨hinj, hfrac, hn, (isIntegrallyClosed_iff_isIntegrallyClosedIn D).mp inferInstance⟩

/-- A finite tuple of integral coordinates is killed by the product of their monic equations. -/
private theorem integral_pi
    (B : Type u) [CommRing B] {n : ℕ} (F : Fin n → Type u)
    [∀ a, CommRing (F a)] [∀ a, Algebra B (F a)]
    (x : ∀ a, F a) (hx : ∀ a, _root_.IsIntegral B (x a)) : _root_.IsIntegral B x := by
  classical
  choose p hp hz using hx
  refine ⟨∏ a, p a, Polynomial.monic_prod_of_monic _ _ (fun a _ ↦ hp a), ?_⟩
  change Polynomial.aeval x (∏ a, p a) = 0
  ext a
  rw [Polynomial.aeval_pi_apply₂, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ a) (by simpa [Polynomial.aeval_def] using hz a)

/-- Clear one denominator in the entire tuple, and use normality for the converse. -/
private theorem normalization_image
    (B A E T : Type u) [CommRing B] [CommRing A] [Field E] [CommRing T]
    [Algebra B A] (b : B) [IsLocalization.Away b A]
    [Algebra B E] [Algebra A E] [IsScalarTower B A E]
    [Algebra A T] [Module.Finite A T]
    (n : ℕ) (F : Fin n → Type u) [∀ a, Field (F a)]
    [∀ a, Algebra E (F a)] [∀ a, Algebra B (F a)] [∀ a, IsScalarTower B E (F a)]
    (d : E ⊗[A] T ≃ₐ[E] (∀ a, F a))
    (hc : @IsIntegrallyClosedIn T (E ⊗[A] T) _ _ Algebra.TensorProduct.rightAlgebra) :
    ∀ x : ∀ a, F a,
      (∃ t : T, d (1 ⊗ₜ[A] t) = x) ↔
      ∃ (c : ∀ a, integralClosure B (F a)) (k : ℕ),
        ∀ a, x a * (algebraMap B (F a) b) ^ k = (c a : F a) := by
  let (a : Fin n) : Algebra A (F a) := Algebra.compHom (F a) (algebraMap A E)
  let (a : Fin n) : IsScalarTower A E (F a) := IsScalarTower.of_algebraMap_eq' rfl
  have (a : Fin n) : IsScalarTower B A (F a) :=
    IsScalarTower.of_algebraMap_eq (by
      intro z
      simp only [IsScalarTower.algebraMap_apply B E (F a),
        IsScalarTower.algebraMap_apply B A E]
      rfl)
  let D := E ⊗[A] T
  let : Algebra T D := Algebra.TensorProduct.rightAlgebra
  let i : T →ₐ[A] D := Algebra.TensorProduct.includeRight
  let da := d.restrictScalars A
  intro x
  constructor
  · rintro ⟨t, rfl⟩
    have ht : _root_.IsIntegral A (d (i t)) := (IsIntegral.of_finite (R := A) t).map
      (da.toAlgHom.comp i)
    obtain ⟨s, hs⟩ := ht.exists_multiple_integral_of_isLocalization (Submonoid.powers b) _
    obtain ⟨k, hk⟩ := s.property
    have h : _root_.IsIntegral B (fun a ↦ d (i t) a * algebraMap B (F a) b ^ k) := by
      have hh : s • d (i t) =
          (fun a ↦ d (i t) a * algebraMap B (F a) b ^ k) := by
        funext a
        simp only [Submonoid.smul_def, Algebra.smul_def, Pi.mul_apply,
          ← hk, map_pow, Pi.pow_apply, Pi.algebraMap_apply, mul_comm]
      rw [hh] at hs
      exact hs
    refine ⟨fun a ↦ ⟨_, h.map (Pi.evalAlgHom B F a)⟩, k, fun a ↦ rfl⟩
  · rintro ⟨c, k, hck⟩
    have h : _root_.IsIntegral B (x * algebraMap B (∀ a, F a) b ^ k) := by
      convert integral_pi B F (fun a ↦ (c a : F a)) (fun a ↦ (c a).property) using 1
      exact funext hck
    have hu := (IsLocalization.Away.algebraMap_isUnit (S := A) b).pow k
    obtain ⟨u, hu⟩ := hu
    have hu' : algebraMap A (∀ a, F a) (↑u⁻¹ : A) *
        algebraMap B (∀ a, F a) b ^ k = 1 := by
      rw [← map_pow, IsScalarTower.algebraMap_apply B A (∀ a, F a), map_pow, ← hu]
      rw [← map_mul, Units.inv_mul, map_one]
    have hx : _root_.IsIntegral A x := IsIntegral.of_mul_unit hu' h.tower_top
    obtain ⟨t, ht⟩ := (isIntegrallyClosedIn_iff.mp hc).2
      (hx.map da.symm.toAlgHom).tower_top
    refine ⟨t, ?_⟩
    change d (algebraMap T D t) = x
    rw [ht]
    exact d.apply_symm_apply x

/-- The image equality identifies the localized normalization with the etale algebra. -/
private theorem normalization_tensor
    (B A E T : Type u) [CommRing B] [CommRing A] [Field E] [CommRing T]
    [Algebra B A] (b : B) [IsLocalization.Away b A]
    [Algebra B E] [Algebra A E] [IsScalarTower B A E]
    [Algebra A T] [Module.Finite A T]
    (n : ℕ) (F : Fin n → Type u) [∀ a, Field (F a)]
    [∀ a, Algebra E (F a)] [∀ a, Algebra B (F a)] [∀ a, IsScalarTower B E (F a)]
    (d : E ⊗[A] T ≃ₐ[E] (∀ a, F a))
    (hi : Function.Injective (Algebra.TensorProduct.includeRight : T →ₐ[A] E ⊗[A] T))
    (hc : @IsIntegrallyClosedIn T (E ⊗[A] T) _ _ Algebra.TensorProduct.rightAlgebra) :
    Nonempty (A ⊗[B] (∀ a, integralClosure B (F a)) ≃ₐ[A] T) := by
  let (a : Fin n) : Algebra A (F a) := Algebra.compHom (F a) (algebraMap A E)
  let (a : Fin n) : IsScalarTower A E (F a) := IsScalarTower.of_algebraMap_eq' rfl
  have (a : Fin n) : IsScalarTower B A (F a) :=
    IsScalarTower.of_algebraMap_eq (by
      intro z
      simp only [IsScalarTower.algebraMap_apply B E (F a),
        IsScalarTower.algebraMap_apply B A E]
      rfl)
  let C := ∀ a, integralClosure B (F a)
  let Q := ∀ a, F a
  let cv : C →ₐ[B] Q := AlgHom.pi fun a ↦
    (integralClosure B (F a)).val.comp (Pi.evalAlgHom B _ a)
  have hcv : Function.Injective cv := by
    intro c c' h
    ext a
    exact congrFun h a
  let φ : A ⊗[B] C →ₐ[A] Q := Algebra.TensorProduct.lift (Algebra.ofId A Q) cv
    (fun x y ↦ Commute.all _ _)
  have hφc (c : C) : φ (1 ⊗ₜ[B] c) = cv c := by simp [φ]
  have hφi : Function.Injective φ := by
    let : Algebra C (A ⊗[B] C) := Algebra.TensorProduct.rightAlgebra
    have : IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers b))
        (A ⊗[B] C) := inferInstance
    apply IsLocalization.injective_of_map_algebraMap_zero
      (M := Algebra.algebraMapSubmonoid C (Submonoid.powers b)) (A ⊗[B] C) φ.toRingHom
    intro c hc
    change φ (1 ⊗ₜ[B] c) = 0 at hc
    rw [hφc] at hc
    have hcz := hcv (hc.trans cv.map_zero.symm)
    rw [hcz, map_zero]
  let t : T →ₐ[A] Q := (d.restrictScalars A).toAlgHom.comp
    (Algebra.TensorProduct.includeRight : T →ₐ[A] E ⊗[A] T)
  have hti : Function.Injective t := d.injective.comp hi
  have hφmem (y : A ⊗[B] C) : φ y ∈ t.range := by
    have hy : _root_.IsIntegral A (φ y) := by
      induction y using TensorProduct.induction_on with
      | zero => exact isIntegral_zero
      | tmul a c =>
        rw [Algebra.TensorProduct.lift_tmul]
        exact isIntegral_algebraMap.mul
          (integral_pi B F (cv c) (fun j ↦ (c j).property)).tower_top
      | add x y hx hy => simpa only [map_add] using hx.add hy
    let : Algebra T (E ⊗[A] T) := Algebra.TensorProduct.rightAlgebra
    obtain ⟨z, hz⟩ := (isIntegrallyClosedIn_iff.mp hc).2
      (hy.map (d.restrictScalars A).symm.toAlgHom).tower_top
    exact ⟨z, by change d (algebraMap T _ z) = φ y; rw [hz]; exact d.apply_symm_apply _⟩
  let ψ := φ.codRestrict t.range hφmem
  have hψ : Function.Bijective ψ := by
    refine ⟨fun x y h ↦ hφi (congrArg Subtype.val h), ?_⟩
    rintro ⟨x, z, rfl⟩
    obtain ⟨c, k, hck⟩ := (normalization_image B A E T b n F d hc (t z)).mp ⟨z, rfl⟩
    obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit (S := A) b).pow k
    refine ⟨(↑u⁻¹ : A) ⊗ₜ[B] c, Subtype.ext ?_⟩
    change φ ((↑u⁻¹ : A) ⊗ₜ[B] c) = t z
    rw [Algebra.TensorProduct.lift_tmul]
    have hck' : cv c = t z * algebraMap B Q b ^ k := (funext hck).symm
    change algebraMap A Q (↑u⁻¹ : A) * cv c = t z
    rw [hck', ← mul_assoc, mul_comm (algebraMap A Q _), mul_assoc]
    rw [← map_pow, IsScalarTower.algebraMap_apply B A Q, map_pow, ← hu,
      ← map_mul, Units.inv_mul, map_one, mul_one]
  exact ⟨(AlgEquiv.ofBijective ψ hψ).trans (AlgEquiv.ofInjective t hti).symm⟩

/-- A surjection from a finite product to a field factors through one coordinate. -/
private theorem product_field_quotient
    (E : Type u) [Field E] {n : ℕ} (L : Fin n → Type u)
    [∀ j, CommRing (L j)] [∀ j, Algebra E (L j)]
    (F : Type u) [Field F] [Algebra E F]
    (q : (∀ j, L j) →ₐ[E] F) (hq : Function.Surjective q) :
    ∃ (j : Fin n) (r : L j →ₐ[E] F), Function.Surjective r ∧
      (RingHom.ker r.toRingHom).IsMaximal ∧ ∀ x, q x = r (x j) := by
  let p : PrimeSpectrum (∀ j, L j) := ⟨RingHom.ker q.toRingHom, RingHom.ker_isPrime _⟩
  obtain ⟨j, p', hp⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq p
  have hker : RingHom.ker (Pi.evalRingHom L j) ≤ RingHom.ker q.toRingHom := by
    change RingHom.ker (Pi.evalRingHom L j) ≤ p.asIdeal
    rw [← congrArg PrimeSpectrum.asIdeal hp]
    exact Ideal.ker_le_comap _
  have hs : Function.Surjective (Pi.evalAlgHom E L j) := Function.surjective_eval _
  let r := AlgHom.liftOfSurjective (Pi.evalAlgHom E L j) hs q hker
  have hr : Function.Surjective r := AlgHom.liftOfSurjective_surjective _ hs q hker hq
  refine ⟨j, r, hr, RingHom.ker_isMaximal_of_surjective r.toRingHom hr, fun x ↦ ?_⟩
  exact (AlgHom.liftOfSurjective_apply _ hs q hker x).symm

/-- Recover the algebra equivalence, retaining the chosen base algebra structures. -/
private theorem spec_iso_algEquiv
    (D S T : Type u) [CommRing D] [CommRing S] [CommRing T]
    [Algebra D S] [Algebra D T]
    (e : Spec (.of S) ≅ Spec (.of T))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap D T)) =
      Spec.map (CommRingCat.ofHom (algebraMap D S))) : Nonempty (S ≃ₐ[D] T) := by
  let q := (Scheme.Spec.preimageIso e).unop
  let er := q.commRingCatIsoToRingEquiv
  refine ⟨(AlgEquiv.ofRingEquiv (f := er) ?_).symm⟩
  intro d
  have h : CommRingCat.ofHom (algebraMap D T) ≫ q.hom =
      CommRingCat.ofHom (algebraMap D S) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    change Spec.map (Spec.preimage e.hom) ≫ _ = _
    rw [Spec.map_preimage]
    exact he
  exact congrArg (fun k ↦ k.hom d) h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Use a small group and a universe-correct spectrum coproduct to obtain field factors. -/
private theorem finite_action_fields
    (K : Type u) [Field K] (G : Type v) [Group G] [Finite G]
    (P : GaloisCoverAction G (Spec (.of K)))
    (S : Type u) [CommRing S] [Algebra K S]
    (e : Spec (.of S) ≅ P.Z)
    (he : e.hom ≫ P.π = Spec.map (CommRingCat.ofHom (algebraMap K S))) :
    ∃ (n : ℕ) (_ : 0 < n) (L : Fin n → Type u)
      (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra K (L i))
      (_d : S ≃ₐ[K] (∀ i, L i)),
      ∀ i, FiniteDimensional K (L i) ∧ IsGalois K (L i) ∧
        Module.finrank K (L i) ∣ Nat.card G := by
  classical
  let H := Shrink.{u + 1} G
  let h : H ≃* G := Shrink.mulEquiv
  have : IsFinite P.π := P.isFinite
  have : Etale P.π := P.etale
  let P' : GaloisCover H (Spec (.of K)) :=
    { P := P.Z
      π := P.π
      isFinite := P.isFinite
      etale := P.etale
      surjective := P.surjective
      smul := fun g ↦ P.smul (h g)
      smul_π := fun g ↦ P.smul_π (h g)
      one_smul := by simp only [map_one, P.one_smul]
      mul_smul := fun g g' ↦ by simp only [map_mul, P.mul_smul]
      isIso_sigmaDesc := action_comparison H P.π (fun g ↦ P.smul (h g))
        (fun g ↦ P.smul_π (h g)) (by simp only [map_one, P.one_smul])
        (fun g g' ↦ by simp only [map_mul, P.mul_smul]) (by
          intro Ω _ _ x y hxy
          obtain ⟨g, hg, hu⟩ := P.simply_transitive Ω x y hxy
          exact ⟨h.symm g, by simpa using hg, fun g' hg' ↦
            h.injective ((hu _ hg').trans (h.apply_symm_apply g).symm)⟩) }
  obtain ⟨n, L, hL, aL, hprop, eL, heL⟩ := field_torsor_galois_components K H P'
  let := hL
  let := aL
  let j : ULift.{u} (Fin n) ≃ Fin n := Equiv.ulift
  let er := Sigma.reindex j (fun i ↦ Spec (CommRingCat.of (L i)))
  let ep := RingEquiv.piCongrLeft L j
  -- Mathlib's finite sigmaSpec instance applies to this index in Type u.
  let es := asIso (sigmaSpec (fun i : ULift.{u} (Fin n) ↦ CommRingCat.of (L i.down)))
  let eπ := Scheme.Spec.mapIso ep.symm.toCommRingCatIso.op
  have hstruct : (er.symm ≪≫ es ≪≫ eπ).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (∀ i, L i))) =
        Sigma.desc (fun i : Fin n ↦
          Spec.map (CommRingCat.ofHom (algebraMap K (L i)))) := by
    rw [← cancel_epi er.hom]
    dsimp only [Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, es, asIso_hom]
    ext i
    erw [ι_sigmaSpec_assoc]
    dsimp only [eπ]
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i)) ≫
      Spec.map (CommRingCat.ofHom ep.symm.toRingHom) ≫ _ = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    dsimp only [er]
    rw [Sigma.ι_reindex_hom_assoc, Sigma.ι_desc]
    congr 1
  obtain ⟨d⟩ := spec_iso_algEquiv K S (∀ i, L i)
    (e ≪≫ eL ≪≫ er.symm ≪≫ es ≪≫ eπ) (by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc] at hstruct ⊢
      rw [hstruct, heL]
      exact he)
  have hn : 0 < n := by
    by_contra hzero
    have hn : n = 0 := Nat.eq_zero_of_not_pos hzero
    have : Subsingleton (∀ i : Fin n, L i) := by
      subst n
      infer_instance
    have : Subsingleton S := d.injective.subsingleton
    have : IsEmpty (Spec (.of S)) := ⟨fun x ↦ x.isPrime.ne_top
      (Subsingleton.elim _ _)⟩
    have : IsEmpty P.Z := Function.isEmpty e.inv
    obtain ⟨z, hz⟩ := P.surjective.1 (IsLocalRing.closedPoint K)
    exact isEmptyElim z
  refine ⟨n, hn, L, hL, aL, d, fun i ↦ ?_⟩
  exact ⟨(hprop i).1, (hprop i).2.1,
    by simpa only [Nat.card_congr h.toEquiv] using (hprop i).2.2⟩

/-- The affine pullback comparison with both its projections fixed. -/
private theorem affine_tensor_comparison
    (D C S : Type u) [CommRing D] [CommRing C] [CommRing S]
    [Algebra D C] [Algebra D S] {Z : Scheme.{u}}
    (π : Z ⟶ Spec (.of D)) (e : Spec (.of S) ≅ Z)
    (he : e.hom ≫ π = Spec.map (CommRingCat.ofHom (algebraMap D S))) :
    ∃ t : Spec (.of (C ⊗[D] S)) ≅
        pullback π (Spec.map (CommRingCat.ofHom (algebraMap D C))),
      t.hom ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[D] S))) ∧
      t.hom ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : S →ₐ[D] C ⊗[D] S).toRingHom) ≫ e.hom := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap D C))
  let p := Spec.map (CommRingCat.ofHom (algebraMap D S))
  let b := pullback.map j p j π (𝟙 _) e.hom (𝟙 _)
    (by simp) (by simpa using he.symm)
  have : IsIso b := by dsimp [b]; infer_instance
  let t := (pullbackSpecIso D C S).symm ≪≫ asIso b ≪≫ pullbackSymmetry j π
  refine ⟨t, ?_, ?_⟩
  · simp [t, b, j, p]
    rfl
  · simp [t, b, j, p]

/-- Finite normalization in the generic fields recovers the actual pulled-back torsor.

Source: ILO, IX Proposition 2.1(ii), pp.133-134; Stacks 032L, 033C, 034M, 0307, 01I4.
(blueprint: lem-sfb-pulled-torsor-normalization-model)

Proof:
1. Finiteness makes the given torsor affine. Construct pulled actions directly.
   The diagonal section and lem-sfb-finite-etale-torsor-section-trivialization
   identify their torsor comparisons; affine faithfully flat descent supplies
   their quotient property. Mathlib pullbackSpecIso gives affine presentations.
   The two projection equations below retain the actual covers and structural maps.
   Associativity and localization give the generic comparison, with the displayed
   pure-tensor formula (in the scalar-first convention).
2. Apply lem-sbc-field-torsor-galois-components over K and E, and
   lem-weil-pbc-finite-affine-coproduct-spectrum. Nonempty fibres make both finite
   index sets nonempty. The field extensions are Galois, and their K-degrees divide
   the group order. Tensor distributes over a finite product by the coordinate
   idempotents. Exactly one coordinate idempotent survives in each field quotient;
   this supplies the indicated surjection and maximal kernel with its E-structure.
3. By lem-weil-pbc-localization-normal-domain the localized base is a normal domain.
   lem-weil-pbc-etale-algebra-flat and lem-trf-flat-module-torsionfree-domain make
   the generic map injective. Every generic element has a nonzero base denominator.
   The generic algebra is finite-dimensional over E, hence Artinian. Localization
   preserves nonzerodivisors, which are units in an Artinian ring. Enlarging the
   denominator submonoid therefore identifies the total fractions.
4. lem-weil-pbc-etale-over-normal-ring-normal makes T normal, and
   lem-weil-pbc-normal-ring-integrally-closed-total makes it integrally closed there.
5. Apply lem-weil-pbc-noetherian-normal-separable-integral-closure-finite to each
   finite separable F_a/E. The finite product of the closures is finite over B.
   Integral tuples are precisely tuples of integral coordinates, by multiplying
   the finitely many monic annihilating polynomials.
6. Finite implies integral. Clear a common localization denominator in the monic
   equation of the entire tuple to obtain a B-integral multiple. Conversely an
   integral tuple divided by a power of f is A'-integral, thus T-integral, and lies
   in T by step 4. This gives the final literal image equivalence.
7. Map A' tensor C into the product of fields. Localization gives injectivity;
   integrality puts its image in T, and step 6 gives surjectivity. The resulting
   A'-algebra equivalence and pullbackSpecIso give the spectrum model over A'.
   Compose with the retained affine comparison to obtain the actual pulled torsor.
   No excellence hypothesis is used. -/
theorem pulled_torsor_normalization_model
    (R B A A' K E : Type u)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    [Algebra R B] (hRB : Function.Injective (algebraMap R B))
    (f : R) (hf : f ≠ 0)
    [CommRing A] [Algebra R A] [IsLocalization.Away f A]
    [CommRing A'] [Algebra B A'] [IsLocalization.Away (algebraMap R B f) A']
    [Algebra R A'] [IsScalarTower R B A']
    [Algebra A A'] [IsScalarTower R A A']
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra A K] [IsScalarTower R A K]
    [Field E] [Algebra B E] [IsFractionRing B E]
    [Algebra R E] [IsScalarTower R B E]
    [Algebra K E] [IsScalarTower R K E]
    [Algebra A' E] [IsScalarTower B A' E]
    [Algebra A E] [IsScalarTower A A' E] [IsScalarTower A K E]
    (G : Type v) [Group G] [Finite G]
    (P : GaloisCoverAction G (Spec (CommRingCat.of A))) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra A S)
      (e : Spec (CommRingCat.of S) ≅ P.Z),
      e.hom ≫ P.π = Spec.map (CommRingCat.ofHom (algebraMap A S)) ∧
    ∃ (W : GaloisCoverAction G (Spec (CommRingCat.of A')))
      (ι : W.Z ≅ pullback P.π (Spec.map (CommRingCat.ofHom (algebraMap A A')))),
      ι.hom ≫ pullback.snd P.π
        (Spec.map (CommRingCat.ofHom (algebraMap A A'))) = W.π ∧
      (∀ g : G, W.smul g ≫ ι.hom ≫ pullback.fst P.π
        (Spec.map (CommRingCat.ofHom (algebraMap A A'))) =
        ι.hom ≫ pullback.fst P.π
          (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ≫ P.smul g) ∧
    ∃ (eT : Spec (CommRingCat.of (A' ⊗[A] S)) ≅
        pullback P.π (Spec.map (CommRingCat.ofHom (algebraMap A A'))))
      (eK : Spec (CommRingCat.of (K ⊗[A] S)) ≅
        pullback P.π (Spec.map (CommRingCat.ofHom (algebraMap A K)))),
      eT.hom ≫ pullback.snd P.π
        (Spec.map (CommRingCat.ofHom (algebraMap A A'))) =
        Spec.map (CommRingCat.ofHom (algebraMap A' (A' ⊗[A] S))) ∧
      eT.hom ≫ pullback.fst P.π
        (Spec.map (CommRingCat.ofHom (algebraMap A A'))) =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : S →ₐ[A] A' ⊗[A] S).toRingHom) ≫ e.hom ∧
      eK.hom ≫ pullback.snd P.π
        (Spec.map (CommRingCat.ofHom (algebraMap A K))) =
        Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[A] S))) ∧
      eK.hom ≫ pullback.fst P.π
        (Spec.map (CommRingCat.ofHom (algebraMap A K))) =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : S →ₐ[A] K ⊗[A] S).toRingHom) ≫ e.hom ∧
    ∃ (n m : ℕ) (_ : 0 < n) (_ : 0 < m)
      (L : Fin n → Type u) (_ : ∀ j, Field (L j)) (_ : ∀ j, Algebra K (L j))
      (F : Fin m → Type u) (_ : ∀ a, Field (F a)) (_ : ∀ a, Algebra E (F a))
      (_ : ∀ a, Algebra B (F a)) (_ : ∀ a, IsScalarTower B E (F a))
      (dK : K ⊗[A] S ≃ₐ[K] (∀ j, L j))
      (base : E ⊗[A'] (A' ⊗[A] S) ≃ₐ[E] E ⊗[K] (∀ j, L j))
      (prod : E ⊗[K] (∀ j, L j) ≃ₐ[E] (∀ j, E ⊗[K] L j))
      (fields : (∀ j, E ⊗[K] L j) ≃ₐ[E] (∀ a, F a)),
      (∀ j, FiniteDimensional K (L j) ∧ IsGalois K (L j) ∧
        Module.finrank K (L j) ∣ Nat.card G) ∧
      (∀ a, FiniteDimensional E (F a) ∧ IsGalois E (F a)) ∧
      (∀ (z : E) (a' : A') (s : S),
        base (z ⊗ₜ[A'] (a' ⊗ₜ[A] s)) =
          (z * algebraMap A' E a') ⊗ₜ[K] dK (1 ⊗ₜ[A] s)) ∧
      (∀ (z : E) (l : ∀ j, L j) (j : Fin n), prod (z ⊗ₜ[K] l) j = z ⊗ₜ[K] l j) ∧
      (∀ a, ∃ (j : Fin n) (q : E ⊗[K] L j →ₐ[E] F a),
        Function.Surjective q ∧ (RingHom.ker q.toRingHom).IsMaximal ∧
        ∀ x : ∀ j, E ⊗[K] L j, fields x a = q (x j)) ∧
      Function.Injective
        (Algebra.TensorProduct.includeRight : A' ⊗[A] S →ₐ[A'] E ⊗[A'] (A' ⊗[A] S)) ∧
      @IsLocalization (A' ⊗[A] S) _ (nonZeroDivisors (A' ⊗[A] S))
        (E ⊗[A'] (A' ⊗[A] S)) _ Algebra.TensorProduct.rightAlgebra ∧
      (∀ (p : Ideal (A' ⊗[A] S)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ∧
      @IsIntegrallyClosedIn (A' ⊗[A] S) (E ⊗[A'] (A' ⊗[A] S)) _ _
        Algebra.TensorProduct.rightAlgebra ∧
      (∀ a, Module.Finite B (integralClosure B (F a))) ∧
      Module.Finite B (∀ a, integralClosure B (F a)) ∧
      (∀ x : ∀ a, F a,
        (∃ t : A' ⊗[A] S, fields (prod (base (1 ⊗ₜ[A'] t))) = x) ↔
        ∃ (c : ∀ a, integralClosure B (F a)) (k : ℕ),
          ∀ a, x a * (algebraMap B (F a) (algebraMap R B f)) ^ k = (c a : F a)) ∧
      ∃ model : pullback
          (Spec.map (CommRingCat.ofHom (algebraMap B (∀ a, integralClosure B (F a)))))
          (Spec.map (CommRingCat.ofHom (algebraMap B A'))) ≅
          Spec (CommRingCat.of (A' ⊗[A] S)),
        model.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A' (A' ⊗[A] S))) =
          pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap B (∀ a, integralClosure B (F a)))))
            (Spec.map (CommRingCat.ofHom (algebraMap B A'))) := by
  classical
  have : IsFinite P.π := P.isFinite
  have : Etale P.π := P.etale
  have : Surjective P.π := P.surjective
  have : IsAffine P.Z := isAffine_of_isAffineHom P.π
  let S : Type u := Γ(P.Z, ⊤)
  let : Algebra A S := P.π.ΓAlgebra
  have : Module.Finite A S := RingHom.Finite.comp P.π.finite_appTop
    (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of A)).inv).2)
  have : Algebra.Etale A S := (P.π.etale_iff_etale_ΓAlgebra).mp inferInstance
  let e : Spec (.of S) ≅ P.Z := P.Z.isoSpec.symm
  have he : e.hom ≫ P.π = Spec.map (CommRingCat.ofHom (algebraMap A S)) := by
    rw [← cancel_epi P.Z.isoSpec.hom]
    dsimp only [e, Iso.symm_hom]
    rw [Iso.hom_inv_id_assoc]
    change P.π = P.Z.toSpecΓ ≫ Spec.map ((ΓSpecIso (.of A)).inv ≫ P.π.appTop)
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  refine ⟨S, inferInstance, inferInstance, e, he, ?_⟩
  obtain ⟨W, ι, hι, hact⟩ := action_base_change G P
    (Spec.map (CommRingCat.ofHom (algebraMap A A')))
  refine ⟨W, ι, hι, hact, ?_⟩
  obtain ⟨eT, heT₂, heT₁⟩ := affine_tensor_comparison A A' S P.π e he
  obtain ⟨eK, heK₂, heK₁⟩ := affine_tensor_comparison A K S P.π e he
  refine ⟨eT, eK, heT₂, heT₁, heK₂, heK₁, ?_⟩
  obtain ⟨PK, ιK, hιK, _⟩ := action_base_change G P
    (Spec.map (CommRingCat.ofHom (algebraMap A K)))
  obtain ⟨n, hn, L, hL, aL, dK, hpL⟩ :=
    finite_action_fields K G PK (K ⊗[A] S) (eK ≪≫ ιK.symm) (by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
      rw [← hιK, Iso.inv_hom_id_assoc]
      exact heK₂)
  let := hL
  let := aL
  let base : E ⊗[A'] (A' ⊗[A] S) ≃ₐ[E] E ⊗[K] (∀ j, L j) :=
    (Algebra.TensorProduct.cancelBaseChange A A' E E S).trans
      ((Algebra.TensorProduct.cancelBaseChange A K E E S).symm.trans
        (Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[E] E) dK))
  let prod := Algebra.TensorProduct.piRight K E E L
  obtain ⟨PE, ιE, hιE, _⟩ := action_base_change G W
    (Spec.map (CommRingCat.ofHom (algebraMap A' E)))
  let eW : Spec (.of (A' ⊗[A] S)) ≅ W.Z := eT ≪≫ ι.symm
  have heW : eW.hom ≫ W.π =
      Spec.map (CommRingCat.ofHom (algebraMap A' (A' ⊗[A] S))) := by
    dsimp only [eW, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, ← hι, Iso.inv_hom_id_assoc]
    exact heT₂
  obtain ⟨eE, heE₂, _⟩ := affine_tensor_comparison A' E (A' ⊗[A] S) W.π eW heW
  obtain ⟨m, hm, F, hF, aF, dE, hpF⟩ :=
    finite_action_fields E G PE (E ⊗[A'] (A' ⊗[A] S)) (eE ≪≫ ιE.symm) (by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
      rw [← hιE, Iso.inv_hom_id_assoc]
      exact heE₂)
  let := hF
  let := aF
  let (a : Fin m) : Algebra B (F a) := Algebra.compHom (F a) (algebraMap B E)
  let (a : Fin m) : IsScalarTower B E (F a) := IsScalarTower.of_algebraMap_eq' rfl
  let fields := prod.symm.trans (base.symm.trans dE)
  have hfB : algebraMap R B f ≠ 0 := fun h ↦ hf (hRB (h.trans (map_zero _).symm))
  have : IsDomain A' := IsLocalization.isDomain_of_le_nonZeroDivisors A'
    (powers_le_nonZeroDivisors_of_noZeroDivisors hfB)
  have : IsIntegrallyClosed A' := isIntegrallyClosed_of_isLocalization A'
    (Submonoid.powers (algebraMap R B f))
    (powers_le_nonZeroDivisors_of_noZeroDivisors hfB)
  have : IsFractionRing A' E := IsFractionRing.isFractionRing_of_isLocalization
    (Submonoid.powers (algebraMap R B f)) A' E
    (powers_le_nonZeroDivisors_of_noZeroDivisors hfB)
  obtain ⟨hinj, hfrac, hnormal, hclosed⟩ := finite_etale_generic_normal A' E (A' ⊗[A] S)
  have hfinite (a : Fin m) : Module.Finite B (integralClosure B (F a)) := by
    have := (hpF a).1
    have := (hpF a).2.1
    exact IsIntegralClosure.finite B E (F a) _
  have : ∀ a, Module.Finite B (integralClosure B (F a)) := hfinite
  refine ⟨n, m, hn, hm, L, hL, aL, F, hF, aF, inferInstance, inferInstance,
    dK, base, prod, fields, hpL, fun a ↦ ⟨(hpF a).1, (hpF a).2.1⟩, ?_, ?_, ?_,
    hinj, hfrac, hnormal, hclosed, hfinite, inferInstance, ?_, ?_⟩
  · intro z a' s
    simp [base, Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def, mul_comm]
  · intro z l j
    rfl
  · intro a
    exact product_field_quotient E (fun j ↦ E ⊗[K] L j) (F a)
      ((Pi.evalAlgHom E F a).comp fields.toAlgHom)
      ((Function.surjective_eval _).comp fields.surjective)
  · intro x
    simpa only [fields, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply] using
      normalization_image B A' E (A' ⊗[A] S) (algebraMap R B f) m F dE hclosed x
  · obtain ⟨et⟩ := normalization_tensor B A' E (A' ⊗[A] S)
      (algebraMap R B f) m F dE hinj hclosed
    let C := ∀ a, integralClosure B (F a)
    let ec : C ⊗[B] A' ≃+* A' ⊗[B] C := (Algebra.TensorProduct.comm B C A').toRingEquiv
    let model := pullbackSpecIso B C A' ≪≫
      (Scheme.Spec.mapIso ec.toCommRingCatIso.op).symm ≪≫
      Scheme.Spec.mapIso et.symm.toRingEquiv.toCommRingCatIso.op
    refine ⟨model, ?_⟩
    dsimp only [model, Iso.trans_hom, Iso.symm_hom]
    rw [← pullbackSpecIso_hom_snd]
    simp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.op_hom, Iso.op_inv,
      Scheme.Spec_map]
    rw [Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    apply congrArg (fun k ↦ (pullbackSpecIso B C A').hom ≫ k)
    apply congrArg Spec.map
    ext a
    change ec.symm (et.symm (algebraMap A' (A' ⊗[A] S) a)) = 1 ⊗ₜ[B] a
    rw [et.symm.commutes]
    rfl

end AlgebraicGeometry.Scheme

