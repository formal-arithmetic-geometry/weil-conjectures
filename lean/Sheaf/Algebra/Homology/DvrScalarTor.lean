/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Tor of finite modules over a discrete valuation ring -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

open ZeroObject
open scoped TensorProduct

private noncomputable def twoTermResolution {A : Type u} [CommRing A]
    {X Y Z : ModuleCat.{u} A} [Projective X] [Projective Y]
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0)
    (hs : (ShortComplex.mk f g h).ShortExact) : ProjectiveResolution Z := by
  let K := HomologicalComplex.double f (by decide : (ComplexShape.down ℕ).Rel 1 0)
  let φ : K.X 0 ⟶ Z := (HomologicalComplex.doubleXIso₁ f _ (by decide)).hom ≫ g
  let ε : K ⟶ (ChainComplex.single₀ (ModuleCat.{u} A)).obj Z :=
    HomologicalComplex.mkHomToSingle φ (by
      intro i hi
      have : i = 1 := by simpa using hi.symm
      subst i
      simp [K, φ, HomologicalComplex.double_d, h])
  have hq : QuasiIso ε := by
    rw [quasiIso_iff]
    intro n
    cases n with
    | zero =>
      apply (ChainComplex.quasiIsoAt₀_iff ε).2
      apply (ShortComplex.quasiIso_iff_of_zeros' _ (by simp [K])
        (by simp) (by simp)).2
      constructor
      · apply ShortComplex.exact_of_iso _ hs.exact
        refine ShortComplex.isoMk
          (HomologicalComplex.doubleXIso₀ f
            (by decide : (ComplexShape.down ℕ).Rel 1 0)).symm
          (HomologicalComplex.doubleXIso₁ f
            (by decide : (ComplexShape.down ℕ).Rel 1 0) (by decide)).symm
          (Iso.refl _) ?_ ?_
        · simp [K, HomologicalComplex.double_d]
        · simp [ε, φ, HomologicalComplex.mkHomToSingle_f]
      · simpa [ε, φ, HomologicalComplex.mkHomToSingle] using hs.epi_g
    | succ n =>
      apply (quasiIsoAt_iff_exactAt' ε (n + 1)
        (ChainComplex.exactAt_succ_single_obj _ _)).2
      cases n with
      | zero =>
        apply (HomologicalComplex.exactAt_iff' K 2 1 0 (by simp) (by simp)).2
        apply (ShortComplex.exact_iff_mono _ (by
          change K.d 2 1 = 0
          exact HomologicalComplex.double_d_eq_zero₀ f _ 2 1 (by decide))).2
        have : Mono f := hs.mono_f
        change Mono (K.d 1 0)
        dsimp only [K]
        rw [HomologicalComplex.double_d f _ (by decide)]
        infer_instance
      | succ n =>
        apply HomologicalComplex.ExactAt.of_isZero
        exact HomologicalComplex.isZero_double_X f _ _ (by omega) (by omega)
  refine { complex := K, π := ε, quasiIso := hq, projective := ?_ }
  intro n
  by_cases h₁ : n = 1
  · subst n
    exact Projective.of_iso (HomologicalComplex.doubleXIso₀ f
      (by decide : (ComplexShape.down ℕ).Rel 1 0)).symm inferInstance
  · by_cases h₀ : n = 0
    · subst n
      exact Projective.of_iso (HomologicalComplex.doubleXIso₁ f
        (by decide : (ComplexShape.down ℕ).Rel 1 0) (by decide)).symm inferInstance
    · exact (HomologicalComplex.isZero_double_X f _ n h₁ h₀).projective

private theorem finite_homology {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) [Module.Finite A (K.X n)] :
    Module.FinitePresentation A (K.homology n) := by
  let S := K.sc n
  have : Module.Finite A S.X₂ := inferInstanceAs (Module.Finite A (K.X n))
  have : Module.Finite A (LinearMap.ker S.g.hom) := inferInstance
  have : Module.FinitePresentation A S.moduleCatLeftHomologyData.H := by
    change Module.FinitePresentation A
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    exact Module.finitePresentation_of_finite _ _
  exact Module.FinitePresentation.of_equiv (S.moduleCatHomologyIso.toLinearEquiv.symm)

private theorem finite_tor {A : Type u} [CommRing A] [IsDomain A]
    [IsPrincipalIdealRing A] [IsNoetherianRing A]
    (P Q : ModuleCat.{u} A) [Module.FinitePresentation A P] [Module.FinitePresentation A Q] :
    (∀ n : ℕ, 2 ≤ n → IsZero (((Tor' (ModuleCat.{u} A) n).obj P).obj Q)) ∧
    (∀ n : ℕ, Module.FinitePresentation A (((Tor' (ModuleCat.{u} A) n).obj P).obj Q)) := by
  obtain ⟨m, N, e, hN⟩ := Module.FinitePresentation.exists_fin A P
  let X : ModuleCat.{u} A := ModuleCat.of A N
  let Y : ModuleCat.{u} A := ModuleCat.of A (Fin m → A)
  have : Module.Finite A X := Module.Finite.of_fg hN
  have : Module.Free A X := inferInstance
  let f : X ⟶ Y := ModuleCat.ofHom N.subtype
  let g : Y ⟶ P := ModuleCat.ofHom (e.symm.toLinearMap.comp N.mkQ)
  have h : f ≫ g = 0 := by
    ext x
    change e.symm (Submodule.Quotient.mk x.val) = 0
    rw [(Submodule.Quotient.mk_eq_zero N).2 x.property, map_zero]
  have hs : (ShortComplex.mk f g h).ShortExact := by
    have : Mono f := (ModuleCat.mono_iff_injective _).2 N.injective_subtype
    have : Epi g := (ModuleCat.epi_iff_surjective _).2
      (e.symm.surjective.comp N.mkQ_surjective)
    refine { mono_f := inferInstance, epi_g := inferInstance, exact := ?_ }
    apply (ShortComplex.moduleCat_exact_iff _).2
    intro y hy
    have hy' : (Submodule.Quotient.mk y : (Fin m → A) ⧸ N) = 0 :=
      e.symm.map_eq_zero_iff.mp hy
    exact ⟨⟨y, (Submodule.Quotient.mk_eq_zero N).1 hy'⟩, rfl⟩
  let res := twoTermResolution f g h hs
  let T := MonoidalCategory.tensorRight Q
  let K := (T.mapHomologicalComplex (.down ℕ)).obj res.complex
  have eTor (n : ℕ) : (((Tor' (ModuleCat.{u} A) n).obj P).obj Q) ≅ K.homology n :=
    res.isoLeftDerivedObj T n
  have hz (n : ℕ) (hn : 2 ≤ n) : IsZero (K.X n) := by
    apply T.map_isZero
    exact HomologicalComplex.isZero_double_X f
      (by decide : (ComplexShape.down ℕ).Rel 1 0) n (by omega) (by omega)
  constructor
  · intro n hn
    exact (HomologicalComplex.ExactAt.of_isZero (hz n hn)).isZero_homology.of_iso (eTor n)
  · intro n
    have hterm : Module.Finite A (K.X n) := by
      by_cases hn₀ : n = 0
      · subst n
        change Module.Finite A (T.obj (res.complex.X 0))
        have e' := T.mapIso (HomologicalComplex.doubleXIso₁ f
          (by decide : (ComplexShape.down ℕ).Rel 1 0) (by decide))
        have : Module.Finite A (T.obj Y) := by
          change Module.Finite A ((Fin m → A) ⊗[A] Q)
          infer_instance
        exact Module.Finite.of_surjective e'.inv.hom e'.toLinearEquiv.symm.surjective
      · by_cases hn₁ : n = 1
        · subst n
          have e' := T.mapIso (HomologicalComplex.doubleXIso₀ f
            (by decide : (ComplexShape.down ℕ).Rel 1 0))
          have : Module.Finite A (T.obj X) := by
            change Module.Finite A (X ⊗[A] Q)
            infer_instance
          exact Module.Finite.of_surjective e'.inv.hom e'.toLinearEquiv.symm.surjective
        · have := (ModuleCat.isZero_iff_subsingleton.mp (hz n (by omega)))
          infer_instance
    have := finite_homology K n
    exact Module.FinitePresentation.of_equiv (eTor n).toLinearEquiv.symm

private theorem cyclic_tor_le {A : Type u} [CommRing A] [IsDomain A]
    (π : A) (hπ : π ≠ 0) (r s : ℕ) (hsr : s ≤ r) (n : ℕ) (hn : n ≤ 1) :
    Nonempty ((((Tor' (ModuleCat.{u} A) n).obj
      (ModuleCat.of A (A ⧸ Ideal.span {π ^ r}))).obj
        (ModuleCat.of A (A ⧸ Ideal.span {π ^ s}))) ≅
      ModuleCat.of A (A ⧸ Ideal.span {π ^ s})) := by
  let I : Ideal A := Ideal.span {π ^ r}
  let B : ModuleCat.{u} A := ModuleCat.of A A
  let Z : ModuleCat.{u} A := ModuleCat.of A (A ⧸ I)
  let Q : ModuleCat.{u} A := ModuleCat.of A (A ⧸ Ideal.span {π ^ s})
  let f : B ⟶ B := ModuleCat.ofHom ((π ^ r) • LinearMap.id)
  let g : B ⟶ Z := ModuleCat.ofHom I.mkQ
  have h : f ≫ g = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Submodule.Quotient.mk (π ^ r * x) = (0 : A ⧸ I)
    apply (Submodule.Quotient.mk_eq_zero I).mpr
    exact Ideal.mul_mem_right x _ (Ideal.subset_span (by simp))
  have hs : (ShortComplex.mk f g h).ShortExact := by
    have : Mono f := (ModuleCat.mono_iff_injective _).2 (by
      intro x y hxy
      exact mul_left_cancel₀ (pow_ne_zero r hπ) hxy)
    have : Epi g := (ModuleCat.epi_iff_surjective _).2 I.mkQ_surjective
    refine { mono_f := inferInstance, epi_g := inferInstance, exact := ?_ }
    apply (ShortComplex.moduleCat_exact_iff _).2
    intro x hx
    have hxI : x ∈ I := (Submodule.Quotient.mk_eq_zero I).mp hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hxI
    exact ⟨y, hy.symm⟩
  let res := twoTermResolution f g h hs
  let T := MonoidalCategory.tensorRight Q
  let K := (T.mapHomologicalComplex (.down ℕ)).obj res.complex
  have htf : T.map f = 0 := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro a q
    change (π ^ r * a) ⊗ₜ[A] q = 0
    rw [← smul_eq_mul, TensorProduct.smul_tmul]
    have hz : (π ^ r) • q = (0 : Q) := by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
      change Ideal.Quotient.mk _ (π ^ r * x) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply Ideal.mul_mem_right x
      apply Ideal.mem_span_singleton.mpr
      exact pow_dvd_pow π hsr
    rw [hz, TensorProduct.tmul_zero]
  have hd (i j : ℕ) : K.d i j = 0 := by
    change T.map ((HomologicalComplex.double f
      (by decide : (ComplexShape.down ℕ).Rel 1 0)).d i j) = 0
    by_cases hi : i = 1
    · subst i
      by_cases hj : j = 0
      · subst j
        rw [HomologicalComplex.double_d f _ (by decide), Functor.map_comp,
          Functor.map_comp, htf]
        simp
      · rw [HomologicalComplex.double_d_eq_zero₁ f _ _ _ hj, Functor.map_zero]
    · rw [HomologicalComplex.double_d_eq_zero₀ f _ _ _ hi, Functor.map_zero]
  let eH : K.homology n ≅ K.X n :=
    (K.isoHomologyπ (n + 1) n (by simp) (hd _ _)).symm ≪≫
      K.iCyclesIso n _ rfl (hd _ _)
  have eX : Nonempty (K.X n ≅ Q) := by
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · exact ⟨T.mapIso (HomologicalComplex.doubleXIso₁ f
        (by decide : (ComplexShape.down ℕ).Rel 1 0) (by decide)) ≪≫
          (TensorProduct.lid A Q).toModuleIso⟩
    · exact ⟨T.mapIso (HomologicalComplex.doubleXIso₀ f
        (by decide : (ComplexShape.down ℕ).Rel 1 0)) ≪≫
          (TensorProduct.lid A Q).toModuleIso⟩
  exact ⟨res.isoLeftDerivedObj T n ≪≫ eH ≪≫ eX.some⟩

/-- Tor of finite modules over a DVR is finite, vanishes above degree one, and has
cyclic-power value A/(pi^min(r,s)) in degrees zero and one.

Source: Stacks Project, Algebra, Tags 00LY, 00M1 and 00PD; blueprint main-20261015,
sk-lem-integral-models-operations.proof.md, paragraph (2), scalar calculation
(blueprint: lem-sfb-dvr-scalar-tor).

Proof: A finite presentation has finite free kernel because a DVR is a Noetherian
PID. It therefore gives a projective resolution of length one by finite free modules.
Tensor this resolution with Q. Its two terms are finite modules; their kernel and
cokernel are finite over the Noetherian ring A, and hence finitely presented. The
complex is zero above degree one. For A/(pi^r), use the resolution A --pi^r--> A.
After tensoring with A/(pi^s), if r >= s the differential is zero. If r < s, its
cokernel is A/(pi^r), while multiplication by pi^(s-r) identifies its kernel with
A/(pi^r). Both injectivity and surjectivity follow by cancellation of the nonzero
power of pi in the domain A. The quotient cases r=0 or s=0 are zero modules; the
statement below requires positive exponents. The zero module and empty presentations
are covered by the same resolution calculation.

The implementation uses the proved symmetry of ordinary module Tor to put the
larger exponent in the resolved factor. Its tensor differential is then zero,
so both degrees identify directly with the smaller quotient. -/
theorem dvr_scalar_tor {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (π : A)
    (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π})
    (P Q : ModuleCat.{u} A) [Module.FinitePresentation A P]
    [Module.FinitePresentation A Q] :
    (∀ n : ℕ, 2 ≤ n → IsZero (((Tor' (ModuleCat.{u} A) n).obj P).obj Q)) ∧
    (∀ n : ℕ, Module.FinitePresentation A (((Tor' (ModuleCat.{u} A) n).obj P).obj Q)) ∧
    (∀ r s : ℕ, 1 ≤ r → 1 ≤ s → ∀ n : ℕ, n ≤ 1 →
      Nonempty ((((Tor' (ModuleCat.{u} A) n).obj
        (ModuleCat.of A (A ⧸ Ideal.span {π ^ r}))).obj
          (ModuleCat.of A (A ⧸ Ideal.span {π ^ s}))) ≅
        ModuleCat.of A (A ⧸ Ideal.span {π ^ min r s}))) := by
  obtain ⟨hhigh, hfinite⟩ := finite_tor P Q
  refine ⟨hhigh, hfinite, ?_⟩
  intro r s _hr _hs n hn
  have hp : π ≠ 0 :=
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 hπ).ne_zero
  by_cases hsr : s ≤ r
  · rw [Nat.min_eq_right hsr]
    exact cyclic_tor_le π hp r s hsr n hn
  · have hrs : r ≤ s := by omega
    obtain ⟨e⟩ := cyclic_tor_le π hp s r hrs n hn
    obtain ⟨σ⟩ := CategoryTheory.nonempty_tor'_flip_iso A n
    exact ⟨(σ.app (ModuleCat.of A (A ⧸ Ideal.span {π ^ r}))).app
      (ModuleCat.of A (A ⧸ Ideal.span {π ^ s})) ≪≫ e ≪≫
        eqToIso (by rw [min_eq_left hrs])⟩

end ModuleCat
