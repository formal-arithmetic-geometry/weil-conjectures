/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.CohomologyFilteredColimit
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Functorial nonnegative injective resolutions

Source: Stacks Project, Derived Categories, Tag 013K, applied with functorial
injective embeddings in a Grothendieck category. Successively embed each cokernel
in an injective object. All choices belong to the existing functorial embedding;
the complex and its augmentation are constructed explicitly.
(blueprint: new-finite-cover-functorial-injective-resolution)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v uK vK w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {K : Type uK} [Category.{vK} K] (D : K ⥤ C)

/-- The successive cokernels of the natural injective embeddings.
Source: Stacks Project, Tag 013K.
(blueprint: new-finite-cover-functorial-injective-resolution) -/
def nonnegativeInjectiveSyzygy : ℕ → K ⥤ C
  | 0 => D
  | n + 1 => cokernel (nonnegativeInjectiveSyzygy n).toInjectiveExtension

/-- The terms of the resolution are functorial injective extensions of the syzygies.
Source: Stacks Project, Tag 013K.
(blueprint: new-finite-cover-functorial-injective-resolution) -/
def nonnegativeInjectiveTerm (n : ℕ) : K ⥤ C :=
  (D.nonnegativeInjectiveSyzygy n).injectiveExtension

/-- The differential is the cokernel projection followed by the next embedding.
Source: Stacks Project, Tag 013K.
(blueprint: new-finite-cover-functorial-injective-resolution) -/
def nonnegativeInjectiveDifferential (n : ℕ) :
    D.nonnegativeInjectiveTerm n ⟶ D.nonnegativeInjectiveTerm (n + 1) :=
  cokernel.π (D.nonnegativeInjectiveSyzygy n).toInjectiveExtension ≫
    (D.nonnegativeInjectiveSyzygy (n + 1)).toInjectiveExtension

/-- Consecutive differentials compose to zero by the cokernel relation.
Source: Stacks Project, Tag 013K.
(blueprint: new-finite-cover-functorial-injective-resolution) -/
theorem nonnegativeInjectiveDifferential_squared (n : ℕ) :
    D.nonnegativeInjectiveDifferential n ≫
      D.nonnegativeInjectiveDifferential (n + 1) = 0 := by
  simp [nonnegativeInjectiveDifferential, Category.assoc]

/-- The explicit nonnegative complex of functorial injective terms.
Source: Stacks Project, Tag 013K.
(blueprint: new-finite-cover-functorial-injective-resolution) -/
def nonnegativeInjectiveComplex : CochainComplex (K ⥤ C) ℕ :=
  CochainComplex.of (D.nonnegativeInjectiveTerm) (D.nonnegativeInjectiveDifferential)
    (D.nonnegativeInjectiveDifferential_squared)

private theorem nonnegativeInjectiveComplex_exact (n : ℕ) :
    (ShortComplex.mk (D.nonnegativeInjectiveDifferential n)
      (D.nonnegativeInjectiveDifferential (n + 1))
      (D.nonnegativeInjectiveDifferential_squared n)).Exact := by
  let i := (D.nonnegativeInjectiveSyzygy (n + 1)).toInjectiveExtension
  let j := (D.nonnegativeInjectiveSyzygy (n + 2)).toInjectiveExtension
  haveI : Mono i := by
    apply NatTrans.mono_of_mono_app
  haveI : Mono j := by
    apply NatTrans.mono_of_mono_app
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  let T := ShortComplex.mk i (cokernel.π i ≫ j) (by simp [Category.assoc])
  let α : S ⟶ T := { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := j }
  have hT : T.Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).mp (ShortComplex.exact_cokernel i)
  let β : ShortComplex.mk (D.nonnegativeInjectiveDifferential n)
      (D.nonnegativeInjectiveDifferential (n + 1))
      (D.nonnegativeInjectiveDifferential_squared n) ⟶ T :=
    { τ₁ := cokernel.π (D.nonnegativeInjectiveSyzygy n).toInjectiveExtension
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [nonnegativeInjectiveDifferential, i, T]
      comm₂₃ := by simp [nonnegativeInjectiveDifferential, i, j, T] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono β).mpr hT

/-- The natural augmentation of the explicit resolution.
Source: Stacks Project, Tag 013K.
(blueprint: new-finite-cover-functorial-injective-resolution) -/
def nonnegativeInjectiveAugmentation :
    (CochainComplex.single₀ (K ⥤ C)).obj D ⟶ D.nonnegativeInjectiveComplex :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨D.toInjectiveExtension, by
      dsimp [nonnegativeInjectiveComplex, CochainComplex.of, CochainComplex.of.d,
        nonnegativeInjectiveDifferential, nonnegativeInjectiveTerm,
        nonnegativeInjectiveSyzygy]
      simp [Category.assoc]⟩

/-- The augmentation is a quasi-isomorphism, already as a complex of diagrams.
Source: Stacks Project, Tag 013K. At positive degrees, exactness follows from the
cokernel sequence: precomposing the kernel embedding with an epimorphism and
postcomposing the cokernel projection with a monomorphism preserve exactness.
At degree zero the first embedding is a kernel of the first differential.
(blueprint: new-finite-cover-functorial-injective-resolution) -/
instance quasiIso_nonnegativeInjectiveAugmentation :
    QuasiIso D.nonnegativeInjectiveAugmentation := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · let i := D.toInjectiveExtension
      haveI : Mono i := by apply NatTrans.mono_of_mono_app
      let j := (D.nonnegativeInjectiveSyzygy 1).toInjectiveExtension
      haveI : Mono j := by apply NatTrans.mono_of_mono_app
      let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
      let T := ShortComplex.mk i (cokernel.π i ≫ j) (by simp [Category.assoc])
      let α : S ⟶ T := { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := j }
      have hT := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).mp
        (ShortComplex.exact_cokernel i)
      change (ShortComplex.mk (D.nonnegativeInjectiveAugmentation.f 0)
        (D.nonnegativeInjectiveComplex.d 0 1) _).Exact ∧
          Mono (D.nonnegativeInjectiveAugmentation.f 0)
      have haug : D.nonnegativeInjectiveAugmentation.f 0 = D.toInjectiveExtension := by
        exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _
      have hd : D.nonnegativeInjectiveComplex.d 0 1 =
          D.nonnegativeInjectiveDifferential 0 := by
        unfold nonnegativeInjectiveComplex
        exact CochainComplex.of_d (D.nonnegativeInjectiveTerm)
          (D.nonnegativeInjectiveDifferential) 0
      simp only [haug, hd]
      exact ⟨hT, inferInstance⟩
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
      change (ShortComplex.mk
        (CochainComplex.of.d (D.nonnegativeInjectiveTerm)
          (D.nonnegativeInjectiveDifferential) n (n + 1))
        (CochainComplex.of.d (D.nonnegativeInjectiveTerm)
          (D.nonnegativeInjectiveDifferential) (n + 1) (n + 1 + 1)) _).Exact
      simpa only [CochainComplex.of_d] using nonnegativeInjectiveComplex_exact D n
    · apply CochainComplex.exactAt_succ_single_obj

/-- Evaluate the constructed diagram resolution to obtain an injective resolution.
Source: Stacks Project, Tag 013K. Evaluation is exact, and every evaluated term is
the injective extension of the corresponding syzygy.
(blueprint: new-finite-cover-functorial-injective-resolution) -/
def nonnegativeInjectiveResolution (x : K) : InjectiveResolution (D.obj x) where
  cocomplex := (((evaluation K C).obj x).mapHomologicalComplex _).obj
    D.nonnegativeInjectiveComplex
  injective n := by
    change Injective ((D.nonnegativeInjectiveSyzygy n).injectiveExtension.obj x)
    infer_instance
  ι := ((evaluation K C).obj x).mapResolution D.nonnegativeInjectiveAugmentation

end CategoryTheory.Functor
