/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectCategoricalTrace
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectTrace
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Chain-level supertrace with finite dual frames

Source: Weil conjectures blueprint, trace formula, `sk-p-trace`,
`lem-trf-chain-supertrace` and its twelve-step DAG proof
(blueprint: lem-trf-chain-supertrace).

The frame package is the existing finite-free splitting package: its columns and
coordinate functionals are precisely a finite dual frame, including nonfree projectives.
The dual is the recorded total module Hom into the degree-zero unit. All tensors,
associators and unitors are the canonical total-complex constructions; the braiding
is the Koszul braiding. The interval in the finite sums is any interval supporting `P`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace DerivedCategory

variable {A : Type u} [CommRing A]

/-- Degree zero of the chain tensor unit is the coefficient module.
Source: the unit convention in `lem-trf-chain-supertrace`
(blueprint: lem-trf-chain-supertrace). -/
noncomputable def chainTraceUnitCoordinate :
    (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)).X 0 ≅ ModuleCat.of A A :=
  HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)

/-- A frame functional placed in dual degree `-i`, zero in every other component.
Source: the displayed dual and dual-frame conventions in `lem-trf-chain-supertrace`
(blueprint: lem-trf-chain-supertrace). -/
noncomputable def chainTraceFrameDual {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ) (a : Fin (s.N i)) :
    (perfectTraceModelDual P).X (-i) :=
  CochainComplex.HomComplex.Cochain.single
    (ModuleCat.ofHom (perfectTraceFrameFunctional s i a) ≫ chainTraceUnitCoordinate.inv) (-i)

/-- The finite dual-frame tensor in total degree zero.
Source: the coevaluation formula in `lem-trf-chain-supertrace`
(blueprint: lem-trf-chain-supertrace). -/
noncomputable def chainTraceFrameTensor {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ) (a : Fin (s.N i)) :
    (P ⊗ perfectTraceModelDual P).X 0 :=
  (HomologicalComplex.ιTensorObj P (perfectTraceModelDual P) i (-i) 0
    (add_neg_cancel i)).hom
      (perfectTraceFrameVector s i a ⊗ₜ[A] chainTraceFrameDual s i a)

/-- The ordinary projective-module trace in degree `i`, computed with a finite dual frame.
This definition does not assume that the projective term has a basis.
Source: the ordinary trace convention in `lem-trf-chain-supertrace`
(blueprint: lem-trf-chain-supertrace). -/
noncomputable def chainTraceTerm {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ)
    (t : P.X i ⟶ P.X i) : A :=
  ∑ a : Fin (s.N i), perfectTraceFrameFunctional s i a (t.hom (perfectTraceFrameVector s i a))

/-- The alternating sum of ordinary projective traces on a finite supporting interval.
Source: part (c) of `lem-trf-chain-supertrace`
(blueprint: lem-trf-chain-supertrace). -/
noncomputable def chainSupertrace {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (a b : ℤ) (v : P ⟶ P) : A :=
  ∑ i ∈ Finset.Icc a b, i.negOnePow • chainTraceTerm s i (v.f i)

private noncomputable abbrev chainTraceComplexMonoidal :
    MonoidalCategory (CochainComplex (ModuleCat.{u} A) ℤ) := inferInstance

section
attribute [local instance] chainTraceComplexMonoidal

private theorem chainTraceFrame_identity {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ) (x : P.X i) :
    ∑ r, perfectTraceFrameFunctional s i r x • perfectTraceFrameVector s i r = x := by
  classical
  have hx : (s.i i).hom x = ∑ r, (s.i i).hom x r • Pi.single r (1 : A) := by
    ext r
    simp [Pi.single_apply]
  calc
    _ = (s.p i).hom (∑ r, (s.i i).hom x r • Pi.single r (1 : A)) := by
      simp only [perfectTraceFrameFunctional, perfectTraceFrameVector,
        LinearMap.comp_apply, LinearMap.proj_apply, map_sum, map_smul]
    _ = (s.p i).hom ((s.i i).hom x) := congrArg (s.p i).hom hx.symm
    _ = x := by
      have h := congrArg (fun (f : P.X i ⟶ P.X i) ↦ f.hom x) (s.splitting i)
      exact h

private theorem chainTrace_exists_package (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hfinite : ∀ i : ℤ, Module.Finite A (P.X i))
    (hprojective : ∀ i : ℤ, Module.Projective A (P.X i)) :
    ∃ s : ModuleCat.StrictPerfectCoefficientPackage P,
      ∀ i : ℤ, IsZero (P.X i) → s.N i = 0 := by
  classical
  have h (i : ℤ) : ∃ (n : ℕ)
      (f : ModuleCat.of A (Fin n → A) ⟶ P.X i)
      (g : P.X i ⟶ ModuleCat.of A (Fin n → A)),
      g ≫ f = 𝟙 (P.X i) ∧ (IsZero (P.X i) → n = 0) := by
    by_cases hi : IsZero (P.X i)
    · exact ⟨0, 0, 0, by simpa using hi.eq_of_src 0 (𝟙 _), fun _ ↦ rfl⟩
    · let := hfinite i
      let := hprojective i
      obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A (P.X i)
      exact ⟨n, ModuleCat.ofHom f, ModuleCat.ofHom g,
        ModuleCat.hom_ext hfg, fun hzero ↦ False.elim (hi hzero)⟩
  choose n f g hfg hempty using h
  exact ⟨⟨n, g, f, hfg⟩, hempty⟩

private theorem chainTrace_frame_cyclic
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {r t : ℕ} (e : Fin r → M) (ε : Fin r → Module.Dual A M)
    (q : Fin t → N) (μ : Fin t → Module.Dual A N)
    (he : ∀ x, ∑ a, ε a x • e a = x) (hq : ∀ x, ∑ b, μ b x • q b = x)
    (f : M →ₗ[A] N) (g : N →ₗ[A] M) :
    ∑ a, ε a (g (f (e a))) = ∑ b, μ b (f (g (q b))) := by
  classical
  calc
    _ = ∑ a, ∑ b, μ b (f (e a)) * ε a (g (q b)) := by
      apply Finset.sum_congr rfl
      intro a _
      have h := congrArg (fun x ↦ ε a (g x)) (hq (f (e a)))
      simpa only [map_sum, map_smul, smul_eq_mul] using h.symm
    _ = ∑ b, ∑ a, ε a (g (q b)) * μ b (f (e a)) := by
      rw [Finset.sum_comm]
      simp only [mul_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      have h := congrArg (fun x ↦ μ b (f x)) (he (g (q b)))
      simpa only [map_sum, map_smul, smul_eq_mul] using h

private theorem chainTraceTerm_cyclic {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s t : ModuleCat.StrictPerfectCoefficientPackage P) (i j : ℤ)
    (f : P.X i ⟶ P.X j) (g : P.X j ⟶ P.X i) :
    chainTraceTerm s i (f ≫ g) = chainTraceTerm t j (g ≫ f) :=
  chainTrace_frame_cyclic (perfectTraceFrameVector s i) (perfectTraceFrameFunctional s i)
    (perfectTraceFrameVector t j) (perfectTraceFrameFunctional t j)
    (chainTraceFrame_identity s i) (chainTraceFrame_identity t j) f.hom g.hom

private theorem chainTraceTerm_independent {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s t : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ) (v : P.X i ⟶ P.X i) :
    chainTraceTerm s i v = chainTraceTerm t i v := by
  simpa using chainTraceTerm_cyclic s t i i v (𝟙 _)

private theorem chainTraceTerm_basis {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ) (n : ℕ)
    (e : Module.Basis (Fin n) A (P.X i)) (v : P.X i ⟶ P.X i) :
    chainTraceTerm s i v = ∑ r, e.repr (v.hom (e r)) r := by
  classical
  exact chainTrace_frame_cyclic (perfectTraceFrameVector s i)
    (perfectTraceFrameFunctional s i) e e.coord (chainTraceFrame_identity s i)
    (fun x ↦ e.sum_repr x) v.hom LinearMap.id

private theorem chainSupertrace_homotopy {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] (v w : P ⟶ P)
    (h : Nonempty (Homotopy v w)) : chainSupertrace s a b v = chainSupertrace s a b w := by
  classical
  let τ (i : ℤ) : (P.X i ⟶ P.X i) →+ A :=
    { toFun := chainTraceTerm s i
      map_zero' := by simp only [chainTraceTerm, ModuleCat.hom_zero, LinearMap.zero_apply,
        map_zero, Finset.sum_const_zero]
      map_add' := by
        intro f g
        simp only [chainTraceTerm, ModuleCat.hom_add, LinearMap.add_apply,
          map_add, Finset.sum_add_distrib] }
  exact h.some.sum_negOnePow_smul_eq a b τ
    (fun i j f g ↦ chainTraceTerm_cyclic s s i j f g)

open TensorProduct

section

variable {M : Type*} [AddCommGroup M] [Module A M] {n : ℕ} (ξ : Fin n → Module.Dual A M)
  (m : Fin n → M) (h : ∀ q, ∑ j, ξ j q • m j = q)
include h

private lemma chainTrace_contract_zig' (q : M) :
    LinearMap.lTensor M (contractLeft A M)
      (TensorProduct.assoc A M (Module.Dual A M) M ((∑ j, m j ⊗ₜ[A] ξ j) ⊗ₜ[A] q)) =
      q ⊗ₜ[A] (1 : A) := by
  simp only [sum_tmul, map_sum, TensorProduct.assoc_tmul, LinearMap.lTensor_tmul,
    contractLeft_apply]
  conv_rhs => rw [← h q, sum_tmul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [smul_tmul, smul_eq_mul, mul_one]

private lemma chainTrace_contract_zig :
    (contractLeft A M).lTensor M ∘ₗ (TensorProduct.assoc A _ _ _).toLinearMap ∘ₗ
      (LinearMap.toSpanSingleton A _ (∑ j, m j ⊗ₜ[A] ξ j)).rTensor M =
      (TensorProduct.rid A M).symm.toLinearMap ∘ₗ (TensorProduct.lid A M).toLinearMap := by
  refine TensorProduct.ext' fun r q ↦ ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.rTensor_tmul, LinearMap.toSpanSingleton_apply, TensorProduct.lid_tmul,
    TensorProduct.rid_symm_apply, ← smul_tmul', map_smul, chainTrace_contract_zig' ξ m h q]

private lemma chainTrace_contract_zag' (φ : Module.Dual A M) :
    LinearMap.rTensor (Module.Dual A M) (contractLeft A M)
      ((TensorProduct.assoc A (Module.Dual A M) M (Module.Dual A M)).symm
        (φ ⊗ₜ[A] ∑ j, m j ⊗ₜ[A] ξ j)) = (1 : A) ⊗ₜ[A] φ := by
  simp only [tmul_sum, map_sum, TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul,
    contractLeft_apply]
  have hφ : ∑ j, φ (m j) • ξ j = φ := by
    ext q
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    conv_rhs => rw [← h q, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  conv_rhs => rw [← hφ, tmul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← smul_tmul, smul_eq_mul, mul_one]
private lemma chainTrace_contract_zag :
    (contractLeft A M).rTensor (Module.Dual A M) ∘ₗ
      (TensorProduct.assoc A _ _ _).symm.toLinearMap ∘ₗ
        (LinearMap.toSpanSingleton A _ (∑ j, m j ⊗ₜ[A] ξ j)).lTensor (Module.Dual A M) =
      (TensorProduct.lid A _).symm.toLinearMap ∘ₗ (TensorProduct.rid A _).toLinearMap := by
  refine TensorProduct.ext' fun φ r ↦ ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, TensorProduct.rid_tmul,
    TensorProduct.lid_symm_apply, tmul_smul, map_smul, chainTrace_contract_zag' ξ m h φ]


end

set_option warn.classDefReducibility false in
private noncomputable def chainTraceFramePairing
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ) :
    ExactPairing (P.X i) (ModuleCat.of A (Module.Dual A (P.X i))) where
  coevaluation' := ModuleCat.ofHom (LinearMap.toSpanSingleton A _
    (∑ r, perfectTraceFrameVector s i r ⊗ₜ[A] perfectTraceFrameFunctional s i r))
  evaluation' := ModuleCat.ofHom (contractLeft A (P.X i))
  coevaluation_evaluation' := by
    ext : 1
    exact chainTrace_contract_zag (perfectTraceFrameFunctional s i)
      (perfectTraceFrameVector s i) (chainTraceFrame_identity s i)
  evaluation_coevaluation' := by
    ext : 1
    exact chainTrace_contract_zig (perfectTraceFrameFunctional s i)
      (perfectTraceFrameVector s i) (chainTraceFrame_identity s i)

private noncomputable abbrev chainTraceFrameHasDual
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ) : HasRightDual (P.X i) :=
  { rightDual := ModuleCat.of A (Module.Dual A (P.X i))
    exact := chainTraceFramePairing s i }

private theorem chainTraceFrame_mate
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (i j : ℤ)
    (f : P.X i ⟶ P.X j) :
    letI : ∀ n, HasRightDual (P.X n) := chainTraceFrameHasDual s
    ∀ (φ : Module.Dual A (P.X j)) (x : P.X i),
      DFunLike.coe (F := Module.Dual A (P.X i)) ((rightAdjointMate f).hom φ) x =
        φ (f.hom x) := by
  let : ∀ n, HasRightDual (P.X n) := chainTraceFrameHasDual s
  intro φ x
  have h := rightAdjointMate_comp_evaluation f
  have hx := congrArg (fun (g : ModuleCat.of A (Module.Dual A (P.X j)) ⊗ P.X i ⟶
      ModuleCat.of A A) ↦ g.hom (φ ⊗ₜ[A] x)) h
  change contractLeft A (P.X i)
      (((rightAdjointMate f).hom φ) ⊗ₜ[A] x) =
    contractLeft A (P.X j) (φ ⊗ₜ[A] f.hom x) at hx
  exact hx

private noncomputable def chainTraceDualCoordinateHom
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    CochainComplex.HomComplex.Cochain P
      (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)) n →ₗ[A] Module.Dual A (P.X (-n)) :=
    { toFun := fun φ ↦ chainTraceUnitCoordinate.hom.hom.comp
        (φ.v (-n) 0 (neg_add_cancel n)).hom
      map_add' := by
        intro φ ψ
        ext x
        change chainTraceUnitCoordinate.hom.hom
          ((φ.v (-n) 0 _).hom x + (ψ.v (-n) 0 _).hom x) = _
        exact map_add _ _ _
      map_smul' := by
        intro a φ
        ext x
        change chainTraceUnitCoordinate.hom.hom (a • (φ.v (-n) 0 _).hom x) =
          a • chainTraceUnitCoordinate.hom.hom ((φ.v (-n) 0 _).hom x)
        exact map_smul _ _ _ }

private noncomputable def chainTraceDualCoordinateInv
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    Module.Dual A (P.X (-n)) →ₗ[A] CochainComplex.HomComplex.Cochain P
      (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)) n :=
    { toFun := fun φ ↦ CochainComplex.HomComplex.Cochain.single
        (ModuleCat.ofHom φ ≫ chainTraceUnitCoordinate.inv) n
      map_add' := by
        intro φ ψ
        apply CochainComplex.HomComplex.Cochain.ext
        intro p q hpq
        change (CochainComplex.HomComplex.Cochain.single
          (ModuleCat.ofHom (φ + ψ) ≫ chainTraceUnitCoordinate.inv) n).v p q hpq =
            (CochainComplex.HomComplex.Cochain.single
              (ModuleCat.ofHom φ ≫ chainTraceUnitCoordinate.inv) n).v p q hpq +
            (CochainComplex.HomComplex.Cochain.single
              (ModuleCat.ofHom ψ ≫ chainTraceUnitCoordinate.inv) n).v p q hpq
        by_cases hp : p = -n
        · subst p
          have hq : q = 0 := by omega
          subst hq
          simp
        · simp [CochainComplex.HomComplex.Cochain.single_v_eq_zero _ _ _ _ _ hp]
      map_smul' := by
        intro a φ
        apply CochainComplex.HomComplex.Cochain.ext
        intro p q hpq
        change (CochainComplex.HomComplex.Cochain.single
          (ModuleCat.ofHom (a • φ) ≫ chainTraceUnitCoordinate.inv) n).v p q hpq =
            a • (CochainComplex.HomComplex.Cochain.single
              (ModuleCat.ofHom φ ≫ chainTraceUnitCoordinate.inv) n).v p q hpq
        by_cases hp : p = -n
        · subst p
          have hq : q = 0 := by omega
          subst hq
          simp only [CochainComplex.HomComplex.Cochain.single_v]
          apply ModuleCat.hom_ext
          ext x
          change chainTraceUnitCoordinate.inv.hom (a • φ x) =
            a • chainTraceUnitCoordinate.inv.hom (φ x)
          exact map_smul _ _ _
        · simp [CochainComplex.HomComplex.Cochain.single_v_eq_zero _ _ _ _ _ hp] }

private noncomputable def chainTraceDualCoordinate
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (perfectTraceModelDual P).X n ≅ ModuleCat.of A (Module.Dual A (P.X (-n))) where
  hom := ModuleCat.ofHom (chainTraceDualCoordinateHom P n)
  inv := ModuleCat.ofHom (chainTraceDualCoordinateInv P n)
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    by_cases hq : q = 0
    · subst hq
      have hp : p = -n := by omega
      subst p
      change (CochainComplex.HomComplex.Cochain.single
        (ModuleCat.ofHom (chainTraceUnitCoordinate.hom.hom.comp
          (φ.v (-n) 0 (neg_add_cancel n)).hom) ≫ chainTraceUnitCoordinate.inv) n).v
          (-n) 0 hpq = φ.v (-n) 0 hpq
      simp only [CochainComplex.HomComplex.Cochain.single_v]
      apply ModuleCat.hom_ext
      ext x
      simp
    · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of A A) q hq
      exact hz.eq_of_tgt _ _
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    change chainTraceUnitCoordinate.hom.hom
      (((CochainComplex.HomComplex.Cochain.single
        (ModuleCat.ofHom φ ≫ chainTraceUnitCoordinate.inv) n).v (-n) 0
          (neg_add_cancel n)).hom x) = φ x
    rw [CochainComplex.HomComplex.Cochain.single_v]
    exact congr($(chainTraceUnitCoordinate.inv_hom_id).hom (φ x))

@[irreducible]
private noncomputable def chainTraceDualIso
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) :
    letI : ∀ n, HasRightDual (P.X n) := chainTraceFrameHasDual s
    perfectTraceModelDual P ≅ P.rightDual := by
  letI : ∀ n, HasRightDual (P.X n) := chainTraceFrameHasDual s
  refine HomologicalComplex.Hom.isoOfComponents (chainTraceDualCoordinate P) ?_
  intro n m hnm
  symm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  change chainTraceUnitCoordinate.hom.hom
      (((CochainComplex.HomComplex.δ n m φ).v (-m) 0 (neg_add_cancel m)).hom x) =
    DFunLike.coe (F := Module.Dual A (P.X (-m)))
      ((m.negOnePow • (rightAdjointMate (P.d (-m) (-n)))).hom
        (chainTraceUnitCoordinate.hom.hom.comp (φ.v (-n) 0 (neg_add_cancel n)).hom)) x
  have hnm' : n + 1 = m := hnm
  rw [CochainComplex.HomComplex.δ_v n m hnm' φ (-m) 0 (neg_add_cancel m)
    (-1) (-n) rfl (by omega)]
  rw [CochainComplex.singleFunctor_obj_d, comp_zero, zero_add]
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  change m.negOnePow • _ = m.negOnePow •
    DFunLike.coe (F := Module.Dual A (P.X (-m)))
      ((rightAdjointMate (P.d (-m) (-n))).hom
        (chainTraceUnitCoordinate.hom.hom.comp (φ.v (-n) 0 (neg_add_cancel n)).hom)) x
  rw [chainTraceFrame_mate]
  rfl

private theorem chainTraceDualIso_hom_f
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (n : ℤ) :
    letI : ∀ i, HasRightDual (P.X i) := chainTraceFrameHasDual s
    (chainTraceDualIso s).hom.f n = (chainTraceDualCoordinate P n).hom := by
  unfold chainTraceDualIso
  rfl

private theorem chainTraceDualIso_inv_f
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (n : ℤ) :
    letI : ∀ i, HasRightDual (P.X i) := chainTraceFrameHasDual s
    (chainTraceDualIso s).inv.f n = (chainTraceDualCoordinate P n).inv := by
  unfold chainTraceDualIso
  rfl

set_option warn.classDefReducibility false in
private noncomputable def chainTracePairing
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] : ExactPairing P (perfectTraceModelDual P) :=
  letI : ∀ n, HasRightDual (P.X n) := chainTraceFrameHasDual s
  letI := CochainComplex.exactPairingRightDual P a b
  exactPairingCongrRight (chainTraceDualIso s)

private theorem chainTracePairing_evaluation
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] :
    letI : ∀ n, HasRightDual (P.X n) := chainTraceFrameHasDual s
    (chainTracePairing s a b).evaluation' =
      (chainTraceDualIso s).hom ▷ P ≫ CochainComplex.rightDual.eval P := rfl

private theorem chainTracePairing_coevaluation
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] :
    letI : ∀ n, HasRightDual (P.X n) := chainTraceFrameHasDual s
    (chainTracePairing s a b).coevaluation' =
      CochainComplex.rightDual.coev P a b ≫ P ◁ (chainTraceDualIso s).inv := rfl

private theorem chainTraceDual_evalPQ
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (q p : ℤ) (hpq : q + p = 0)
    (φ : (perfectTraceModelDual P).X q) (x : P.X p) :
    letI : ∀ n, HasRightDual (P.X n) := chainTraceFrameHasDual s
    ((((chainTraceDualIso s).hom.f q ▷ P.X p) ≫
      CochainComplex.rightDual.evalPQ P q p hpq).hom (φ ⊗ₜ[A] x)) =
      chainTraceUnitCoordinate.hom.hom ((φ.v p 0 (by omega)).hom x) := by
  obtain rfl : p = -q := by omega
  rw [chainTraceDualIso_hom_f]
  rfl

private theorem chainTracePairing_eval
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (i : ℤ) (φ : (perfectTraceModelDual P).X (-i)) (x : P.X i) :
    letI := chainTracePairing s a b
    chainTraceUnitCoordinate.hom.hom
      (((ε_ P (perfectTraceModelDual P)).f 0).hom
        ((HomologicalComplex.ιTensorObj (perfectTraceModelDual P) P (-i) i 0
          (neg_add_cancel i)).hom (φ ⊗ₜ[A] x))) =
        chainTraceUnitCoordinate.hom.hom ((φ.v i 0 (add_neg_cancel i)).hom x) := by
  let : ∀ n, HasRightDual (P.X n) := chainTraceFrameHasDual s
  let := chainTracePairing s a b
  have hι := CochainComplex.Monoidal.ι_whiskerRight
    (L := P) (chainTraceDualIso s).hom (-i) i 0 (neg_add_cancel i)
  have he := CochainComplex.rightDual.ι_eval_f P (-i) i (neg_add_cancel i)
  have h : HomologicalComplex.ιTensorObj (perfectTraceModelDual P) P (-i) i 0
      (neg_add_cancel i) ≫ (ε_ P (perfectTraceModelDual P)).f 0 =
      ((chainTraceDualIso s).hom.f (-i) ▷ P.X i) ≫
        CochainComplex.rightDual.evalPQ P (-i) i (neg_add_cancel i) ≫
          chainTraceUnitCoordinate.inv := by
    change _ ≫ (chainTracePairing s a b).evaluation'.f 0 = _
    rw [chainTracePairing_evaluation]
    simp only [HomologicalComplex.comp_f]
    rw [reassoc_of% hι, he]
    rfl
  have hx := congrArg (fun f ↦ chainTraceUnitCoordinate.hom.hom
    (f.hom (φ ⊗ₜ[A] x))) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx
  change _ = chainTraceUnitCoordinate.hom.hom
    (chainTraceUnitCoordinate.inv.hom
      (((chainTraceDualIso s).hom.f (-i) ▷ P.X i ≫
        CochainComplex.rightDual.evalPQ P (-i) i (neg_add_cancel i)).hom
          (φ ⊗ₜ[A] x))) at hx
  rw [chainTraceDual_evalPQ s (-i) i (neg_add_cancel i)] at hx
  refine hx.trans ?_
  exact congr($(chainTraceUnitCoordinate.inv_hom_id).hom
    (chainTraceUnitCoordinate.hom.hom ((φ.v i 0 (add_neg_cancel i)).hom x)))

private theorem chainTraceDual_coevPQ
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (p q : ℤ) (hpq : p + q = 0) :
    letI : ∀ n, HasRightDual (P.X n) := chainTraceFrameHasDual s
    (CochainComplex.rightDual.coevPQ P p q hpq ≫
      P.X p ◁ (chainTraceDualIso s).inv.f q).hom 1 =
        ∑ r, perfectTraceFrameVector s p r ⊗ₜ[A]
          CochainComplex.HomComplex.Cochain.single
            (ModuleCat.ofHom (perfectTraceFrameFunctional s p r) ≫
              chainTraceUnitCoordinate.inv) q := by
  classical
  let : ∀ n, HasRightDual (P.X n) := chainTraceFrameHasDual s
  obtain rfl : p = -q := by omega
  rw [chainTraceDualIso_inv_f]
  dsimp only [CochainComplex.rightDual.coevPQ]
  rw [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, id_whiskerRight, Category.comp_id]
  change (LinearMap.lTensor (P.X (-q)) (chainTraceDualCoordinateInv P q))
    ((LinearMap.toSpanSingleton A _
      (∑ r, perfectTraceFrameVector s (-q) r ⊗ₜ[A]
        perfectTraceFrameFunctional s (-q) r)) 1) = _
  rw [LinearMap.toSpanSingleton_apply, one_smul, map_sum]
  rfl

private theorem chainTrace_sum_comp_apply {I : Type*} (t : Finset I)
    {M N T : ModuleCat.{u} A} (f : I → (M ⟶ N)) (g : N ⟶ T) (x : M) :
    ((∑ i ∈ t, f i) ≫ g).hom x = ∑ i ∈ t, (f i ≫ g).hom x := by
  simp only [Preadditive.sum_comp, ModuleCat.hom_sum, LinearMap.sum_apply]

private theorem chainTracePairing_coev
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] :
    letI := chainTracePairing s a b
    ((η_ P (perfectTraceModelDual P)).f 0).hom (chainTraceUnitCoordinate.inv.hom 1) =
      ∑ i ∈ Finset.Icc a b, ∑ r, chainTraceFrameTensor s i r := by
  classical
  let : ∀ n, HasRightDual (P.X n) := chainTraceFrameHasDual s
  let := chainTracePairing s a b
  have hη : η_ P (perfectTraceModelDual P) =
      CochainComplex.rightDual.coev P a b ≫ P ◁ (chainTraceDualIso s).inv :=
    chainTracePairing_coevaluation s a b
  rw [hη]
  change (chainTraceUnitCoordinate.inv ≫
    ((CochainComplex.rightDual.coev P a b).f 0 ≫
      (P ◁ (chainTraceDualIso s).inv).f 0)).hom 1 = _
  rw [← Category.assoc]
  change ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).inv ≫
    (CochainComplex.rightDual.coev P a b).f 0 ≫
      (P ◁ (chainTraceDualIso s).inv).f 0).hom 1 = _
  rw [← Category.assoc]
  erw [CochainComplex.rightDual.singleObjXSelf_inv_coev_f P a b]
  rw [CochainComplex.rightDual.coevZero, chainTrace_sum_comp_apply]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Category.assoc, CochainComplex.ιTensorObj_whiskerLeft_f,
    ← Category.assoc]
  change (HomologicalComplex.ιTensorObj P (perfectTraceModelDual P) i (-i) 0
    (add_neg_cancel i)).hom
      ((CochainComplex.rightDual.coevPQ P i (-i) (add_neg_cancel i) ≫
        P.X i ◁ (chainTraceDualIso s).inv.f (-i)).hom 1) = _
  erw [chainTraceDual_coevPQ]
  change (HomologicalComplex.ιTensorObj P (perfectTraceModelDual P) i (-i) 0
    (add_neg_cancel i)).hom (∑ r, perfectTraceFrameVector s i r ⊗ₜ[A]
      chainTraceFrameDual s i r) = _
  rw [map_sum]
  rfl

private theorem chainTrace_coev_eq {C : Type*} [Category C] [MonoidalCategory C]
    {X Y : C} (p₁ p₂ : ExactPairing X Y) (h : p₁.evaluation' = p₂.evaluation') :
    p₁.coevaluation' = p₂.coevaluation' := by
  let := p₁
  apply (tensorLeftHomEquiv (𝟙_ C) X Y Y).symm.injective
  change Y ◁ p₁.coevaluation' ≫ (α_ _ _ _).inv ≫ p₁.evaluation' ▷ Y ≫ (λ_ Y).hom =
    Y ◁ p₂.coevaluation' ≫ (α_ _ _ _).inv ≫ p₁.evaluation' ▷ Y ≫ (λ_ Y).hom
  calc
    _ = (ρ_ Y).hom := by
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
        congrArg (fun f ↦ f ≫ (λ_ Y).hom) p₁.coevaluation_evaluation'
    _ = _ := by
      rw [h]
      symm
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
        congrArg (fun f ↦ f ≫ (λ_ Y).hom) p₂.coevaluation_evaluation'

private theorem chainTraceTerm_trace {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ) (v : P.X i ⟶ P.X i) :
    letI : HasRightDual (P.X i) := chainTraceFrameHasDual s i
    (trace v).hom 1 = chainTraceTerm s i v := by
  classical
  let : HasRightDual (P.X i) := chainTraceFrameHasDual s i
  have hη : η_ (P.X i) (P.X i)ᘁ = ModuleCat.ofHom
      (LinearMap.toSpanSingleton A _
        (∑ r, perfectTraceFrameVector s i r ⊗ₜ[A] perfectTraceFrameFunctional s i r)) := rfl
  have hε : ε_ (P.X i) (P.X i)ᘁ = ModuleCat.ofHom (contractLeft A (P.X i)) := rfl
  rw [trace, hη, hε]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
  erw [LinearMap.toSpanSingleton_apply, one_smul]
  simp only [map_sum]
  rfl

private theorem chainTraceTerm_basis_trace {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ) (n : ℕ)
    (e : Module.Basis (Fin n) A (P.X i)) (v : P.X i ⟶ P.X i) :
    chainTraceTerm s i v = ∑ r : Fin n, e.repr (v.hom (e r)) r ∧
      chainTraceTerm s i v = LinearMap.trace A (P.X i) v.hom ∧
      chainTraceTerm s i (𝟙 (P.X i)) = (n : A) := by
  classical
  refine ⟨chainTraceTerm_basis s i n e v, ?_, ?_⟩
  · rw [chainTraceTerm_basis s i n e v, LinearMap.trace_eq_matrix_trace A e]
    simp [Matrix.trace, LinearMap.toMatrix_apply]
  · rw [chainTraceTerm_basis s i n e (𝟙 _)]
    simp

private theorem chainTracePairing_eval_independent
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s t : ModuleCat.StrictPerfectCoefficientPackage P) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] :
    (chainTracePairing s a b).evaluation' = (chainTracePairing t a b).evaluation' := by
  apply HomologicalComplex.to_single_hom_ext
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro q p hpq
  have hqp : q + p = 0 := hpq
  obtain rfl : q = -p := by omega
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro φ x
  apply chainTraceUnitCoordinate.toLinearEquiv.injective
  exact (chainTracePairing_eval s a b p φ x).trans
    (chainTracePairing_eval t a b p φ x).symm

private theorem chainTracePairing_coev_independent
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s t : ModuleCat.StrictPerfectCoefficientPackage P) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] :
    (chainTracePairing s a b).coevaluation' = (chainTracePairing t a b).coevaluation' :=
  chainTrace_coev_eq _ _ (chainTracePairing_eval_independent s t a b)

private theorem chainTracePairing_trace
    {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (s t : ModuleCat.StrictPerfectCoefficientPackage P) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] (v : P ⟶ P) :
    (chainTracePairing s a b).coevaluation' ≫ v ▷ perfectTraceModelDual P ≫
      (CochainComplex.Monoidal.braiding P (perfectTraceModelDual P)).hom ≫
      (chainTracePairing s a b).evaluation' =
        (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map
          (ModuleCat.ofHom (chainSupertrace t a b v • LinearMap.id)) := by
  classical
  let : ∀ n, HasRightDual (P.X n) := chainTraceFrameHasDual s
  let := CochainComplex.hasRightDual P a b
  let := chainTracePairing s a b
  change η_ P (perfectTraceModelDual P) ≫ v ▷ perfectTraceModelDual P ≫
    (β_ P (perfectTraceModelDual P)).hom ≫ ε_ P (perfectTraceModelDual P) = _
  rw [← trace_eq_of_exactPairing]
  apply HomologicalComplex.from_single_hom_ext
  rw [CochainComplex.trace_f_zero_eq P a b v]
  erw [HomologicalComplex.single_map_f_self]
  congr 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_smul,
    LinearMap.smul_apply]
  change (∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • (trace (v.f i)).hom 1) =
    (chainSupertrace t a b v • (LinearMap.id : A →ₗ[A] A)) (1 : A)
  rw [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, mul_one]
  unfold chainSupertrace
  apply Finset.sum_congr rfl
  intro i hi
  rw [chainTraceTerm_trace, chainTraceTerm_independent s t]
  rfl

section
variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C]
private theorem canonical_eval_transport {P T : C} (e : P ≅ T) :
    (β_ ((ihom T).obj (𝟙_ C)) T).hom ≫ (ihom.ev T).app (𝟙_ C) =
      ((MonoidalClosed.pre e.hom).app (𝟙_ C) ⊗ₘ e.inv) ≫
        (β_ ((ihom P).obj (𝟙_ C)) P).hom ≫ (ihom.ev P).app (𝟙_ C) := by
  rw [tensorHom_def, Category.assoc,
    BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_naturality_left_assoc]
  rw [whisker_exchange_assoc,
    MonoidalClosed.id_tensor_pre_app_comp_ev]
  simp
end

private theorem iso_naturality_cancel {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {X Y : C} (f : X ⟶ Y) :
    (e.app X).hom ≫ G.map f ≫ (e.app Y).inv = F.map f := by
  simp only [Iso.app_hom, Iso.app_inv]
  rw [← e.hom.naturality_assoc]
  simp only [Iso.hom_inv_id_app, Category.comp_id]

private theorem tensor_iso_cancel {C : Type*} [Category C] [MonoidalCategory C]
    {X X' Y Y' : C} (e : X ≅ X') (f : Y ≅ Y') :
    (e.hom ⊗ₘ f.hom) ≫ (e.inv ⊗ₘ f.inv) = 𝟙 _ := by
  rw [tensorHom_comp_tensorHom, e.hom_inv_id, f.hom_inv_id, id_tensorHom_id]


end

variable [HasDerivedCategory.{u} (ModuleCat.{u} A)]

/-- The canonical comparison between the image of the chain unit and the derived unit.
Source: the scalar identification and derived-model paragraph of `lem-trf-chain-supertrace`
(blueprint: lem-trf-chain-supertrace). -/
noncomputable def chainTraceUnitIso :
    Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)) ≅
      𝟙_ (DerivedCategory (ModuleCat.{u} A)) :=
  ((singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app (ModuleCat.of A A)).symm ≪≫
    singleFunctorObjUnitIso (ModuleCat.{u} A)

private noncomputable abbrev chainTraceDerivedMonoidal :
    MonoidalCategory (DerivedCategory (ModuleCat.{u} A)) := inferInstance

section
attribute [local instance] chainTraceComplexMonoidal chainTraceDerivedMonoidal

open Functor.LaxMonoidal Functor.OplaxMonoidal
private theorem chainTrace_derived_pairing
    (P D : CochainComplex (ModuleCat.{u} A) ℤ) (p : ExactPairing P D)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P)
    (hD : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat D) :
    ∃ q : ExactPairing (Q.obj P) (Q.obj D),
      q.evaluation' = (QObjTensorQObjIsoOfKFlatRight D P hP).hom ≫ Q.map p.evaluation' ≫
        chainTraceUnitIso.hom ∧
      q.coevaluation' = chainTraceUnitIso.inv ≫ Q.map p.coevaluation' ≫
        (QObjTensorQObjIsoOfKFlatLeft P D hP).inv := by
  let H := HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)
  let X : (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat.FullSubcategory :=
    ⟨H.obj P, (HomotopyCategory.kFlat_quotient_obj_iff _).2 hP⟩
  let Y : (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat.FullSubcategory :=
    ⟨H.obj D, (HomotopyCategory.kFlat_quotient_obj_iff _).2 hD⟩
  let := p
  let hp : ExactPairing (H.obj P) (H.obj D) := @ExactPairing.map _ _ _ _ _ _ H _ P D p
  let : ExactPairing ((ObjectProperty.ι _).obj X) ((ObjectProperty.ι _).obj Y) := hp
  let hxy : ExactPairing X Y :=
    @ExactPairing.ofFullyFaithful _ _ _ _ _ _ (ObjectProperty.ι _) _ _ _ X Y hp
  let := hxy
  let := Functor.Monoidal.ofLaxMonoidal (kFlatQh (ModuleCat.{u} A))
  let q : ExactPairing (Qh.obj (H.obj P)) (Qh.obj (H.obj D)) :=
    @ExactPairing.map _ _ _ _ _ _ (kFlatQh (ModuleCat.{u} A)) _ X Y hxy
  let : ExactPairing ((H ⋙ Qh).obj P) ((H ⋙ Qh).obj D) := q
  let r : ExactPairing (Q.obj P) (Q.obj D) :=
    exactPairingCongr ((quotientCompQhIso _).app P).symm
      ((quotientCompQhIso _).app D).symm
  have he : (ObjectProperty.ι _).map hxy.evaluation' = hp.evaluation' := by
    change (ObjectProperty.ι _).map ((ObjectProperty.ι _).preimage
      (δ (ObjectProperty.ι _) Y X ≫ hp.evaluation' ≫ ε (ObjectProperty.ι _))) = _
    erw [Functor.map_preimage]
    change 𝟙 _ ≫ hp.evaluation' ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
  have hc : (ObjectProperty.ι _).map hxy.coevaluation' = hp.coevaluation' := by
    change (ObjectProperty.ι _).map ((ObjectProperty.ι _).preimage
      (η (ObjectProperty.ι _) ≫ hp.coevaluation' ≫ μ (ObjectProperty.ι _) X Y)) = _
    erw [Functor.map_preimage]
    change 𝟙 _ ≫ hp.coevaluation' ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
  have hqe : q.evaluation' = μ Qh (H.obj D) (H.obj P) ≫
      Qh.map hp.evaluation' ≫ inv (ε Qh) := by
    change μ (kFlatQh (ModuleCat.{u} A)) Y X ≫
      Qh.map ((ObjectProperty.ι _).map hxy.evaluation') ≫
        η (kFlatQh (ModuleCat.{u} A)) = _
    rw [he, ← Functor.Monoidal.inv_ε]
    change (μ Qh (H.obj D) (H.obj P) ≫ Qh.map (𝟙 _)) ≫
      Qh.map hp.evaluation' ≫ inv (ε Qh ≫ Qh.map (𝟙 _)) = _
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  have : IsIso (μ Qh (H.obj P) (H.obj D)) :=
    isIso_μ_Qh_of_kFlat _ _ X.property
  have hqc : q.coevaluation' = ε Qh ≫ Qh.map hp.coevaluation' ≫
      inv (μ Qh (H.obj P) (H.obj D)) := by
    change ε (kFlatQh (ModuleCat.{u} A)) ≫
      Qh.map ((ObjectProperty.ι _).map hxy.coevaluation') ≫
        δ (kFlatQh (ModuleCat.{u} A)) X Y = _
    rw [hc, ← Functor.Monoidal.inv_μ]
    change (ε Qh ≫ Qh.map (𝟙 _)) ≫ Qh.map hp.coevaluation' ≫
      inv (μ Qh (H.obj P) (H.obj D) ≫ Qh.map (𝟙 _)) = _
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  let E := quotientCompQhIso (ModuleCat.{u} A)
  let U := chainTraceUnitIso (A := A)
  have hu : U.hom = (E.app (𝟙_ _)).inv ≫ Qh.map (η H) ≫ inv (ε Qh) := by
    simp only [U, chainTraceUnitIso, singleFunctorObjUnitIso, Iso.trans_hom,
      Iso.symm_hom, Iso.app_hom,
      Functor.mapIso_hom, Functor.Monoidal.εIso_inv, asIso_inv]
    change ((singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app (𝟙_ _)).inv ≫
      ((singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app (𝟙_ _)).hom ≫ _ = _
    rw [Iso.inv_hom_id_assoc]
    rfl
  have ht : (QObjTensorQObjIsoOfKFlatRight D P hP).hom =
      ((E.app D).inv ⊗ₘ (E.app P).inv) ≫ μ Qh (H.obj D) (H.obj P) ≫
        Qh.map (μ H D P) ≫ (E.app (D ⊗ P)).hom := by
    rfl
  refine ⟨r, ?_, ?_⟩
  · change Q.obj D ◁ (E.app P).inv ≫
      (E.app D).inv ▷ Qh.obj (H.obj P) ≫ q.evaluation' = _
    erw [← tensorHom_def'_assoc, hqe]
    change _ = (QObjTensorQObjIsoOfKFlatRight D P hP).hom ≫ Q.map p.evaluation' ≫ U.hom
    have hn := iso_naturality_cancel E p.evaluation'
    change (E.app (D ⊗ P)).hom ≫ Q.map p.evaluation' ≫
      (E.app (𝟙_ _)).inv = Qh.map (H.map p.evaluation') at hn
    have heval : hp.evaluation' = μ H D P ≫ H.map p.evaluation' ≫ η H := rfl
    rw [heval, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      ht, hu]
    simp only [Category.assoc]
    simpa only [Category.assoc] using congrArg (fun f ↦
      ((E.app D).inv ⊗ₘ (E.app P).inv) ≫
      μ Qh (H.obj D) (H.obj P) ≫ Qh.map (μ H D P) ≫ f ≫
        Qh.map (η H) ≫ inv (ε Qh)) hn.symm
  · apply (cancel_mono (QObjTensorQObjIsoOfKFlatLeft P D hP).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change ((q.coevaluation' ≫ Qh.obj (H.obj P) ◁ (E.app D).hom) ≫
      (E.app P).hom ▷ Q.obj D) ≫ _ = _
    simp only [Category.assoc]
    erw [← tensorHom_def'_assoc]
    have ht' : (QObjTensorQObjIsoOfKFlatLeft P D hP).hom =
        ((E.app P).inv ⊗ₘ (E.app D).inv) ≫ μ Qh (H.obj P) (H.obj D) ≫
          Qh.map (μ H P D) ≫ (E.app (P ⊗ D)).hom := rfl
    change _ = U.inv ≫ Q.map p.coevaluation'
    apply (cancel_epi U.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [hu, hqc, ht']
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    erw [reassoc_of% (tensor_iso_cancel (E.app P) (E.app D))]
    rw [IsIso.inv_hom_id_assoc]
    have hcoev : hp.coevaluation' = ε H ≫ H.map p.coevaluation' ≫ δ H P D := rfl
    rw [hcoev, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]
    have hunit : Qh.map (η H) ≫ Qh.map (ε H) = 𝟙 _ := by
      exact (Qh.map_comp _ _).symm.trans
        ((congrArg Qh.map (Functor.Monoidal.η_ε H)).trans (Qh.map_id _))
    have htensor : Qh.map (δ H P D) ≫ Qh.map (μ H P D) = 𝟙 _ := by
      exact (Qh.map_comp _ _).symm.trans
        ((congrArg Qh.map (Functor.Monoidal.δ_μ H P D)).trans (Qh.map_id _))
    rw [reassoc_of% hunit, reassoc_of% htensor]
    have hn := E.hom.naturality p.coevaluation'
    change Qh.map (H.map p.coevaluation') ≫ (E.app (P ⊗ D)).hom =
      (E.app (𝟙_ _)).hom ≫ Q.map p.coevaluation' at hn
    rw [hn, Iso.inv_hom_id_assoc]

private theorem dualiso_pair {C : Type*} [Category C] [MonoidalCategory C]
    {X Y Z : C} (p : ExactPairing X Y) (q : ExactPairing X Z) :
    q.evaluation' = (rightDualIso p q).inv ▷ X ≫ p.evaluation' ∧
      q.coevaluation' = p.coevaluation' ≫ X ◁ (rightDualIso p q).hom := by
  constructor
  · symm
    exact (by
      simpa only [rightDualIso, ExactPairing.evaluation, whiskerLeft_id, Category.id_comp] using
        (@rightAdjointMate_comp_evaluation C _ _ X X ⟨Y⟩ ⟨Z⟩ (𝟙 X)))
  · symm
    simpa only [rightDualIso, ExactPairing.coevaluation, id_whiskerRight, Category.comp_id] using
      (@coevaluation_comp_rightAdjointMate C _ _ X X ⟨Z⟩ ⟨Y⟩ (𝟙 X))

private theorem chainTrace_derived_trace (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (s : ModuleCat.StrictPerfectCoefficientPackage P)
    (hP : IsPerfectRingComplex (Q.obj P)) (v : P ⟶ P) :
    perfectCategoricalTrace (Q.obj P) hP (Q.map v) = chainSupertrace s a b v := by
  let := perfectTraceCanonicalBraiding (ModuleCat.{u} A)
  let := perfectTraceHasRightDual (Q.obj P) hP
  let : ∀ n, HasRightDual (P.X n) := chainTraceFrameHasDual s
  let : ExactPairing (Q.obj P) (perfectTraceDual (Q.obj P)) :=
    (perfectTraceHasRightDual (Q.obj P) hP).exact
  let H := HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)
  let φ : Q.obj P ≅ Qh.obj (H.obj P) := ((quotientCompQhIso _).app P).symm
  let : ExactPairing (Qh.obj (H.obj P)) (perfectTraceDual (Q.obj P)) :=
    exactPairingCongrLeft φ.symm
  let : HasRightDual (Qh.obj (H.obj P)) := ⟨perfectTraceDual (Q.obj P)⟩
  have hh : Q.map v ≫ φ.hom = φ.hom ≫ Qh.map (H.map v) := by
    exact (quotientCompQhIso _).inv.naturality v
  unfold perfectCategoricalTrace
  rw [trace_eq_of_iso φ (Q.map v) (Qh.map (H.map v)) hh,
    trace_Qh_map_quotient_map (fun X Y _ _ ↦ braiding_hom_μ_Qh X Y) P a b v]
  let := CochainComplex.hasRightDual P a b
  let := chainTracePairing s a b
  have hT : trace v = (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).map
      (algebraMap A (End (𝟙_ (ModuleCat.{u} A)))
        (chainSupertrace s a b v)) := by
    rw [trace_eq_of_exactPairing (Y := perfectTraceModelDual P)]
    change (chainTracePairing s a b).coevaluation' ≫ v ▷ perfectTraceModelDual P ≫
      (CochainComplex.Monoidal.braiding P (perfectTraceModelDual P)).hom ≫
      (chainTracePairing s a b).evaluation' = _
    rw [chainTracePairing_trace s s a b v]
    congr 2
  rw [hT, ε_Qh_comp_map_single_map_algebraMap_comp_inv]
  unfold perfectTraceScalar
  let r : A := chainSupertrace s a b v
  change ((singleFunctor (ModuleCat.{u} A) 0).preimage
      ((singleFunctorObjUnitIso (ModuleCat.{u} A)).hom ≫
        algebraMap A (End (𝟙_ (DerivedCategory (ModuleCat.{u} A)))) r ≫
        (singleFunctorObjUnitIso (ModuleCat.{u} A)).inv)).hom 1 = r
  have hpre : (singleFunctor (ModuleCat.{u} A) 0).preimage
      ((singleFunctorObjUnitIso (ModuleCat.{u} A)).hom ≫
        algebraMap A (End (𝟙_ (DerivedCategory (ModuleCat.{u} A)))) r ≫
        (singleFunctorObjUnitIso (ModuleCat.{u} A)).inv) =
      algebraMap A (End (𝟙_ (ModuleCat.{u} A))) r := by
    apply (singleFunctor (ModuleCat.{u} A) 0).map_injective
    rw [Functor.map_preimage]
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      End.one_def, End.one_def]
    rw [Linear.smul_comp, Linear.comp_smul]
    simp only [Category.id_comp, Iso.hom_inv_id]
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  rw [hpre]
  rw [Algebra.algebraMap_eq_smul_one, End.one_def]
  change (r • (LinearMap.id : A →ₗ[A] A)) 1 = r
  simp

private theorem chainTrace_representative (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (b : ℤ) [P.IsStrictlyLE b]
    (hp : ∀ n, Module.Projective A (P.X n)) (v : Q.obj P ⟶ Q.obj P) :
    ∃ w : P ⟶ P, Q.map w = v := by
  let : ∀ n, Module.Projective A (P.X n) := hp
  let : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  let H := HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)
  let e := (quotientCompQhIso (ModuleCat.{u} A)).app P
  obtain ⟨f, hf⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P (H.obj P)).surjective
    (e.hom ≫ v ≫ e.inv)
  obtain ⟨w, hw⟩ := H.map_surjective f
  refine ⟨w, ?_⟩
  have hn := (quotientCompQhIso (ModuleCat.{u} A)).hom.naturality w
  change Qh.map (H.map w) ≫ e.hom = e.hom ≫ Q.map w at hn
  rw [hw, hf] at hn
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    cancel_epi] using hn.symm

private theorem chainTrace_eval_transport {P T : DerivedCategory (ModuleCat.{u} A)} (e : P ≅ T) :
    perfectTraceEvaluation T = (perfectTraceDualMap e.hom ⊗ₘ e.inv) ≫
      perfectTraceEvaluation P := by
  let := perfectTraceCanonicalBraiding (ModuleCat.{u} A)
  exact canonical_eval_transport e

private theorem chainTrace_trace_transport {P T : DerivedCategory (ModuleCat.{u} A)}
    (hP : IsPerfectRingComplex P) (hT : IsPerfectRingComplex T) (e : P ≅ T) (v : P ⟶ P) :
    perfectCategoricalTrace T hT (e.inv ≫ v ≫ e.hom) = perfectCategoricalTrace P hP v := by
  let := perfectTraceCanonicalBraiding (ModuleCat.{u} A)
  let := perfectTraceHasRightDual P hP
  let := perfectTraceHasRightDual T hT
  unfold perfectCategoricalTrace
  congr 1
  symm
  apply trace_eq_of_iso e
  simp
private theorem chainTrace_coev_transport {P T : DerivedCategory (ModuleCat.{u} A)}
    (hP : IsPerfectRingComplex P) (hT : IsPerfectRingComplex T) (e : P ≅ T) :
    perfectTraceCoevaluation T hT = perfectTraceCoevaluation P hP ≫
      (e.hom ⊗ₘ perfectTraceDualMap e.inv) := by
  let := perfectTraceCanonicalBraiding (ModuleCat.{u} A)
  let p : ExactPairing P (perfectTraceDual P) := (perfectTraceHasRightDual P hP).exact
  let t : ExactPairing T (perfectTraceDual T) := (perfectTraceHasRightDual T hT).exact
  let j : perfectTraceDual T ≅ perfectTraceDual P :=
    { hom := perfectTraceDualMap e.hom
      inv := perfectTraceDualMap e.inv
      hom_inv_id := by
        change (MonoidalClosed.pre e.hom).app _ ≫ (MonoidalClosed.pre e.inv).app _ = _
        rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, Iso.inv_hom_id,
          MonoidalClosed.pre_id]
        rfl
      inv_hom_id := by
        change (MonoidalClosed.pre e.inv).app _ ≫ (MonoidalClosed.pre e.hom).app _ = _
        rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, Iso.hom_inv_id,
          MonoidalClosed.pre_id]
        rfl }
  let := p
  let q : ExactPairing T (perfectTraceDual T) := exactPairingCongr e.symm j
  have he : t.evaluation' = q.evaluation' := by
    change perfectTraceEvaluation T = perfectTraceDual T ◁ e.inv ≫
      perfectTraceDualMap e.hom ▷ P ≫ perfectTraceEvaluation P
    rw [← tensorHom_def'_assoc]
    exact canonical_eval_transport e
  have hc := chainTrace_coev_eq t q he
  change perfectTraceCoevaluation T hT =
    (perfectTraceCoevaluation P hP ≫ P ◁ j.inv) ≫ e.hom ▷ perfectTraceDual T at hc
  simpa only [tensorHom_def', Category.assoc] using hc

private theorem chainTrace_descent
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (s : ModuleCat.StrictPerfectCoefficientPackage P)
    (hP : IsPerfectRingComplex (Q.obj P)) :
    ∃ (hflat : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P)
      (δ : Q.obj (perfectTraceModelDual P) ≅ perfectTraceDual (Q.obj P)),
      perfectTraceEvaluation (Q.obj P) = (δ.inv ⊗ₘ 𝟙 (Q.obj P)) ≫
        (QObjTensorQObjIsoOfKFlatRight (perfectTraceModelDual P) P hflat).hom ≫
        Q.map (chainTracePairing s a b).evaluation' ≫ chainTraceUnitIso.hom ∧
      perfectTraceCoevaluation (Q.obj P) hP =
        chainTraceUnitIso.inv ≫ Q.map (chainTracePairing s a b).coevaluation' ≫
          (QObjTensorQObjIsoOfKFlatLeft P (perfectTraceModelDual P) hflat).inv ≫
            (𝟙 (Q.obj P) ⊗ₘ δ.hom) := by
  let := perfectTraceCanonicalBraiding (ModuleCat.{u} A)
  let : ∀ n, HasRightDual (P.X n) := chainTraceFrameHasDual s
  have hf : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P :=
    CochainComplex.kFlat_of_bounded_of_flat P a b
      (fun n ↦ (isDualizable_of_hasRightDual _).flat)
  have hterms : ∀ n, IsDualizable (P.rightDual.X n) := fun n ↦
    ⟨{ rightDual := P.X (-n)
       exact := BraidedCategory.exactPairing_swap (P.X (-n)) (P.X (-n))ᘁ }⟩
  have hd : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat
      (perfectTraceModelDual P) :=
    ObjectProperty.prop_of_iso _ (chainTraceDualIso s).symm
      (CochainComplex.kFlat_of_bounded_of_flat P.rightDual (-b) (-a)
        (fun n ↦ (hterms n).flat))
  obtain ⟨q, hqe, hqc⟩ := chainTrace_derived_pairing P (perfectTraceModelDual P)
    (chainTracePairing s a b) hf hd
  let p : ExactPairing (Q.obj P) (perfectTraceDual (Q.obj P)) :=
    (perfectTraceHasRightDual (Q.obj P) hP).exact
  refine ⟨hf, rightDualIso q p, ?_, ?_⟩
  · have he := (dualiso_pair q p).1
    change perfectTraceEvaluation (Q.obj P) = _ at he
    rw [hqe] at he
    simpa only [tensorHom_id, Category.assoc] using he
  · have hc := (dualiso_pair q p).2
    change perfectTraceCoevaluation (Q.obj P) hP = _ at hc
    rw [hqc] at hc
    simpa only [id_tensorHom, Category.assoc] using hc

end

/-- The explicit evaluation and frame coevaluation are chain maps, are independent of
frames, satisfy both triangle identities, and compute the categorical trace and its
derived descent. Source: trace formula, `sk-p-trace/lem-trf-chain-supertrace`, parts
(a)--(c) and the concluding derived-invariance paragraph
(blueprint: lem-trf-chain-supertrace).

Proof (the twelve steps of the DAG node):
1. Split a finite free surjection onto each finite projective term. Its columns and
coordinate maps give a finite dual frame, empty for a zero term. Duals and finite tensors
are again finite projective by taking duals and tensors of these splittings (Stacks 00NX).
2. Expand each vector of one frame in another frame. The two finite double sums show
that the coevaluation tensor is independent of the splitting.
3. For maps between two framed modules expand both frames to prove rectangular cyclicity
of the frame trace. Taking an identity map proves frame independence. A basis gives the
diagonal matrix sum, and its identity trace is its rank times one.
4. The total Hom differential is the stated signed dual differential. Its square and
the tensor differential square vanish. The Koszul symmetry commutes with the differential;
the canonical associators and unitors preserve these differentials and satisfy coherence.
5. Evaluation is zero outside total degree zero. On degree minus one its two differential
terms have coefficients (-1)^(j+1) and (-1)^j and cancel.
6. In degree (i+1,-i) the differential of coevaluation is the sum of d(e_i) tensor eps_i
minus e_(i+1) tensor (eps_(i+1) composed with d). Expanding the two frames cancels it.
7. The two triangle composites are the frame identity and its dual identity, respectively.
8. Apply coevaluation, v, the symmetry, and evaluation. The symmetry contributes
(-1)^(i*(-i)) = (-1)^i, giving the alternating projective trace and the identity formula.
9. For a homotopy v-w=dh+hd use rectangular cyclicity and shift the finite summation index;
the two alternating sums cancel.
10. Projective terms are flat (lem-weil-pbc-projective-module-flat); bounded flat complexes
are K-flat (lem-pc-module-bounded-flat-kflat). The identity K-flat models compute the
derived tensor comparisons (lem-pc-derived-tensor-second-factor-functor). The fully faithful
single functor identifies the scalar with its value at one
(lem-weil-pbc-derived-single-fully-faithful).
11. The homotopy-to-derived Hom map from a bounded projective complex is bijective
(lem-pc-ring-derived-map-representative). Thus every derived endomorphism has a chain
representative, unique up to homotopy; step 9 defines the function on all endomorphisms.
12. Precomposition defines the dual of a chain map. Frame expansion proves naturality of
evaluation and coevaluation. The dual homotopy in degree j is (-1)^j times precomposition
by the original homotopy. Consequently derived representative isomorphisms transport both
duality maps, and naturality of the Koszul symmetry cancels the inverse pairs in the trace.
This is exactly perfectCategoricalTrace, hence its finite-coefficient specialization. -/
theorem chain_supertrace (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hfinite : ∀ i : ℤ, Module.Finite A (P.X i))
    (hprojective : ∀ i : ℤ, Module.Projective A (P.X i)) :
    (∃ s : ModuleCat.StrictPerfectCoefficientPackage P,
      ∀ i : ℤ, IsZero (P.X i) → s.N i = 0) ∧
    ∃ (ev : perfectTraceModelDual P ⊗ P ⟶ 𝟙_ _) (coev : 𝟙_ _ ⟶ P ⊗ perfectTraceModelDual P)
      (hP : IsPerfectRingComplex (Q.obj P)),
      (∀ (i : ℤ) (φ : (perfectTraceModelDual P).X (-i)) (p : P.X i),
        chainTraceUnitCoordinate.hom.hom
          ((ev.f 0).hom ((HomologicalComplex.ιTensorObj (perfectTraceModelDual P) P
            (-i) i 0 (neg_add_cancel i)).hom (φ ⊗ₜ[A] p))) =
        chainTraceUnitCoordinate.hom.hom ((φ.v i 0 (add_neg_cancel i)).hom p)) ∧
      (∀ n : ℤ, n ≠ 0 → ev.f n = 0) ∧
      (∀ s : ModuleCat.StrictPerfectCoefficientPackage P,
        (∀ i : ℤ, IsZero (P.X i) → s.N i = 0) →
        (coev.f 0).hom (chainTraceUnitCoordinate.inv.hom 1) =
          ∑ i ∈ Finset.Icc a b, ∑ r : Fin (s.N i), chainTraceFrameTensor s i r) ∧
      ((ρ_ (perfectTraceModelDual P)).inv ≫ perfectTraceModelDual P ◁ coev ≫
        (α_ (perfectTraceModelDual P) P (perfectTraceModelDual P)).inv ≫
        ev ▷ perfectTraceModelDual P ≫ (λ_ (perfectTraceModelDual P)).hom = 𝟙 _) ∧
      ((λ_ P).inv ≫ coev ▷ P ≫ (α_ P (perfectTraceModelDual P) P).hom ≫
        P ◁ ev ≫ (ρ_ P).hom = 𝟙 P) ∧
      (∀ (s : ModuleCat.StrictPerfectCoefficientPackage P) (v : P ⟶ P),
        coev ≫ v ▷ perfectTraceModelDual P ≫
          (CochainComplex.Monoidal.braiding P (perfectTraceModelDual P)).hom ≫ ev =
        (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map
          (ModuleCat.ofHom (chainSupertrace s a b v • LinearMap.id))) ∧
      (∀ (s t : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ)
        (v : P.X i ⟶ P.X i), chainTraceTerm s i v = chainTraceTerm t i v) ∧
      (∀ (s : ModuleCat.StrictPerfectCoefficientPackage P) (i : ℤ) (n : ℕ)
        (e : Module.Basis (Fin n) A (P.X i)) (v : P.X i ⟶ P.X i),
        chainTraceTerm s i v = ∑ r : Fin n, e.repr (v.hom (e r)) r ∧
        chainTraceTerm s i v = LinearMap.trace A (P.X i) v.hom ∧
        chainTraceTerm s i (𝟙 (P.X i)) = (n : A)) ∧
      (∀ s : ModuleCat.StrictPerfectCoefficientPackage P,
        perfectCategoricalTrace (Q.obj P) hP (𝟙 (Q.obj P)) =
          ∑ i ∈ Finset.Icc a b, i.negOnePow • chainTraceTerm s i (𝟙 (P.X i))) ∧
      (∀ (s : ModuleCat.StrictPerfectCoefficientPackage P) (v w : P ⟶ P),
        Nonempty (Homotopy v w) → chainSupertrace s a b v = chainSupertrace s a b w) ∧
      (∃ (hflat : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P)
        (δ : Q.obj (perfectTraceModelDual P) ≅ perfectTraceDual (Q.obj P)),
        perfectTraceEvaluation (Q.obj P) =
          (δ.inv ⊗ₘ 𝟙 (Q.obj P)) ≫
            (QObjTensorQObjIsoOfKFlatRight (perfectTraceModelDual P) P hflat).hom ≫
            Q.map ev ≫ chainTraceUnitIso.hom ∧
        perfectTraceCoevaluation (Q.obj P) hP =
          chainTraceUnitIso.inv ≫ Q.map coev ≫
            (QObjTensorQObjIsoOfKFlatLeft P (perfectTraceModelDual P) hflat).inv ≫
            (𝟙 (Q.obj P) ⊗ₘ δ.hom)) ∧
      (∀ (s : ModuleCat.StrictPerfectCoefficientPackage P) (v : P ⟶ P),
        perfectCategoricalTrace (Q.obj P) hP (Q.map v) = chainSupertrace s a b v) ∧
      (∀ v : Q.obj P ⟶ Q.obj P, ∃ w : P ⟶ P, Q.map w = v ∧
        ∀ s : ModuleCat.StrictPerfectCoefficientPackage P,
          perfectCategoricalTrace (Q.obj P) hP v = chainSupertrace s a b w) ∧
      (∀ (T : DerivedCategory (ModuleCat.{u} A)) (hT : IsPerfectRingComplex T)
        (e : Q.obj P ≅ T),
        perfectTraceCoevaluation T hT = perfectTraceCoevaluation (Q.obj P) hP ≫
          (e.hom ⊗ₘ perfectTraceDualMap e.inv) ∧
        perfectTraceEvaluation T = (perfectTraceDualMap e.hom ⊗ₘ e.inv) ≫
          perfectTraceEvaluation (Q.obj P) ∧
        ∀ v : Q.obj P ⟶ Q.obj P,
          perfectCategoricalTrace T hT (e.inv ≫ v ≫ e.hom) =
            perfectCategoricalTrace (Q.obj P) hP v) := by
  classical
  let := chainTraceComplexMonoidal (A := A)
  let := chainTraceDerivedMonoidal (A := A)
  obtain ⟨s, hs⟩ := chainTrace_exists_package P hfinite hprojective
  let pair : ExactPairing P (perfectTraceModelDual P) := chainTracePairing s a b
  have hP : IsPerfectRingComplex (Q.obj P) :=
    ⟨P, a, b, inferInstance, inferInstance,
      fun i ↦ ⟨hprojective i, hfinite i⟩, ⟨Iso.refl _⟩⟩
  refine ⟨⟨s, hs⟩, pair.evaluation', pair.coevaluation', hP,
    chainTracePairing_eval s a b, ?_, ?_, ?_, ?_, (fun t v ↦ chainTracePairing_trace s t a b v),
    chainTraceTerm_independent, chainTraceTerm_basis_trace, ?_,
    (fun t v w h ↦ chainSupertrace_homotopy t a b v w h), ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
      (ModuleCat.of A A) n hn).eq_of_tgt _ _
  · intro t ht
    have h := chainTracePairing_coev_independent s t a b
    change ((pair.coevaluation').f 0).hom _ = _
    rw [show pair.coevaluation' = (chainTracePairing t a b).coevaluation' from h]
    exact chainTracePairing_coev t a b
  · simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.id_comp, Category.comp_id] using
      congrArg (fun f ↦ (ρ_ (perfectTraceModelDual P)).inv ≫ f ≫
        (λ_ (perfectTraceModelDual P)).hom) pair.coevaluation_evaluation'
  · simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.id_comp, Category.comp_id] using
      congrArg (fun f ↦ (λ_ P).inv ≫ f ≫ (ρ_ P).hom) pair.evaluation_coevaluation'
  · intro t
    simpa only [CategoryTheory.Functor.map_id, chainSupertrace, HomologicalComplex.id_f] using
      chainTrace_derived_trace P a b t hP (𝟙 P)
  · exact chainTrace_descent P a b s hP
  · exact fun t v ↦ chainTrace_derived_trace P a b t hP v
  · intro v
    obtain ⟨w, hw⟩ := chainTrace_representative P b hprojective v
    refine ⟨w, hw, ?_⟩
    intro t
    rw [← hw]
    exact chainTrace_derived_trace P a b t hP w
  · intro T hT e
    exact ⟨chainTrace_coev_transport hP hT e, chainTrace_eval_transport e,
      fun v ↦ chainTrace_trace_transport hP hT e v⟩

end DerivedCategory
