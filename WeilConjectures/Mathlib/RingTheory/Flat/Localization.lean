/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Localization.BaseChange
public import WeilConjectures.Mathlib.RingTheory.Filtration
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Openness of the flat locus

Let `R` be a noetherian ring, `S` a finite type `R`-algebra and `M` a finite `S`-module. The set
of primes `q` of `S` such that `M_q` is flat over `R` is open (Stacks, Tag 00RC; Matsumura,
Theorem 24.3).

## Main results

- `Module.lTensor_localizedModule_injective_iff`: injectivity of `M_T ⊗ N' → M_T ⊗ N` in terms of
  the kernel of `M ⊗ N' → M ⊗ N`.
- `Module.flat_localizedModule_iff`: flatness of `M_T` in terms of the kernels of `M ⊗ J → M`.
- `Module.exists_notMem_pow_smul_eq_zero`: generic flatness relative to a prime of the base.
- `Module.Flat.exists_notMem_forall_flat_localizedModule`: openness of the flat locus.
-/

@[expose] public section

open TensorProduct

namespace Module

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
  [Module S M] [IsScalarTower R S M]

/-- Let `T` be a multiplicative subset of `S`. Then `M_T ⊗ N' → M_T ⊗ N` is injective if and only
if every element of the kernel of `M ⊗ N' → M ⊗ N` is killed by an element of `T`. -/
lemma lTensor_localizedModule_injective_iff (T : Submonoid S) {N N' : Type*} [AddCommGroup N]
    [Module R N] [AddCommGroup N'] [Module R N'] (f : N' →ₗ[R] N) :
    Function.Injective (f.lTensor (LocalizedModule T M)) ↔
      ∀ y : M ⊗[R] N', f.lTensor M y = 0 → ∃ t ∈ T, t • y = 0 := by
  set L := LocalizedModule T M
  set ℓ := LocalizedModule.mkLinearMap T M
  let g' := AlgebraTensorModule.rTensor R N' ℓ
  let g := AlgebraTensorModule.rTensor R N ℓ
  have : IsLocalizedModule T g' := IsLocalizedModule.rTensor (A := S) T ℓ
  have : IsLocalizedModule T g := IsLocalizedModule.rTensor (A := S) T ℓ
  let fM := AlgebraTensorModule.lTensor S M f
  let fL := AlgebraTensorModule.lTensor S L f
  have hsq (y : M ⊗[R] N') : fL (g' y) = g (fM y) := by
    induction y with
    | zero => simp
    | add y z hy hz => rw [map_add, map_add, map_add, map_add, hy, hz]
    | tmul m n => rfl
  constructor
  · intro h y hy
    have h1 : g' y = 0 := by
      apply h
      rw [map_zero]
      change fL (g' y) = 0
      rw [hsq]
      change g (f.lTensor M y) = 0
      rw [hy, map_zero]
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff T (f := g')).mp h1
    exact ⟨t, t.2, ht⟩
  · intro h
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨⟨y, s⟩, hs⟩ := IsLocalizedModule.surj T g' w
    simp only at hs
    have h1 : g (fM y) = 0 := by
      rw [← hsq, ← hs, Submonoid.smul_def, map_smul]
      change (s : S) • f.lTensor L w = 0
      rw [hw, smul_zero]
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff T (f := g)).mp h1
    rw [Submonoid.smul_def, ← map_smul] at ht
    obtain ⟨t', ht', ht'y⟩ := h _ ht
    have h2 : g' y = 0 := by
      rw [IsLocalizedModule.eq_zero_iff T]
      exact ⟨⟨t' * t, mul_mem ht' t.2⟩, by rw [Submonoid.smul_def, mul_smul]; exact ht'y⟩
    rw [h2, Submonoid.smul_def] at hs
    have hu := IsLocalizedModule.map_units g' s
    have : (algebraMap S (Module.End S _) s) w = (algebraMap S (Module.End S _) s) 0 := by
      rw [map_zero, Module.algebraMap_end_apply, hs]
    exact (Module.End.isUnit_iff _).mp hu |>.1 this

/-- Let `T` be a multiplicative subset of `S`. Then `M_T` is flat over `R` if and only if every
element of the kernel of `M ⊗ J → M`, `J` an ideal of `R`, is killed by an element of `T`. -/
lemma flat_localizedModule_iff (T : Submonoid S) :
    Flat R (LocalizedModule T M) ↔ ∀ (J : Ideal R) (y : M ⊗[R] J),
      J.subtype.lTensor M y = 0 → ∃ t ∈ T, t • y = 0 := by
  rw [Flat.iff_lTensor_injective']
  exact forall_congr' fun J ↦ lTensor_localizedModule_injective_iff T J.subtype

universe v in
/-- **Generic flatness relative to a prime of the base.** Let `R` be noetherian, `p` a prime of
`R`, `S` a finite type `R`-algebra and `M` a finite `S`-module killed by `p`. Then there is
`a ∉ p` such that for every injective map `N' → N` of modules killed by `p`, every element of the
kernel of `M ⊗ N' → M ⊗ N` is killed by a power of `a`. This is generic flatness
(`Module.exists_flat_localizedModule_powers`) over the domain `R ⧸ p`. -/
theorem exists_notMem_pow_smul_eq_zero [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    [Algebra.FiniteType R S] [Module.Finite S M] (hM : ∀ r ∈ p, ∀ m : M, r • m = 0) :
    ∃ a ∉ p, ∀ (N N' : Type v) [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'],
      (∀ r ∈ p, ∀ n : N, r • n = 0) → (∀ r ∈ p, ∀ n : N', r • n = 0) →
      ∀ f : N' →ₗ[R] N, Function.Injective f →
      ∀ y : M ⊗[R] N', f.lTensor M y = 0 → ∃ k : ℕ, a ^ k • y = 0 := by
  have hMt : IsTorsionBySet R M p := fun m r ↦ hM r r.2 m
  have hMS : IsTorsionBySet S M (p.map (algebraMap R S)) := by
    intro m ⟨s, hs⟩
    change s • m = 0
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨r, hr, rfl⟩ := hs
      rw [algebraMap_smul]
      exact hM r hr m
    | zero => exact zero_smul _ _
    | add s t _ _ hs ht => rw [add_smul, hs, ht, add_zero]
    | smul s t _ ht => rw [smul_eq_mul, mul_smul, ht, smul_zero]
  let := hMt.module
  let := hMS.module
  let : Algebra (R ⧸ p) (S ⧸ p.map (algebraMap R S)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsScalarTower (R ⧸ p) (S ⧸ p.map (algebraMap R S)) M := by
    refine ⟨fun a s m ↦ ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    have h1 : Ideal.Quotient.mk p a • Ideal.Quotient.mk (p.map (algebraMap R S)) s =
        Ideal.Quotient.mk (p.map (algebraMap R S)) (algebraMap R S a * s) := by
      rw [Algebra.smul_def]
      rfl
    rw [h1]
    erw [Module.IsTorsionBySet.mk_smul]
    change (algebraMap R S a * s) • m = a • (s • m)
    rw [mul_smul, algebraMap_smul]
  have : Algebra.FiniteType R (S ⧸ p.map (algebraMap R S)) :=
    Algebra.FiniteType.trans (S := S) ‹_› inferInstance
  have : IsScalarTower R (R ⧸ p) (S ⧸ p.map (algebraMap R S)) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ rfl
  have : Algebra.FiniteType (R ⧸ p) (S ⧸ p.map (algebraMap R S)) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  have : Module.Finite (S ⧸ p.map (algebraMap R S)) M := by
    obtain ⟨σ, hσ⟩ := Module.Finite.fg_top (R := S) (M := M)
    refine ⟨⟨σ, eq_top_iff.mpr fun m hm' ↦ ?_⟩⟩
    clear hm'
    have hm : m ∈ Submodule.span S (σ : Set M) := hσ ▸ trivial
    induction hm using Submodule.span_induction with
    | mem m hm => exact Submodule.subset_span hm
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul s m _ hm => exact Submodule.smul_mem _ (Ideal.Quotient.mk _ s) hm
  obtain ⟨ā, hā, hflat⟩ := exists_flat_localizedModule_powers (R := R ⧸ p)
    (S := S ⧸ p.map (algebraMap R S)) M
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective ā
  refine ⟨a, fun ha ↦ hā (Ideal.Quotient.eq_zero_iff_mem.mpr ha), ?_⟩
  intro N N' _ _ _ _ hN hN' f hf y hy
  let := (show IsTorsionBySet R N p from fun n r ↦ hN r r.2 n).module
  let := (show IsTorsionBySet R N' p from fun n r ↦ hN' r r.2 n).module
  let f' : N' →ₗ[R ⧸ p] N :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        rintro ⟨r⟩ n
        exact f.map_smul r n }
  have hinj : Function.Injective
      (f'.lTensor (LocalizedModule (Submonoid.powers (Ideal.Quotient.mk p a)) M)) :=
    Flat.lTensor_preserves_injective_linearMap f' hf
  rw [lTensor_localizedModule_injective_iff (R := R ⧸ p) (S := R ⧸ p)] at hinj
  have hsurj : Function.Surjective (algebraMap R (R ⧸ p)) := Ideal.Quotient.mk_surjective
  have : CompatibleSMul R (R ⧸ p) M N := CompatibleSMul.of_algebraMap_surjective _ _ hsurj
  have : CompatibleSMul R (R ⧸ p) M N' := CompatibleSMul.of_algebraMap_surjective _ _ hsurj
  let e' := equivOfCompatibleSMul R (R ⧸ p) R M N'
  let e := equivOfCompatibleSMul R (R ⧸ p) R M N
  have hcomm (z : M ⊗[R ⧸ p] N') : e (f'.lTensor M z) = f.lTensor M (e' z) := by
    induction z with
    | zero => simp
    | add z w hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]
    | tmul m n => rfl
  obtain ⟨_, ⟨k, rfl⟩, ht⟩ := hinj (e'.symm y) (by
    apply e.injective
    rw [hcomm, LinearEquiv.apply_symm_apply, hy, map_zero])
  refine ⟨k, ?_⟩
  have hsmul (z : M ⊗[R ⧸ p] N') : a ^ k • z = (Ideal.Quotient.mk p a) ^ k • z := by
    induction z with
    | zero => simp
    | add z w hz hw => rw [smul_add, smul_add, hz, hw]
    | tmul m n =>
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', ← map_pow]
      rfl
  apply e'.symm.injective
  rw [map_zero, map_smul, hsmul, ht]

omit [Module R M] [IsScalarTower R S M] in
lemma _root_.Submodule.restrictScalars_map_smul_top [Module R M] [IsScalarTower R S M]
    (I : Ideal R) :
    (I.map (algebraMap R S) • (⊤ : Submodule S M)).restrictScalars R =
      I • (⊤ : Submodule R M) := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    induction hx using Submodule.smul_induction_on' with
    | smul a ha m _ =>
      induction ha using Submodule.span_induction generalizing m with
      | mem a ha =>
        obtain ⟨r, hr, rfl⟩ := ha
        rw [algebraMap_smul]
        exact Submodule.smul_mem_smul hr trivial
      | zero => rw [zero_smul]; exact zero_mem _
      | add a b _ _ ha hb =>
        rw [add_smul]; exact Submodule.add_mem _ (ha m trivial) (hb m trivial)
      | smul s a _ ha => rw [smul_eq_mul, mul_comm, mul_smul]; exact ha _ trivial
    | add x _ y _ hx hy => exact Submodule.add_mem _ hx hy
  · rw [Submodule.smul_le]
    intro r hr m _
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul S r m]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial

/-- **Openness of the flat locus** (Stacks, Tag 00RC; Matsumura, Theorem 24.3). Let `R` be a
noetherian ring, `S` a finite type `R`-algebra and `M` a finite `S`-module. If `M_P` is flat over
`R` for a prime `P` of `S`, then there is `g ∉ P` such that `M_Q` is flat over `R` for every prime
`Q` of `S` not containing `g`. -/
theorem Flat.exists_notMem_forall_flat_localizedModule [IsNoetherianRing R]
    [Algebra.FiniteType R S] [Module.Finite S M] (P : Ideal S) [P.IsPrime]
    (hP : Flat R (LocalizedModule P.primeCompl M)) :
    ∃ g ∉ P, ∀ (Q : Ideal S) [Q.IsPrime], g ∉ Q → Flat R (LocalizedModule Q.primeCompl M) := by
  classical
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  suffices H : ∃ g ∉ P, ∀ Q : Ideal S, Q.IsPrime → g ∉ Q →
      ∀ [Q.IsPrime], Flat R (LocalizedModule Q.primeCompl M) by
    obtain ⟨g, hg, H⟩ := H
    exact ⟨g, hg, fun Q _ hgQ ↦ H Q ‹_› hgQ⟩
  refine Ideal.exists_notMem_forall_of_isNoetherianRing
    (fun Q ↦ ∀ [Q.IsPrime], Flat R (LocalizedModule Q.primeCompl M)) ?_ ?_ P (by exact hP)
  · intro Q Q' hQp _ hle hQ _
    have hQ := @hQ hQp
    rw [flat_localizedModule_iff] at hQ ⊢
    intro J y hy
    obtain ⟨t, ht, hty⟩ := hQ J y hy
    exact ⟨t, fun h ↦ ht (hle h), hty⟩
  intro Q₀ hQ₀ hU
  have := hQ₀
  have hU := @hU hQ₀
  set p₀ := Q₀.comap (algebraMap R S)
  -- (1) The kernel of `M ⊗ p₀ → M` is killed by a single `b ∉ Q₀`.
  set K := LinearMap.ker (AlgebraTensorModule.lTensor S M p₀.subtype)
  have : Module.Finite R p₀ := IsNoetherian.finite R p₀
  have : Module.Finite S (M ⊗[R] p₀) :=
    Module.Finite.equiv (AlgebraTensorModule.cancelBaseChange R S S M p₀)
  obtain ⟨σ, hσ⟩ := (IsNoetherian.noetherian K : K.FG)
  have hσK : ∀ y ∈ σ, ∃ t ∉ Q₀, t • y = 0 := by
    intro y hy
    have hyK : y ∈ K := hσ ▸ Submodule.subset_span hy
    obtain ⟨t, ht, hty⟩ := (flat_localizedModule_iff _).mp hU p₀ y hyK
    exact ⟨t, ht, hty⟩
  choose! t ht hty using hσK
  set b := ∏ y ∈ σ, t y
  have hb : b ∉ Q₀ := by
    rw [Ideal.IsPrime.prod_mem_iff]
    push Not
    exact fun y hy ↦ ht y hy
  have hbK : ∀ y ∈ K, b • y = 0 := by
    intro y hy
    rw [← hσ] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      change (∏ y ∈ σ, t y) • y = 0
      rw [← Finset.prod_erase_mul σ t hy, mul_smul, hty y hy, smul_zero]
    | zero => exact smul_zero _
    | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul s y _ hy => rw [smul_comm, hy, smul_zero]
  -- (2) Generic flatness of `M ⧸ p₀ M` over `R ⧸ p₀`.
  set P₀ := p₀.map (algebraMap R S) • (⊤ : Submodule S M)
  have hkill : ∀ r ∈ p₀, ∀ m : M ⧸ P₀, r • m = 0 := by
    intro r hr m
    induction m using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← algebraMap_smul S r m]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial
  obtain ⟨a, ha, hGF⟩ := exists_notMem_pow_smul_eq_zero.{_, _, _, _} (S := S) p₀ (M := M ⧸ P₀) hkill
  have ha' : algebraMap R S a ∉ Q₀ := ha
  refine ⟨b * algebraMap R S a, fun h ↦ (hQ₀.mul_mem_iff_mem_or_mem.mp h).elim hb ha', ?_⟩
  intro Q hQ hle hg _
  have hbQ : b ∉ Q := fun h ↦ hg (Q.mul_mem_right _ h)
  have haQ : algebraMap R S a ∉ Q := fun h ↦ hg (Q.mul_mem_left _ h)
  -- (3) The local criterion at `Q`.
  have hπ : (Submodule.restrictScalars R P₀) = p₀ • (⊤ : Submodule R M) :=
    Submodule.restrictScalars_map_smul_top p₀
  let φ : (M ⧸ p₀ • (⊤ : Submodule R M)) ≃ₗ[R] M ⧸ P₀ :=
    (Submodule.quotEquivOfEq _ _ hπ.symm).trans (Submodule.Quotient.restrictScalarsEquiv R P₀)
  have hbij (N : Type u_1) [AddCommGroup N] [Module R N] (hN : ∀ r ∈ p₀, ∀ n : N, r • n = 0) :
      Function.Bijective ((P₀.mkQ.restrictScalars R).rTensor N) := by
    have : (P₀.mkQ.restrictScalars R).rTensor N =
        φ.toLinearMap.rTensor N ∘ₗ (p₀ • (⊤ : Submodule R M)).mkQ.rTensor N := by
      rw [← LinearMap.rTensor_comp]
      rfl
    rw [this, LinearMap.coe_comp]
    exact (LinearEquiv.bijective (φ.rTensor N)).comp
      (Flat.bijective_rTensor_mkQ_of_smul_eq_zero p₀ hN)
  have hjac : p₀.map (algebraMap R (Localization.AtPrime Q)) ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply R S (Localization.AtPrime Q),
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q]
    exact hle hr
  refine Flat.of_lTensor_injective_of_forall (S := Localization.AtPrime Q) p₀ hjac ?_ ?_
  · intro N _ _ hN N'
    rw [lTensor_localizedModule_injective_iff]
    intro y hy
    have hN' : ∀ r ∈ p₀, ∀ n : N', r • n = 0 := fun r hr n ↦ Subtype.ext (hN r hr n)
    set π := P₀.mkQ.restrictScalars R
    have h1 : N'.subtype.lTensor (M ⧸ P₀) (π.rTensor N' y) = 0 := by
      rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
        LinearMap.comp_apply, hy, map_zero]
    obtain ⟨k, hk⟩ := hGF N N' hN hN' N'.subtype Subtype.val_injective _ h1
    refine ⟨algebraMap R S a ^ k, fun h ↦ haQ (hQ.mem_of_pow_mem k h), ?_⟩
    apply (hbij (↥N') hN').1
    rw [map_zero, ← map_pow, algebraMap_smul, map_smul, hk]
  · rw [lTensor_localizedModule_injective_iff]
    intro y hy
    exact ⟨b, hbQ, hbK y hy⟩

end Module
