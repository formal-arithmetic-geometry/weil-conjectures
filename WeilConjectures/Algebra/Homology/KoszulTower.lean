/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# The Koszul tower of a finite sequence

Let `R` be a commutative ring and `f = (f₁, …, f_r)` a finite sequence in `R`. The Koszul
complex `K_•(f) = ⋀^• R^r` (`ExteriorAlgebra.koszulComplex`, Stacks Tags 0622/0623) has the
differential given by contraction with the linear form `eᵢ ↦ fᵢ`. For `c, g : Fin r → R`, the
exterior powers of the diagonal map `eᵢ ↦ cᵢ eᵢ` form a chain map
`K_•(c * g) ⟶ K_•(g)` (`ExteriorAlgebra.koszulComplexMap`): it is the identity in degree `0`
and the multiplication by `c` in degree `1`, i.e. the tensor product over `j` of the two-term
chain maps `[R --cⱼgⱼ--> R] ⟶ [R --gⱼ--> R]` with components `cⱼ` and `1`.

In particular `m ↦ K_•(f^m)` with these transition maps is a tower of complexes, the *Koszul
tower* (`ExteriorAlgebra.koszulTower`). Its main property is that the positive-degree homology
is pro-zero when `R` is Noetherian (`ExteriorAlgebra.exists_homologyMap_koszulTower_eq_zero`):
the transition from level `b` to level `a` has image in `Iᵇ⁻ᵃ K_•(f^a)` in positive degrees
(`ExteriorAlgebra.koszulComplexMap_mem_smul_top`), the homology of `K_•(f^a)` is killed by the
ideal `(f₁ᵃ, …, f_rᵃ)` (`ExteriorAlgebra.smul_mem_range_koszulBoundary`), which contains a power
of `I = (f₁, …, f_r)`, and the Artin–Rees lemma compares `Iᵏ K ∩ Z` with `Iᵏ⁻ᶜ Z` for the cycles
`Z` of the finite free module `K = K_n(f^a)`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace ExteriorAlgebra

variable {R : Type u} [CommRing R] {r : ℕ}

/-! ### Functoriality of the contraction -/

section Contraction

variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Contraction is natural with respect to the maps of exterior algebras induced by linear
maps: `φ ⌋ (⋀ D x) = ⋀ D ((φ ∘ D) ⌋ x)`. -/
lemma contractLeft_map (φ : Module.Dual R N) (D : M →ₗ[R] N) (x : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R N)) φ (map D x) =
      map D (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) (φ ∘ₗ D) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap a =>
    rw [AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap,
      CliffordAlgebra.contractLeft_algebraMap, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | ι_mul x m hx =>
    have h₁ := CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm R N)) φ (D m)
      (map D x)
    have h₂ := CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm R M)) (φ ∘ₗ D) m x
    change CliffordAlgebra.contractLeft φ (map D (ι R m * x)) = map D
      (CliffordAlgebra.contractLeft (φ ∘ₗ D) (ι R m * x))
    rw [map_mul, map_apply_ι]
    change CliffordAlgebra.contractLeft φ (ι R (D m) * map D x) = _
    rw [h₁, hx]
    change _ = map D (CliffordAlgebra.contractLeft (φ ∘ₗ D) (ι R m * x))
    rw [h₂, map_sub, map_smul, map_mul, map_apply_ι]
    rfl

/-- The map of exterior algebras induced by a linear map preserves the exterior powers. -/
lemma map_mem_exteriorPower (D : M →ₗ[R] N) (n : ℕ) {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^n M) : map D x ∈ ⋀[R]^n N := by
  have : (⋀[R]^n M).map (map D).toLinearMap ≤ ⋀[R]^n N := by
    rw [exteriorPower, exteriorPower, Submodule.map_pow]
    refine pow_le_pow_left' ?_ n
    rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    exact ⟨D m, (map_apply_ι D m).symm⟩
  exact this (Submodule.mem_map_of_mem hx)

/-- Left multiplication by a vector raises the exterior degree by one. -/
lemma ι_mul_mem_exteriorPower (v : M) (n : ℕ) {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^n M) : ι R v * x ∈ ⋀[R]^(n + 1) M := by
  rw [exteriorPower, pow_succ']
  exact Submodule.mul_mem_mul ⟨v, rfl⟩ hx

end Contraction

/-! ### The transition maps -/

/-- The diagonal endomorphism `eᵢ ↦ cᵢ eᵢ` of `R^r`. -/
noncomputable def diagonalMap (c : Fin r → R) : (Fin r →₀ R) →ₗ[R] (Fin r →₀ R) :=
  Finsupp.linearCombination R fun i ↦ Finsupp.single i (c i)

lemma linearCombination_comp_diagonalMap (c g : Fin r → R) :
    Finsupp.linearCombination R g ∘ₗ diagonalMap c = Finsupp.linearCombination R (c * g) := by
  ext i
  simp [diagonalMap]

lemma diagonalMap_mul (c d : Fin r → R) :
    diagonalMap c ∘ₗ diagonalMap d = diagonalMap (c * d) := by
  ext i
  simp [diagonalMap, mul_comm]

lemma diagonalMap_one : diagonalMap (1 : Fin r → R) = LinearMap.id := by
  ext i
  simp [diagonalMap]

/-- The degree `n` component of the chain map `K_•(c * g) ⟶ K_•(g)`: the `n`-th exterior power
of the diagonal map `eᵢ ↦ cᵢ eᵢ`. -/
noncomputable def koszulMap (c : Fin r → R) (n : ℕ) :
    ⋀[R]^n (Fin r →₀ R) →ₗ[R] ⋀[R]^n (Fin r →₀ R) :=
  LinearMap.codRestrict (⋀[R]^n (Fin r →₀ R))
    ((map (diagonalMap c)).toLinearMap.comp (⋀[R]^n (Fin r →₀ R)).subtype)
    fun x ↦ map_mem_exteriorPower _ n x.2

@[simp]
lemma koszulMap_coe (c : Fin r → R) (n : ℕ) (x : ⋀[R]^n (Fin r →₀ R)) :
    (koszulMap c n x : ExteriorAlgebra R (Fin r →₀ R)) = map (diagonalMap c) x := rfl

lemma koszulMap_comp (c d : Fin r → R) (n : ℕ) :
    koszulMap c n ∘ₗ koszulMap d n = koszulMap (c * d) n := by
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, koszulMap_coe]
  rw [← AlgHom.comp_apply, map_comp_map, diagonalMap_mul]

lemma koszulMap_one (n : ℕ) : koszulMap (1 : Fin r → R) n = LinearMap.id := by
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  simp [diagonalMap_one, ExteriorAlgebra.map_id]

lemma koszulBoundary_koszulMap (c g : Fin r → R) (n : ℕ) :
    koszulBoundary R r g n ∘ₗ koszulMap c (n + 1) =
      koszulMap c n ∘ₗ koszulBoundary R r (c * g) n := by
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  change CliffordAlgebra.contractLeft (Finsupp.linearCombination R g)
    (map (diagonalMap c) (x : ExteriorAlgebra R (Fin r →₀ R))) =
      map (diagonalMap c) (CliffordAlgebra.contractLeft (Finsupp.linearCombination R (c * g))
        (x : ExteriorAlgebra R (Fin r →₀ R)))
  rw [contractLeft_map, linearCombination_comp_diagonalMap]

/-- The chain map `K_•(h) ⟶ K_•(g)`, for `h = c * g`, given by the exterior powers of the
diagonal map `eᵢ ↦ cᵢ eᵢ`. It is the identity in degree `0` and the diagonal map in degree
`1`. -/
noncomputable def koszulComplexMap (c g h : Fin r → R) (hh : h = c * g) :
    koszulComplex R r h ⟶ koszulComplex R r g :=
  ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (koszulMap c n)) fun n ↦ by
    subst hh
    simp only [koszulComplex, ChainComplex.of_d]
    rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp, koszulBoundary_koszulMap]

@[simp]
lemma koszulComplexMap_f (c g h : Fin r → R) (hh : h = c * g) (n : ℕ) :
    (koszulComplexMap c g h hh).f n = ModuleCat.ofHom (koszulMap c n) := rfl

lemma koszulComplexMap_one (g : Fin r → R) :
    koszulComplexMap 1 g g (one_mul g).symm = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  rw [koszulComplexMap_f, koszulMap_one]
  rfl

@[reassoc]
lemma koszulComplexMap_comp (c d g h k : Fin r → R) (hh : h = c * g) (hk : k = d * h) :
    koszulComplexMap d h k hk ≫ koszulComplexMap c g h hh =
      koszulComplexMap (c * d) g k (by rw [hk, hh, mul_comm c d, mul_assoc]) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext ?_
  exact koszulMap_comp c d n

/-! ### The Koszul tower -/

lemma pow_sub_mul_pow (f : Fin r → R) {a b : ℕ} (h : a ≤ b) : f ^ b = f ^ (b - a) * f ^ a := by
  rw [← pow_add, Nat.sub_add_cancel h]

/-- The Koszul tower `m ↦ K_•(f₁ᵐ, …, f_rᵐ)`, the transition map `K_•(f^b) ⟶ K_•(f^a)` for
`a ≤ b` being `koszulComplexMap` for `f^b = f^(b - a) * f^a` (multiplication by `fⱼᵇ⁻ᵃ` on the
`j`-th coordinate). -/
noncomputable def koszulTower (f : Fin r → R) : ℕᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ where
  obj m := koszulComplex R r (f ^ m.unop)
  map {m m'} h := koszulComplexMap (f ^ (m.unop - m'.unop)) (f ^ m'.unop) (f ^ m.unop)
    (pow_sub_mul_pow f (leOfHom h.unop))
  map_id m := by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
    simp only [Nat.sub_self, pow_zero, koszulComplexMap_f, koszulMap_one]
    rfl
  map_comp {m m' m''} h h' := by
    rw [koszulComplexMap_comp]
    have h₁ := leOfHom h.unop
    have h₂ := leOfHom h'.unop
    congr 1
    rw [← pow_add]
    congr 1
    omega

@[simp]
lemma koszulTower_map_f (f : Fin r → R) {m m' : ℕᵒᵖ} (h : m ⟶ m') (n : ℕ) :
    ((koszulTower f).map h).f n = ModuleCat.ofHom (koszulMap (f ^ (m.unop - m'.unop)) n) := rfl

/-! ### Images of the transition maps -/

lemma diagonalMap_mem_smul_top (c : Fin r → R) (x : Fin r →₀ R) :
    diagonalMap c x ∈ (Ideal.span (Set.range c)) • (⊤ : Submodule R (Fin r →₀ R)) := by
  rw [diagonalMap, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ ?_
  rw [show Finsupp.single i (c i) = c i • Finsupp.single i (1 : R) by simp]
  exact Submodule.smul_mem_smul (Ideal.subset_span ⟨i, rfl⟩) trivial

/-- In positive degrees, the image of the transition map `koszulMap c` lies in `(c) ⋀ⁿ R^r`:
every wedge `v₀ ∧ ⋯ ∧ vₙ` is sent to `D v₀ ∧ ⋯ ∧ D vₙ` and `D v₀ ∈ (c) R^r`. -/
lemma koszulMap_mem_smul_top (c : Fin r → R) (n : ℕ) (x : ⋀[R]^(n + 1) (Fin r →₀ R)) :
    koszulMap c (n + 1) x ∈
      (Ideal.span (Set.range c)) • (⊤ : Submodule R (⋀[R]^(n + 1) (Fin r →₀ R))) := by
  have hx : x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R (n + 1))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    have hval : koszulMap c (n + 1) (exteriorPower.ιMulti R (n + 1) v) =
        exteriorPower.ιMulti R (n + 1) (diagonalMap c ∘ v) := by
      ext
      simp [ExteriorAlgebra.map_apply_ιMulti]
      rfl
    rw [hval]
    let L := (exteriorPower.ιMulti R (n + 1)).toMultilinearMap.toLinearMap
      (diagonalMap c ∘ v) 0
    have hL : exteriorPower.ιMulti R (n + 1) (diagonalMap c ∘ v) = L (diagonalMap c (v 0)) := by
      simp only [L, MultilinearMap.toLinearMap_apply]
      exact congrArg _ (Function.update_eq_self 0 _).symm
    rw [hL]
    have := Submodule.mem_map_of_mem (f := L) (diagonalMap_mem_smul_top c (v 0))
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ a hy

/-! ### The homology of the Koszul complex is killed by the ideal -/

/-- Left multiplication by `eᵢ`, the null-homotopy of multiplication by `gᵢ`:
`d (eᵢ ∧ z) = gᵢ z - eᵢ ∧ d z`. -/
lemma koszulBoundary_ι_mul (g : Fin r → R) (n : ℕ) (i : Fin r)
    (z : ⋀[R]^(n + 1) (Fin r →₀ R)) :
    (koszulBoundary R r g (n + 1)
        ⟨ι R (Finsupp.single i (1 : R)) * (z : ExteriorAlgebra R (Fin r →₀ R)),
          ι_mul_mem_exteriorPower _ _ z.2⟩ : ExteriorAlgebra R (Fin r →₀ R)) =
      g i • (z : ExteriorAlgebra R (Fin r →₀ R)) -
        ι R (Finsupp.single i (1 : R)) *
          (koszulBoundary R r g n z : ExteriorAlgebra R (Fin r →₀ R)) :=
  (CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm R (Fin r →₀ R)))
    (Finsupp.linearCombination R g) _ _).trans (by
    simp
    rfl)

/-- The positive-degree cycles of `K_•(g)` multiplied by an element of `(g₁, …, g_r)` are
boundaries. -/
lemma smul_mem_range_koszulBoundary (g : Fin r → R) (n : ℕ) {z : ⋀[R]^(n + 1) (Fin r →₀ R)}
    (hz : koszulBoundary R r g n z = 0) {a : R} (ha : a ∈ Ideal.span (Set.range g)) :
    a • z ∈ LinearMap.range (koszulBoundary R r g (n + 1)) := by
  induction ha using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨i, rfl⟩ := hb
    refine ⟨⟨_, ι_mul_mem_exteriorPower (Finsupp.single i (1 : R)) _ z.2⟩, Subtype.ext ?_⟩
    rw [koszulBoundary_ι_mul, hz]
    simp
  | zero => simp
  | add b b' _ _ hb hb' => rw [add_smul]; exact add_mem hb hb'
  | smul b b' _ hb' => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ b hb'

/-! ### Pro-vanishing of the positive-degree Koszul homology -/

/-- **Pro-vanishing of the Koszul homology.** Let `R` be Noetherian and `I = (f₁, …, f_r)`. For
every level `a` and degree `n + 1 ≥ 1` there is a level `b ≥ a` such that the transition map
`K_•(f^b) ⟶ K_•(f^a)` sends the cycles of degree `n + 1` to boundaries. -/
theorem exists_koszulMap_mem_range [IsNoetherianRing R] (f : Fin r → R) (a n : ℕ) :
    ∃ k : ℕ, ∀ z : ⋀[R]^(n + 1) (Fin r →₀ R), koszulBoundary R r (f ^ (k + a)) n z = 0 →
      koszulMap (f ^ k) (n + 1) z ∈ LinearMap.range (koszulBoundary R r (f ^ a) (n + 1)) := by
  set I : Ideal R := Ideal.span (Set.range f)
  set Z : Submodule R (⋀[R]^(n + 1) (Fin r →₀ R)) := LinearMap.ker (koszulBoundary R r (f ^ a) n)
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul Z
  have hrad : I ≤ (Ideal.span (Set.range (f ^ a))).radical := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨a, Ideal.subset_span ⟨i, rfl⟩⟩
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (Submodule.fg_span (Set.finite_range f))
  refine ⟨c + N, fun z hz ↦ ?_⟩
  have hZ : koszulMap (f ^ (c + N)) (n + 1) z ∈ Z := by
    have := LinearMap.congr_fun (koszulBoundary_koszulMap (f ^ (c + N)) (f ^ a) n) z
    rw [LinearMap.mem_ker]
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    rw [this, ← pow_add, hz, map_zero]
  have hI : koszulMap (f ^ (c + N)) (n + 1) z ∈
      I ^ (c + N) • (⊤ : Submodule R (⋀[R]^(n + 1) (Fin r →₀ R))) := by
    refine Submodule.smul_mono_left ?_ (koszulMap_mem_smul_top _ n z)
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i) : f i ∈ I) _
  have hmem : koszulMap (f ^ (c + N)) (n + 1) z ∈ I ^ N • Z := by
    have h := hc (c + N) (Nat.le_add_right c N)
    rw [Nat.add_sub_cancel_left] at h
    have : koszulMap (f ^ (c + N)) (n + 1) z ∈
        I ^ (c + N) • (⊤ : Submodule R (⋀[R]^(n + 1) (Fin r →₀ R))) ⊓ Z := ⟨hI, hZ⟩
    rw [h] at this
    exact Submodule.smul_mono le_rfl inf_le_right this
  refine Submodule.smul_induction_on hmem (fun x hx y hy ↦ ?_) (fun _ _ ↦ add_mem)
  exact smul_mem_range_koszulBoundary (f ^ a) n hy (hN hx)

/-! ### Degree zero -/

section DegreeZero

variable {M : Type*} [AddCommGroup M] [Module R M]

lemma coe_zeroEquiv_symm (a : R) :
    ((exteriorPower.zeroEquiv R M).symm a : ExteriorAlgebra R M) = algebraMap R _ a := by
  rw [exteriorPower.zeroEquiv_symm_apply, Submodule.coe_smul, exteriorPower.ιMulti_apply_coe,
    ιMulti_zero_apply, Algebra.algebraMap_eq_smul_one]

lemma coe_eq_algebraMap_zeroEquiv (x : ⋀[R]^0 M) :
    (x : ExteriorAlgebra R M) = algebraMap R _ (exteriorPower.zeroEquiv R M x) := by
  conv_lhs => rw [← (exteriorPower.zeroEquiv R M).symm_apply_apply x]
  exact coe_zeroEquiv_symm _

lemma coe_oneEquiv_symm (v : M) :
    ((exteriorPower.oneEquiv R M).symm v : ExteriorAlgebra R M) = ι R v := by
  rw [exteriorPower.oneEquiv_symm_apply, exteriorPower.ιMulti_apply_coe, ιMulti_apply]
  simp

end DegreeZero

lemma koszulMap_zero (c : Fin r → R) : koszulMap c 0 = LinearMap.id := by
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  rw [koszulMap_coe, coe_eq_algebraMap_zeroEquiv x, AlgHom.commutes, LinearMap.id_apply]
  exact (coe_eq_algebraMap_zeroEquiv x).symm

/-- In degree one, the Koszul differential is `eᵢ ↦ gᵢ`, read through `⋀⁰ R^r ≅ R` and
`⋀¹ R^r ≅ R^r`. -/
lemma zeroEquiv_koszulBoundary_zero (g : Fin r → R) (x : ⋀[R]^1 (Fin r →₀ R)) :
    exteriorPower.zeroEquiv R _ (koszulBoundary R r g 0 x) =
      Finsupp.linearCombination R g (exteriorPower.oneEquiv R _ x) := by
  obtain ⟨v, rfl⟩ := (exteriorPower.oneEquiv R (Fin r →₀ R)).symm.surjective x
  rw [LinearEquiv.apply_symm_apply]
  apply (algebraMap_leftInverse (R := R) (Fin r →₀ R)).injective
  rw [← coe_eq_algebraMap_zeroEquiv]
  change CliffordAlgebra.contractLeft (Finsupp.linearCombination R g)
    ((exteriorPower.oneEquiv R _).symm v : ExteriorAlgebra R (Fin r →₀ R)) = _
  rw [coe_oneEquiv_symm, CliffordAlgebra.contractLeft_ι]

/-- The augmentation `⋀⁰ R^r ≅ R ⟶ R ⧸ J` of the Koszul complex. -/
noncomputable def koszulAug (J : Ideal R) : ⋀[R]^0 (Fin r →₀ R) →ₗ[R] R ⧸ J :=
  J.mkQ ∘ₗ (exteriorPower.zeroEquiv R _).toLinearMap

lemma koszulAug_apply (J : Ideal R) (x : ⋀[R]^0 (Fin r →₀ R)) :
    koszulAug J x = Ideal.Quotient.mk J (exteriorPower.zeroEquiv R _ x) := rfl

lemma koszulAug_surjective (J : Ideal R) : Function.Surjective (koszulAug (r := r) J) :=
  (Submodule.mkQ_surjective J).comp (exteriorPower.zeroEquiv R _).surjective

/-- The image of the Koszul differential `⋀¹ R^r ⟶ ⋀⁰ R^r ≅ R` is the ideal `(g₁, …, g_r)`. -/
lemma map_zeroEquiv_range_koszulBoundary_zero (g : Fin r → R) :
    (LinearMap.range (koszulBoundary R r g 0)).map (exteriorPower.zeroEquiv R _).toLinearMap =
      Ideal.span (Set.range g) := by
  rw [← LinearMap.range_comp]
  have : (exteriorPower.zeroEquiv R _).toLinearMap ∘ₗ koszulBoundary R r g 0 =
      Finsupp.linearCombination R g ∘ₗ (exteriorPower.oneEquiv R _).toLinearMap :=
    LinearMap.ext (zeroEquiv_koszulBoundary_zero g)
  rw [this, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    Finsupp.range_linearCombination]
  rfl

lemma koszulAug_comp_koszulBoundary (g : Fin r → R) {J : Ideal R}
    (hJ : Ideal.span (Set.range g) ≤ J) : koszulAug J ∘ₗ koszulBoundary R r g 0 = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  rw [LinearMap.comp_apply, koszulAug_apply, LinearMap.zero_apply,
    Ideal.Quotient.eq_zero_iff_mem]
  apply hJ
  rw [← map_zeroEquiv_range_koszulBoundary_zero]
  exact Submodule.mem_map_of_mem (LinearMap.mem_range_self _ x)

/-- The augmentation is a cokernel of the first Koszul differential: `H₀(K_•(g)) = R ⧸ (g)`. -/
lemma ker_koszulAug (g : Fin r → R) :
    LinearMap.ker (koszulAug (Ideal.span (Set.range g))) =
      LinearMap.range (koszulBoundary R r g 0) := by
  ext x
  rw [LinearMap.mem_ker, koszulAug_apply, Ideal.Quotient.eq_zero_iff_mem,
    ← map_zeroEquiv_range_koszulBoundary_zero, Submodule.mem_map_equiv,
    LinearEquiv.symm_apply_apply]

/-! ### Vanishing above the rank -/

instance subsingleton_exteriorPower_of_lt {n : ℕ} [Fact (r < n)] :
    Subsingleton (⋀[R]^n (Fin r →₀ R)) := by
  have hn : r < n := Fact.out
  have : IsEmpty (Set.powersetCard (Fin r) n) := by
    refine ⟨fun s ↦ ?_⟩
    have := s.2
    have h := Finset.card_le_univ (s : Finset (Fin r))
    simp only [Fintype.card_fin] at h
    rw [Set.powersetCard.mem_iff] at this
    omega
  exact ((Finsupp.basisSingleOne (R := R) (ι := Fin r)).exteriorPower n).repr.toEquiv
    |>.subsingleton

/-! ### Homology of the Koszul tower -/

/-- **Pro-vanishing of the Koszul homology**, homological form. For every level `a` and every
positive degree `n + 1`, the transition `K_•(f^(k + a)) ⟶ K_•(f^a)` is zero on `H_{n+1}` for
some `k`. -/
theorem exists_homologyMap_koszulTower_eq_zero [IsNoetherianRing R] (f : Fin r → R)
    (a n : ℕ) : ∃ k : ℕ, HomologicalComplex.homologyMap
      ((koszulTower f).map (homOfLE (Nat.le_add_left a k)).op) (n + 1) = 0 := by
  obtain ⟨k, hk⟩ := exists_koszulMap_mem_range f a n
  refine ⟨k, ?_⟩
  set K := (koszulTower f).obj (op (k + a))
  set L := (koszulTower f).obj (op a)
  set φ := (koszulTower f).map (homOfLE (Nat.le_add_left a k)).op
  rw [← cancel_epi (K.homologyπ (n + 1)), HomologicalComplex.homologyπ_naturality, comp_zero]
  ext x
  obtain ⟨y, hy⟩ : ∃ y, koszulBoundary R r (f ^ a) (n + 1) y =
      ((K.iCycles (n + 1) ≫ φ.f (n + 1)).hom x) := by
    have hd : koszulBoundary R r (f ^ (k + a)) n (K.iCycles (n + 1) x) = 0 := by
      have := congr($(K.iCycles_d (n + 1) n) x)
      simpa [K, koszulTower, koszulComplex, ChainComplex.of_d] using this
    have := hk _ hd
    simp only [φ, koszulTower_map_f, Nat.add_sub_cancel, unop_op] at this ⊢
    exact this
  have hx : (HomologicalComplex.cyclesMap φ (n + 1)) x = (L.toCycles (n + 2) (n + 1)) y := by
    apply (ModuleCat.mono_iff_injective (L.iCycles (n + 1))).1 inferInstance
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.toCycles_i]
    rw [← hy]
    simp [L, koszulTower, koszulComplex, ChainComplex.of_d]
  rw [ModuleCat.comp_apply, hx, ← ModuleCat.comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
  rfl

end ExteriorAlgebra
