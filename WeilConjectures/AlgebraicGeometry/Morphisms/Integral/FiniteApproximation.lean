/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.Algebra.DualNumber
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski

/-!
# Integral morphisms are limits of finite morphisms

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section IsLimitOfCover

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- Two morphisms to the point of a cone `c` over a cofiltered diagram of schemes agree if they
agree after composition with all the projections of `c`, provided that the restrictions of `c`
to the members of an open cover of some stage are limit cones. -/
lemma hom_ext_of_isLimit_opensCone [IsCofiltered I] (i₀ : I) {σ : Type*}
    (U : σ → (D.obj i₀).Opens) (hU : ⨆ a, U a = ⊤)
    (h : ∀ a, IsLimit (opensCone D c i₀ (U a))) {P : Scheme.{u}} (m₁ m₂ : P ⟶ c.pt)
    (hm : ∀ j, m₁ ≫ c.π.app j = m₂ ≫ c.π.app j) : m₁ = m₂ := by
  let q := m₁ ≫ c.π.app i₀
  let 𝒱 : P.OpenCover := Scheme.Cover.mkOfCovers σ (fun a ↦ (q ⁻¹ᵁ U a).toScheme)
    (fun a ↦ Scheme.Opens.ι _) (fun x ↦ by
      have : q x ∈ ⨆ a, U a := by rw [hU]; trivial
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp this
      exact ⟨a, ⟨x, ha⟩, rfl⟩)
  refine 𝒱.hom_ext _ _ fun a ↦ ?_
  change (q ⁻¹ᵁ U a).ι ≫ m₁ = (q ⁻¹ᵁ U a).ι ≫ m₂
  have hr (m : P ⟶ c.pt) (hm' : m ≫ c.π.app i₀ = q) :
      Set.range ((q ⁻¹ᵁ U a).ι ≫ m) ⊆ Set.range (c.π.app i₀ ⁻¹ᵁ U a).ι := by
    rintro - ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (((q ⁻¹ᵁ U a).ι ≫ m) ≫ c.π.app i₀) t ∈ U a
    rw [Category.assoc, hm']
    exact t.2
  have h₁ := hr m₁ rfl
  have h₂ := hr m₂ (hm i₀).symm
  rw [← IsOpenImmersion.lift_fac (c.π.app i₀ ⁻¹ᵁ U a).ι _ h₁,
    ← IsOpenImmersion.lift_fac (c.π.app i₀ ⁻¹ᵁ U a).ι _ h₂]
  congr 1
  refine (h a).hom_ext fun j ↦ ?_
  rw [← cancel_mono (D.map j.hom ⁻¹ᵁ U a).ι]
  simp only [opensCone_π_app, Category.assoc, Scheme.Hom.resLE_comp_ι]
  rw [IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac_assoc, Category.assoc,
    Category.assoc, hm]


variable {D c} in
lemma lift_opensCone_ι_π_app [IsCofiltered I] {i₀ : I} {V : (D.obj i₀).Opens}
    (hV : IsLimit (opensCone D c i₀ V)) (s : Cone D) (j : I) :
    hV.lift (opensCone D s i₀ V) ≫ (c.π.app i₀ ⁻¹ᵁ V).ι ≫ c.π.app j =
      (s.π.app i₀ ⁻¹ᵁ V).ι ≫ s.π.app j := by
  obtain ⟨k, fkj, fki₀, -⟩ := IsCofilteredOrEmpty.cone_objs j i₀
  have h1 := lift_opensCone_ι_comp D hV s (Over.mk fki₀)
  rw [← c.w fkj, ← s.w fkj]
  simp only [← Category.assoc] at h1 ⊢
  exact congrArg (· ≫ D.map fkj) h1

/-- **Being a limit cone is local on a stage.** Let `{Dᵢ}` be a cofiltered diagram of schemes and
let `c` be a cone over it. Suppose some stage `D.obj i₀` has an open cover `{U a}` such that the
restriction of `c` to every `U a` is a limit cone. Then `c` is a limit cone.

Compared to `AlgebraicGeometry.isLimitOfIsLimitOpensCone`, no hypothesis on the intersections
`U a ⊓ U b` is needed. -/
noncomputable def isLimitOfIsLimitOpensCone' [IsCofiltered I] (i₀ : I) {σ : Type*}
    (U : σ → (D.obj i₀).Opens) (hU : ⨆ a, U a = ⊤)
    (h : ∀ a, IsLimit (opensCone D c i₀ (U a))) : IsLimit c where
  lift s := (preimageCover D i₀ U hU s).glueMorphisms
    (fun a ↦ (h a).lift (opensCone D s i₀ (U a)) ≫ (c.π.app i₀ ⁻¹ᵁ U a).ι) fun a b ↦
      hom_ext_of_isLimit_opensCone D c i₀ U hU h _ _ fun j ↦ by
        simp only [Category.assoc]
        rw [lift_opensCone_ι_π_app (h a), lift_opensCone_ι_π_app (h b)]
        exact pullback.condition_assoc _
  fac s j := by
    apply (preimageCover D i₀ U hU s).hom_ext
    intro a
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, Category.assoc]
    exact lift_opensCone_ι_π_app (h a) s j
  uniq s m hm := by
    refine hom_ext_of_isLimit_opensCone D c i₀ U hU h _ _ fun j ↦ ?_
    rw [hm]
    apply (preimageCover D i₀ U hU s).hom_ext
    intro a
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, Category.assoc]
    exact (lift_opensCone_ι_π_app (h a) s j).symm

end IsLimitOfCover
end AlgebraicGeometry

section Ring

open TrivSqZeroExt

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']

/-- A ring homomorphism `g : A →+* A'` induces a ring homomorphism `A[ε] →+* A'[ε]` of dual
numbers. -/
def DualNumber.map (g : A →+* A') : DualNumber A →+* DualNumber A' where
  toFun z := inl (g z.fst) + inr (g z.snd)
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [add_comm, add_left_comm]

@[simp]
lemma DualNumber.fst_map (g : A →+* A') (z : DualNumber A) :
    (DualNumber.map g z).fst = g z.fst := by
  simp [DualNumber.map]

@[simp]
lemma DualNumber.snd_map (g : A →+* A') (z : DualNumber A) :
    (DualNumber.map g z).snd = g z.snd := by
  simp [DualNumber.map]

/-- For a ring homomorphism `α : R →+* A`, the subring `α(R) + εA` of the dual numbers `A[ε]`.
Its ideals contained in `εA` are the `R`-submodules of `A`. -/
def RingHom.dualSubring (α : R →+* A) : Subring (DualNumber A) :=
  α.range.comap (fstHom ℤ A A).toRingHom

lemma RingHom.mem_dualSubring {α : R →+* A} {z : DualNumber A} :
    z ∈ α.dualSubring ↔ z.fst ∈ α.range :=
  Iff.rfl

lemma RingHom.inr_mem_dualSubring (α : R →+* A) (a : A) : inr a ∈ α.dualSubring := by
  simp [RingHom.mem_dualSubring, zero_mem]

lemma RingHom.inl_mem_dualSubring (α : R →+* A) (r : R) : inl (α r) ∈ α.dualSubring := by
  simp [RingHom.mem_dualSubring]

/-- The inclusion `R →+* α(R) + εA`. -/
def RingHom.toDualSubring (α : R →+* A) : R →+* α.dualSubring :=
  ((inlHom A A).comp α).codRestrict _ fun r ↦ α.inl_mem_dualSubring r

/-- The ring homomorphism `α(R) + εA →+* α'(R') + εA'` induced by a commutative square. -/
def RingHom.dualSubringMap (α : R →+* A) (α' : R' →+* A') (ρR : R →+* R') (ρ : A →+* A')
    (h : ρ.comp α = α'.comp ρR) : α.dualSubring →+* α'.dualSubring :=
  (DualNumber.map ρ).restrict _ _ fun z hz ↦ by
    obtain ⟨r, hr⟩ := RingHom.mem_dualSubring.mp hz
    refine RingHom.mem_dualSubring.mpr ⟨ρR r, ?_⟩
    rw [DualNumber.fst_map, ← hr]
    exact (RingHom.congr_fun h r).symm


lemma RingHom.coe_dualSubringMap (α : R →+* A) (α' : R' →+* A') (ρR : R →+* R') (ρ : A →+* A')
    (h : ρ.comp α = α'.comp ρR) (z : α.dualSubring) :
    (RingHom.dualSubringMap α α' ρR ρ h z : DualNumber A') = DualNumber.map ρ z :=
  rfl

@[simp]
lemma RingHom.coe_toDualSubring (α : R →+* A) (r : R) :
    (α.toDualSubring r : DualNumber A) = inl (α r) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Formation of `α(R) + εA` commutes with localization away from an element of `R`. -/
lemma RingHom.isLocalization_dualSubringMap (α : R →+* A) (α' : R' →+* A') (ρR : R →+* R')
    (ρ : A →+* A') (h : ρ.comp α = α'.comp ρR) (r : R)
    (hR : letI := ρR.toAlgebra; IsLocalization.Away r R')
    (hA : letI := ρ.toAlgebra; IsLocalization.Away (α r) A') :
    letI := (RingHom.dualSubringMap α α' ρR ρ h).toAlgebra
    IsLocalization.Away (α.toDualSubring r) α'.dualSubring := by
  let := ρR.toAlgebra
  let := ρ.toAlgebra
  let := (RingHom.dualSubringMap α α' ρR ρ h).toAlgebra
  have hcomm (t : R) : ρ (α t) = α' (ρR t) := RingHom.congr_fun h t
  have hφ (z : α.dualSubring) : (algebraMap α.dualSubring α'.dualSubring z : DualNumber A') =
      DualNumber.map ρ z := rfl
  have hu : IsUnit (ρR r) := IsLocalization.Away.algebraMap_isUnit (S := R') r
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · refine isUnit_iff_exists_inv.mpr ⟨α'.toDualSubring ↑hu.unit⁻¹, Subtype.ext ?_⟩
    rw [Subring.coe_mul, hφ, RingHom.coe_toDualSubring, RingHom.coe_toDualSubring,
      Subring.coe_one]
    ext
    · simp only [fst_mul, DualNumber.fst_map, fst_inl, fst_one, hcomm, ← map_mul,
        IsUnit.mul_val_inv, map_one]
    · simp
  · intro z
    obtain ⟨t', ht'⟩ := RingHom.mem_dualSubring.mp z.2
    obtain ⟨n, a, hn⟩ := IsLocalization.Away.surj r t'
    obtain ⟨m, b, hm⟩ := IsLocalization.Away.surj (α r) (z : DualNumber A').snd
    rw [RingHom.algebraMap_toAlgebra] at hn hm
    refine ⟨n + m, ⟨inl (α (a * r ^ m)) + inr (b * α r ^ n), ?_⟩, Subtype.ext ?_⟩
    · exact RingHom.mem_dualSubring.mpr ⟨a * r ^ m, by simp⟩
    rw [Subring.coe_mul, ← map_pow, hφ, hφ, SubmonoidClass.coe_pow, RingHom.coe_toDualSubring]
    ext
    · simp only [fst_mul, fst_pow, DualNumber.fst_map, fst_inl, fst_add, fst_inr, add_zero,
        ← ht', hcomm, map_mul, map_pow, pow_add, ← mul_assoc]
      rw [← map_pow α' (ρR r) n, ← map_mul, hn]
    · simp only [snd_mul, fst_pow, snd_pow, DualNumber.fst_map, DualNumber.snd_map, fst_inl,
        snd_inl, snd_add, snd_inr, fst_add, fst_inr, add_zero, smul_zero, map_mul, map_pow,
        smul_eq_mul, op_smul_eq_mul, mul_zero, zero_add, pow_add, ← mul_assoc, ← hm, map_zero,
        zero_mul]
      ring
  · intro x y hxy
    have h1 := congrArg (fun z : α'.dualSubring ↦ (z : DualNumber A').fst) hxy
    have h2 := congrArg (fun z : α'.dualSubring ↦ (z : DualNumber A').snd) hxy
    simp only [hφ, DualNumber.fst_map, DualNumber.snd_map] at h1 h2
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (S := A') (α r) h1
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (S := A') (α r) h2
    refine ⟨n + m, Subtype.ext ?_⟩
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, RingHom.coe_toDualSubring]
    ext
    · simp only [fst_mul, fst_pow, fst_inl, pow_add]
      linear_combination (α r) ^ m * hn
    · simp only [snd_mul, fst_mul, fst_pow, snd_pow, fst_inl, snd_inl, smul_zero, add_zero,
        smul_eq_mul, op_smul_eq_mul, zero_add, nsmul_zero, mul_zero, pow_add, map_zero, zero_mul]
      linear_combination (α r) ^ n * hm


set_option backward.isDefEq.respectTransparency false in
/-- Let `A'` be the localization of `A` away from `s`, let `B ⊆ A` be a subring containing `s`,
and let `B' ⊆ A'` be a subring containing `ρ(B)` and the inverse of `ρ(s)`, every element of which
is a fraction `ρ(b) / ρ(s) ^ n` with `b ∈ B`. Then `B'` is the localization of `B` away from
`s`. -/
lemma Subring.isLocalization_away_of_le (ρ : A →+* A') (s : A)
    (hA : letI := ρ.toAlgebra; IsLocalization.Away s A') (B : Subring A) (B' : Subring A')
    (hs : s ∈ B) (hBB' : ∀ b ∈ B, ρ b ∈ B') (hinv : ∃ u ∈ B', u * ρ s = 1)
    (hfrac : ∀ b' ∈ B', ∃ b ∈ B, ∃ n : ℕ, b' * ρ s ^ n = ρ b) :
    letI := (ρ.restrict B B' hBB').toAlgebra
    IsLocalization.Away (⟨s, hs⟩ : B) B' := by
  let := ρ.toAlgebra
  let := (ρ.restrict B B' hBB').toAlgebra
  have hφ (b : B) : (algebraMap B B' b : A') = ρ b := rfl
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · obtain ⟨u, hu, hus⟩ := hinv
    refine isUnit_iff_exists_inv.mpr ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, hφ, mul_comm]
    exact hus
  · intro z
    obtain ⟨b, hb, n, hn⟩ := hfrac z z.2
    refine ⟨n, ⟨b, hb⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, ← map_pow, hφ, hφ]
    simpa using hn
  · intro x y hxy
    have h1 : algebraMap A A' x = algebraMap A A' y := congrArg Subtype.val hxy
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (S := A') s h1
    exact ⟨n, Subtype.ext (by simpa using hn)⟩

end Ring
