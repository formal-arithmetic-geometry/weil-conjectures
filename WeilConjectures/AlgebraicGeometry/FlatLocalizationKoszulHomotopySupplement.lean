/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ExtendedLocalizationCechSupplement
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.Ring

/-! # Signed contraction of the sheaf Koszul complex

Source: Stacks Project, Tags 0626, 0663, 0913 and 099H
(blueprint: lem-weil-pbc-localization-koszul-contractions).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules.LocalizationCech

section Generic
variable {D : Type*} [Category D] [Abelian D]
private theorem scalarNat_homology
    (z : 𝟭 D ⟶ 𝟭 D) (K : CochainComplex D ℤ) (μ : End K)
    (hμ : ∀ q, μ.f q = z.app (K.X q)) (q : ℤ) :
    HomologicalComplex.homologyMap μ q = z.app (K.homology q) := by
  have hc : HomologicalComplex.cyclesMap μ q = z.app (K.cycles q) := by
    apply (cancel_mono (K.iCycles q)).1
    rw [HomologicalComplex.cyclesMap_i, hμ]
    exact z.naturality (K.iCycles q)
  apply (cancel_epi (K.homologyπ q)).1
  rw [HomologicalComplex.homologyπ_naturality, hc]
  exact (z.naturality (K.homologyπ q)).symm
end Generic

private theorem erase_degree {r : ℕ} {q : ℤ}
    (s : Indices r (q + 1)) (j : Fin r) (h : j ∈ s.val) :
    ((s.val.erase j).card : ℤ) = q := by
  have hc := Finset.card_erase_add_one h
  have hs := s.property
  omega

private theorem sign_cancel {r : ℕ} (s : Finset (Fin r)) (j k : Fin r)
    (hj : j ∈ s) (hk : k ∉ s) (hjk : j ≠ k) :
    (-1 : ℤ) ^ (s.filter (· < k)).card *
        (-1 : ℤ) ^ ((insert k s).filter (· < j)).card +
      (-1 : ℤ) ^ (s.filter (· < j)).card *
        (-1 : ℤ) ^ ((s.erase j).filter (· < k)).card = 0 := by
  classical
  by_cases hlt : k < j
  · have hjk' : ¬ j < k := by omega
    have hfilter : (s.erase j).filter (· < k) = s.filter (· < k) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor <;> intro h
      · exact ⟨h.1.2, h.2⟩
      · exact ⟨⟨by omega, h.1⟩, h.2⟩
    rw [Finset.filter_insert, if_pos hlt, Finset.card_insert_of_notMem]
    · rw [hfilter, pow_succ]
      ring
    · simp [hk]
  · have hlt' : j < k := by omega
    have hfilter : (insert k s).filter (· < j) = s.filter (· < j) := by
      rw [Finset.filter_insert, if_neg hlt]
    have hcard : ((s.erase j).filter (· < k)).card + 1 =
        (s.filter (· < k)).card := by
      rw [Finset.filter_erase]
      exact Finset.card_erase_add_one (by simp [hj, hlt'])
    rw [hfilter, ← hcard, pow_succ]
    ring

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

private noncomputable def contractionTerm (R : Sheaf J CommRingCat.{u})
    (r : ℕ) (j : Fin r) (q : ℤ) : term R r (q + 1) ⟶ term R r q := by
  classical
  exact Sigma.desc (fun s ↦ if h : j ∈ s.val then
    (-1 : ℤ) ^ (s.val.filter (· < j)).card •
      Sigma.ι (fun _ : Indices r q ↦ unit (rings R))
        ⟨s.val.erase j, erase_degree s j h⟩
    else 0)

private theorem sign_square {r : ℕ} (s : Finset (Fin r)) (j : Fin r) :
    (-1 : ℤ) ^ (s.filter (· < j)).card * (-1 : ℤ) ^ (s.filter (· < j)).card = 1 := by
  rw [← pow_add, ← two_mul]
  simp

private theorem contraction_differential_of_not_mem
    (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) (q : ℤ)
    (j : Fin r) (s : Indices r (q + 1)) (hj : j ∉ s.val) :
    Sigma.ι (fun _ : Indices r (q + 1) ↦ unit (rings R)) s ≫
        differential R r f n (q + 1) ≫ contractionTerm R r j (q + 1) =
      (scalar R (f j) ^ (n + 1)) ≫
        Sigma.ι (fun _ : Indices r (q + 1) ↦ unit (rings R))
          s := by
  classical
  simp only [differential, Sigma.ι_desc_assoc, Preadditive.sum_comp]
  rw [Finset.sum_eq_single j]
  · rw [dif_pos hj, Preadditive.zsmul_comp, Category.assoc]
    simp only [contractionTerm, Sigma.ι_desc]
    rw [dif_pos (Finset.mem_insert_self j s.val)]
    simp only [Preadditive.comp_zsmul]
    have hfilt : (insert j s.val).filter (· < j) = s.val.filter (· < j) := by
      rw [Finset.filter_insert, if_neg (lt_irrefl j)]
    rw [hfilt, smul_smul, sign_square, one_smul]
    congr 2
    exact Subtype.ext (Finset.erase_insert hj)
  · intro k _ hkj
    by_cases hk : k ∈ s.val
    · simp [hk]
    · rw [dif_pos hk, Preadditive.zsmul_comp, Category.assoc]
      simp only [contractionTerm, Sigma.ι_desc]
      rw [dif_neg (by simp [hj, Ne.symm hkj])]
      simp
  · simp

private theorem contraction_differential_of_mem
    (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) (q : ℤ)
    (j : Fin r) (s : Indices r (q + 1)) (hj : j ∈ s.val) :
    Sigma.ι (fun _ : Indices r (q + 1) ↦ unit (rings R)) s ≫
        differential R r f n (q + 1) ≫ contractionTerm R r j (q + 1) +
      Sigma.ι (fun _ : Indices r (q + 1) ↦ unit (rings R)) s ≫
        contractionTerm R r j q ≫ differential R r f n q =
      (scalar R (f j) ^ (n + 1)) ≫
        Sigma.ι (fun _ : Indices r (q + 1) ↦ unit (rings R))
          s := by
  classical
  let a (k : Fin r) : unit (rings R) ⟶ term R r (q + 1) :=
    if hk : k ∉ s.val then
      ((-1 : ℤ) ^ (s.val.filter (· < k)).card *
        (-1 : ℤ) ^ ((insert k s.val).filter (· < j)).card) •
        ((scalar R (f k) ^ (n + 1)) ≫
          Sigma.ι (fun _ : Indices r (q + 1) ↦ unit (rings R))
            ⟨(insert k s.val).erase j, erase_degree
              ⟨insert k s.val, insert_degree s k hk⟩ j (by simp [hj])⟩)
    else 0
  have hd : Sigma.ι (fun _ : Indices r (q + 1) ↦ unit (rings R)) s ≫
      differential R r f n (q + 1) ≫ contractionTerm R r j (q + 1) = ∑ k, a k := by
    simp only [differential, Sigma.ι_desc_assoc, Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k ∈ s.val
    · simp [hk, a]
    · rw [dif_pos hk, Preadditive.zsmul_comp, Category.assoc]
      simp only [contractionTerm, Sigma.ι_desc]
      rw [dif_pos (by simp [hj])]
      simp only [Preadditive.comp_zsmul, smul_smul]
      simp only [a, dif_pos hk]
  rw [hd]
  simp only [contractionTerm, Sigma.ι_desc_assoc, dif_pos hj,
    Preadditive.zsmul_comp, differential, Sigma.ι_desc, Finset.smul_sum]
  rw [← Finset.sum_add_distrib, Finset.sum_eq_single j]
  · simp only [a, dif_neg (not_not_intro hj), zero_add,
      dif_pos (show j ∉ s.val.erase j by simp), smul_smul]
    have hfilt : (s.val.erase j).filter (· < j) = s.val.filter (· < j) := by
      rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
      simp
    rw [hfilt, sign_square, one_smul]
    congr 2
    exact Subtype.ext (Finset.insert_erase hj)
  · intro k _ hkj
    by_cases hk : k ∈ s.val
    · simp [a, hk, hkj]
    · have hke : k ∉ s.val.erase j := by simp [hk]
      simp only [a, dif_pos hk, dif_pos hke, smul_smul]
      have hindex : (⟨(insert k s.val).erase j, erase_degree
          ⟨insert k s.val, insert_degree s k hk⟩ j (by simp [hj])⟩ :
          Indices r (q + 1)) =
          ⟨insert k (s.val.erase j),
            insert_degree ⟨s.val.erase j, erase_degree s j hj⟩ k hke⟩ := by
        apply Subtype.ext
        exact Finset.erase_insert_of_ne hkj
      rw [hindex, ← add_smul, sign_cancel s.val j k hj hk (Ne.symm hkj), zero_smul]
  · simp

/-- Removing a fixed index gives the signed Koszul contraction.
Source: Stacks Project, Tag 0626 and Tag 099H
(blueprint: lem-weil-pbc-localization-koszul-contractions).

Proof: on the summand indexed by I, remove j with sign equal to the parity of
its position, and use zero when j is absent. If j is absent, only insertion of j
survives. If j is present, insertion of j after removal gives the diagonal scalar;
for every other index k the two insertion/removal orders have opposite signs.
The latter assertion follows by distinguishing k < j from j < k. Thus all
other summands cancel. Coproduct extensionality proves the identity in every degree. -/
private theorem koszul_has_contractions
    (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) :
    ∀ j : Fin r, ∃ h : ∀ q : ℤ, term R r (q + 1) ⟶ term R r q,
      ∀ q : ℤ, differential R r f n (q + 1) ≫ h (q + 1) +
          h q ≫ differential R r f n q =
        Sigma.desc (fun s : Indices r (q + 1) ↦
          (scalar R (f j) ^ (n + 1)) ≫
            Sigma.ι (fun _ : Indices r (q + 1) ↦ unit (rings R)) s) := by
  classical
  intro j
  refine ⟨contractionTerm R r j, ?_⟩
  intro q
  apply Sigma.hom_ext
  intro s
  rw [Preadditive.comp_add, Sigma.ι_desc]
  by_cases hj : j ∈ s.val
  · exact contraction_differential_of_mem R r f n q j s hj
  · rw [contraction_differential_of_not_mem R r f n q j s hj]
    simp [contractionTerm, hj]

/-- Each generator to the Koszul exponent acts by zero on cohomology.
Source: Stacks Project, Tags 0626, 0663 and 099H
(blueprint: lem-weil-pbc-localization-koszul-contractions).

Proof: use the signed removal contraction above to build a null-homotopic chain
map. In every degree its matrix is multiplication by f_j^(n+1) on each free
summand. A null-homotopic map induces zero on homology. -/
private theorem koszul_scalar_endomorphism_nullhomology
    (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) :
    ∀ j : Fin r, ∃ μ : End (koszul R r f n),
      (∀ q : ℤ, μ.f q = Sigma.desc (fun s : Indices r q ↦
        (scalar R (f j) ^ (n + 1)) ≫
          Sigma.ι (fun _ : Indices r q ↦ unit (rings R)) s)) ∧
      ∀ q : ℤ, HomologicalComplex.homologyMap μ q = 0 := by
  classical
  intro j
  obtain ⟨h, hh⟩ := koszul_has_contractions R r f n j
  let h' (i k : ℤ) (hik : (ComplexShape.up ℤ).Rel k i) :
      (koszul R r f n).X i ⟶ (koszul R r f n).X k := by
    have hik' : k + 1 = i := hik
    subst i
    exact h k
  refine ⟨Homotopy.nullHomotopicMap' h', ?_, ?_⟩
  · intro q
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, p + 1 = q := ⟨q - 1, by omega⟩
    rw [Homotopy.nullHomotopicMap'_f (k₂ := p) (k₀ := p + 1 + 1) rfl rfl]
    simpa only [koszul, CochainComplex.of_d, h'] using hh p
  · intro q
    simpa using (Homotopy.nullHomotopy' h').homologyMap_eq q


set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionScalarNat
    (R : Sheaf J CommRingCat.{u}) (s : (unit (rings R)).sections) (e : ℕ) :
    𝟭 (CategoryTheory.ringedSiteModules.{u} (rings R)) ⟶
      𝟭 (CategoryTheory.ringedSiteModules.{u} (rings R)) where
  app M := ⟨{
    app X := ModuleCat.ofHom
      (LinearMap.lsmul (R.obj.obj X) (M.val.obj X)
        ((show R.obj.obj X from s.val X) ^ e))
    naturality {X Y} f := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ((show R.obj.obj Y from s.val Y) ^ e) • M.val.map f x =
        M.val.map f (((show R.obj.obj X from s.val X) ^ e) • x)
      rw [M.val.map_smul]
      have hs : R.obj.map f (show R.obj.obj X from s.val X) =
          (show R.obj.obj Y from s.val Y) := s.property f
      change ((show R.obj.obj Y from s.val Y) ^ e) • M.val.map f x =
        R.obj.map f ((show R.obj.obj X from s.val X) ^ e) • M.val.map f x
      rw [map_pow, hs] }⟩
  naturality M N g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ((g.val.app X).hom.map_smul ((show R.obj.obj X from s.val X) ^ e) x).symm

set_option backward.isDefEq.respectTransparency false in
private theorem sectionScalarNat_unit
    (R : Sheaf J CommRingCat.{u}) (s : (unit (rings R)).sections) (e : ℕ) :
    (sectionScalarNat R s e).app (unit (rings R)) = scalar R s ^ e := by
  induction e with
  | zero =>
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro X
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [sectionScalarNat]
  | succ e ih =>
      rw [pow_succ, ← ih]
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro X
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change R.obj.obj X at x
      change ((show R.obj.obj X from s.val X) ^ (e + 1)) * x =
        ((show R.obj.obj X from s.val X) ^ e) *
          (x * (show R.obj.obj X from s.val X))
      rw [pow_succ]
      ring

set_option backward.isDefEq.respectTransparency false in
/-- Each generator power annihilates every local section of Koszul cohomology.
Source: Stacks Project, Tags 0626, 0663 and 099H
(blueprint: lem-weil-pbc-localization-koszul-contractions).

Proof: signed index removal gives a null-homotopic diagonal scalar endomorphism.
Sectionwise scalar multiplication is natural on all module sheaves and agrees
with the diagonal matrix on each free term. Naturality on the cycles inclusion
and the homology projection identifies its induced map with sectionwise scalar
multiplication on cohomology. A null-homotopic map induces zero on cohomology. -/
private theorem koszul_scalar_annihilates_homology
    (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) :
    ∀ (j : Fin r) (q : ℤ) (X : Cᵒᵖ) (x : ((koszul R r f n).homology q).val.obj X),
      ((show R.obj.obj X from (f j).val X) ^ (n + 1)) • x = 0 := by
  intro j q X x
  obtain ⟨μ, hμ, hzero⟩ := koszul_scalar_endomorphism_nullhomology R r f n j
  have hmatrix (k : ℤ) :
      μ.f k = (sectionScalarNat R (f j) (n + 1)).app ((koszul R r f n).X k) := by
    rw [hμ k]
    symm
    apply Sigma.hom_ext
    intro s
    rw [Sigma.ι_desc]
    let ιs : unit (rings R) ⟶ term R r k :=
      Sigma.ι (fun _ : Indices r k ↦ unit (rings R)) s
    have hn := (sectionScalarNat R (f j) (n + 1)).naturality ιs
    change ιs ≫ (sectionScalarNat R (f j) (n + 1)).app (term R r k) =
      (sectionScalarNat R (f j) (n + 1)).app (unit (rings R)) ≫ ιs at hn
    rw [sectionScalarNat_unit] at hn
    exact hn
  have heq := scalarNat_homology (sectionScalarNat R (f j) (n + 1))
    (koszul R r f n) μ hmatrix q
  have hz := heq.symm.trans (hzero q)
  exact congrArg (fun g : End ((koszul R r f n).homology q) ↦ g.val.app X x) hz


private theorem span_pow_le_of_generator_powers
    {S : Type*} [CommRing S] {ι : Type*} (s : Finset ι) (f : ι → S)
    (e : ℕ) (A : Ideal S) (h : ∀ j ∈ s, f j ^ e ∈ A) :
    (Ideal.span (f '' (s : Set ι))) ^ (s.card * e + 1) ≤ A := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have hs : (Ideal.span (f '' (s : Set ι))) ^ (s.card * e + 1) ≤ A :=
      ih (fun k hk ↦ h k (Finset.mem_insert_of_mem hk))
    have hexp : (insert j s).card * e + 1 = e + (s.card * e + 1) := by
      rw [Finset.card_insert_of_notMem hj, Nat.add_mul, Nat.one_mul]
      omega
    rw [hexp, Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert]
    apply Ideal.sup_pow_add_le_pow_sup_pow.trans
    apply sup_le _ hs
    rw [Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
    exact h j (Finset.mem_insert_self j s)


/-- A uniform positive ideal power annihilates every local section of Koszul cohomology.
Source: Stacks Project, Tags 0626, 0663 and 099H
(blueprint: lem-weil-pbc-localization-koszul-contractions).

Proof: signed removal makes each generator power null-homotopic, hence zero on
cohomology, by naturality of scalar multiplication on cycles and homology.
For a finite set s of generators with e-th powers in an ideal A, induction on s
shows that span(s)^(card(s)*e+1) is contained in A. The empty case is the zero ideal
to the first power. For an inserted generator, use the ideal inequality
(I sup J)^(e+card(s)*e+1) <= I^e sup J^(card(s)*e+1), and the inductive hypothesis.
Apply this with A the annihilator of the module of sections of the cohomology sheaf.
This gives exponent r*(n+1)+1 uniformly on all site objects and in all degrees. -/
theorem koszul_ideal_power_annihilates_homology
    (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (n : ℕ) :
    ∀ (q : ℤ) (X : Cᵒᵖ) (a : R.obj.obj X),
      a ∈ (Ideal.span (Set.range (fun j : Fin r ↦
        (show R.obj.obj X from (f j).val X)))) ^ (r * (n + 1) + 1) →
      ∀ (x : ((koszul R r f n).homology q).val.obj X), a • x = 0 := by
  intro q X a ha x
  let g : Fin r → R.obj.obj X := fun j ↦ (f j).val X
  let A := Module.annihilator (R.obj.obj X) (((koszul R r f n).homology q).val.obj X)
  have hgen : ∀ j ∈ (Finset.univ : Finset (Fin r)), g j ^ (n + 1) ∈ A := by
    intro j _
    exact Module.mem_annihilator.mpr (koszul_scalar_annihilates_homology R r f n j q X)
  have hh : (Ideal.span (Set.range g)) ^ (r * (n + 1) + 1) ≤ A := by
    simpa using span_pow_le_of_generator_powers Finset.univ g (n + 1) A hgen
  exact Module.mem_annihilator.mp (hh ha) x

end SheafOfModules.LocalizationCech
