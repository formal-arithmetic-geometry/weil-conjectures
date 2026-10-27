module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Set.Card
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Data.PNat.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Polynomial growth of a positive lattice monoid length convolution

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé VI, §1.6(i)–(ii),
printed p. 70 (PDF p. 76), formal monoid models; the lattice-counting refinement
is agent supplied (blueprint: lem-trf-positive-monoid-length-growth).
-/

@[expose] public section

universe u

namespace AddSubmonoid

open scoped NNReal

private theorem decomposition_weight_bound {G : Type u} [AddCommGroup G]
    (P : AddSubmonoid G) (w : G →+ ℤ)
    (hpos : ∀ p : P, p ≠ 0 → 0 < w (p : G))
    {p : P} {l : ℕ} (f : Fin l → P) (hf : ∀ i, f i ≠ 0)
    (hs : ∑ i, f i = p) : (l : ℤ) ≤ w (p : G) := by
  have hsum : (l : ℤ) ≤ ∑ i : Fin l, w (f i : G) := by
    calc
      (l : ℤ) = ∑ _i : Fin l, (1 : ℤ) := by simp
      _ ≤ ∑ i : Fin l, w (f i : G) :=
        Finset.sum_le_sum fun i _ ↦ hpos (f i) (hf i)
  have heq : (∑ i, w (f i : G)) = w (p : G) := by
    change (∑ i, (w.comp P.subtype) (f i)) = _
    rw [← map_sum, hs]
    rfl
  exact heq ▸ hsum

private theorem positive_length_max {G : Type u} [AddCommGroup G]
    (P : AddSubmonoid G) (w : G →+ ℤ)
    (hpos : ∀ p : P, p ≠ 0 → 0 < w (p : G)) :
    ∃ ν : P → ℕ,
      (∀ p : P, IsGreatest {l : ℕ | ∃ f : Fin l → P,
        (∀ i, f i ≠ 0) ∧ (∑ i, f i) = p} (ν p)) ∧
      ν 0 = 0 ∧ ∀ p : P, (ν p : ℤ) ≤ w (p : G) := by
  classical
  let D (p : P) (l : ℕ) := ∃ f : Fin l → P,
    (∀ i, f i ≠ 0) ∧ (∑ i, f i) = p
  have hne (p : P) : ∃ l, D p l := by
    by_cases hp : p = 0
    · exact ⟨0, Fin.elim0, by simp [hp]⟩
    · exact ⟨1, fun _ ↦ p, by simp [hp]⟩
  have hbd (p : P) {l : ℕ} (hl : D p l) : l ≤ (w (p : G)).toNat := by
    obtain ⟨f, hf, hs⟩ := hl
    have h := decomposition_weight_bound P w hpos f hf hs
    omega
  let ν (p : P) := Nat.findGreatest (D p) (w (p : G)).toNat
  have hmax (p : P) : IsGreatest {l | D p l} (ν p) := by
    obtain ⟨l, hl⟩ := hne p
    exact ⟨Nat.findGreatest_spec (hbd p hl) hl,
      fun _ hk ↦ Nat.le_findGreatest (hbd p hk) hk⟩
  refine ⟨ν, hmax, ?_, ?_⟩
  · have h := hbd 0 (hmax 0).1
    simpa using h
  · intro p
    obtain ⟨f, hf, hs⟩ := (hmax p).1
    exact decomposition_weight_bound P w hpos f hf hs

private theorem generator_word {G : Type u} [AddCommGroup G]
    (P : AddSubmonoid G) {s : ℕ} (g : Fin s → P)
    (hg : AddSubmonoid.closure (Set.range (fun i ↦ (g i : G))) = P) (p : P) :
    ∃ (t : ℕ) (a : Fin t → Fin s), ∑ i, (g (a i) : G) = p := by
  classical
  have hp : (p : G) ∈ AddSubmonoid.closure (Set.range (fun i ↦ (g i : G))) := by
    rw [hg]
    exact p.property
  obtain ⟨l, hl, hs⟩ := AddSubmonoid.exists_list_of_mem_closure hp
  choose a ha using fun i : Fin l.length ↦ hl (l.get i) (List.get_mem l i)
  refine ⟨l.length, a, ?_⟩
  simp_rw [ha]
  rw [← Fin.sum_ofFn, List.ofFn_get, hs]

private theorem nonzero_generators {G : Type u} [AddCommGroup G]
    (P : AddSubmonoid G) (hfg : P.FG) :
    ∃ (s : ℕ) (g : Fin s → P), (∀ i, g i ≠ 0) ∧
      AddSubmonoid.closure (Set.range (fun i ↦ (g i : G))) = P := by
  classical
  obtain ⟨t, ht, hfin⟩ := (AddSubmonoid.fg_iff P).mp hfg
  let T := t \ {0}
  have hT : AddSubmonoid.closure T = P := by
    simpa only [T, AddSubmonoid.closure_sdiff_singleton_zero] using ht
  let : Fintype T := (hfin.subset Set.sdiff_subset).fintype
  let e := Fintype.equivFin T
  let g : Fin (Fintype.card T) → P := fun i ↦
    ⟨(e.symm i : G), hT ▸ AddSubmonoid.subset_closure (e.symm i).property⟩
  refine ⟨_, g, ?_, ?_⟩
  · intro i hi
    have hz : (e.symm i : G) = 0 := congrArg Subtype.val hi
    exact (e.symm i).property.2 (by simp [hz])
  · have hrange : Set.range (fun i ↦ (g i : G)) = T := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (e.symm i).property
      · intro hx
        exact ⟨e ⟨x, hx⟩, by simp [g]⟩
    rw [hrange, hT]

private theorem generator_length_bound {G : Type u} [AddCommGroup G]
    (P : AddSubmonoid G) (ν : P → ℕ)
    (hν : ∀ p : P, IsGreatest {l : ℕ | ∃ f : Fin l → P,
      (∀ i, f i ≠ 0) ∧ (∑ i, f i) = p} (ν p))
    {s : ℕ} (g : Fin s → P) (hgne : ∀ i, g i ≠ 0)
    {t : ℕ} (a : Fin t → Fin s) {p : P} (hp : ∑ i, (g (a i) : G) = p) :
    t ≤ ν p := by
  apply (hν p).2
  refine ⟨fun i ↦ g (a i), fun i ↦ hgne (a i), ?_⟩
  apply Subtype.ext
  simpa using hp

private theorem generator_weight_comparison {G : Type u} [AddCommGroup G]
    (P : AddSubmonoid G) (w : G →+ ℤ)
    (hpos : ∀ p : P, p ≠ 0 → 0 < w (p : G))
    (ν : P → ℕ)
    (hν : ∀ p : P, IsGreatest {l : ℕ | ∃ f : Fin l → P,
      (∀ i, f i ≠ 0) ∧ (∑ i, f i) = p} (ν p))
    {s : ℕ} (g : Fin s → P) (hgne : ∀ i, g i ≠ 0)
    (hg : AddSubmonoid.closure (Set.range (fun i ↦ (g i : G))) = P)
    (M : ℕ) (hM : M = Finset.univ.sup (fun i ↦ (w (g i : G)).toNat)) (p : P) :
    (w (p : G) : ℝ) / (M : ℝ) ≤ (ν p : ℝ) ∧ (ν p : ℤ) ≤ w (p : G) := by
  classical
  have hw (i : Fin s) : w (g i : G) ≤ (M : ℤ) := by
    have h := Finset.le_sup (f := fun i ↦ (w (g i : G)).toNat) (Finset.mem_univ i)
    rw [← hM] at h
    omega
  obtain ⟨t, a, ha⟩ := generator_word P g hg p
  have ht := generator_length_bound P ν hν g hgne a ha
  have hbound : w (p : G) ≤ (M : ℤ) * (ν p : ℤ) := by
    calc
      w (p : G) = ∑ i, w (g (a i) : G) := by rw [← map_sum, ha]
      _ ≤ ∑ _i : Fin t, (M : ℤ) := Finset.sum_le_sum fun i _ ↦ hw (a i)
      _ = (M : ℤ) * t := by simp [mul_comm]
      _ ≤ (M : ℤ) * (ν p : ℤ) := by gcongr
  constructor
  · by_cases hzero : M = 0
    · simp [hzero]
    · apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hzero)).mpr
      exact_mod_cast (by simpa [mul_comm] using hbound :
        w (p : G) ≤ (ν p : ℤ) * M)
  · obtain ⟨f, hf, hs⟩ := (hν p).1
    exact decomposition_weight_bound P w hpos f hf hs

private theorem generator_coordinate_bound {r : ℕ} {G : Type u} [AddCommGroup G]
    (B : Module.Basis (Fin r) ℤ G) (P : AddSubmonoid G) (ν : P → ℕ)
    (hν : ∀ p : P, IsGreatest {l : ℕ | ∃ f : Fin l → P,
      (∀ i, f i ≠ 0) ∧ (∑ i, f i) = p} (ν p))
    {s : ℕ} (g : Fin s → P) (hgne : ∀ i, g i ≠ 0)
    (hg : AddSubmonoid.closure (Set.range (fun i ↦ (g i : G))) = P)
    (C : ℕ) (hC : ∀ (i : Fin s) (j : Fin r), |B.repr (g i : G) j| ≤ (C : ℤ))
    (n : ℕ) (p : P) (hp : ν p < n) (j : Fin r) :
    |B.repr (p : G) j| ≤ (C * n : ℕ) := by
  classical
  obtain ⟨t, a, ha⟩ := generator_word P g hg p
  have ht := generator_length_bound P ν hν g hgne a ha
  calc
    |B.repr (p : G) j| = |∑ i, B.repr (g (a i) : G) j| := by
      rw [← ha, map_sum, Finsupp.finsetSum_apply]
    _ ≤ ∑ i : Fin t, |B.repr (g (a i) : G) j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin t, (C : ℤ) := Finset.sum_le_sum fun i _ ↦ hC (a i) j
    _ = (C : ℤ) * t := by simp [mul_comm]
    _ ≤ (C * n : ℕ) := by push_cast; gcongr; omega

private theorem generator_coordinate_count {r : ℕ} {G : Type u} [AddCommGroup G]
    (B : Module.Basis (Fin r) ℤ G) (P : AddSubmonoid G) (ν : P → ℕ)
    (hν : ∀ p : P, IsGreatest {l : ℕ | ∃ f : Fin l → P,
      (∀ i, f i ≠ 0) ∧ (∑ i, f i) = p} (ν p))
    {s : ℕ} (g : Fin s → P) (hgne : ∀ i, g i ≠ 0)
    (hg : AddSubmonoid.closure (Set.range (fun i ↦ (g i : G))) = P)
    (C : ℕ) (hC : ∀ (i : Fin s) (j : Fin r), |B.repr (g i : G) j| ≤ (C : ℤ))
    (n : ℕ) : Set.Finite {p : P | ν p < n} ∧
      Set.ncard {p : P | ν p < n} ≤ (2 * C * n + 1) ^ r := by
  classical
  let S := {p : P | ν p < n}
  let box := Fin r → Set.Icc (-(C * n : ℕ) : ℤ) (C * n : ℕ)
  let f : S → box := fun p j ↦ ⟨B.repr (p.1 : G) j, by
    have h := generator_coordinate_bound B P ν hν g hgne hg C hC n p.1 p.2 j
    exact abs_le.mp h⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    apply B.repr.injective
    ext j
    exact congrArg Subtype.val (congrFun hpq j)
  let : Finite S := Finite.of_injective f hf
  have hfin : S.Finite := Set.toFinite S
  refine ⟨hfin, ?_⟩
  let := hfin.fintype
  have hc : Fintype.card (Set.Icc (-(C * n : ℕ) : ℤ) (C * n : ℕ)) =
      2 * C * n + 1 := by
    have h := Int.card_fintype_Icc_of_le (a := -(C * n : ℕ)) (b := (C * n : ℕ))
      (by
        have hnonneg : (0 : ℤ) ≤ (C * n : ℕ) := Nat.cast_nonneg _
        omega)
    have heq : ((2 * C * n + 1 : ℕ) : ℤ) =
        (C * n : ℕ) + 1 - (-(C * n : ℕ) : ℤ) := by push_cast; ring
    exact_mod_cast h.trans heq.symm
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [box, Fintype.card_fun, Fintype.card_fin, hc, Set.fintypeCard_eq_ncard]
    using hcard

private theorem independent_generators {r : ℕ} {G : Type u} [AddCommGroup G]
    (B : Module.Basis (Fin r) ℤ G) (P : AddSubmonoid G)
    (hspan : AddSubgroup.closure (P : Set G) = ⊤)
    {s : ℕ} (g : Fin s → P)
    (hg : AddSubmonoid.closure (Set.range (fun i ↦ (g i : G))) = P) :
    ∃ v : Fin r → Fin s, LinearIndependent ℤ (fun j ↦ (g (v j) : G)) := by
  classical
  let E : G →ₗ[ℤ] (Fin r → ℚ) :=
    { toFun := fun x j ↦ (B.repr x j : ℚ)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  let q : Fin s → (Fin r → ℚ) := fun i ↦ E (g i)
  let V := Submodule.span ℚ (Set.range q)
  have hgen : AddSubgroup.closure (Set.range (fun i ↦ (g i : G))) = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply (AddSubgroup.closure_le _).mpr
    intro x hx
    have hp : P ≤ (AddSubgroup.closure (Set.range (fun i ↦ (g i : G)))).toAddSubmonoid := by
      calc
        P = AddSubmonoid.closure (Set.range (fun i ↦ (g i : G))) := hg.symm
        _ ≤ _ := AddSubmonoid.closure_le.mpr fun x hx ↦ AddSubgroup.subset_closure hx
    exact hp hx
  have hE : ∀ x : G, E x ∈ V := by
    intro x
    have hx : x ∈ AddSubgroup.closure (Set.range (fun i ↦ (g i : G))) := by
      rw [hgen]; trivial
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span (Set.mem_range_self i)
    | zero => simp
    | add x y hx hy hEx hEy => simpa using V.add_mem hEx hEy
    | neg x hx hEx => simpa using V.neg_mem hEx
  have hV : V = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro x
    have heq : x = ∑ j : Fin r, x j • E (B j) := by
      ext i
      simp [E, Finsupp.single_apply, eq_comm]
    rw [heq]
    exact V.sum_mem fun j _ ↦ V.smul_mem (x j) (hE (B j))
  have hdim : Module.finrank ℚ V = r := by
    rw [hV, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range q)
  rw [show Submodule.span ℚ (Set.range q) = V from rfl, hdim] at hex
  obtain ⟨f, hf, _, hli⟩ := hex
  choose v hv using hf
  refine ⟨v, LinearIndependent.of_comp E ?_⟩
  have hq : (fun j ↦ E (g (v j))) = f := funext hv
  rw [show E ∘ (fun j ↦ (g (v j) : G)) = f from hq]
  exact hli.restrict_scalars' ℤ

private theorem independent_box {r : ℕ} {G : Type u} [AddCommGroup G]
    (P : AddSubmonoid G) (w : G →+ ℤ)
    (hpos : ∀ p : P, p ≠ 0 → 0 < w (p : G))
    (ν : P → ℕ) (hνw : ∀ p : P, (ν p : ℤ) ≤ w (p : G))
    {s : ℕ} (g : Fin s → P) (hgne : ∀ i, g i ≠ 0)
    (v : Fin r → Fin s) (hv : LinearIndependent ℤ (fun j ↦ (g (v j) : G)))
    (W : ℕ) (hW : W = Finset.univ.sup (fun j ↦ (w (g (v j) : G)).toNat))
    (n : ℕ) :
    Function.Injective
      (fun b : Fin r → Fin (n / (4 * r * W) + 1) ↦ ∑ j, (b j : ℕ) • g (v j)) ∧
    ∀ b : Fin r → Fin (n / (4 * r * W) + 1),
      (ν (∑ j, (b j : ℕ) • g (v j)) : ℝ) ≤ (n : ℝ) / 4 := by
  classical
  let m := n / (4 * r * W)
  have hw (j : Fin r) : w (g (v j) : G) ≤ (W : ℤ) := by
    have h := Finset.le_sup (f := fun j ↦ (w (g (v j) : G)).toNat)
      (Finset.mem_univ j)
    rw [← hW] at h
    omega
  constructor
  · intro b c hbc
    have hbc' : (∑ j, (b j : ℤ) • (g (v j) : G)) =
        ∑ j, (c j : ℤ) • (g (v j) : G) := by
      simpa using congrArg (fun p : P ↦ (p : G)) hbc
    have heq := (Fintype.linearIndependent_iffₛ.mp hv)
      (fun j ↦ (b j : ℤ)) (fun j ↦ (c j : ℤ)) hbc'
    funext j
    apply Fin.ext
    exact_mod_cast heq j
  · intro b
    have hweight : w (↑(∑ j, (b j : ℕ) • g (v j)) : G) ≤
        (r : ℤ) * m * W := by
      calc
        w (↑(∑ j, (b j : ℕ) • g (v j)) : G) =
            ∑ j, (b j : ℤ) * w (g (v j) : G) := by simp
        _ ≤ ∑ _j : Fin r, (m : ℤ) * W := by
          apply Finset.sum_le_sum
          intro j _
          have hbj : (b j : ℕ) ≤ m := Nat.le_of_lt_succ (b j).isLt
          have hposj := hpos (g (v j)) (hgne (v j))
          have hbj' : (b j : ℤ) ≤ m := by exact_mod_cast hbj
          calc
            (b j : ℤ) * w (g (v j) : G) ≤ (m : ℤ) * w (g (v j) : G) :=
              mul_le_mul_of_nonneg_right hbj' hposj.le
            _ ≤ (m : ℤ) * W := mul_le_mul_of_nonneg_left (hw j) (by positivity)
        _ = (r : ℤ) * m * W := by simp [mul_comm, mul_left_comm]
    have hdiv : 4 * (r * m * W) ≤ n := by
      have h := Nat.div_mul_le_self n (4 * r * W)
      dsimp [m]
      nlinarith only [h]
    have hlen := hνw (∑ j, (b j : ℕ) • g (v j))
    have hfour : 4 * ν (∑ j, (b j : ℕ) • g (v j)) ≤ n := by
      have hdiv' : (4 : ℤ) * ((r : ℤ) * m * W) ≤ n := by exact_mod_cast hdiv
      have hi : (4 : ℤ) * ν (∑ j, (b j : ℕ) • g (v j)) ≤ n := by omega
      exact_mod_cast hi
    have hf : (4 : ℝ) * ν (∑ j, (b j : ℕ) • g (v j)) ≤ n := by
      exact_mod_cast hfour
    linarith

private theorem convolution_upper {G : Type u} [AddCommGroup G]
    (P : AddSubmonoid G) (ν : P → ℕ)
    (hfin : ∀ n : ℕ+, Set.Finite {p : P | ν p < (n : ℕ)})
    (lam : ℕ+ → ℝ≥0) (hmono : Monotone lam) (n : ℕ+) :
    (∑ᶠ p : {p : P // ν p < (n : ℕ)}, lam (((n : ℕ) - ν p.1).toPNat')) ≤
      (Set.ncard {p : P | ν p < (n : ℕ)} : ℝ≥0) * lam n := by
  classical
  let : Fintype {p : P // ν p < (n : ℕ)} := (hfin n).fintype
  rw [finsum_eq_sum_of_fintype]
  calc
    _ ≤ ∑ _p : {p : P // ν p < (n : ℕ)}, lam n := by
      apply Finset.sum_le_sum
      intro p _
      apply hmono
      change (((n : ℕ) - ν p.1).toPNat' : ℕ) ≤ (n : ℕ)
      rw [PNat.toPNat'_coe (Nat.sub_pos_of_lt p.2)]
      exact Nat.sub_le _ _
    _ = _ := by
      have hc : Fintype.card {p : P // ν p < (n : ℕ)} =
          Set.ncard {p : P | ν p < (n : ℕ)} :=
        @Set.fintypeCard_eq_ncard P {p : P | ν p < (n : ℕ)} ((hfin n).fintype)
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]

private theorem convolution_lower {G : Type u} [AddCommGroup G]
    (P : AddSubmonoid G) (ν : P → ℕ)
    (hfin : ∀ n : ℕ+, Set.Finite {p : P | ν p < (n : ℕ)})
    (lam : ℕ+ → ℝ≥0) (hmono : Monotone lam)
    {r m : ℕ} (n : ℕ+) (hn : 2 ≤ (n : ℕ))
    (f : (Fin r → Fin (m + 1)) → P) (hf : Function.Injective f)
    (hsmall : ∀ b, (ν (f b) : ℝ) ≤ (n : ℝ) / 4) :
    (((m + 1) ^ r : ℕ) : ℝ≥0) * lam (((n : ℕ) / 2).toPNat') ≤
      ∑ᶠ p : {p : P // ν p < (n : ℕ)}, lam (((n : ℕ) - ν p.1).toPNat') := by
  classical
  let : Fintype {p : P // ν p < (n : ℕ)} := (hfin n).fintype
  have hquarter (b) : 4 * ν (f b) ≤ (n : ℕ) := by
    have h := hsmall b
    have hi : (4 : ℝ) * ν (f b) ≤ n := by linarith
    exact_mod_cast hi
  have hmem (b) : ν (f b) < (n : ℕ) := by
    have h := hquarter b
    omega
  let e : (Fin r → Fin (m + 1)) → {p : P // ν p < (n : ℕ)} :=
    fun b ↦ ⟨f b, hmem b⟩
  have he : Function.Injective e := fun _ _ h ↦ hf (congrArg Subtype.val h)
  let L (p : {p : P // ν p < (n : ℕ)}) := lam (((n : ℕ) - ν p.1).toPNat')
  rw [finsum_eq_sum_of_fintype]
  calc
    (((m + 1) ^ r : ℕ) : ℝ≥0) * lam (((n : ℕ) / 2).toPNat') =
        ∑ _b : Fin r → Fin (m + 1), lam (((n : ℕ) / 2).toPNat') := by simp
    _ ≤ ∑ b : Fin r → Fin (m + 1), L (e b) := by
      apply Finset.sum_le_sum
      intro b _
      apply hmono
      change (((n : ℕ) / 2).toPNat' : ℕ) ≤ (((n : ℕ) - ν (f b)).toPNat' : ℕ)
      rw [PNat.toPNat'_coe (by omega), PNat.toPNat'_coe (by have h := hmem b; omega)]
      have h := hquarter b
      omega
    _ = ∑ p ∈ Finset.image e Finset.univ, L p := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h ↦ he h
    _ ≤ ∑ p : {p : P // ν p < (n : ℕ)}, L p := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ by positivity)

private theorem polynomial_of_convolution_bounds (r d C D : ℕ) (hD : 0 < D)
    (lam F : ℕ+ → ℝ≥0)
    (hgrowth : ∃ a b : ℝ≥0, 0 < a ∧ 0 < b ∧ ∃ k₀ : ℕ+,
      ∀ k : ℕ+, k₀ ≤ k → a * (k : ℝ≥0) ^ d ≤ lam k ∧ lam k ≤ b * (k : ℝ≥0) ^ d)
    (hupper : ∀ n : ℕ+, 2 ≤ (n : ℕ) →
      F n ≤ ((2 * C * (n : ℕ) + 1) ^ r : ℕ) * lam n)
    (hlower : ∀ n : ℕ+, 2 ≤ (n : ℕ) →
      ((((n : ℕ) / D + 1) ^ r : ℕ) : ℝ≥0) * lam (((n : ℕ) / 2).toPNat') ≤ F n) :
    ∃ a' b' : ℝ≥0, 0 < a' ∧ 0 < b' ∧ ∃ n₀ : ℕ+,
      ∀ n : ℕ+, n₀ ≤ n →
        a' * (n : ℝ≥0) ^ (d + r) ≤ F n ∧ F n ≤ b' * (n : ℝ≥0) ^ (d + r) := by
  obtain ⟨a, b, ha, hb, k₀, hk⟩ := hgrowth
  have hD' : (0 : ℝ≥0) < D := by exact_mod_cast hD
  let a' : ℝ≥0 := a / (3 ^ d * (D : ℝ≥0) ^ r)
  let b' : ℝ≥0 := b * ((2 * C + 1 : ℕ) : ℝ≥0) ^ r
  refine ⟨a', b', by positivity, by positivity,
    ⟨max 3 (2 * (k₀ : ℕ)), by omega⟩, ?_⟩
  intro n hn
  have hn3 : 3 ≤ (n : ℕ) := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ (n : ℕ) := by omega
  have hnk : 2 * (k₀ : ℕ) ≤ (n : ℕ) := (le_max_right _ _).trans hn
  have hhalfpos : 0 < (n : ℕ) / 2 := by omega
  have hhalfcast : (((n : ℕ) / 2).toPNat' : ℝ≥0) = (((n : ℕ) / 2 : ℕ) : ℝ≥0) := by
    rw [PNat.toPNat'_coe hhalfpos]
  have hhalfk : k₀ ≤ ((n : ℕ) / 2).toPNat' := by
    change (k₀ : ℕ) ≤ (((n : ℕ) / 2).toPNat' : ℕ)
    rw [PNat.toPNat'_coe hhalfpos]
    omega
  have hhalf := hk _ hhalfk
  have hnfull := hk n (show k₀ ≤ n by change (k₀ : ℕ) ≤ (n : ℕ); omega)
  have hhalfnum : (n : ℝ≥0) / 3 ≤ (((n : ℕ) / 2).toPNat' : ℝ≥0) := by
    rw [hhalfcast, div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 3)]
    have h : (n : ℕ) ≤ (n : ℕ) / 2 * 3 := by omega
    exact_mod_cast h
  have hbox : (n : ℝ≥0) / (D : ℝ≥0) ≤ (((n : ℕ) / D + 1 : ℕ) : ℝ≥0) := by
    rw [div_le_iff₀ hD']
    have h : (n : ℕ) ≤ ((n : ℕ) / D + 1) * D := by
      simpa [mul_comm] using (Nat.lt_mul_div_succ (n : ℕ) hD).le
    exact_mod_cast h
  have hcoord : ((2 * C * (n : ℕ) + 1 : ℕ) : ℝ≥0) ≤
      ((2 * C + 1 : ℕ) : ℝ≥0) * (n : ℝ≥0) := by
    have h : 2 * C * (n : ℕ) + 1 ≤ (2 * C + 1) * (n : ℕ) := by nlinarith
    exact_mod_cast h
  constructor
  · calc
      a' * (n : ℝ≥0) ^ (d + r) =
          ((n : ℝ≥0) / (D : ℝ≥0)) ^ r * (a * ((n : ℝ≥0) / 3) ^ d) := by
        dsimp [a']
        rw [pow_add, div_pow, div_pow]
        field_simp
      _ ≤ (((n : ℕ) / D + 1 : ℕ) : ℝ≥0) ^ r *
          (a * (((n : ℕ) / 2).toPNat' : ℝ≥0) ^ d) := by gcongr
      _ ≤ (((n : ℕ) / D + 1 : ℕ) : ℝ≥0) ^ r * lam (((n : ℕ) / 2).toPNat') :=
        mul_le_mul_of_nonneg_left hhalf.1 (by positivity)
      _ ≤ F n := by simpa only [Nat.cast_pow] using hlower n hn2
  · calc
      F n ≤ ((2 * C * (n : ℕ) + 1) ^ r : ℕ) * lam n := hupper n hn2
      _ ≤ (((2 * C + 1 : ℕ) : ℝ≥0) * (n : ℝ≥0)) ^ r *
          (b * (n : ℝ≥0) ^ d) := by
        push_cast
        gcongr
        · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hcoord
        · exact hnfull.2
      _ = b' * (n : ℝ≥0) ^ (d + r) := by
        dsimp [b']
        rw [mul_pow, pow_add]
        ring

open Classical in
/-- Maximal decomposition lengths and the full polynomial convolution estimates.

Source: ILO, Exposé VI, §1.6(i)–(ii), printed p. 70 (PDF p. 76), formal monoid
models; agent-supplied lattice-counting refinement
(blueprint: lem-trf-positive-monoid-length-growth).

`B` is the chosen integral lattice basis. `ν` is uniquely characterized by the
attained maximum of all nonzero-summand decomposition lengths, including the
empty decomposition at zero. `F` is uniquely specified by the displayed finite
sum. `Nat.toPNat'` only occurs on positive arguments in these formulas:
`ν p < n` implies `0 < n - ν p`, and `2 ≤ n` implies `0 < n / 2`.
The maxima `M` and `W` use natural weights; positivity makes these exactly the
integer weight maxima in the node. An independent selection `v` indexes the
original generators. The finite box uses `Fin (n / (4 * r * W) + 1)` in each
coordinate, namely the integers from zero through the specified floor.

Proof plan:
1. Positive integral weights bound each decomposition length by `w p`; the
   singleton decomposition (or the empty one at zero) makes the bounded set
   nonempty. Its maximum is attained, and only the empty sum represents zero.
2. In rank zero the lattice and monoid are zero, so the sum is `lam n` and its
   growth constants are the given ones. Otherwise remove zero generators.
   If their weight maximum is `M`, a generator expression of length `t` has
   `t ≤ ν p` and `w p ≤ M * t`, proving both length comparisons.
3. In coordinates each generator has absolute coordinates at most `C`, so a
   point of length less than `n` has coordinates in `[-C*n, C*n]`. This finite
   box gives finiteness and the cardinal bound `(2*C*n+1)^r`.
4. The generators span the rational coordinate space since their integer
   subgroup is all of `G`. Apply `lem-weil-span-independent-subfamily` and
   `lem-weil-dimension-span-independent-family` to select `r` generators.
   Rational independence implies their integral independence.
5. For any independent selection with weight maximum `W`, the displayed box
   map is injective by independence. Its images have weight at most
   `r * (n / (4*r*W)) * W ≤ n/4`, hence length at most `n/4`.
6. Monotonicity bounds every summand above by `lam n`; restricting below to the
   independent box bounds each summand below by `lam (n/2)`. Nonnegativity gives
   the two convolution bounds, with all sums finite by step 3.
7. For `n ≥ max 3 (2*k₀)`, use `n/2 ≥ n/3` (with the left side floored),
   `n/(4*r*W)+1 ≥ n/(4*r*W)` (left quotient floored), and
   `2*C*n+1 ≤ (2*C+1)*n`. The growth constants may be chosen as
   `a * 3^(-d) * (4*r*W)^(-r)` and `b * (2*C+1)^r`, both positive.
   Zeroth powers cover `d = 0`.
-/
theorem positiveMonoid_length_growth
    (r d : ℕ) (G : Type u) [AddCommGroup G] (B : Module.Basis (Fin r) ℤ G)
    (P : AddSubmonoid G) (hfg : P.FG)
    (hspan : AddSubgroup.closure (P : Set G) = ⊤)
    (w : G →+ ℤ) (hpos : ∀ p : P, p ≠ 0 → 0 < w (p : G))
    (lam : ℕ+ → ℝ≥0) (hmono : Monotone lam)
    (hgrowth : ∃ a b : ℝ≥0, 0 < a ∧ 0 < b ∧ ∃ k₀ : ℕ+,
      ∀ k : ℕ+, k₀ ≤ k → a * (k : ℝ≥0) ^ d ≤ lam k ∧ lam k ≤ b * (k : ℝ≥0) ^ d) :
    ∃ ν : P → ℕ,
      (∀ p : P, IsGreatest {l : ℕ | ∃ f : Fin l → P,
        (∀ i : Fin l, f i ≠ 0) ∧ (∑ i, f i) = p} (ν p)) ∧
      ν 0 = 0 ∧
      (∀ n : ℕ+, Set.Finite {p : P | ν p < (n : ℕ)}) ∧
      ∃ F : ℕ+ → ℝ≥0,
        (∀ n : ℕ+, F n = ∑ᶠ p : {p : P // ν p < (n : ℕ)},
          lam (((n : ℕ) - ν p.1).toPNat')) ∧
        (∃ a' b' : ℝ≥0, 0 < a' ∧ 0 < b' ∧ ∃ n₀ : ℕ+,
          ∀ n : ℕ+, n₀ ≤ n →
            a' * (n : ℝ≥0) ^ (d + r) ≤ F n ∧ F n ≤ b' * (n : ℝ≥0) ^ (d + r)) ∧
        (r = 0 → P = ⊥ ∧ ∀ n : ℕ+, F n = lam n) ∧
        (0 < r →
          (∃ (s : ℕ) (g : Fin s → P),
            (∀ i : Fin s, g i ≠ 0) ∧
            AddSubmonoid.closure (Set.range (fun i ↦ (g i : G))) = P) ∧
          ∀ (s : ℕ) (g : Fin s → P), (∀ i : Fin s, g i ≠ 0) →
            AddSubmonoid.closure (Set.range (fun i ↦ (g i : G))) = P →
            (∀ M : ℕ, M = Finset.univ.sup (fun i ↦ (w (g i : G)).toNat) →
              ∀ p : P, (w (p : G) : ℝ) / (M : ℝ) ≤ (ν p : ℝ) ∧
                (ν p : ℤ) ≤ w (p : G)) ∧
            (∀ C : ℕ, 1 ≤ C →
              (∀ (i : Fin s) (j : Fin r), |B.repr (g i : G) j| ≤ (C : ℤ)) →
              (∀ n : ℕ+, Set.ncard {p : P | ν p < (n : ℕ)} ≤
                (2 * C * (n : ℕ) + 1) ^ r) ∧
              ∀ n : ℕ+, 2 ≤ (n : ℕ) →
                F n ≤ ((2 * C * (n : ℕ) + 1) ^ r : ℕ) * lam n) ∧
            (∃ v : Fin r → Fin s, LinearIndependent ℤ (fun j ↦ (g (v j) : G))) ∧
            (∀ v : Fin r → Fin s, LinearIndependent ℤ (fun j ↦ (g (v j) : G)) →
              ∀ W : ℕ, W = Finset.univ.sup (fun j ↦ (w (g (v j) : G)).toNat) →
                ∀ n : ℕ+, 2 ≤ (n : ℕ) →
                  Function.Injective
                    (fun b : Fin r → Fin ((n : ℕ) / (4 * r * W) + 1) ↦
                      ∑ j : Fin r, (b j : ℕ) • g (v j)) ∧
                  (∀ b : Fin r → Fin ((n : ℕ) / (4 * r * W) + 1),
                    (ν (∑ j : Fin r, (b j : ℕ) • g (v j)) : ℝ) ≤ (n : ℝ) / 4) ∧
                  ((((n : ℕ) / (4 * r * W) + 1) ^ r : ℕ) : ℝ≥0) *
                    lam (((n : ℕ) / 2).toPNat') ≤ F n)) := by
  classical
  obtain ⟨ν, hν, hν0, hνw⟩ := positive_length_max P w hpos
  obtain ⟨s₀, g₀, hgne₀, hg₀⟩ := nonzero_generators P hfg
  have coords {s : ℕ} (g : Fin s → P) : ∃ C : ℕ, 1 ≤ C ∧
      ∀ (i : Fin s) (j : Fin r), |B.repr (g i : G) j| ≤ (C : ℤ) := by
    let C := max 1 (Finset.univ.sup fun i ↦ Finset.univ.sup fun j ↦
      (B.repr (g i : G) j).natAbs)
    refine ⟨C, le_max_left _ _, ?_⟩
    intro i j
    have hj := Finset.le_sup (f := fun j ↦ (B.repr (g i : G) j).natAbs)
      (Finset.mem_univ j)
    have hi := Finset.le_sup
      (f := fun i ↦ Finset.univ.sup fun j ↦ (B.repr (g i : G) j).natAbs)
      (Finset.mem_univ i)
    have hle : (B.repr (g i : G) j).natAbs ≤ C :=
      hj.trans (hi.trans (le_max_right _ _))
    have hcast : ((B.repr (g i : G) j).natAbs : ℤ) ≤ C := by exact_mod_cast hle
    simpa only [Int.natCast_natAbs] using hcast
  obtain ⟨C₀, _, hcoords₀⟩ := coords g₀
  have hfin (n : ℕ+) : Set.Finite {p : P | ν p < (n : ℕ)} :=
    (generator_coordinate_count B P ν hν g₀ hgne₀ hg₀ C₀ hcoords₀ n).1
  let F : ℕ+ → ℝ≥0 := fun n ↦
    ∑ᶠ p : {p : P // ν p < (n : ℕ)}, lam (((n : ℕ) - ν p.1).toPNat')
  have hupper {s : ℕ} (g : Fin s → P) (hgne : ∀ i, g i ≠ 0)
      (hg : AddSubmonoid.closure (Set.range (fun i ↦ (g i : G))) = P)
      (C : ℕ) (hcoords : ∀ (i : Fin s) (j : Fin r),
        |B.repr (g i : G) j| ≤ (C : ℤ)) (n : ℕ+) :
      F n ≤ ((2 * C * (n : ℕ) + 1) ^ r : ℕ) * lam n := by
    have hc := (generator_coordinate_count B P ν hν g hgne hg C hcoords n).2
    calc
      F n ≤ (Set.ncard {p : P | ν p < (n : ℕ)} : ℝ≥0) * lam n :=
        convolution_upper P ν hfin lam hmono n
      _ ≤ ((2 * C * (n : ℕ) + 1) ^ r : ℕ) * lam n := by
        gcongr
  have hlower {s : ℕ} (g : Fin s → P) (hgne : ∀ i, g i ≠ 0)
      (v : Fin r → Fin s) (hv : LinearIndependent ℤ (fun j ↦ (g (v j) : G)))
      (W : ℕ) (hW : W = Finset.univ.sup (fun j ↦ (w (g (v j) : G)).toNat))
      (n : ℕ+) (hn : 2 ≤ (n : ℕ)) :
      Function.Injective
        (fun b : Fin r → Fin ((n : ℕ) / (4 * r * W) + 1) ↦
          ∑ j, (b j : ℕ) • g (v j)) ∧
      (∀ b : Fin r → Fin ((n : ℕ) / (4 * r * W) + 1),
        (ν (∑ j, (b j : ℕ) • g (v j)) : ℝ) ≤ (n : ℝ) / 4) ∧
      ((((n : ℕ) / (4 * r * W) + 1) ^ r : ℕ) : ℝ≥0) *
        lam (((n : ℕ) / 2).toPNat') ≤ F n := by
    obtain ⟨hi, hs⟩ := independent_box P w hpos ν hνw g hgne v hv W hW n
    exact ⟨hi, hs, convolution_lower P ν hfin lam hmono n hn _ hi hs⟩
  have hzero : r = 0 → P = ⊥ ∧ ∀ n : ℕ+, F n = lam n := by
    intro hr
    subst r
    have hG (x : G) : x = 0 := by
      apply B.repr.injective
      ext i
      exact Fin.elim0 i
    refine ⟨?_, ?_⟩
    · apply le_antisymm _ bot_le
      intro x _
      exact hG x
    · intro n
      let z : {p : P // ν p < (n : ℕ)} := ⟨0, by simp [hν0]⟩
      dsimp [F]
      rw [finsum_eq_single _ z]
      · simp [z, hν0]
      · intro x hx
        exfalso
        apply hx
        apply Subtype.ext
        apply Subtype.ext
        exact hG _
  have hFg : ∃ a' b' : ℝ≥0, 0 < a' ∧ 0 < b' ∧ ∃ n₀ : ℕ+,
      ∀ n : ℕ+, n₀ ≤ n →
        a' * (n : ℝ≥0) ^ (d + r) ≤ F n ∧ F n ≤ b' * (n : ℝ≥0) ^ (d + r) := by
    by_cases hr : r = 0
    · obtain ⟨a, b, ha, hb, k₀, hk⟩ := hgrowth
      refine ⟨a, b, ha, hb, k₀, ?_⟩
      intro n hn
      simpa [hr, (hzero hr).2 n] using hk n hn
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      obtain ⟨v, hv⟩ := independent_generators B P hspan g₀ hg₀
      let W := Finset.univ.sup (fun j ↦ (w (g₀ (v j) : G)).toNat)
      have hWpos : 0 < W := by
        let j : Fin r := ⟨0, hrpos⟩
        have hw := hpos (g₀ (v j)) (hgne₀ (v j))
        have hj : 0 < (w (g₀ (v j) : G)).toNat := by omega
        exact hj.trans_le (Finset.le_sup
          (f := fun j ↦ (w (g₀ (v j) : G)).toNat) (Finset.mem_univ j))
      exact polynomial_of_convolution_bounds r d C₀ (4 * r * W) (by positivity) lam F
        hgrowth (fun n _ ↦ hupper g₀ hgne₀ hg₀ C₀ hcoords₀ n)
        (fun n hn ↦ (hlower g₀ hgne₀ v hv W rfl n hn).2.2)
  refine ⟨ν, hν, hν0, hfin, F, fun _ ↦ rfl, hFg, hzero, ?_⟩
  intro _
  refine ⟨⟨s₀, g₀, hgne₀, hg₀⟩, ?_⟩
  intro s g hgne hg
  refine ⟨?_, ?_, independent_generators B P hspan g hg, ?_⟩
  · intro M hM p
    exact generator_weight_comparison P w hpos ν hν g hgne hg M hM p
  · intro C _ hcoords
    exact ⟨fun n ↦ (generator_coordinate_count B P ν hν g hgne hg C hcoords n).2,
      fun n _ ↦ hupper g hgne hg C hcoords n⟩
  · exact hlower g hgne

end AddSubmonoid
