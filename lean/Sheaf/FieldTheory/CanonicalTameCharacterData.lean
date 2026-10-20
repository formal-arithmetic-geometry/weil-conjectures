/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.FieldTheory.TameRootsProduct
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology

import Sheaf.FieldTheory.FiniteCanonicalKummerCharacter
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Construction of the canonical tame character. -/

@[expose] public section
set_option autoImplicit false
universe u v w z
namespace IsDiscreteValuationRing

private theorem tame_order_isUnit
    (R : Type u) [CommRing R] [IsLocalRing R]
    (p : ℕ) (hp : p = if ringChar (IsLocalRing.ResidueField R) = 0 then 1
      else ringChar (IsLocalRing.ResidueField R)) (d : TameRoots.Order p) :
    IsUnit (d.1 : R) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  rw [map_natCast]
  change ¬(d.1 : IsLocalRing.ResidueField R) = 0
  rw [ringChar.spec]
  by_cases h : ringChar (IsLocalRing.ResidueField R) = 0
  · simpa [h] using d.2.1.ne'
  · have hp' : p = ringChar (IsLocalRing.ResidueField R) := by simpa [h] using hp
    intro hd
    have : p = 1 := Nat.eq_one_of_dvd_coprimes d.2.2 (hp' ▸ hd) dvd_rfl
    exact CharP.ringChar_ne_one (R := IsLocalRing.ResidueField R) (hp' ▸ this)

private theorem mem_tame_limit {F : Type z} [Field F] {p : ℕ}
    (x : TameRoots.Order p → Fˣ) : x ∈ TameRoots.limitSubgroup F p ↔
      (∀ d, x d ^ d.1 = 1) ∧
      ∀ d e : TameRoots.Order p, d.1 ∣ e.1 → x e ^ (e.1 / d.1) = x d := by
  simp only [TameRoots.limitSubgroup, Subgroup.mem_inf, Subgroup.mem_pi,
    Set.mem_univ, forall_const, Subgroup.mem_iInf, MonoidHom.eqLocus]
  rfl

private theorem compatible_radical_family
    (F : Type w) [Field F] [IsSepClosed F] (p : ℕ)
    (hn : ∀ d : TameRoots.Order p, (d.1 : F) ≠ 0) (a : F) :
    ∃ α : TameRoots.Order p → F, (∀ d, α d ^ d.1 = a) ∧
      ∀ d e : TameRoots.Order p, d.1 ∣ e.1 → α e ^ (e.1 / d.1) = α d := by
  classical
  let : LE (TameRoots.Order p) := ⟨fun d e ↦ d.1 ∣ e.1⟩
  let : LT (TameRoots.Order p) := ⟨fun d e ↦ d.1 ∣ e.1 ∧ ¬e.1 ∣ d.1⟩
  let : Preorder (TameRoots.Order p) := {
    le d e := d.1 ∣ e.1
    le_refl d := dvd_refl d.1
    le_trans _ _ _ := dvd_trans }
  let : IsDirectedOrder (TameRoots.Order p) := ⟨fun d e ↦
    ⟨⟨d.1 * e.1, Nat.mul_pos d.2.1 e.2.1, d.2.2.mul_left e.2.2⟩,
      dvd_mul_right _ _, dvd_mul_left _ _⟩⟩
  let A := fun d : TameRoots.Order p ↦ {x : F // x ^ d.1 = a}
  have hfinite (d : TameRoots.Order p) : Finite (A d) := by
    have h := Polynomial.finite_setOfPred_isRoot
      (Polynomial.monic_X_pow_sub_C a d.2.1.ne').ne_zero
    have h' : Set.Finite {x : F | x ^ d.1 = a} := by
      simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using h
    exact h'.to_subtype
  have hnonempty (d : TameRoots.Order p) : Nonempty (A d) := by
    let : NeZero (d.1 : F) := ⟨hn d⟩
    obtain ⟨x, hx⟩ := IsSepClosed.exists_pow_nat_eq a d.1
    exact ⟨⟨x, hx⟩⟩
  let S : CategoryTheory.Functor (TameRoots.Order p)ᵒᵖ (Type w) := {
    obj := fun d ↦ A d.unop
    map := fun {d e} f ↦ TypeCat.ofHom fun x ↦ ⟨x.1 ^ (d.unop.1 / e.unop.1), by
      rw [← pow_mul, Nat.div_mul_cancel (CategoryTheory.leOfHom f.unop)]
      exact x.2⟩
    map_id := by
      intro d
      ext x
      simp [Nat.div_self d.unop.2.1]
    map_comp := by
      intro d e f h k
      ext x
      dsimp
      rw [← pow_mul]
      congr 1
      apply Nat.eq_of_mul_eq_mul_right f.unop.2.1
      rw [Nat.mul_assoc, Nat.div_mul_cancel (CategoryTheory.leOfHom k.unop),
        Nat.div_mul_cancel (CategoryTheory.leOfHom h.unop),
        Nat.div_mul_cancel
          (dvd_trans (CategoryTheory.leOfHom k.unop) (CategoryTheory.leOfHom h.unop))] }
  let : ∀ d, Finite (S.obj d) := fun d ↦ hfinite d.unop
  let : ∀ d, Nonempty (S.obj d) := fun d ↦ hnonempty d.unop
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system S
  exact ⟨fun d ↦ (s (.op d)).1, fun d ↦ (s (.op d)).2,
    fun d e h ↦ congrArg Subtype.val (hs (CategoryTheory.homOfLE h).op)⟩

/-- Construction part of the canonical tame character theorem. The proof follows the root
extension and compatible-family construction in Expose XVII, section 1.2.

Proof: Each prime-to-p order is a unit of R and remains nonzero in Ksep. The finite root
sets of X^d-π form an inverse system by divisibility powers. Finite inverse-system
compactness gives compatible radicals. The finite canonical Kummer characters have the
same power compatibility by their formulas, and hence assemble into the actual tame root
limit. Continuity holds coordinatewise. For any target family, each finite-coordinate
fiber is nonempty by finite character surjectivity and is closed in the compact absolute
Galois group. The fibers are directed by intersection using the product of two orders.
Their intersection is nonempty, proving surjectivity without extending a union of fields.
The finite character formula gives the required formula for every uniformizer and every
compatible family at once.
(blueprint: lem-per-trait-tame-character-data). -/
theorem canonical_tame_character_data
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsStrictlyHenselianLocalRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (Ksep : Type w) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (Ω : Type z) [Field Ω] [IsAlgClosed Ω] [Algebra Ksep Ω]
    (p : ℕ) (hp : p = if ringChar (IsLocalRing.ResidueField R) = 0 then 1
      else ringChar (IsLocalRing.ResidueField R)) :
    ∃ t : Gal(Ksep/K) →* TameRoots.limitSubgroup Ω p,
      @Continuous _ _ inferInstance (TameRoots.limitTopology Ω p) t ∧
      Function.Surjective t ∧
      (∀ π : R, Irreducible π →
        ∃ α : TameRoots.Order p → Ksep,
          (∀ d : TameRoots.Order p,
            α d ^ d.1 = algebraMap K Ksep (algebraMap R K π)) ∧
          ∀ d e : TameRoots.Order p, d.1 ∣ e.1 → α e ^ (e.1 / d.1) = α d) ∧
      (∀ (π : R), Irreducible π → ∀ α : TameRoots.Order p → Ksep,
        (∀ d : TameRoots.Order p,
          α d ^ d.1 = algebraMap K Ksep (algebraMap R K π)) →
        (∀ d e : TameRoots.Order p, d.1 ∣ e.1 → α e ^ (e.1 / d.1) = α d) →
        ∀ (h : Gal(Ksep/K)) (d : TameRoots.Order p),
          (((t h).1 d : Ωˣ) : Ω) = algebraMap Ksep Ω (h (α d) / α d)) := by
  classical
  have : IsSepClosed Ksep := IsSepClosure.sep_closed K
  have hn (d : TameRoots.Order p) : (d.1 : Ksep) ≠ 0 := by
    have hu := (tame_order_isUnit R p hp d).map
      ((algebraMap K Ksep).comp (algebraMap R K))
    simpa only [RingHom.coe_comp, Function.comp_apply, map_natCast] using hu.ne_zero
  have hroots (π : R) (_ : Irreducible π) :=
    compatible_radical_family Ksep p hn (algebraMap K Ksep (algebraMap R K π))
  choose χ hχc hχs hχf using fun d : TameRoots.Order p ↦
    finite_canonical_kummer_character R K Ksep Ω d.1 d.2.1
      (tame_order_isUnit R p hp d)
  obtain ⟨π, hπ⟩ := exists_irreducible R
  obtain ⟨α, hα, hαc⟩ := hroots π hπ
  have hcomp (h : Gal(Ksep/K)) (d e : TameRoots.Order p) (hde : d.1 ∣ e.1) :
      (χ e h : Ωˣ) ^ (e.1 / d.1) = (χ d h : Ωˣ) := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val]
    rw [hχf e π hπ (α e) (hα e), ← map_pow, div_pow, ← map_pow,
      hαc d e hde, hχf d π hπ (α d) (hα d)]
  let t : Gal(Ksep/K) →* TameRoots.limitSubgroup Ω p := {
    toFun h := ⟨fun d ↦ (χ d h : Ωˣ), (mem_tame_limit _).mpr
      ⟨fun d ↦ (mem_rootsOfUnity _ _).mp (χ d h).2, hcomp h⟩⟩
    map_one' := Subtype.ext (funext fun d ↦ congrArg Subtype.val (map_one (χ d)))
    map_mul' h k := Subtype.ext (funext fun d ↦ congrArg Subtype.val (map_mul (χ d) h k)) }
  have ht : @Continuous _ _ inferInstance (TameRoots.limitTopology Ω p) t := by
    apply continuous_iInf_rng.mpr
    intro d
    exact continuous_induced_rng.mpr (hχc d)
  have hs : Function.Surjective t := by
    intro x
    let : TopologicalSpace Ωˣ := ⊥
    let : DiscreteTopology Ωˣ := ⟨rfl⟩
    let A (d : TameRoots.Order p) : Set Gal(Ksep/K) :=
      {h | (χ d h : Ωˣ) = x.1 d}
    have hclosed (d : TameRoots.Order p) : IsClosed (A d) :=
      isClosed_singleton.preimage (hχc d)
    have hnonempty (d : TameRoots.Order p) : (A d).Nonempty := by
      let y : rootsOfUnity d.1 Ω :=
        ⟨x.1 d, ((mem_tame_limit x.1).mp x.2).1 d⟩
      obtain ⟨h, hh⟩ := hχs d y
      exact ⟨h, congrArg Subtype.val hh⟩
    have hdir : Directed (· ⊇ ·) A := by
      intro d e
      let f : TameRoots.Order p :=
        ⟨d.1 * e.1, Nat.mul_pos d.2.1 e.2.1, d.2.2.mul_left e.2.2⟩
      refine ⟨f, ?_, ?_⟩
      · intro h hh
        exact (hcomp h d f (dvd_mul_right _ _)).symm.trans
          ((congrArg (fun z : Ωˣ ↦ z ^ (f.1 / d.1)) hh).trans
            (((mem_tame_limit x.1).mp x.2).2 d f (dvd_mul_right _ _)))
      · intro h hh
        exact (hcomp h e f (dvd_mul_left _ _)).symm.trans
          ((congrArg (fun z : Ωˣ ↦ z ^ (f.1 / e.1)) hh).trans
            (((mem_tame_limit x.1).mp x.2).2 e f (dvd_mul_left _ _)))
    let : Nonempty (TameRoots.Order p) := ⟨⟨1, by simp⟩⟩
    obtain ⟨h, hh⟩ :=
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed A hdir
        hnonempty (fun d ↦ (hclosed d).isCompact) hclosed
    exact ⟨h, Subtype.ext (funext fun d ↦ Set.mem_iInter.mp hh d)⟩
  exact ⟨t, ht, hs, hroots, fun π hπ α hα _ h d ↦ hχf d π hπ (α d) (hα d) h⟩

end IsDiscreteValuationRing
