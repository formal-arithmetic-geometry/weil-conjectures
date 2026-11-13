/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.Subring.Basic

import Mathlib.FieldTheory.Finite.Basic
import WeilConjectures.RingTheory.ArtinSchreierKernel

/-!
# Frobenius-fixed global sections of arbitrary schemes

## Main statements

- `AlgebraicGeometry.Scheme.exists_frobeniusFixedSections_ringEquiv`: the ring of locally constant
  prime-field functions is naturally the subring of Frobenius-fixed global sections. The restriction
  clause characterizes the equivalence as gluing the constants on the open fibres.

## References

* Stacks Project, Etale Cohomology, Tag 0A3J.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace TopCat

namespace AlgebraicGeometry.Scheme

private theorem exists_germ_constant (p : ℕ) (hp : p.Prime) (W : Scheme.{u})
    (b : LocallyConstant W (ZMod p)) :
    ∃ s : Γ(W, ⊤), ∀ x : W,
      W.presheaf.germ ⊤ x (by trivial) s = (ZMod.cast (b x) : W.presheaf.stalk x) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let U : ZMod p → W.Opens := fun a ↦
    ⟨b ⁻¹' {a}, (IsLocallyConstant.iff_isOpen_fiber.mp b.isLocallyConstant a)⟩
  have empty_eq (V : W.Opens) (hV : V = ⊥) (s t : Γ(W, V)) : s = t := by
    apply TopCat.Presheaf.section_ext W.sheaf V s t
    intro x hx
    rw [hV] at hx
    exact False.elim hx
  have hdisj : ∀ a c : ZMod p, a ≠ c → U a ⊓ U c = ⊥ := by
    intro a c hac
    apply le_antisymm
    · intro x hx
      exfalso
      apply hac
      exact (show b x = a from hx.1).symm.trans (show b x = c from hx.2)
    · exact bot_le
  let sf : ∀ a : ZMod p, Γ(W, U a) := fun a ↦ (a.val : Γ(W, U a))
  have hcompat : TopCat.Presheaf.IsCompatible W.sheaf.obj U sf := by
    intro a c
    by_cases hac : a = c
    · subst c
      rfl
    · apply empty_eq (U a ⊓ U c) (hdisj a c hac)
  have hcover : (⊤ : W.Opens) ≤ iSup U := by
    intro x hx
    simp only [Opens.mem_iSup]
    exact ⟨b x, rfl⟩
  obtain ⟨s, hs, _⟩ := TopCat.Sheaf.existsUnique_gluing' W.sheaf U ⊤
    (fun _ ↦ homOfLE (le_top : U _ ≤ ⊤)) hcover sf hcompat
  refine ⟨s, ?_⟩
  intro x
  let a := b x
  have hxU : x ∈ U a := rfl
  have hs' : W.presheaf.map (homOfLE (show U a ≤ ⊤ from le_top)).op s =
      (a.val : Γ(W, U a)) := hs a
  have hg := congrArg (W.presheaf.germ (U a) x hxU) hs'
  simpa only [W.presheaf.germ_res_apply, sf, map_natCast, ZMod.cast_eq_val] using hg

private theorem fixed_germ_locally_constant (p : ℕ) (hp : p.Prime)
    (W : Scheme.{u}) (hW : (p : Γ(W, ⊤)) = 0) (s : Γ(W, ⊤)) (hs : s ^ p = s) :
    ∃ b : LocallyConstant W (ZMod p), ∀ x : W,
      W.presheaf.germ ⊤ x (by trivial) s = (ZMod.cast (b x) : W.presheaf.stalk x) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hchar (x : W) : (p : W.presheaf.stalk x) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (W.presheaf.germ ⊤ x (by trivial)) hW
  have hlocal (x : W) : ∃! a : ZMod p,
      (ZMod.cast a : W.presheaf.stalk x) = W.presheaf.germ ⊤ x (by trivial) s := by
    apply (IsLocalRing.pow_eq_self_iff_existsUnique_zmod p hp (hchar x) _).mp
    simpa only [map_pow] using congrArg (W.presheaf.germ ⊤ x (by trivial)) hs
  choose b hb hbuniq using hlocal
  have hbcont : IsLocallyConstant b := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro a
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    change b x = a at hx
    have heq : W.presheaf.germ ⊤ x (by trivial) s =
        W.presheaf.germ ⊤ x (by trivial) (a.val : Γ(W, ⊤)) := by
      simpa only [map_natCast, ZMod.cast_eq_val, hx] using (hb x).symm
    obtain ⟨V, hxV, i, j, heqV⟩ := W.presheaf.germ_eq x (by trivial) (by trivial) s
      (a.val : Γ(W, ⊤)) heq
    have hV : (V : Set W) ⊆ b ⁻¹' {a} := by
      intro y hy
      change b y = a
      symm
      apply hbuniq y a
      have hh := congrArg (W.presheaf.germ V y hy) heqV
      simpa only [W.presheaf.germ_res_apply, map_natCast, ZMod.cast_eq_val] using hh.symm
    exact Filter.mem_of_superset (V.isOpen.mem_nhds hxV) hV
  exact ⟨⟨b, hbcont⟩, fun x ↦ (hb x).symm⟩

private noncomputable def glued (p : ℕ) (hp : p.Prime) (W : Scheme.{u})
    (b : LocallyConstant W (ZMod p)) : Γ(W, ⊤) :=
  (exists_germ_constant p hp W b).choose

private theorem glued_germ (p : ℕ) (hp : p.Prime) (W : Scheme.{u})
    (b : LocallyConstant W (ZMod p)) (x : W) :
    W.presheaf.germ ⊤ x (by trivial) (glued p hp W b) =
      (ZMod.cast (b x) : W.presheaf.stalk x) :=
  (exists_germ_constant p hp W b).choose_spec x

private theorem stalk_char (p : ℕ) (W : Scheme.{u})
    (hW : (p : Γ(W, ⊤)) = 0) (x : W) : (p : W.presheaf.stalk x) = 0 := by
  simpa only [map_natCast, map_zero] using
    congrArg (W.presheaf.germ ⊤ x (by trivial)) hW

private noncomputable def fixedSubring (p : ℕ) (hp : p.Prime) (W : Scheme.{u})
    (hW : (p : Γ(W, ⊤)) = 0) : Subring Γ(W, ⊤) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  refine
    { carrier := {s | s ^ p = s}
      mul_mem' := ?_
      one_mem' := ?_
      add_mem' := ?_
      zero_mem' := ?_
      neg_mem' := ?_ }
  · intro a b ha hb
    change (a * b) ^ p = a * b
    rw [mul_pow, ha, hb]
  · simp
  · intro a b ha hb
    change (a + b) ^ p = a + b
    apply TopCat.Presheaf.section_ext W.sheaf ⊤
    intro x hx
    have : CharP (W.presheaf.stalk x) p :=
      (CharP.charP_iff_prime_eq_zero hp).mpr (stalk_char p W hW x)
    change W.presheaf.germ ⊤ x hx ((a + b) ^ p) = W.presheaf.germ ⊤ x hx (a + b)
    rw [map_pow, map_add, add_pow_char, ← map_pow, ha, ← map_pow, hb]
  · simp [hp.ne_zero]
  · intro a ha
    change (-a) ^ p = -a
    apply TopCat.Presheaf.section_ext W.sheaf ⊤
    intro x hx
    have : CharP (W.presheaf.stalk x) p :=
      (CharP.charP_iff_prime_eq_zero hp).mpr (stalk_char p W hW x)
    have hh : W.presheaf.germ ⊤ x hx a ^ p = W.presheaf.germ ⊤ x hx a := by
      simpa only [map_pow] using congrArg (W.presheaf.germ ⊤ x hx) ha
    change W.presheaf.germ ⊤ x hx ((-a) ^ p) = W.presheaf.germ ⊤ x hx (-a)
    have hz := sub_pow_char (0 : W.presheaf.stalk x) (W.presheaf.germ ⊤ x hx a) (p := p)
    simpa only [zero_sub, zero_pow hp.ne_zero, hh, map_pow, map_neg] using hz

private theorem mem_fixedSubring (p : ℕ) (hp : p.Prime) (W : Scheme.{u})
    (hW : (p : Γ(W, ⊤)) = 0) (s : Γ(W, ⊤)) :
    s ∈ fixedSubring p hp W hW ↔ s ^ p = s := by
  unfold fixedSubring
  rfl

private theorem glued_fixed (p : ℕ) (hp : p.Prime) (W : Scheme.{u})
    (hW : (p : Γ(W, ⊤)) = 0) (b : LocallyConstant W (ZMod p)) :
    glued p hp W b ^ p = glued p hp W b := by
  have : Fact p.Prime := ⟨hp⟩
  apply TopCat.Presheaf.section_ext W.sheaf ⊤
  intro x hx
  have : CharP (W.presheaf.stalk x) p :=
    (CharP.charP_iff_prime_eq_zero hp).mpr (stalk_char p W hW x)
  change W.presheaf.germ ⊤ x hx (glued p hp W b ^ p) =
    W.presheaf.germ ⊤ x hx (glued p hp W b)
  rw [map_pow, glued_germ, ← ZMod.cast_pow dvd_rfl, ZMod.pow_card]

private noncomputable def gluedHom (p : ℕ) (hp : p.Prime) (W : Scheme.{u})
    (hW : (p : Γ(W, ⊤)) = 0) : LocallyConstant W (ZMod p) →+* fixedSubring p hp W hW where
  toFun b := ⟨glued p hp W b, (mem_fixedSubring p hp W hW _).mpr (glued_fixed p hp W hW b)⟩
  map_one' := by
    apply Subtype.ext
    apply TopCat.Presheaf.section_ext W.sheaf ⊤
    intro x hx
    change W.presheaf.germ ⊤ x hx (glued p hp W 1) = W.presheaf.germ ⊤ x hx 1
    have : Fact p.Prime := ⟨hp⟩
    have : CharP (W.presheaf.stalk x) p :=
      (CharP.charP_iff_prime_eq_zero hp).mpr (stalk_char p W hW x)
    rw [map_one, glued_germ]
    exact ZMod.cast_one (R := W.presheaf.stalk x) (m := p) dvd_rfl
  map_mul' b c := by
    apply Subtype.ext
    apply TopCat.Presheaf.section_ext W.sheaf ⊤
    intro x hx
    have : Fact p.Prime := ⟨hp⟩
    have : CharP (W.presheaf.stalk x) p :=
      (CharP.charP_iff_prime_eq_zero hp).mpr (stalk_char p W hW x)
    change W.presheaf.germ ⊤ x hx (glued p hp W (b * c)) =
      W.presheaf.germ ⊤ x hx (glued p hp W b * glued p hp W c)
    rw [map_mul, glued_germ, glued_germ, glued_germ]
    exact ZMod.cast_mul dvd_rfl _ _
  map_zero' := by
    apply Subtype.ext
    apply TopCat.Presheaf.section_ext W.sheaf ⊤
    intro x hx
    change W.presheaf.germ ⊤ x hx (glued p hp W 0) = W.presheaf.germ ⊤ x hx 0
    rw [map_zero, glued_germ]
    exact ZMod.cast_zero
  map_add' b c := by
    apply Subtype.ext
    apply TopCat.Presheaf.section_ext W.sheaf ⊤
    intro x hx
    have : Fact p.Prime := ⟨hp⟩
    have : CharP (W.presheaf.stalk x) p :=
      (CharP.charP_iff_prime_eq_zero hp).mpr (stalk_char p W hW x)
    change W.presheaf.germ ⊤ x hx (glued p hp W (b + c)) =
      W.presheaf.germ ⊤ x hx (glued p hp W b + glued p hp W c)
    rw [map_add, glued_germ, glued_germ, glued_germ]
    exact ZMod.cast_add dvd_rfl _ _

private theorem gluedHom_bijective (p : ℕ) (hp : p.Prime) (W : Scheme.{u})
    (hW : (p : Γ(W, ⊤)) = 0) : Function.Bijective (gluedHom p hp W hW) := by
  have : Fact p.Prime := ⟨hp⟩
  constructor
  · intro b c hbc
    apply LocallyConstant.ext
    intro x
    have : CharP (W.presheaf.stalk x) p :=
      (CharP.charP_iff_prime_eq_zero hp).mpr (stalk_char p W hW x)
    apply ZMod.castHom_injective (W.presheaf.stalk x)
    have hh := congrArg (fun z ↦ W.presheaf.germ ⊤ x (by trivial) z.val) hbc
    change W.presheaf.germ ⊤ x (by trivial) (glued p hp W b) =
      W.presheaf.germ ⊤ x (by trivial) (glued p hp W c) at hh
    simpa only [glued_germ, ZMod.castHom_apply] using hh
  · intro s
    obtain ⟨b, hb⟩ := fixed_germ_locally_constant p hp W hW s.val
      ((mem_fixedSubring p hp W hW _).mp s.property)
    refine ⟨b, Subtype.ext ?_⟩
    apply TopCat.Presheaf.section_ext W.sheaf ⊤
    intro x hx
    exact (glued_germ p hp W b x).trans (hb x).symm

/-- Frobenius-fixed global sections are locally constant prime-field functions, naturally in every
scheme on which `p` vanishes. The existential subring has exactly the carrier `e ^ p = e`, and the
restriction clause specifies the canonical gluing map, rather than an arbitrary equivalence.
The scalar `a.val` denotes the canonical constant `a · 1`, including in the zero section ring.
(Stacks, Tag 0A3J) -/
theorem exists_frobeniusFixedSections_ringEquiv (p : ℕ) (hp : p.Prime) :
    ∃ S : (W : Scheme.{u}) → (p : Γ(W, ⊤)) = 0 → Subring Γ(W, ⊤),
    ∃ ι : (W : Scheme.{u}) → (hW : (p : Γ(W, ⊤)) = 0) →
      LocallyConstant W (ZMod p) ≃+* S W hW,
    ∀ (W : Scheme.{u}) (hW : (p : Γ(W, ⊤)) = 0),
      (∀ e : Γ(W, ⊤), e ∈ S W hW ↔ e ^ p = e) ∧
      (∀ (b : LocallyConstant W (ZMod p)) (a : ZMod p) (U : W.Opens),
        (U : Set W) = {w : W | b w = a} →
        W.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          ((ι W hW b : S W hW) : Γ(W, ⊤)) = (a.val : Γ(W, U))) ∧
      (∀ a : ZMod p,
        ((ι W hW (LocallyConstant.const W a) : S W hW) : Γ(W, ⊤)) =
          (a.val : Γ(W, ⊤))) ∧
      (∀ (W' : Scheme.{u}) (hW' : (p : Γ(W', ⊤)) = 0) (v : W' ⟶ W)
        (b : LocallyConstant W (ZMod p)),
        v.appTop ((ι W hW b : S W hW) : Γ(W, ⊤)) =
          ((ι W' hW' (LocallyConstant.comap v.base.hom b) : S W' hW') : Γ(W', ⊤))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let S := fixedSubring p hp
  let ι (W : Scheme.{u}) (hW : (p : Γ(W, ⊤)) = 0) :=
    RingEquiv.ofBijective (gluedHom p hp W hW) (gluedHom_bijective p hp W hW)
  refine ⟨S, ι, ?_⟩
  intro W hW
  refine ⟨fun e ↦ mem_fixedSubring p hp W hW e, ?_, ?_, ?_⟩
  · intro b a U hU
    change W.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (glued p hp W b) = _
    apply TopCat.Presheaf.section_ext W.sheaf U
    intro x hx
    have hbx : b x = a := by
      have : x ∈ ({w : W | b w = a} : Set W) := hU ▸ hx
      exact this
    change W.presheaf.germ U x hx
      (W.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (glued p hp W b)) =
        W.presheaf.germ U x hx (a.val : Γ(W, U))
    rw [W.presheaf.germ_res_apply, glued_germ, map_natCast, hbx, ZMod.cast_eq_val]
  · intro a
    change glued p hp W (LocallyConstant.const W a) = _
    apply TopCat.Presheaf.section_ext W.sheaf ⊤
    intro x hx
    change W.presheaf.germ ⊤ x hx (glued p hp W (LocallyConstant.const W a)) =
      W.presheaf.germ ⊤ x hx (a.val : Γ(W, ⊤))
    rw [glued_germ, map_natCast, ZMod.cast_eq_val]
    rfl
  · intro W' hW' v b
    change v.appTop (glued p hp W b) = glued p hp W' (LocallyConstant.comap v.base.hom b)
    apply TopCat.Presheaf.section_ext W'.sheaf ⊤
    intro x hx
    change W'.presheaf.germ ⊤ x hx (v.appTop (glued p hp W b)) =
      W'.presheaf.germ ⊤ x hx (glued p hp W' (LocallyConstant.comap v.base.hom b))
    have hnat := v.germ_stalkMap_apply ⊤ x (by trivial) (glued p hp W b)
    change v.stalkMap x (W.presheaf.germ ⊤ (v x) (by trivial) (glued p hp W b)) =
      W'.presheaf.germ ⊤ x hx (v.appTop (glued p hp W b)) at hnat
    rw [← hnat, glued_germ, glued_germ]
    simp only [ZMod.cast_eq_val, map_natCast]
    rfl

end AlgebraicGeometry.Scheme
