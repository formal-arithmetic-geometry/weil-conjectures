/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.RingTheory.FiniteProjectiveK0
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Finiteness.Prod

/-!
# The K₀ class of a finite projective module with a finite free resolution

Source: literature/stacks-project/more-algebra.tex, Tag 0AFY
(blueprint: lem-trf-invertible-module-k0-class).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

open Module

namespace Module.FiniteProjectiveK0

private theorem presentation_equiv {S : Type u} [CommRing S]
    {P Q : Presentation S}
    (h : (Quot.mk _ P : Classes S) = Quot.mk _ Q) :
    Nonempty (P.Carrier ≃ₗ[S] Q.Carrier) := by
  have hh := Quot.eq.mp h
  clear h
  induction hh with
  | rel _ _ h => exact h
  | refl _ => exact ⟨LinearEquiv.refl _ _⟩
  | symm _ _ _ ih => exact ⟨ih.some.symm⟩
  | trans _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.some.trans ih₂.some⟩

private theorem mk_equiv {S : Type u} [CommRing S]
    {A : Type*} {B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module S A] [Module S B] [Module.Finite S A] [Module.Projective S A]
    [Module.Finite S B] [Module.Projective S B] (e : A ≃ₗ[S] B) :
    mk S A = mk S B := by
  unfold mk
  congr 2
  exact Quot.sound ⟨(Module.Finite.reprEquiv S A).trans
    (e.trans (Module.Finite.reprEquiv S B).symm)⟩

private theorem mk_prod {S : Type u} [CommRing S]
    (A : Type*) (B : Type*) [AddCommGroup A] [AddCommGroup B]
    [Module S A] [Module S B] [Module.Finite S A] [Module.Projective S A]
    [Module.Finite S B] [Module.Projective S B] :
    mk S (A × B) = mk S A + mk S B := by
  classical
  let a : Classes S := Quot.mk _ (presentationOf S A)
  let b : Classes S := Quot.mk _ (presentationOf S B)
  have ea := (presentation_equiv (Quot.out_eq a)).some
  have eb := (presentation_equiv (Quot.out_eq b)).some
  have e : (sumPresentation S a.out b.out).Carrier ≃ₗ[S] A × B :=
    (sumEquiv S a.out b.out).trans
      ((ea.trans (Module.Finite.reprEquiv S A)).prodCongr
        (eb.trans (Module.Finite.reprEquiv S B)))
  have hc : sumClass S a b = Quot.mk _ (presentationOf S (A × B)) :=
    Quot.sound ⟨e.trans (Module.Finite.reprEquiv S (A × B)).symm⟩
  have hr := (relations S).toQuotient_relation (a, b)
  change (relations S).toQuotient
    (Finsupp.single a 1 + Finsupp.single b 1 - Finsupp.single (sumClass S a b) 1) = 0 at hr
  rw [map_sub, map_add, hc] at hr
  exact (sub_eq_zero.mp hr).symm

private theorem mk_fin {S : Type u} [CommRing S] (n : ℕ) :
    mk S (Fin n → S) = (n : ℤ) • mk S S := by
  induction n with
  | zero =>
    have e : (Fin 0 → S) ≃ₗ[S] ((Fin 0 → S) × (Fin 0 → S)) :=
      LinearEquiv.ofSubsingleton (R := S) _ _
    have h := (mk_equiv e).trans (mk_prod (Fin 0 → S) (Fin 0 → S))
    have hz : mk S (Fin 0 → S) = 0 := by
      exact add_left_cancel (a := mk S (Fin 0 → S)) (by simpa using h.symm)
    simpa using hz
  | succ n ih =>
    rw [mk_equiv (Fin.consLinearEquiv S (fun _ : Fin (n + 1) ↦ S)).symm,
      mk_prod, ih]
    simp [add_smul, add_comm]

/--
A finite free resolution gives the alternating sum of the classes of its free terms.
The family `M` encodes the displayed sequence: `M 0` is `L`, and `M (i.succ)` is
`F_i`; the map indexed by `i` goes from the term at `i.succ` to the term at `i`.
The hypotheses `hsurj` and `hinj` express exactness at the two endpoints, while
`hexact` expresses exactness at every interior term.  The basis hypothesis records
that `F_i` has a basis with `r i` elements.

Source: Stacks Project, More on Algebra, Tag 0AFY (more-algebra-lemma-perfect-to-K-group),
clauses (2) and (3), lines 36491--36558
(blueprint: lem-trf-invertible-module-k0-class).

Proof:
1. Let the successive syzygies be the images and kernels in the given exact
   sequence. Exactness produces short exact sequences between consecutive
   syzygies, with the leftmost map an isomorphism.
2. Starting with the finitely generated projective module `L`, split each short
   exact sequence using the projective lifting property. Each next syzygy is a
   finitely generated projective direct summand of a finite free module. This
   uses `def-weil-pbc-projective-module`, `def-weil-pbc-free-module`,
   `def-weil-finitely-generated-module`, and `def-weil-pbc-exact-sequence`.
3. In `def-trf-k0-group`, split sequences give `[F_i] = [K_(i+1)] + [K_i]`
   (and `[F_d] = [K_d]`), so the alternating sum telescopes to `[L]`.
4. A basis of `r_i` elements identifies `F_i` with `S^(r_i)`. The direct-sum
   relation in `def-trf-k0-group` therefore gives `[F_i] = r_i [S]`, yielding
   the displayed alternating sum and hence the final existential assertion.
-/
theorem class_of_finite_free_resolution
    (S : Type u) [CommRing S]
    (d : ℕ) (r : Fin (d + 1) → ℕ)
    (M : Fin (d + 2) → Type v)
    [hAdd : ∀ i, AddCommGroup (M i)] [hMod : ∀ i, Module S (M i)]
    [Module.Finite S (M 0)] [Module.Projective S (M 0)]
    (h : ∀ i : Fin (d + 1),
      M i.succ →ₗ[S] M i.castSucc)
    (hfree : ∀ i : Fin (d + 1),
      Nonempty (Basis (Fin (r i)) S (M i.succ)))
    (hexact : ∀ i : Fin d,
      Function.Exact (h i.succ) (h i.castSucc))
    (hsurj : Function.Surjective (h 0))
    (hinj : Function.Injective (h (Fin.last d))) :
    mk S (M 0) =
        (∑ i : Fin (d + 1), (-1 : ℤ) ^ (i : ℕ) * (r i : ℤ)) • mk S S ∧
      ∃ n : ℤ, mk S (M 0) = n • mk S S := by
  classical
  suffices hc : mk S (M 0) =
      (∑ i : Fin (d + 1), (-1 : ℤ) ^ (i : ℕ) * (r i : ℤ)) • mk S S from
    ⟨hc, _, hc⟩
  induction d with
  | zero =>
    have : Module.Finite S (M (0 : Fin 1).castSucc) := by
      simpa only [Fin.castSucc_zero] using ‹Module.Finite S (M 0)›
    have : Module.Projective S (M (0 : Fin 1).castSucc) := by
      simpa only [Fin.castSucc_zero] using ‹Module.Projective S (M 0)›
    have : Module.Finite S (M (0 : Fin 1).succ) := Module.Finite.of_basis (hfree 0).some
    have : Module.Projective S (M (0 : Fin 1).succ) :=
      Module.Projective.of_basis (hfree 0).some
    let e := LinearEquiv.ofBijective (h 0) ⟨hinj, hsurj⟩
    have hc := mk_equiv ((hfree 0).some.equivFun.symm.trans e)
    simpa using hc.symm.trans (mk_fin (r 0))
  | succ d ih =>
    have : Module.Finite S (M (0 : Fin (d + 2)).succ) :=
      Module.Finite.equiv (hfree 0).some.equivFun.symm
    have : Module.Projective S (M (0 : Fin (d + 2)).succ) :=
      Module.Projective.of_basis (hfree 0).some
    have : Module.Projective S (M (0 : Fin (d + 2)).castSucc) := by
      simpa only [Fin.castSucc_zero] using ‹Module.Projective S (M 0)›
    obtain ⟨s, hs⟩ := Module.projective_lifting_property (h 0) LinearMap.id hsurj
    let K := LinearMap.ker (h 0)
    let e : M (0 : Fin (d + 2)).succ ≃ₗ[S] K × M 0 :=
      ((LinearMap.exact_subtype_ker_map (h 0)).splitSurjectiveEquiv
        K.injective_subtype ⟨s, hs⟩).val
    let p := (LinearMap.fst S K (M 0)).comp e.toLinearMap
    let j := e.symm.toLinearMap.comp (LinearMap.inl S K (M 0))
    have hp : p.comp j = LinearMap.id := by
      apply LinearMap.ext
      intro x
      change (e (e.symm (x, 0))).1 = x
      exact congrArg Prod.fst (e.apply_symm_apply (x, 0))
    have hKfinite : Module.Finite S K := Module.Finite.of_surjective p (by
      intro x; exact ⟨j x, DFunLike.congr_fun hp x⟩)
    have hKprojective : Module.Projective S K := Module.Projective.of_split j p hp
    have hc : mk S (M (0 : Fin (d + 2)).succ) = mk S K + mk S (M 0) :=
      (mk_equiv e).trans (mk_prod K (M 0))
    let N : Fin (d + 2) → Type v :=
      Fin.cases K (fun i ↦ M i.succ.succ)
    let addN : ∀ i, AddCommGroup (N i) := by
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · dsimp [N]; infer_instance
      · dsimp [N]; infer_instance
    let modN : ∀ i, Module S (N i) := by
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · dsimp [N, addN]; infer_instance
      · dsimp [N, addN]; infer_instance
    let g : M (1 : Fin (d + 2)).succ →ₗ[S] K :=
      (h 1).codRestrict K (fun x ↦ (hexact 0).apply_apply_eq_zero x)
    let hN : ∀ i : Fin (d + 1), N i.succ →ₗ[S] N i.castSucc :=
      Fin.cases g (fun i ↦ h i.succ.succ)
    have exactN : ∀ i : Fin d, Function.Exact (hN i.succ) (hN i.castSucc) := by
      cases d with
      | zero => exact fun i ↦ Fin.elim0 i
      | succ d =>
        intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · intro x
          constructor
          · intro hx
            have hx' : (h 1) x = 0 := congrArg Subtype.val hx
            obtain ⟨y, hy⟩ := (hexact 1 x).mp hx'
            exact ⟨y, hy⟩
          · rintro ⟨y, rfl⟩
            apply Subtype.ext
            exact (hexact 1).apply_apply_eq_zero y
        · exact hexact j.succ.succ
    have surjN : Function.Surjective (hN 0) := by
      intro x
      change K at x
      obtain ⟨y, hy⟩ := (hexact 0 x.val).mp x.property
      exact ⟨y, Subtype.ext hy⟩
    have injN : Function.Injective (hN (Fin.last d)) := by
      cases d with
      | zero =>
        intro x y hh
        exact hinj (congrArg Subtype.val hh)
      | succ d => exact hinj
    have : Module.Finite S (N 0) := hKfinite
    have : Module.Projective S (N 0) := hKprojective
    have hn : mk S K = (∑ i : Fin (d + 1), (-1 : ℤ) ^ i.val * (r i.succ : ℤ)) •
        mk S S := ih (fun i ↦ r i.succ) N hN (fun i ↦ by
      simpa [N] using hfree i.succ) exactN surjN injN
    have hf : mk S (M (0 : Fin (d + 2)).succ) = (r 0 : ℤ) • mk S S :=
      (mk_equiv (hfree 0).some.equivFun).trans (mk_fin (r 0))
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ', neg_mul]
    rw [Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_smul, ← hn]
    exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hc.symm.trans hf)

end Module.FiniteProjectiveK0
