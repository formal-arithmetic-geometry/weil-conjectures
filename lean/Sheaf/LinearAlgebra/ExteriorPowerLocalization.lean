/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Localization.Module
import Mathlib.Algebra.Module.LocalizedModule.Int

/-! # Localization of exterior powers

Source: the localization argument of
`new-q1-exterior-sheaf-affine-unit-bijective`, step 2, using the alternating
universal property of exterior powers (Stacks Project, Algebra, Section 00DM).
(blueprint: new-v2-exterior-power-localization). -/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory

namespace exteriorPower

-- Extend one variable at a time, currying the remaining variables into the codomain.
private theorem extend_multilinear
    {R B M N : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (S : Submonoid R) [IsLocalization S B]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] (n : ℕ)
    {P : Type u} [AddCommGroup P] [Module R P] [Module B P] [IsScalarTower R B P]
    (p : MultilinearMap R (fun _ : Fin n ↦ M) P) :
    ∃ F : MultilinearMap R (fun _ : Fin n ↦ N) P,
      ∀ a : Fin n → M, F (fun i ↦ f (a i)) = p a := by
  induction n generalizing P with
  | zero =>
    refine ⟨MultilinearMap.constOfIsEmpty R _ (p 0), ?_⟩
    intro a
    change p 0 = p a
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    let := isLocalizedModule_id S P B
    obtain ⟨F, hF⟩ := ih p.curryRight
    let T := IsLocalizedModule.map S f (LinearMap.id (R := R) (M := P))
    refine ⟨(T.compMultilinearMap F).uncurryRight, ?_⟩
    intro a
    change T (F (fun i ↦ f (a i.castSucc))) (f (a (Fin.last n))) = p a
    rw [hF]
    simp only [T, IsLocalizedModule.map_apply, LinearMap.id_apply,
      MultilinearMap.curryRight_apply]
    change p (Fin.snoc (Fin.init a) (a (Fin.last n))) = p a
    rw [Fin.snoc_init_self]

-- A common denominator reduces equality to the tuples of numerators.
private theorem localized_multilinear_ext
    {R B M N P : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (S : Submonoid R) [IsLocalization S B]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f]
    [AddCommGroup P] [Module R P] [Module B P] [IsScalarTower R B P]
    {n : ℕ} (F G : MultilinearMap R (fun _ : Fin n ↦ N) P)
    (h : ∀ a : Fin n → M, F (fun i ↦ f (a i)) = G (fun i ↦ f (a i))) :
    F = G := by
  classical
  let := isLocalizedModule_id S P B
  ext v
  obtain ⟨t, ht⟩ := IsLocalizedModule.exist_integer_multiples_of_finite S f v
  choose a ha using ht
  have hv : (fun i ↦ f (a i)) = fun i ↦ (t : R) • v i := funext ha
  have he := h a
  rw [hv, F.map_smul_univ, G.map_smul_univ] at he
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at he
  exact IsLocalizedModule.smul_injective (LinearMap.id (R := R) (M := P))
    (t ^ n) he

-- Recover B-linearity coordinatewise and preserve alternation using equal numerators.
private theorem extend_alternating
    {R B M N P : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (S : Submonoid R) [IsLocalization S B]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module B N] [IsScalarTower R B N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f]
    [AddCommGroup P] [Module R P] [Module B P] [IsScalarTower R B P]
    {n : ℕ} (p : M [⋀^Fin n]→ₗ[R] P) :
    ∃ F : N [⋀^Fin n]→ₗ[B] P,
      ∀ a : Fin n → M, F (fun i ↦ f (a i)) = p a := by
  classical
  obtain ⟨F, hF⟩ := extend_multilinear (B := B) S f n p.toMultilinearMap
  let FB : MultilinearMap B (fun _ : Fin n ↦ N) P :=
    MultilinearMap.mk' F F.map_update_add fun v i c x ↦
      ((F.toLinearMap v i).extendScalarsOfIsLocalization S B).map_smul c x
  have halt : ∀ (v : Fin n → N) (i j : Fin n), v i = v j → i ≠ j → FB v = 0 := by
    intro v i j hv hij
    let := isLocalizedModule_id S P B
    obtain ⟨t, ht⟩ := IsLocalizedModule.exist_integer_multiples_of_finite S f v
    choose a ha using ht
    let a' := Function.update a i (a j)
    have he : (fun k ↦ f (a' k)) = fun k ↦ (t : R) • v k := by
      funext k
      by_cases hk : k = i
      · subst k
        simpa [a', hv] using ha j
      · simpa [a', hk] using ha k
    have hp : p a' = 0 := p.map_eq_zero_of_eq a' (by simp [a', Ne.symm hij]) hij
    have hz := hF a'
    change F (fun k ↦ f (a' k)) = p a' at hz
    rw [he, F.map_smul_univ, hp] at hz
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hz
    exact IsLocalizedModule.smul_injective (LinearMap.id (R := R) (M := P))
      (t ^ n) (by
        change (t : R) ^ n • F v = (t : R) ^ n • (0 : P)
        simpa only [smul_zero] using hz)
  exact ⟨{ toMultilinearMap := FB, map_eq_zero_of_eq' := halt }, hF⟩

/-- A map of exterior powers characterized on pure wedges preserves localization.
Source: Stacks Project, Algebra, Section 00DM; the fraction construction in step 2
of `new-q1-exterior-sheaf-affine-unit-bijective`.
(blueprint: new-v2-exterior-power-localization).

Proof: Write N as S⁻¹M via f. The alternating map on fractions sends
(m₁/s₁, ..., mₙ/sₙ) to (m₁ wedge ... wedge mₙ)/(s₁ ... sₙ) in
S⁻¹(⋀^n_R M). This is well defined: replacing a representative multiplies the
numerator equality by an element of S; after multiplication by the product of
all denominators the two wedges agree by multilinearity. The same argument
proves additivity and scalar linearity in each variable and alternation. It is
B-multilinear, since B = S⁻¹R, so the exterior universal property gives a map
from ⋀^n_B N to S⁻¹(⋀^n_R M). Conversely, g extends uniquely to this localization
because every element of S acts invertibly on the B-module ⋀^n_B N. The composites
fix pure wedges of numerators. They fix arbitrary fractions by linearity and
invertibility of denominators, and then all elements since pure wedges span.
Thus g identifies its codomain with the localization of its domain. For n=0,
the construction is the ring localization R → B, with empty denominator product
1. If S contains zero, B and N and both localized exterior powers are zero; the
same formulas still apply. No freeness or finite-generation hypothesis is used. -/
theorem isLocalizedModule_of_wedge
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (S : Submonoid R) [IsLocalization S B]
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} B)
    (f : M ⟶ (ModuleCat.restrictScalars (algebraMap R B)).obj N)
    [IsLocalizedModule S f.hom] (n : ℕ)
    (g : ModuleCat.of R (⋀[R]^n M) ⟶
      (ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B (⋀[B]^n N)))
    (hg : ∀ a : Fin n → M,
      g (ιMulti R n a) = ιMulti B n (fun i ↦ f (a i))) :
    IsLocalizedModule S g.hom := by
  let : Module R N := ((ModuleCat.restrictScalars (algebraMap R B)).obj N).isModule
  let : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module R (⋀[B]^n N) :=
    ((ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B (⋀[B]^n N))).isModule
  let : IsScalarTower R B (⋀[B]^n N) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let fR : M →ₗ[R] N := f.hom
  have hgR (a : Fin n → M) :
      g.hom (ιMulti R n a) = ιMulti B n (fun i ↦ fR (a i)) := hg a
  let L := LocalizedModule S (⋀[R]^n M)
  let j : (⋀[R]^n M) →ₗ[R] L := LocalizedModule.mkLinearMap S _
  let : Module B L := IsLocalizedModule.module S j
  let : IsScalarTower R B L := IsLocalizedModule.isScalarTower_module S j
  obtain ⟨F, hF⟩ := extend_alternating (B := B) (N := N) S fR
    (j.compAlternatingMap (ιMulti R n))
  let h : (⋀[B]^n N) →ₗ[B] L := alternatingMapLinearEquiv F
  let hR := h.restrictScalars R
  let := isLocalizedModule_id S (⋀[B]^n N) B
  let k : L →ₗ[R] (⋀[B]^n N) :=
    LocalizedModule.lift S g.hom
      (IsLocalizedModule.map_units (LinearMap.id (R := R) (M := ⋀[B]^n N)))
  have kj : k.comp j = g.hom := LocalizedModule.lift_comp S _ _
  have hk : hR.comp k = LinearMap.id := by
    apply IsLocalizedModule.ext S j (IsLocalizedModule.map_units j)
    rw [LinearMap.comp_assoc, LocalizedModule.lift_comp, LinearMap.id_comp]
    apply exteriorPower.linearMap_ext
    ext a
    change h (g (ιMulti R n a)) = j (ιMulti R n a)
    rw [hgR]
    change alternatingMapLinearEquiv F (ιMulti B n (fun i ↦ fR (a i))) = _
    rw [alternatingMapLinearEquiv_apply_ιMulti]
    exact hF a
  have kh : k.comp hR = LinearMap.id := by
    let kB := k.extendScalarsOfIsLocalization S B
    have he : kB.comp h = LinearMap.id := by
      apply exteriorPower.linearMap_ext
      have hm := localized_multilinear_ext (B := B) (N := N) S fR
        (((kB.comp h).compAlternatingMap (ιMulti B n)).toMultilinearMap.restrictScalars R)
        ((ιMulti B n (M := N)).toMultilinearMap.restrictScalars R) (by
          intro a
          change k (alternatingMapLinearEquiv F
            (ιMulti B n (fun i ↦ fR (a i)))) = ιMulti B n (fun i ↦ fR (a i))
          rw [alternatingMapLinearEquiv_apply_ιMulti, hF]
          change k (j (ιMulti R n a)) = _
          rw [← LinearMap.comp_apply, kj]
          exact hgR a)
      exact AlternatingMap.ext (fun v ↦ DFunLike.congr_fun hm v)
    exact congrArg (LinearMap.restrictScalars R) he
  let e : L ≃ₗ[R] (⋀[B]^n N) := LinearEquiv.ofLinearMap k hR kh hk
  have he : e.toLinearMap.comp j = g.hom := kj
  rw [← he]
  exact IsLocalizedModule.of_linearEquiv S j e

end exteriorPower
