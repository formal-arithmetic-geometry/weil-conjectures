/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Coherent
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyTrivial
public import WeilConjectures.Mathlib.Data.Fintype.BigOperators

/-!
# Twisting a sheaf of modules by integer tensor powers of invertible sheaves

Let `X` be a scheme, `F` a sheaf of `𝒪ₓ`-modules, `L₁, …, L_r` invertible `𝒪ₓ`-modules and
`m : Fin r → ℤ` an integer vector. This file defines the twisted sheaf
`F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r` and shows that it is coherent when `F` is. This is the sheaf
whose Euler characteristic is the subject of Snapper's theorem.

The integer tensor power `hL.zpow m` of a single invertible sheaf of modules is defined in
`WeilConjectures.AlgebraicGeometry.Modules.Picard`, and tensoring by an invertible sheaf of
modules preserves quasi-coherence, being of finite type and coherence by
`AlgebraicGeometry.Scheme.Modules.isCoherent_tensorObj_of_invertible`, proved in
`WeilConjectures.AlgebraicGeometry.Modules.LocallyTrivial`. So the only thing left to do here is
to package the twisting factor `L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r` as a single invertible sheaf of
modules `AlgebraicGeometry.Scheme.Modules.zpowProd`, whose class in the Picard group is
`∏ j, Pic.mk (L j) (hL j) ^ m j`; coherence of the twist is then one application of
`isCoherent_tensorObj_of_invertible`.

Recording the class of `zpowProd L hL m` in the Picard group is what makes the twist usable:
the comparison isomorphisms Snapper's proof needs — bumping one exponent, concatenating two
families, negating a block, permuting the factors — are all instances of
`AlgebraicGeometry.Scheme.Pic.mk_eq_mk_iff` applied to an identity between products in the
Picard group, and none of them requires an induction on `r`.

Tensoring a short exact sequence of sheaves of modules by an invertible one keeps it exact,
which is the other thing Snapper's induction needs: this is
`SheafOfModules.Invertible.isEquivalence_tensorRight` of
`WeilConjectures.AlgebraicGeometry.Modules.Picard` together with
`CategoryTheory.ShortComplex.ShortExact.map_of_exact`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.zpowProd`: the invertible sheaf of modules
  `L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r`.
- `AlgebraicGeometry.Scheme.Modules.tensorZPow`: the sheaf `F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r`,
  together with `tensorZPowZeroIso` and `tensorZPowSuccIso`, which peel off the last factor.

## Main results

- `AlgebraicGeometry.Scheme.Modules.invertible_zpowProd`: the twisting factor is invertible, and
  `AlgebraicGeometry.Scheme.Pic.mk_zpowProd`: its class in the Picard group is
  `∏ j, Pic.mk (L j) (hL j) ^ m j`.
- `AlgebraicGeometry.Scheme.Pic.zpowProdHom`: that class, bundled as an additive map from the
  exponent vectors to the Picard group written additively.
- `AlgebraicGeometry.Scheme.Pic.mk_zpowProd_add_single` and
  `AlgebraicGeometry.Scheme.Pic.mk_zpowProd_append`: the two comparisons Snapper's proof makes,
  bumping one exponent and concatenating two families.
- `AlgebraicGeometry.Scheme.Modules.isCoherent_tensorZPow`: **the sheaf
  `F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r` is coherent** when `F` is.
-/

@[expose] public section

open CategoryTheory MonoidalCategory SheafOfModules

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {r : ℕ}

/-- The invertible sheaf of modules `L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r` attached to a finite family `L`
of invertible sheaves of modules and an integer vector `m`, with the factors in the stated
order. -/
noncomputable def zpowProd : ∀ {r : ℕ} (L : Fin r → X.Modules), (∀ j, (L j).Invertible) →
    (Fin r → ℤ) → X.Modules
  | 0, _, _, _ => 𝟙_ X.Modules
  | r + 1, L, hL, m =>
    zpowProd (fun j ↦ L j.castSucc) (fun j ↦ hL j.castSucc) (fun j ↦ m j.castSucc) ⊗
      (hL (Fin.last r)).zpow (m (Fin.last r))

@[simp]
lemma zpowProd_zero (L : Fin 0 → X.Modules) (hL : ∀ j, (L j).Invertible) (m : Fin 0 → ℤ) :
    zpowProd L hL m = 𝟙_ X.Modules :=
  rfl

/-- The last factor of the twisting factor may be peeled off. -/
lemma zpowProd_succ (L : Fin (r + 1) → X.Modules) (hL : ∀ j, (L j).Invertible)
    (m : Fin (r + 1) → ℤ) :
    zpowProd L hL m =
      zpowProd (fun j ↦ L j.castSucc) (fun j ↦ hL j.castSucc) (fun j ↦ m j.castSucc) ⊗
        (hL (Fin.last r)).zpow (m (Fin.last r)) :=
  rfl

/-- **The twisting factor `L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r` is invertible.** -/
theorem invertible_zpowProd : ∀ {r : ℕ} (L : Fin r → X.Modules) (hL : ∀ j, (L j).Invertible)
    (m : Fin r → ℤ), (zpowProd L hL m).Invertible
  | 0, _, _, _ => SheafOfModules.invertible_tensorUnit X.sheaf
  | r + 1, L, hL, m =>
    (invertible_zpowProd (fun j ↦ L j.castSucc) (fun j ↦ hL j.castSucc)
        (fun j ↦ m j.castSucc)).tensorObj
      (SheafOfModules.invertible_zpow (hL (Fin.last r)) (m (Fin.last r)))

/-- **The class of the twisting factor in the Picard group of `X` is
`∏ j, Pic.mk (L j) (hL j) ^ m j`.** Every comparison between twisting factors — bumping one
exponent, concatenating two families, negating a block, permuting the factors — follows from
this computation and `AlgebraicGeometry.Scheme.Pic.mk_eq_mk_iff`, with no induction on `r`. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Pic.mk_zpowProd :
    ∀ {r : ℕ} (L : Fin r → X.Modules) (hL : ∀ j, (L j).Invertible) (m : Fin r → ℤ),
      Pic.mk (zpowProd L hL m) (invertible_zpowProd L hL m) = ∏ j, Pic.mk (L j) (hL j) ^ m j
  | 0, _, _, _ => by
    rw [Fin.prod_univ_zero]
    exact Pic.mk_tensorUnit X
  | r + 1, L, hL, m => by
    have ih := Pic.mk_zpowProd (fun j ↦ L j.castSucc) (fun j ↦ hL j.castSucc)
      (fun j ↦ m j.castSucc)
    rw [Fin.prod_univ_castSucc, ← ih, ← Pic.mk_zpow]
    exact Pic.mk_tensorObj

/-- **The class of the twisting factor in the Picard group of `X`, as an additive function of the
exponent vector.** Its value at `m` is the class of
`AlgebraicGeometry.Scheme.Modules.zpowProd L hL m`, by
`AlgebraicGeometry.Scheme.Pic.mk_zpowProd`. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.Pic.zpowProdHom (L : Fin r → X.Modules)
    (hL : ∀ j, (L j).Invertible) : (Fin r → ℤ) →+ Additive X.Pic :=
  AddMonoidHom.mk' (fun m ↦ Additive.ofMul (∏ j, Pic.mk (L j) (hL j) ^ m j)) fun m m' ↦ by
    simp only [Pi.add_apply, zpow_add]
    rw [Finset.prod_mul_distrib]
    rfl

@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Pic.zpowProdHom_apply (L : Fin r → X.Modules)
    (hL : ∀ j, (L j).Invertible) (m : Fin r → ℤ) :
    Pic.zpowProdHom L hL m = Additive.ofMul (∏ j, Pic.mk (L j) (hL j) ^ m j) := rfl

/-- **Bumping one exponent of the twisting factor** multiplies its class in the Picard group by
the class of the corresponding line bundle. -/
theorem _root_.AlgebraicGeometry.Scheme.Pic.mk_zpowProd_add_single (L : Fin r → X.Modules)
    (hL : ∀ j, (L j).Invertible) (m : Fin r → ℤ) (j : Fin r) :
    Pic.mk (zpowProd L hL (m + Pi.single j 1)) (invertible_zpowProd L hL _) =
      Pic.mk (L j) (hL j) * Pic.mk (zpowProd L hL m) (invertible_zpowProd L hL m) := by
  have hsingle : ∏ i, Pic.mk (L i) (hL i) ^ (Pi.single j 1 : Fin r → ℤ) i =
      Pic.mk (L j) (hL j) := by
    rw [Fintype.prod_zpow_pi_single, zpow_one]
  rw [Pic.mk_zpowProd, Pic.mk_zpowProd, ← hsingle, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [Pi.add_apply, zpow_add, mul_comm]

/-- **Concatenating two families of line bundles and their exponent vectors** multiplies the
classes of the two twisting factors in the Picard group. -/
theorem _root_.AlgebraicGeometry.Scheme.Pic.mk_zpowProd_append {r' : ℕ} {M : Fin r → X.Modules}
    {N : Fin r' → X.Modules} (hM : ∀ i, (M i).Invertible) (hN : ∀ i, (N i).Invertible)
    (h : ∀ j, (Fin.append M N j).Invertible) (m : Fin r → ℤ) (m' : Fin r' → ℤ) :
    Pic.mk (zpowProd (Fin.append M N) h (Fin.append m m'))
        (invertible_zpowProd _ _ _) =
      (∏ i, Pic.mk (M i) (hM i) ^ m i) * ∏ i, Pic.mk (N i) (hN i) ^ m' i := by
  rw [Pic.mk_zpowProd, Fin.prod_univ_add]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ ↦ ?_)
    (Finset.prod_congr rfl fun i _ ↦ ?_)
  · rw [show Fin.append m m' (Fin.castAdd r' i) = m i from Fin.append_left m m' i]
    exact congrArg (· ^ m i) (Pic.mk_congr (Fin.append_left M N i))
  · rw [show Fin.append m m' (Fin.natAdd r i) = m' i from Fin.append_right m m' i]
    exact congrArg (· ^ m' i) (Pic.mk_congr (Fin.append_right M N i))

/-- The sheaf `F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r` attached to a sheaf of modules `F`, a finite
family `L` of invertible sheaves of modules and an integer vector `m`.

This is the sheaf whose Euler characteristic is the subject of Snapper's theorem. -/
noncomputable def tensorZPow (F : X.Modules) (L : Fin r → X.Modules)
    (hL : ∀ j, (L j).Invertible) (m : Fin r → ℤ) : X.Modules :=
  F ⊗ zpowProd L hL m

/-- The empty twist of `F` is `F`. -/
noncomputable def tensorZPowZeroIso (F : X.Modules) (L : Fin 0 → X.Modules)
    (hL : ∀ j, (L j).Invertible) (m : Fin 0 → ℤ) : tensorZPow F L hL m ≅ F :=
  ρ_ F

/-- The last factor of a twist may be peeled off:

```text
  F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r ≅ (F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_{r-1} ^⊗ m_{r-1}) ⊗ L_r ^⊗ m_r
```
-/
noncomputable def tensorZPowSuccIso (F : X.Modules) (L : Fin (r + 1) → X.Modules)
    (hL : ∀ j, (L j).Invertible) (m : Fin (r + 1) → ℤ) :
    tensorZPow F L hL m ≅
      tensorZPow F (fun j ↦ L j.castSucc) (fun j ↦ hL j.castSucc) (fun j ↦ m j.castSucc) ⊗
        (hL (Fin.last r)).zpow (m (Fin.last r)) :=
  (α_ _ _ _).symm

/-- **The sheaf `F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r` is coherent** when `F` is coherent and the `Lⱼ`
are invertible. -/
theorem isCoherent_tensorZPow (F : X.Modules) [F.IsCoherent] (L : Fin r → X.Modules)
    (hL : ∀ j, (L j).Invertible) (m : Fin r → ℤ) : (tensorZPow F L hL m).IsCoherent :=
  isCoherent_tensorObj_of_invertible F (invertible_zpowProd L hL m)

end AlgebraicGeometry.Scheme.Modules
