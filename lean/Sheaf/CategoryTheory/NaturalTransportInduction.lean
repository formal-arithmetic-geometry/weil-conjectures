/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.EqToHom

/-! # Induction for repeated natural transport

Source: the main-20261015 blueprint, sec-trace-formula/sk-d-weil,
lem-trf-frobenius-operator-compact-description.proof.md, the iterate assertion expanded
in the DAG (blueprint: lem-trf-frobenius-transport-induction).

The family index `n` denotes the positive index `r = n + 1` of the source.
The auxiliary definitions are exactly the powers and displayed composites in that statement.
-/

@[expose] public section

set_option autoImplicit false

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.NaturalTransport

/-- Powers with the successor convention `T^(r+1) = T ∘ T^r`.
Source: the iterate assertion of the blueprint proof
lem-trf-frobenius-operator-compact-description.proof.md
(blueprint: lem-trf-frobenius-transport-induction). -/
def power {C : Type u₁} [Category.{v₁} C] (T : C ⥤ C) : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => power T n ⋙ T

/-- The displayed repeated composite `E_r(M)`, with the empty composite at zero.
Source: the iterate assertion of the blueprint proof
lem-trf-frobenius-operator-compact-description.proof.md
(blueprint: lem-trf-frobenius-transport-induction). -/
def repeated {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (H : C ⥤ D) (T : C ⥤ C) (η : H ⟶ T ⋙ H) (M : C) :
    (n : ℕ) → (H.obj M ⟶ H.obj ((power T n).obj M))
  | 0 => 𝟙 (H.obj M)
  | n + 1 => repeated H T η M n ≫ η.app ((power T n).obj M)

/-- The displayed `S_r(M)`: repeated transport followed by `H(d_r⁻¹)`.
The index `n` denotes `r = n + 1`.
Source: the iterate assertion of the blueprint proof
lem-trf-frobenius-operator-compact-description.proof.md
(blueprint: lem-trf-frobenius-transport-induction). -/
def compared {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (H : C ⥤ D) (T : C ⥤ C) (P : ℕ → C ⥤ C)
    (d : ∀ n : ℕ, P n ≅ power T (n + 1)) (η : H ⟶ T ⋙ H)
    (n : ℕ) (M : C) : H.obj M ⟶ H.obj ((P n).obj M) :=
  repeated H T η M (n + 1) ≫ H.map ((d n).inv.app M)

/-- Repeated natural transport agrees with any family satisfying the given recurrence.
The positive source index `r` is represented by `n = r - 1`. The equality `hP` identifies
`P 0` with `T`; `hd` says that its comparison is the identity under this identification.
The equality transport in `hτ₀` only identifies the codomain `H(T M)` with `H(P 0 M)`.
No naturality of `τ` is assumed.

Source: the main-20261015 blueprint, sec-trace-formula/sk-d-weil,
lem-trf-frobenius-operator-compact-description.proof.md, iterate assertion;
expanded formal induction in the DAG (blueprint: lem-trf-frobenius-transport-induction).

Proof plan:
1. Define `E_r(M)` by the repeated composite, so that
   `E_(r+1)(M) = E_r(M) ≫ η_(T^r M)`, and `S_r(M) = E_r(M) ≫ H(d_r⁻¹)`.
   Reassociation uses the category laws of def-nagata-category.
2. At `r = 1`, the comparison is the identity, hence preservation of identities by `H`
   and the category identity laws give `S_1(M) = η_M = τ_1(M)`.
3. Suppose `S_r(M) = τ_r(M)`. The inverse identities give
   `E_r(M) = S_r(M) ≫ H(d_r)`. Naturality of `η` at `d_r(M)` gives
   `H(d_r) ≫ η_(T^r M) = η_(P_r M) ≫ H(T(d_r))`.
   Substitute in `S_(r+1)`, reassociate, and use functoriality of `H` and the coherence
   `T(d_r) ≫ d_(r+1)⁻¹ = b_r`. The result is
   `S_(r+1)(M) = τ_r(M) ≫ η_(P_r M) ≫ H(b_r(M)) = τ_(r+1)(M)`.
4. Induction on `n = r - 1` proves the assertion for every positive `r` and every `M`. -/
theorem compared_eq
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (H : C ⥤ D) (T : C ⥤ C) (P : ℕ → C ⥤ C) (hP : P 0 = T)
    (d : ∀ n : ℕ, P n ≅ power T (n + 1))
    (b : ∀ n : ℕ, P n ⋙ T ≅ P (n + 1))
    (hd : d 0 = eqToIso hP)
    (hdb : ∀ n : ℕ, (Functor.whiskerRight (d n).hom T) ≫ (d (n + 1)).inv = (b n).hom)
    (η : H ⟶ T ⋙ H)
    (τ : ∀ (n : ℕ) (M : C), H.obj M ⟶ H.obj ((P n).obj M))
    (hτ₀ : ∀ M : C, τ 0 M =
      η.app M ≫ H.map (eqToHom (congrArg (fun F : C ⥤ C ↦ F.obj M) hP.symm)))
    (hτ : ∀ (n : ℕ) (M : C),
      τ (n + 1) M = τ n M ≫ η.app ((P n).obj M) ≫ H.map ((b n).hom.app M)) :
    ∀ (n : ℕ) (M : C), compared H T P d η n M = τ n M := by
  intro n
  induction n with
  | zero =>
    intro M
    rw [hτ₀]
    simp [compared, repeated, power, hd]
  | succ n ih =>
    intro M
    have he : repeated H T η M (n + 1) =
        compared H T P d η n M ≫ H.map ((d n).hom.app M) := by
      simp [compared, Category.assoc, ← H.map_comp]
    have hb : T.map ((d n).hom.app M) ≫ (d (n + 1)).inv.app M =
        (b n).hom.app M := by
      exact congrArg (fun α ↦ α.app M) (hdb n)
    calc
      compared H T P d η (n + 1) M =
          (repeated H T η M (n + 1) ≫ η.app ((power T (n + 1)).obj M)) ≫
            H.map ((d (n + 1)).inv.app M) := rfl
      _ = compared H T P d η n M ≫ η.app ((P n).obj M) ≫
          H.map ((b n).hom.app M) := by
        rw [he]
        simp only [Category.assoc]
        rw [← Category.assoc (H.map ((d n).hom.app M)), η.naturality]
        simp only [Functor.comp_map, Category.assoc, ← H.map_comp, hb]
      _ = τ (n + 1) M := by rw [ih, hτ]

end CategoryTheory.NaturalTransport
