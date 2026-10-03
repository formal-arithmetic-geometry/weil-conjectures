/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.Mathlib.Algebra.CharP.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!
# The Artin–Schreier map of relative affine space

The Artin–Schreier map `AS_q : 𝔸(n; S) ⟶ 𝔸(n; S)`, `x ↦ x ^ q - x`, applied coordinatewise.
Over a scheme `S` receiving a ring map from a finite field `k` with `q` elements, it is a finite
étale torsor under `kⁿ` acting by translations.

## Main definitions

- `AlgebraicGeometry.AffineSpace.artinSchreierMap`: the Artin–Schreier map `x ↦ x ^ q - x`.
- `AlgebraicGeometry.AffineSpace.artinSchreierTorsorMap`: the map
  `∐_{a ∈ kⁿ} 𝔸(n; S) ⟶ 𝔸(n; S) ×_{AS_q} 𝔸(n; S)`, `(a, x) ↦ (x, x + a)`.

## Main statements

- `AlgebraicGeometry.AffineSpace.isFinite_artinSchreierMap`: `AS_q` is finite for `q ≠ 1`.
- `AlgebraicGeometry.AffineSpace.etale_artinSchreierMap`: `AS_q` is étale when `q = 0` on `S`.
- `AlgebraicGeometry.AffineSpace.translation_comp_artinSchreierMap_of_finiteField`: `AS_q` is
  invariant under translation by the elements of a finite field with `q` elements.
- `AlgebraicGeometry.AffineSpace.isIso_artinSchreierTorsorMap`: `AS_q` is a torsor under them.

-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.AffineSpace

variable (n : Type u) (S : Scheme.{u})

/-- The Artin–Schreier map `x ↦ x ^ q - x` of `𝔸(n; S)`, applied coordinatewise. -/
def artinSchreierMap (q : ℕ) : 𝔸(n; S) ⟶ 𝔸(n; S) :=
  homOfVector (𝔸(n; S) ↘ S) fun i ↦ coord S i ^ q - coord S i

@[reassoc (attr := simp)]
lemma artinSchreierMap_over (q : ℕ) : artinSchreierMap n S q ≫ 𝔸(n; S) ↘ S = 𝔸(n; S) ↘ S :=
  homOfVector_over _ _

@[simp]
lemma artinSchreierMap_appTop_coord (q : ℕ) (i : n) :
    (artinSchreierMap n S q).appTop (coord S i) = coord S i ^ q - coord S i :=
  homOfVector_appTop_coord _ _ _

/-- For `q ≠ 1` and finitely many coordinates, the Artin–Schreier map `x ↦ x ^ q - x` is
finite. (For `q = 0` it is the isomorphism `x ↦ 1 - x`; for `q = 1` it is the zero map.) -/
lemma isFinite_artinSchreierMap [Finite n] {q : ℕ} (hq : q ≠ 1) :
    IsFinite (artinSchreierMap n S q) :=
  -- each coordinate ring map `T ↦ T ^ q - T` makes `𝒪_S[T]` a free module of rank `q`
  -- over itself
  sorry

/-- If `q = 0` on `S`, the Artin–Schreier map `x ↦ x ^ q - x` of `𝔸(n; S)` is étale. -/
lemma etale_artinSchreierMap [Finite n] {q : ℕ} (hq : (q : Γ(S, ⊤)) = 0) :
    Etale (artinSchreierMap n S q) :=
  -- the Jacobian of `x ↦ x ^ q - x` is `q x ^ (q - 1) - 1 = -1`, a unit
  sorry

variable {n S}

/-- The Artin–Schreier map commutes with the base change map `map f` of `f : S ⟶ T`: the
square of `AlgebraicGeometry.AffineSpace.isPullback_map_artinSchreierMap` commutes. -/
@[reassoc]
lemma map_comp_artinSchreierMap {T : Scheme.{u}} (f : S ⟶ T) (q : ℕ) :
    map n f ≫ artinSchreierMap n T q = artinSchreierMap n S q ≫ map n f :=
  hom_ext (by simp) fun i ↦ by simp

/-- The Artin–Schreier map of `𝔸(n; S)` is the base change of that of `𝔸(n; T)` along
`f : S ⟶ T`, that is, the following square is cartesian:

```
𝔸(n; S) --map f--> 𝔸(n; T)
   |                  |
   | AS_q             | AS_q
   v                  v
𝔸(n; S) --map f--> 𝔸(n; T)
```
-/
lemma isPullback_map_artinSchreierMap {T : Scheme.{u}} (f : S ⟶ T) (q : ℕ) :
    IsPullback (map n f) (artinSchreierMap n S q) (artinSchreierMap n T q) (map n f) :=
  IsPullback.of_bot (by simpa using isPullback_map (n := n) f)
    (map_comp_artinSchreierMap f q) (isPullback_map (n := n) f)

/-- In characteristic `p`, the Artin–Schreier map `x ↦ x ^ (p ^ m) - x` is invariant under
translation by a vector `a` with `a ^ (p ^ m) = a`:

```
𝔸(n; S) --translation a--> 𝔸(n; S)
      \                       |
       \ AS_{p^m}             | AS_{p^m}
        \                     v
         -----------------> 𝔸(n; S)
```
-/
@[reassoc]
lemma translation_comp_artinSchreierMap {p : ℕ} (hp : p.Prime) (hpS : (p : Γ(S, ⊤)) = 0)
    (m : ℕ) (a : n → Γ(S, ⊤)) (ha : ∀ i, a i ^ p ^ m = a i) :
    translation a ≫ artinSchreierMap n S (p ^ m) = artinSchreierMap n S (p ^ m) := by
  refine hom_ext (by simp) fun i ↦ ?_
  nontriviality Γ(𝔸(n; S), ⊤)
  have := CharP.of_ringHom_of_prime (𝔸(n; S) ↘ S).appTop.hom hp hpS
  have := Fact.mk hp
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, artinSchreierMap_appTop_coord, map_sub,
    map_pow, translation_appTop_coord, add_pow_char_pow, ← map_pow, ha]
  ring

/-- Over a scheme `S` with a ring map `φ : k →+* Γ(S, 𝒪_S)` from a finite field `k` with `q`
elements, translation by a vector `a` with entries in `k` leaves the Artin–Schreier map
`x ↦ x ^ q - x` of `𝔸(n; S)` invariant:

```
𝔸(n; S) --translation (φ ∘ a)--> 𝔸(n; S)
      \                             |
       \ AS_q                       | AS_q
        \                           v
         -----------------------> 𝔸(n; S)
```
-/
@[reassoc]
lemma translation_comp_artinSchreierMap_of_finiteField (k : Type*) [Field k] [Fintype k]
    (φ : k →+* Γ(S, ⊤)) (a : n → k) :
    translation (fun i ↦ φ (a i)) ≫ artinSchreierMap n S (Fintype.card k) =
      artinSchreierMap n S (Fintype.card k) := by
  obtain ⟨m, hp, hm⟩ := FiniteField.card k (ringChar k)
  rw [hm]
  refine translation_comp_artinSchreierMap hp ?_ _ _ fun _ ↦ ?_
  · rw [← map_natCast φ, ringChar.Nat.cast_ringChar, map_zero]
  · rw [← map_pow, ← hm, FiniteField.pow_card]

/-- Over a scheme `S` with a ring map `φ : k →+* Γ(S, 𝒪_S)` from a finite field `k` with `q`
elements, the map `∐_{a ∈ kⁿ} 𝔸(n; S) ⟶ 𝔸(n; S) ×_{AS_q} 𝔸(n; S)`, `(a, x) ↦ (x, x + a)`:

```
∐_{a ∈ kⁿ} 𝔸(n; S) ---> 𝔸(n; S) ×_{AS_q} 𝔸(n; S) --snd--> 𝔸(n; S)
                                   |                          |
                               fst |                          | AS_q
                                   v                          v
                                𝔸(n; S) -------- AS_q ------> 𝔸(n; S)
```

On the summand indexed by `a`, its composites with `fst` and `snd` are `𝟙` and
`translation a` (`AlgebraicGeometry.AffineSpace.ι_artinSchreierTorsorMap_fst`,
`AlgebraicGeometry.AffineSpace.ι_artinSchreierTorsorMap_snd`). -/
def artinSchreierTorsorMap (k : Type u) [Field k] [Fintype k] (φ : k →+* Γ(S, ⊤)) :
    ∐ (fun _ : n → k ↦ 𝔸(n; S)) ⟶
      pullback (artinSchreierMap n S (Fintype.card k)) (artinSchreierMap n S (Fintype.card k)) :=
  Sigma.desc fun a ↦ pullback.lift (𝟙 𝔸(n; S)) (translation fun i ↦ φ (a i))
    (by rw [Category.id_comp, translation_comp_artinSchreierMap_of_finiteField])

@[reassoc (attr := simp)]
lemma ι_artinSchreierTorsorMap_fst (k : Type u) [Field k] [Fintype k]
    (φ : k →+* Γ(S, ⊤)) (a : n → k) :
    Sigma.ι _ a ≫ artinSchreierTorsorMap k φ ≫ pullback.fst _ _ = 𝟙 𝔸(n; S) := by
  simp [artinSchreierTorsorMap]

@[reassoc (attr := simp)]
lemma ι_artinSchreierTorsorMap_snd (k : Type u) [Field k] [Fintype k]
    (φ : k →+* Γ(S, ⊤)) (a : n → k) :
    Sigma.ι _ a ≫ artinSchreierTorsorMap k φ ≫ pullback.snd _ _ =
      translation fun i ↦ φ (a i) := by
  simp [artinSchreierTorsorMap]

/-- Over a scheme `S` with a ring map `φ : k →+* Γ(S, 𝒪_S)` from a finite field `k` with `q`
elements, the Artin–Schreier map `AS_q` of `𝔸(n; S)` is a torsor under `kⁿ` acting by
translations: `AlgebraicGeometry.AffineSpace.artinSchreierTorsorMap` is an isomorphism. -/
lemma isIso_artinSchreierTorsorMap [Finite n] (k : Type u) [Field k] [Fintype k]
    (φ : k →+* Γ(S, ⊤)) :
    IsIso (artinSchreierTorsorMap k φ : ∐ (fun _ : n → k ↦ 𝔸(n; S)) ⟶ _) :=
  -- locally on `S`, the fibre product is `Spec 𝒪_S[x, y] / ((y - x) ^ q - (y - x))`
  -- coordinatewise, and `T ^ q - T = ∏_{a ∈ k} (T - φ a)` over any `k`-algebra
  -- (`FiniteField.X_pow_card_sub_X` mapped along `φ`); the differences `φ a - φ b` are units,
  -- so the Chinese remainder theorem splits it as `∏_a 𝒪_S[x]`
  sorry

end AlgebraicGeometry.AffineSpace

end
