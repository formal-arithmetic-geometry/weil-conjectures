/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import WeilConjectures.CategoryTheory.SpectralSequence.ExactCouple

/-!
# The exact couple of a tower of distinguished triangles

Let `T` be a pretriangulated category and `F : T ⥤ C` a homological functor to an abelian
category, equipped with a shift sequence (`F.shift n` plays the role of `Hⁿ`). A *tower of
distinguished triangles* consists of objects `X_q`, `G_q` (`q : ℤ`) and distinguished triangles
```
  X_{q-1} ⟶ X_q ⟶ G_q ⟶ X_{q-1}[1].
```
Applying `F` and taking the long exact homology sequences gives an exact couple of type `0` with
```
  D^{p,q} = H^{p+q}(X_q),    E^{p,q} = H^{p+q}(G_q),
```
`α : D^{p+1,q-1} ⟶ D^{p,q}` induced by `X_{q-1} ⟶ X_q`, `g : D^{p,q} ⟶ E^{p,q}` induced by
`X_q ⟶ G_q` and `f : E^{p,q} ⟶ D^{p+2,q-1}` the connecting morphism
`H^{p+q}(G_q) ⟶ H^{p+q+1}(X_{q-1})`. Exactness of the couple is the exactness of the long exact
sequences (`lem-sp-long-exact-of-triangle`).

The basic example is the canonical truncation tower `X_q = τ_{≤ q} K`, `G_q = H^q(K)[-q]` of an
object `K` of a derived category, pushed forward along a triangulated functor such as a right
derived functor: this is the truncation couple `def-sp-truncation-couple`.

## Main definitions

- `CategoryTheory.Pretriangulated.TriangleTower`: towers of distinguished triangles.
- `CategoryTheory.Pretriangulated.TriangleTower.exactCouple`: the exact couple of a tower under a
  homological functor.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated

namespace Pretriangulated

variable (T : Type*) [Category* T] [HasZeroObject T] [HasShift T ℤ] [Preadditive T]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

/-- A tower of distinguished triangles `X_q ⟶ X_{q'} ⟶ G_{q'} ⟶ X_q[1]` (`q + 1 = q'`) in a
pretriangulated category. -/
structure TriangleTower where
  /-- The objects of the tower. -/
  X (q : ℤ) : T
  /-- The successive cones. -/
  G (q : ℤ) : T
  /-- The transition maps `X_q ⟶ X_{q+1}`. -/
  i (q q' : ℤ) (h : q + 1 = q' := by lia) : X q ⟶ X q'
  /-- The maps `X_q ⟶ G_q`. -/
  j (q : ℤ) : X q ⟶ G q
  /-- The connecting maps `G_{q+1} ⟶ X_q[1]`. -/
  k (q q' : ℤ) (h : q + 1 = q' := by lia) : G q' ⟶ (X q)⟦(1 : ℤ)⟧
  distinguished (q q' : ℤ) (h : q + 1 = q') : Triangle.mk (i q q') (j q') (k q q') ∈ distTriang T

namespace TriangleTower

variable {T} (𝒯 : TriangleTower T)

/-- The distinguished triangle `X_q ⟶ X_{q'} ⟶ G_{q'} ⟶ X_q[1]` of the tower. -/
abbrev triangle (q q' : ℤ) (h : q + 1 = q' := by lia) : Triangle T :=
  Triangle.mk (𝒯.i q q') (𝒯.j q') (𝒯.k q q')

variable {C : Type*} [Category* C] [Abelian C] (F : T ⥤ C) [F.IsHomological]
  [F.ShiftSequence ℤ]

/-- Changing the degree of `F.shift` along an equality of integers. -/
lemma eqToHom_comp_shift_map {a b : ℤ} (h : a = b) {Y Z : T} (φ : Y ⟶ Z)
    (h₁ : (F.shift a).obj Y = (F.shift b).obj Y) (h₂ : (F.shift a).obj Z = (F.shift b).obj Z) :
    eqToHom h₁ ≫ (F.shift b).map φ = (F.shift a).map φ ≫ eqToHom h₂ := by
  subst h
  simp

/-- The exact couple `D^{p,q} = H^{p+q}(X_q)`, `E^{p,q} = H^{p+q}(G_q)` of a tower of
distinguished triangles under a homological functor `F`. In the case of the canonical
truncation tower this is the truncation couple (`def-sp-truncation-couple`), and its exactness
is `lem-sp-truncation-couple-exact`. -/
noncomputable def exactCouple : ExactCouple C 0 where
  D p q := (F.shift (p + q)).obj (𝒯.X q)
  E p q := (F.shift (p + q)).obj (𝒯.G q)
  α p q p' q' hp hq := (F.shift (p + q)).map (𝒯.i q q') ≫ eqToHom (by
    rw [show p + q = p' + q' by lia])
  f p q p' q' hp hq := F.homologySequenceδ (𝒯.triangle q' q) (p + q) (p' + q') (by lia)
  g p q p' q' hp hq := (F.shift (p + q)).map (𝒯.j q) ≫ eqToHom (by
    obtain rfl : p' = p := by lia
    obtain rfl : q' = q := by lia
    rfl)
  f_α a b p q p' q' hp hq hp' hq' := by
    obtain rfl : b = q' := by lia
    rw [← assoc, F.homologySequenceδ_comp _ (𝒯.distinguished q b (by lia)), zero_comp]
  g_f p q p' q' p'' q'' hp hq hp' hq' := by
    obtain rfl : p' = p := by lia
    obtain rfl : q' = q := by lia
    rw [eqToHom_refl, comp_id, F.comp_homologySequenceδ _ (𝒯.distinguished q'' q' (by lia))]
  α_g p q p' q' p'' q'' hp hq hp' hq' := by
    obtain rfl : p'' = p' := by lia
    obtain rfl : q'' = q' := by lia
    rw [eqToHom_refl, comp_id, assoc, eqToHom_comp_shift_map F (by lia) _ _ (by
      rw [show p + q = p' + q' by lia]), ← assoc, ← Functor.map_comp,
      comp_distTriang_mor_zero₁₂ _ (𝒯.distinguished q q' (by lia)), Functor.map_zero, zero_comp]
  exact_f_α a b p q p' q' hp hq hp' hq' := by
    obtain rfl : b = q' := by lia
    refine ShortComplex.exact_of_iso ?_
      (F.homologySequence_exact₁ _ (𝒯.distinguished q b (by lia)) (a + b) (p + q) (by lia))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (eqToIso (by
      rw [show p + q = p' + b by lia])) (by simp) (by simp)
  exact_g_f p q p' q' p'' q'' hp hq hp' hq' := by
    obtain rfl : p' = p := by lia
    obtain rfl : q' = q := by lia
    refine ShortComplex.exact_of_iso ?_
      (F.homologySequence_exact₃ _ (𝒯.distinguished q'' q' (by lia)) (p' + q') (p'' + q'')
        (by lia))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  exact_α_g p q p' q' p'' q'' hp hq hp' hq' := by
    obtain rfl : p'' = p' := by lia
    obtain rfl : q'' = q' := by lia
    refine ShortComplex.exact_of_iso ?_
      (F.homologySequence_exact₂ _ (𝒯.distinguished q q' (by lia)) (p + q))
    refine ShortComplex.isoMk (Iso.refl _) (eqToIso (by rw [show p + q = p' + q' by lia]))
      (eqToIso (by rw [show p + q = p' + q' by lia])) (by simp) ?_
    dsimp
    rw [eqToHom_refl, comp_id, eqToHom_comp_shift_map F (by lia)]

end TriangleTower

end Pretriangulated

end CategoryTheory
