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

/-- Changing the index of a family of functors along an equality. -/
lemma eqToHom_comp_map_of_eq {A B ι : Type*} [Category* A] [Category* B] (G : ι → A ⥤ B)
    {a b : ι} (h : a = b) {Y Z : A} (φ : Y ⟶ Z) (h₁ : (G a).obj Y = (G b).obj Y)
    (h₂ : (G a).obj Z = (G b).obj Z) :
    eqToHom h₁ ≫ (G b).map φ = (G a).map φ ≫ eqToHom h₂ := by
  subst h
  simp

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

@[reassoc (attr := simp)]
lemma i_j (q q' : ℤ) (h : q + 1 = q' := by lia) : 𝒯.i q q' ≫ 𝒯.j q' = 0 :=
  comp_distTriang_mor_zero₁₂ _ (𝒯.distinguished q q' h)

@[reassoc (attr := simp)]
lemma j_k (q q' : ℤ) (h : q + 1 = q' := by lia) : 𝒯.j q' ≫ 𝒯.k q q' = 0 :=
  comp_distTriang_mor_zero₂₃ _ (𝒯.distinguished q q' h)

variable {C : Type*} [Category* C] [Abelian C] (F : T ⥤ C) [F.IsHomological]
  [F.ShiftSequence ℤ]

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
    rw [show p = p' by lia, show q = q' by lia])
  f_α a b p q p' q' hp hq hp' hq' := by
    obtain rfl : q' = b := by lia
    exact (F.homologySequenceδ_comp_assoc _ (𝒯.distinguished q q' (by lia)) _ _ _ _).trans
      zero_comp
  g_f p q p' q' p'' q'' hp hq hp' hq' := by
    obtain rfl : p = p' := by lia
    obtain rfl : q = q' := by lia
    simp only [eqToHom_refl, comp_id]
    exact F.comp_homologySequenceδ _ (𝒯.distinguished q'' q (by lia)) _ _ _
  α_g p q p' q' p'' q'' hp hq hp' hq' := by
    obtain rfl : p' = p'' := by lia
    obtain rfl : q' = q'' := by lia
    simp only [eqToHom_refl, comp_id, assoc]
    rw [eqToHom_comp_map_of_eq F.shift (show p + q = p' + q' by lia) (𝒯.j q') _
      (by rw [show p + q = p' + q' by lia]), ← Functor.map_comp_assoc, 𝒯.i_j q q',
      Functor.map_zero, zero_comp]
  exact_f_α a b p q p' q' hp hq hp' hq' := by
    obtain rfl : q' = b := by lia
    have h := F.homologySequence_exact₁ _ (𝒯.distinguished q q' (by lia)) (a + q') (p + q)
      (by lia)
    change (ShortComplex.mk (F.homologySequenceδ (𝒯.triangle q q') (a + q') (p + q) (by lia))
      ((F.shift (p + q)).map (𝒯.i q q'))
      (F.homologySequenceδ_comp _ (𝒯.distinguished q q' (by lia)) _ _ _)).Exact at h
    refine ShortComplex.exact_of_iso ?_ h
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (eqToIso (congrArg (fun n ↦ (F.shift n).obj (𝒯.X q')) (show p + q = p' + q' by lia)))
      ((id_comp _).trans (comp_id _).symm) (id_comp _)
  exact_g_f p q p' q' p'' q'' hp hq hp' hq' := by
    obtain rfl : p = p' := by lia
    obtain rfl : q = q' := by lia
    have h := F.homologySequence_exact₃ _ (𝒯.distinguished q'' q (by lia)) (p + q) (p'' + q'')
      (by lia)
    change (ShortComplex.mk ((F.shift (p + q)).map (𝒯.j q))
      (F.homologySequenceδ (𝒯.triangle q'' q) (p + q) (p'' + q'') (by lia))
      (F.comp_homologySequenceδ _ (𝒯.distinguished q'' q (by lia)) _ _ _)).Exact at h
    refine ShortComplex.exact_of_iso ?_ h
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
      ((id_comp _).trans (comp_id _).symm)
  exact_α_g p q p' q' p'' q'' hp hq hp' hq' := by
    obtain rfl : p' = p'' := by lia
    obtain rfl : q' = q'' := by lia
    have h := F.homologySequence_exact₂ _ (𝒯.distinguished q q' (by lia)) (p + q)
    change (ShortComplex.mk ((F.shift (p + q)).map (𝒯.i q q')) ((F.shift (p + q)).map (𝒯.j q'))
      (F.homologySequence_comp _ (𝒯.distinguished q q' (by lia)) _)).Exact at h
    refine ShortComplex.exact_of_iso ?_ h
    refine ShortComplex.isoMk (Iso.refl _)
      (eqToIso (congrArg (fun n ↦ (F.shift n).obj (𝒯.X q')) (show p + q = p' + q' by lia)))
      (eqToIso (congrArg (fun n ↦ (F.shift n).obj (𝒯.G q')) (show p + q = p' + q' by lia)))
      (by simp) ?_
    dsimp
    rw [comp_id]
    exact eqToHom_comp_map_of_eq F.shift (show p + q = p' + q' by lia) (𝒯.j q') _ _

/-- A morphism of towers of distinguished triangles: maps `X_q ⟶ X'_q` and `G_q ⟶ G'_q`
commuting with the three maps of the triangles. -/
@[ext]
structure Hom (𝒯' : TriangleTower T) where
  /-- The maps on the objects of the towers. -/
  hX (q : ℤ) : 𝒯.X q ⟶ 𝒯'.X q
  /-- The maps on the cones. -/
  hG (q : ℤ) : 𝒯.G q ⟶ 𝒯'.G q
  comm_i (q q' : ℤ) (h : q + 1 = q' := by lia) : 𝒯.i q q' ≫ hX q' = hX q ≫ 𝒯'.i q q'
  comm_j (q : ℤ) : 𝒯.j q ≫ hG q = hX q ≫ 𝒯'.j q
  comm_k (q q' : ℤ) (h : q + 1 = q' := by lia) :
    𝒯.k q q' ≫ (hX q)⟦(1 : ℤ)⟧' = hG q' ≫ 𝒯'.k q q'

variable {𝒯} {𝒯' : TriangleTower T} (φ : 𝒯.Hom 𝒯')

/-- The morphism of distinguished triangles induced by a morphism of towers. -/
@[simps!]
def Hom.triangleMap (q q' : ℤ) (h : q + 1 = q' := by lia) :
    𝒯.triangle q q' ⟶ 𝒯'.triangle q q' :=
  Triangle.homMk _ _ (φ.hX q) (φ.hX q') (φ.hG q') (φ.comm_i q q') (φ.comm_j q') (φ.comm_k q q')

/-- The morphism of exact couples induced by a morphism of towers of distinguished triangles. -/
@[simps!]
noncomputable def Hom.exactCoupleMap : 𝒯.exactCouple F ⟶ 𝒯'.exactCouple F where
  hD p q := (F.shift (p + q)).map (φ.hX q)
  hE p q := (F.shift (p + q)).map (φ.hG q)
  comm_α p q p' q' hp hq := by
    dsimp only [exactCouple]
    rw [assoc, eqToHom_comp_map_of_eq F.shift (show p + q = p' + q' by lia) (φ.hX q') _
      (congrArg (fun n ↦ (F.shift n).obj (𝒯'.X q')) (show p + q = p' + q' by lia)),
      ← Functor.map_comp_assoc, φ.comm_i q q', Functor.map_comp_assoc]
  comm_f p q p' q' hp hq :=
    (F.homologySequenceδ_naturality _ _ (φ.triangleMap q' q) (p + q) (p' + q')
      (by lia)).symm
  comm_g p q p' q' hp hq := by
    obtain rfl : p = p' := by lia
    obtain rfl : q = q' := by lia
    dsimp only [exactCouple]
    simp only [eqToHom_refl, comp_id, ← Functor.map_comp, φ.comm_j]

end TriangleTower

end Pretriangulated

end CategoryTheory
