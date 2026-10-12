/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.SpectralSequence.ExactCouple.OfTriangles
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Images of towers of distinguished triangles under triangulated functors

A triangulated functor `F : T ⥤ T'` sends a tower of distinguished triangles
`X_q ⟶ X_{q'} ⟶ G_{q'} ⟶ X_q⟦1⟧` of `T` (`CategoryTheory.Pretriangulated.TriangleTower`) to the
tower `F X_q ⟶ F X_{q'} ⟶ F G_{q'} ⟶ (F X_q)⟦1⟧` of `T'`, the third map being `F k`
followed by the shift isomorphism of `F` (`CategoryTheory.Pretriangulated.TriangleTower.map`).
A natural transformation `τ : F₁ ⟶ F₂` of triangulated functors which commutes with the shifts
gives a morphism of the image towers (`CategoryTheory.Pretriangulated.TriangleTower.mapHom`),
hence a morphism of the associated exact couples.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated.TriangleTower

open Category Limits

variable {T T' : Type*} [Category* T] [HasZeroObject T] [HasShift T ℤ] [Preadditive T]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]
  [Category* T'] [HasZeroObject T'] [HasShift T' ℤ] [Preadditive T']
  [∀ n : ℤ, (shiftFunctor T' n).Additive] [Pretriangulated T']

/-- The image of a tower of distinguished triangles under a triangulated functor. -/
@[simps]
noncomputable def map (𝒯 : TriangleTower T) (F : T ⥤ T') [F.CommShift ℤ] [F.IsTriangulated] :
    TriangleTower T' where
  X q := F.obj (𝒯.X q)
  G q := F.obj (𝒯.G q)
  i q q' h := F.map (𝒯.i q q' h)
  j q := F.map (𝒯.j q)
  k q q' h := F.map (𝒯.k q q' h) ≫ (F.commShiftIso (1 : ℤ)).hom.app (𝒯.X q)
  distinguished q q' h := F.map_distinguished _ (𝒯.distinguished q q' h)

/-- The triangles of the image tower are the images of the triangles of the tower. -/
lemma map_triangle (𝒯 : TriangleTower T) (F : T ⥤ T') [F.CommShift ℤ] [F.IsTriangulated]
    (q q' : ℤ) (h : q + 1 = q') :
    (𝒯.map F).triangle q q' h = F.mapTriangle.obj (𝒯.triangle q q' h) :=
  rfl

/-- A natural transformation `τ : F₁ ⟶ F₂` of triangulated functors which commutes with the
shifts induces a morphism between the images of a tower of distinguished triangles. Its
components are the components of `τ` on the objects of the tower. -/
@[simps]
noncomputable def mapHom (𝒯 : TriangleTower T) {F₁ F₂ : T ⥤ T'} [F₁.CommShift ℤ]
    [F₂.CommShift ℤ] [F₁.IsTriangulated] [F₂.IsTriangulated] (τ : F₁ ⟶ F₂)
    [NatTrans.CommShift τ ℤ] : (𝒯.map F₁).Hom (𝒯.map F₂) where
  hX q := τ.app (𝒯.X q)
  hG q := τ.app (𝒯.G q)
  comm_i q q' h := τ.naturality (𝒯.i q q' h)
  comm_j q := τ.naturality (𝒯.j q)
  comm_k q q' h := ((NatTrans.mapTriangle τ).app (𝒯.triangle q q' h)).comm₃

end CategoryTheory.Pretriangulated.TriangleTower
