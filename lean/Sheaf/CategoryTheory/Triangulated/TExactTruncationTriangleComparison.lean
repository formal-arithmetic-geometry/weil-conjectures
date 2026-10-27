/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject

/-! # Normalized comparison of entire truncation triangles

Source: BBD, Proposition 1.3.3(i),(ii), printed pp. 29–30
(blueprint: lem-pod-texact-truncation-triangle-comparison).

The canonical triangle at the cutoff `m` is `triangleLTGE (m + 1)`; its terms are
`truncLT (m + 1) = τ≤m` and `truncGE (m + 1) = τ≥m+1`. The comparison is a natural
isomorphism with values in the category of triangles, including the shifted last square.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC uD vD

namespace CategoryTheory.Triangulated.TStructure

open Limits

/-- An exact t-exact functor identifies entire canonical truncation triangles by the
normalized comparisons, uniquely over the identity of their middle object. This
identification is natural as an isomorphism of triangles, and canonical truncation maps
respect the boundary. Source: BBD, Proposition 1.3.3(i),(ii), printed pp. 29–30
(blueprint: lem-pod-texact-truncation-triangle-comparison).

Proof following the four steps of the DAG node:
1. The canonical triangle is distinguished by `lem-weil-heart-short-exact-triangles`.
   Exactness (`def-weil-triangulated-category`) sends it to the distinguished triangle
   whose last arrow is `F.map δ ≫ (F.commShiftIso 1).hom.app U`. The two t-exactness
   conditions put its outer terms in degrees ≤ m and ≥ m + 1 (`def-weil-t-structure`).
2. Whole-triangle uniqueness from `lem-weil-heart-short-exact-triangles` gives the unique
   triangle isomorphism over the identity. Its first square and the upper truncation
   adjunction identify its first component with the counit-normalized comparison in
   `lem-pod-texact-truncation-comparison`. For the third component b, precompose
   b times the inverse lower comparison with the target truncation unit. The second
   square and the lower normalization show this composite equals the unit; the lower
   adjunction forces b times that inverse to be the identity. Thus the third component
   is the lower comparison. The third square gives the displayed boundary equation.
3. For v : K → L, naturality of the truncation counit gives the first square. TR3
   (`def-weil-triangulated-category`) supplies a third component w; naturality of the
   unit gives the same second square for the lower truncation of v. The lower adjunction
   forces these components equal, and the third square gives boundary naturality.
   Equivalently this morphism is the existing `triangleLTGE.map v`, whose components
   are the upper truncation of v, v, and the lower truncation of v.
4. Applying F to this triangle morphism respects its last square by naturality of the
   specified shift comparison. Naturality of both normalized comparisons from
   `lem-pod-texact-truncation-comparison` identifies the first and third components
   of the comparison square; the middle components are identities. Componentwise
   equality is equality of triangle morphisms, giving the asserted natural isomorphism. -/
theorem texact_truncation_triangle_comparison
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    (tC : TStructure C) (tD : TStructure D)
    (_hC : tC.bounded = ⊤) (_hD : tD.bounded = ⊤)
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tC tD] (m : ℤ) :
    (∃ e : tC.triangleLTGE (m + 1) ⋙ F.mapTriangle ≅ F ⋙ tD.triangleLTGE (m + 1),
      (∀ K : C,
        (e.hom.app K).hom₁ = (F.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K ∧
        (e.hom.app K).hom₂ = 𝟙 (F.obj K) ∧
        (e.hom.app K).hom₃ = (F.eTruncGEIso tC tD (m + 1 : ℤ)).hom.app K ∧
        ∀ β : F.mapTriangle.obj ((tC.triangleLTGE (m + 1)).obj K) ≅
            (tD.triangleLTGE (m + 1)).obj (F.obj K),
          β.hom.hom₂ = 𝟙 (F.obj K) → β = e.app K) ∧
      (∀ K : C,
        (F.eTruncGEIso tC tD (m + 1 : ℤ)).hom.app K ≫
            (tD.truncGEδLT (m + 1)).app (F.obj K) =
          F.map ((tC.truncGEδLT (m + 1)).app K) ≫
            (F.commShiftIso (1 : ℤ)).hom.app ((tC.truncLT (m + 1)).obj K) ≫
            ((F.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K)⟦(1 : ℤ)⟧')) ∧
    (∀ (K L : C) (v : K ⟶ L),
      (tC.truncGE (m + 1)).map v ≫ (tC.truncGEδLT (m + 1)).app L =
        (tC.truncGEδLT (m + 1)).app K ≫
          ((tC.truncLT (m + 1)).map v)⟦(1 : ℤ)⟧') := by
  have hδ (K : C) :
      F.map ((tC.truncGEδLT (m + 1)).app K) ≫
          (F.commShiftIso (1 : ℤ)).hom.app _ ≫
          ((F.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K)⟦(1 : ℤ)⟧' =
        (F.eTruncGEIso tC tD (m + 1 : ℤ)).hom.app K ≫
          (tD.truncGEδLT (m + 1)).app (F.obj K) :=
    F.eTruncGEδLT_comm tC tD (m + 1 : ℤ) K
  let e : tC.triangleLTGE (m + 1) ⋙ F.mapTriangle ≅
      F ⋙ tD.triangleLTGE (m + 1) :=
    Pretriangulated.Triangle.functorIsoMk _ _
      (F.eTruncLTIso tC tD (m + 1 : ℤ)) (Iso.refl F)
      (F.eTruncGEIso tC tD (m + 1 : ℤ))
      (by
        ext K
        exact (Category.comp_id _).trans
          (F.eTruncLTIsoApp_hom_eTruncLTι_app tC tD (m + 1 : ℤ) K).symm)
      (by
        ext K
        exact (F.eTruncGEπ_app_eTruncGEIsoApp_hom tC tD (m + 1 : ℤ) K).trans
          (Category.id_comp _).symm)
      (by
        ext K
        exact (Category.assoc _ _ _).trans (hδ K))
  refine ⟨⟨e, ⟨?_, ?_⟩⟩, ?_⟩
  · intro K
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro β hβ
    apply Iso.ext
    have hLE := tC.isLE_truncLT_obj K (m + 1) m
    exact tD.triangle_map_ext
      (F.map_distinguished _ (tC.triangleLTGE_distinguished (m + 1) K))
      (tD.triangleLTGE_distinguished (m + 1) (F.obj K)) m (m + 1)
      (Functor.IsTExact.isLE_obj tC tD F ((tC.truncLT (m + 1)).obj K) m)
      inferInstance hβ
  · intro K
    exact (hδ K).symm
  · intro K L v
    exact (tC.truncGEδLT (m + 1)).naturality v

end CategoryTheory.Triangulated.TStructure
