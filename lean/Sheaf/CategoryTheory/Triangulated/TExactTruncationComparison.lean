/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology

/-! # Canonical truncation comparisons for t-exact functors

Source: BBD, Proposition 1.3.3(i),(ii), pp. 29–30, and §1.3.16, p. 36; the scalar-extension
and automorphism sentences in the proof of `prop-constructible-truncations` in the blueprint,
chapter `sec-poincare-duality`, unit `sk-lem-finite`
(blueprint: lem-pod-texact-truncation-comparison).

The comparison isomorphisms are the existing `Functor.eTruncLTIso` at `m + 1` and
`Functor.eTruncGEIso` at `m`. Their integer specializations are comparisons for `τ≤m` and
`τ≥m`. The identity and composite clauses quantify over comparisons characterized by the
canonical maps, so they do not require a new choice of t-exactness structures on functors.
-/

@[expose] public section

universe uC vC uD vD uB vB

namespace CategoryTheory.Triangulated.TStructure

open Limits

/-- Canonical comparisons for a t-exact triangulated functor are uniquely characterized by
the truncation counit and unit, commute with every natural transformation, and respect
identity functors and composition. Source: BBD, Proposition 1.3.3(i),(ii), pp. 29–30,
§1.3.16, p. 36; blueprint `prop-constructible-truncations`, scalar-extension and automorphism
sentences (blueprint: lem-pod-texact-truncation-comparison).

Here `truncLT (m + 1)` is `τ≤m` and `truncGE m` is `τ≥m`. The existing upstream
isomorphisms supply existence. Uniqueness is asserted separately for each sign. In the
identity and composition clauses, the quantified isomorphisms are required to satisfy
exactly the defining counit/unit equations; thus these clauses describe the same uniquely
characterized comparisons, independently of any t-exactness instance used to construct them.

Proof plan, following the nine steps of the DAG node:
1. The adjunctions of `lem-weil-heart-short-exact-triangles` identify maps into upper
   truncation from an object in the upper aisle, and maps out of lower truncation into an
   object in the lower aisle. Composition with the counit/unit is bijective.
2. Apply F to the distinguished truncation triangle at cut (m,m+1). Exactness and
   preservation of both halves identify it with the canonical triangle of F(K), by the
   identity on F(K). Its first component is the upper comparison. The first adjunction
   proves its uniqueness, even among all morphisms.
3. Use the cut (m-1,m) for the lower comparison. Its third component satisfies the unit
   equation. Transporting the second adjunction along this isomorphism makes
   precomposition with F of the unit bijective, proving uniqueness.
4. For a map K → L, postcompose the upper naturality square with the truncation counit.
   Naturality of the counit makes the composites equal; the first adjunction cancels it.
5. Precompose the lower naturality square with F of the unit. Naturality of the unit
   gives equality and step 3 cancels this precomposition. Componentwise inverses are
   natural, so both comparisons are natural isomorphisms.
6. For any η : F → G, postcompose the upper compatibility square with the counit at G(K).
   The characterizations and naturality of η and the counit give equality; cancel by step 1.
   No compatibility of η with the shifts is used.
7. Precompose the lower square with F of the unit. Naturality of η and of the unit gives
   equality after composition; cancel using step 3 with target τ≥m G(K).
8. For the identity functor the identity maps satisfy the characterizations, so uniqueness
   gives the identity comparisons.
9. For H after F, apply H to each characterization and then use H's characterization.
   The composite comparisons satisfy the characterizations for HF. The composite exact
   functor preserves both halves, so uniqueness identifies its comparisons with these. -/
theorem texact_truncation_comparison
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    (tC : TStructure C) (tD : TStructure D)
    (_hC : tC.bounded = ⊤) (_hD : tD.bounded = ⊤)
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tC tD] (m : ℤ) :
    (∀ K : C,
      (F.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K ≫
          (tD.truncLTι (m + 1)).app (F.obj K) = F.map ((tC.truncLTι (m + 1)).app K) ∧
      F.map ((tC.truncGEπ m).app K) ≫ (F.eTruncGEIso tC tD m).hom.app K =
          (tD.truncGEπ m).app (F.obj K)) ∧
    (∀ β : tC.truncLT (m + 1) ⋙ F ≅ F ⋙ tD.truncLT (m + 1),
      (∀ K : C, β.hom.app K ≫ (tD.truncLTι (m + 1)).app (F.obj K) =
        F.map ((tC.truncLTι (m + 1)).app K)) →
      β = F.eTruncLTIso tC tD (m + 1 : ℤ)) ∧
    (∀ β : tC.truncGE m ⋙ F ≅ F ⋙ tD.truncGE m,
      (∀ K : C, F.map ((tC.truncGEπ m).app K) ≫ β.hom.app K =
        (tD.truncGEπ m).app (F.obj K)) → β = F.eTruncGEIso tC tD m) ∧
    (∀ (G : C ⥤ D) [G.CommShift ℤ] [G.IsTriangulated] [G.IsTExact tC tD]
      (η : F ⟶ G) (K : C),
      η.app ((tC.truncLT (m + 1)).obj K) ≫
          (G.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K =
        (F.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K ≫
          (tD.truncLT (m + 1)).map (η.app K) ∧
      η.app ((tC.truncGE m).obj K) ≫ (G.eTruncGEIso tC tD m).hom.app K =
        (F.eTruncGEIso tC tD m).hom.app K ≫ (tD.truncGE m).map (η.app K)) ∧
    (∀ (βLE : tC.truncLT (m + 1) ⋙ 𝟭 C ≅ 𝟭 C ⋙ tC.truncLT (m + 1))
      (βGE : tC.truncGE m ⋙ 𝟭 C ≅ 𝟭 C ⋙ tC.truncGE m),
      (∀ K : C, βLE.hom.app K ≫ (tC.truncLTι (m + 1)).app K =
        (tC.truncLTι (m + 1)).app K) →
      (∀ K : C, (tC.truncGEπ m).app K ≫ βGE.hom.app K =
        (tC.truncGEπ m).app K) →
      ∀ K : C, βLE.hom.app K = 𝟙 _ ∧ βGE.hom.app K = 𝟙 _) ∧
    (∀ (B : Type uB) [Category.{vB} B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
      [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B] [IsTriangulated B]
      (tB : TStructure B) (_hB : tB.bounded = ⊤)
      (H : D ⥤ B) [H.CommShift ℤ] [H.IsTriangulated] [H.IsTExact tD tB]
      (βLE : tC.truncLT (m + 1) ⋙ (F ⋙ H) ≅ (F ⋙ H) ⋙ tB.truncLT (m + 1))
      (βGE : tC.truncGE m ⋙ (F ⋙ H) ≅ (F ⋙ H) ⋙ tB.truncGE m),
      (∀ K : C, βLE.hom.app K ≫ (tB.truncLTι (m + 1)).app (H.obj (F.obj K)) =
        H.map (F.map ((tC.truncLTι (m + 1)).app K))) →
      (∀ K : C, H.map (F.map ((tC.truncGEπ m).app K)) ≫ βGE.hom.app K =
        (tB.truncGEπ m).app (H.obj (F.obj K))) →
      ∀ K : C,
        βLE.hom.app K = H.map ((F.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K) ≫
          (H.eTruncLTIso tD tB (m + 1 : ℤ)).hom.app (F.obj K) ∧
        βGE.hom.app K = H.map ((F.eTruncGEIso tC tD m).hom.app K) ≫
          (H.eTruncGEIso tD tB m).hom.app (F.obj K)) := by
  sorry

end CategoryTheory.Triangulated.TStructure
