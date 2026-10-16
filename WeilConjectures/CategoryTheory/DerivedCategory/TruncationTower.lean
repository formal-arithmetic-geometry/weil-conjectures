/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.TruncationTrianglePlus
public import WeilConjectures.CategoryTheory.SpectralSequence.ExactCouple.OfTriangles

/-!
# The tower of canonical truncation triangles

For a bounded below object `K` of the derived category, the truncation triangles
`τ_{≤ q} K ⟶ τ_{≤ q'} K ⟶ H^{q'}(K)[-q'] ⟶ (τ_{≤ q} K)⟦1⟧` (`q + 1 = q'`,
`DerivedCategory.Plus.truncLETriangle_distinguished`) form a tower of distinguished triangles
`DerivedCategory.Plus.truncLETower K` of `D⁺(C)`; a morphism `K ⟶ L` induces a morphism of
towers (`DerivedCategory.Plus.truncLETowerMap`).
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

namespace DerivedCategory.Plus

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The tower of canonical truncation triangles
`τ_{≤ q} K ⟶ τ_{≤ q'} K ⟶ H^{q'}(K)[-q'] ⟶ (τ_{≤ q} K)⟦1⟧` of an object `K` of `D⁺(C)`. -/
@[simps]
noncomputable def truncLETower (K : Plus C) : TriangleTower (Plus C) where
  X q := (truncLE C q).obj K
  G q := (homologySingleFunctor C q).obj K
  i q q' h := (truncLEMapOfLE C q q' (by lia)).app K
  j q := (truncLEToHomologySingle C q).app K
  k q q' h := (truncLEδ q q' h).app K
  distinguished q q' h := truncLETriangle_distinguished q q' h K

/-- The morphism of truncation towers induced by a morphism `K ⟶ L` of `D⁺(C)`. -/
@[simps]
noncomputable def truncLETowerMap {K L : Plus C} (φ : K ⟶ L) :
    (truncLETower K).Hom (truncLETower L) where
  hX q := (truncLE C q).map φ
  hG q := (homologySingleFunctor C q).map φ
  comm_i q q' h := ((truncLEMapOfLE C q q' (by lia)).naturality φ).symm
  comm_j q := ((truncLEToHomologySingle C q).naturality φ).symm
  comm_k q q' h := ((truncLEδ q q' h).naturality φ).symm

end DerivedCategory.Plus
