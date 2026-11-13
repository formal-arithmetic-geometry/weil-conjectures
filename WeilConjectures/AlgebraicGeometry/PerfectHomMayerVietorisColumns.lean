/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.AlgebraicGeometry.PerfectHomPushPullCocone
public import WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisDiagram
public import WeilConjectures.AlgebraicGeometry.PerfectHomLocalComparison
public import WeilConjectures.AlgebraicGeometry.PerfectHomTriangleRow
import WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsEven
import WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsOdd

/-! # Local comparisons for the outer columns of geometric triangle diagrams

## References

* Stacks Project, Tags 09RE and 08BW.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated TopologicalSpace
namespace AlgebraicGeometry

/-- Outer-column recognition for the geometric Mayer--Vietoris construction: given a
representing cocone natural in every testing object and a family whose outer objects and maps
are open direct images and restrictions, the outer columns are local filtered Hom comparisons
(Stacks, Tags 09RE and 08BW). -/
theorem perfect_hom_mayerVietoris_geometric_columns
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s₀] [QuasiCompact s₀] [QuasiSeparated s₀]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (Y : Scheme.{u}) (t : Y ⟶ X) [IsOpenImmersion t]
    (ht : t.opensRange = U ⊔ V)
    (s : Y ⟶ Spec (R.obj i)) (hs : s = t ≫ s₀)
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ W : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d)
    (A : PerfectHomMVFamily Y (t ⁻¹ᵁ U) (t ⁻¹ᵁ V)) :
    ∀ (r : Fin 5), r.val ≠ 2 →
      PerfectHomLocalMap R c i X s₀ U V
        (colimit.desc
          ((A.diagram F h.stageQCoh ⋙ perfectHomTriangleRowFunctor Y P).flip.obj r)
          ⟨(perfectHomTriangleRow Y P (A.cocone F d h.stageQCoh h.limitQCoh).pt).obj r,
            (perfectHomTriangleRowCoconeMap Y P (A.diagram F h.stageQCoh)
              (A.cocone F d h.stageQCoh h.limitQCoh)).app r⟩) := by
  intro r hr
  have cases : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨ r.val = 4 := by omega
  rcases cases with h0 | h1 | h2 | h3 | h4
  · apply perfect_hom_mayerVietoris_geometric_columns_even R c i X s₀ U V hU hV Y t ht s hs
      P Q hP hQ F d h A r
    exact Or.inl h0
  · apply perfect_hom_mayerVietoris_geometric_columns_odd R c i X s₀ U V hU hV Y t ht s hs
      P Q hP hQ F d h A r
    exact Or.inl h1
  · omega
  · apply perfect_hom_mayerVietoris_geometric_columns_even R c i X s₀ U V hU hV Y t ht s hs
      P Q hP hQ F d h A r
    exact Or.inr h3
  · apply perfect_hom_mayerVietoris_geometric_columns_odd R c i X s₀ U V hU hV Y t ht s hs
      P Q hP hQ F d h A r
    exact Or.inr h4

end AlgebraicGeometry
