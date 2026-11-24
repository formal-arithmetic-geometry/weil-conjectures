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
import WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsEvenZero
import WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsEvenThree

/-! # Local comparisons for the outer columns of geometric triangle diagrams

## References

* Stacks Project, Tags 09RE and 08BW.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated TopologicalSpace
namespace AlgebraicGeometry

/-- Outer-column recognition (even case) for the geometric Mayer--Vietoris construction:
given a representing cocone natural in every testing object and a family whose outer objects
and maps are open direct images and restrictions, the outer columns are local filtered Hom
comparisons (Stacks, Tags 09RE and 08BW). -/
theorem perfect_hom_mayerVietoris_geometric_columns_even
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
    ∀ (r : Fin 5), r.val = 0 ∨ r.val = 3 →
      PerfectHomLocalMap R c i X s₀ U V
        (colimit.desc
          ((A.diagram F h.stageQCoh ⋙ perfectHomTriangleRowFunctor Y P).flip.obj r)
          ⟨(perfectHomTriangleRow Y P (A.cocone F d h.stageQCoh h.limitQCoh).pt).obj r,
            (perfectHomTriangleRowCoconeMap Y P (A.diagram F h.stageQCoh)
              (A.cocone F d h.stageQCoh h.limitQCoh)).app r⟩) := by
  intro r hr
  rcases hr with h0 | h3
  · have er : r = (0 : Fin 5) := Fin.ext (by omega)
    subst r
    exact perfect_hom_mayerVietoris_geometric_columns_even_zero
      R c i X s₀ U V hU hV Y t ht s hs P Q hP hQ F d h A
  · have er : r = (3 : Fin 5) := Fin.ext (by omega)
    subst r
    exact perfect_hom_mayerVietoris_geometric_columns_even_three
      R c i X s₀ U V hU hV Y t ht s hs P Q hP hQ F d h A

end AlgebraicGeometry
