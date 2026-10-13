/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Sheaf.AlgebraicGeometry.PerfectHomPushPullCocone
public import Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisDiagram
public import Sheaf.AlgebraicGeometry.PerfectHomLocalComparison
public import Sheaf.AlgebraicGeometry.PerfectHomTriangleRow

/-! # Local comparisons for the outer columns of geometric triangle diagrams

Source: Stacks Project, Tags 09RE and 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-geometric-columns-even).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated TopologicalSpace
namespace AlgebraicGeometry

/-- Fixed outer-column comparison at index 0.
Source: Stacks Project, perfect.tex Tag 09RE.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-geometric-columns-even-zero).
-/
theorem perfect_hom_mayerVietoris_geometric_columns_even_zero
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
      PerfectHomLocalMap R c i X s₀ U V
        (colimit.desc
          ((A.diagram F h.stageQCoh ⋙ perfectHomTriangleRowFunctor Y P).flip.obj (0 : Fin 5))
          ⟨(perfectHomTriangleRow Y P (A.cocone F d h.stageQCoh h.limitQCoh).pt).obj (0 : Fin 5),
            (perfectHomTriangleRowCoconeMap Y P (A.diagram F h.stageQCoh)
              (A.cocone F d h.stageQCoh h.limitQCoh)).app (0 : Fin 5)⟩) := by sorry

end AlgebraicGeometry
