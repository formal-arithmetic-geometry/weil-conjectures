/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-! # Exactness of rows presented by distinguished triangles

## References

* Stacks Project, Tag 08BW.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated
namespace AlgebraicGeometry

/-- Hom-triangle presentations imply exactness, pointwise and at the limit
(Stacks, Tag 08BW). -/
theorem perfect_hom_triangle_presented_rows_exact
    {J : Type u} [Category J]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (S : ComposableArrows (J ⥤ AddCommGrpCat.{max u w}) 4)
    (B : ComposableArrows AddCommGrpCat.{max u w} 4)
    (hS : S.IsComplex) (hB : B.IsComplex)
    (hstage : ∀ (r : ℕ) (hr : r + 2 ≤ 4) (j : J),
      ∃ (Z : Scheme.{u}) (M : schemeDerivedCategory Z)
        (T : Triangle (schemeDerivedCategory Z))
        (hT : T ∈ distTriang (schemeDerivedCategory Z)),
        Nonempty (((S.sc hS r hr).map ((evaluation J AddCommGrpCat.{max u w}).obj j)) ≅
          (shortComplexOfDistTriangle T hT).map
            ((preadditiveCoyoneda.obj (Opposite.op M)) ⋙
              AddCommGrpCat.uliftFunctor.{u})))
    (hlimit : ∀ (r : ℕ) (hr : r + 2 ≤ 4),
      ∃ (Z : Scheme.{u}) (M : schemeDerivedCategory Z)
        (T : Triangle (schemeDerivedCategory Z))
        (hT : T ∈ distTriang (schemeDerivedCategory Z)),
        Nonempty ((B.sc hB r hr) ≅
          (shortComplexOfDistTriangle T hT).map
            ((preadditiveCoyoneda.obj (Opposite.op M)) ⋙
              AddCommGrpCat.uliftFunctor.{u}))) :
    S.Exact ∧ B.Exact := by
  classical
  have point (K : ShortComplex AddCommGrpCat.{max u w})
      (h : ∃ (Z : Scheme.{u}) (M : schemeDerivedCategory Z)
        (T : Triangle (schemeDerivedCategory Z))
        (hT : T ∈ distTriang (schemeDerivedCategory Z)),
        Nonempty (K ≅ (shortComplexOfDistTriangle T hT).map
          ((preadditiveCoyoneda.obj (Opposite.op M)) ⋙ AddCommGrpCat.uliftFunctor.{u}))) :
      K.Exact := by
    obtain ⟨Z, M, T, hT, ⟨e⟩⟩ := h
    apply ShortComplex.exact_of_iso e.symm
    exact ((preadditiveCoyoneda.obj (Opposite.op M)).map_distinguished_exact T hT).map
      AddCommGrpCat.uliftFunctor.{u}
  have joint : JointlyReflectIsomorphisms
      (fun j : J ↦ (evaluation J AddCommGrpCat.{max u w}).obj j) :=
    ⟨by
      intro X Y f hf
      have : ∀ j : J, IsIso (f.app j) := hf
      exact NatIso.isIso_of_isIso_app f⟩
  refine ⟨⟨hS, ?_⟩, ⟨hB, ?_⟩⟩
  · intro r hr
    apply (joint.exact_iff (S.sc hS r hr)).2
    intro j
    exact point _ (hstage r hr j)
  · intro r hr
    exact point _ (hlimit r hr)

end AlgebraicGeometry
