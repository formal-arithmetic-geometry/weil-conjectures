/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.CategoryTheory.BrownCohomologicalRepresentability
import Sheaf.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-!
# Brown representability criterion for a right adjoint

Source: Stacks Project, Derived Categories, Tag 0A8G, Proposition `proposition-brown`
(blueprint: lem-pc-brown-representability-right-adjoint).
-/

@[expose] public section

universe w u₁ u₂ v₁ v₂

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

/-- An exact functor from a compactly generated triangulated category that preserves
set-indexed coproducts has a right adjoint. Source: Stacks Project, Tag 0A8G,
Proposition `proposition-brown` (blueprint: lem-pc-brown-representability-right-adjoint).
The indexing universe contains both morphism universes and an arbitrary universe `w`
for the generating set; object universes are independent.

Proof: For each `d : D`, the additive functor `Hom_D(F(-), d)` is cohomological:
exactness of `F` sends distinguished triangles to distinguished triangles, whose Hom
sequences are exact. Preservation of coproducts by `F` and the universal property of
coproducts show that this functor sends coproducts to products. Apply
`lem-pc-brown-cohomological-representability` to represent it by an object `G(d)` of `C`.
For a morphism `d ⟶ d'`, Yoneda gives the unique map `G(d) ⟶ G(d')` corresponding to
postcomposition on these Hom functors. Uniqueness gives identities and composition,
and makes the representing Hom bijections natural in both variables. These bijections
give the adjunction `F ⊣ G`.
-/
theorem brownRepresentabilityRightAdjoint
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] [IsTriangulated C] [IsTriangulated D]
    [HasCoproducts.{max w v₁ v₂} C] [HasCoproducts.{max w v₁ v₂} D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (hC : IsCompactlyGeneratedTriangulated.{max w v₁ v₂} C)
    (hF : ∀ I : Type (max w v₁ v₂), PreservesColimitsOfShape (Discrete I) F) :
    F.IsLeftAdjoint := by
  apply Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
  funext d
  apply propext
  change (F.op ⋙ yoneda.obj d).IsRepresentable ↔ True
  refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
  let H := F.op ⋙ preadditiveYoneda.obj d
  have hH : ∀ I : Type (max w v₁ v₂), PreservesLimitsOfShape (Discrete I) H := by
    intro I
    let := hF I
    let : PreservesColimitsOfShape (Discrete I)ᵒᵖ F :=
      preservesColimitsOfShape_of_equiv (Discrete.opposite I).symm F
    let : PreservesLimitsOfShape (Discrete I) F.op :=
      preservesLimitsOfShape_op (Discrete I) F
    have : PreservesLimitsOfShape (Discrete I)
        (preadditiveYoneda.obj d ⋙ forget AddCommGrpCat) :=
      inferInstanceAs (PreservesLimitsOfShape (Discrete I) (yoneda.obj d))
    have : PreservesLimitsOfShape (Discrete I) (preadditiveYoneda.obj d) :=
      preservesLimitsOfShape_of_reflects_of_preserves _ (forget AddCommGrpCat)
    change PreservesLimitsOfShape (Discrete I) (F.op ⋙ preadditiveYoneda.obj d)
    infer_instance
  have : H.IsHomological := by
    change (F.op ⋙ preadditiveYoneda.obj d).IsHomological
    infer_instance
  apply brownCohomologicalRepresentabilityUniverseTransfer C hC H hH
  intro A _ _ _ _ _ _ _ _ hA K _ hK
  exact brownCohomologicalRepresentability A hA K hK

end CategoryTheory
