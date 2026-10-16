/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

import Mathlib.CategoryTheory.ObjectProperty.LimitsClosure
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Compatible finite-limit generators of two sheaf topoi

Source: Stacks Project, Sites, Tags 03CI and 03A2, finite-limit closure construction
(blueprint: lem-weil-pbc-topos-compatible-generators).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

private def generatorShapes : Bool → Type
  | false => Discrete PEmpty
  | true => WalkingCospan

private instance (b : Bool) : SmallCategory (generatorShapes b) := by
  cases b <;> dsimp [generatorShapes] <;> infer_instance

private noncomputable instance (b : Bool) : FinCategory (generatorShapes b) := by
  cases b <;> dsimp [generatorShapes] <;> infer_instance

private theorem generators
    {E : Type (u + 1)} [Category.{u} E] [HasFiniteLimits E]
    {I : Type u} (X : I → E) :
    ∃ (C : Type u) (_ : SmallCategory C) (_ : HasFiniteLimits C) (F : C ⥤ E),
      F.Full ∧ F.Faithful ∧ PreservesFiniteLimits F ∧
      ∀ i, ∃ c, Nonempty (F.obj c ≅ X i) := by
  let P := (ObjectProperty.ofObj X).limitsClosure generatorShapes
  have hP (b : Bool) : P.IsClosedUnderLimitsOfShape (generatorShapes b) := inferInstance
  have : P.IsClosedUnderLimitsOfShape (Discrete PEmpty) := hP false
  have : P.IsClosedUnderLimitsOfShape WalkingCospan := hP true
  have : HasFiniteLimits P.FullSubcategory :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesFiniteLimits P.ι :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks P.ι
  have : ObjectProperty.EssentiallySmall.{u} P := inferInstance
  let e := equivSmallModel.{u} P.FullSubcategory
  let F := e.inverse ⋙ P.ι
  have : HasFiniteLimits (SmallModel.{u} P.FullSubcategory) :=
    ⟨fun _ _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence e.inverse⟩
  have : PreservesFiniteLimits F := by
    dsimp [F]
    exact comp_preservesFiniteLimits _ _
  refine ⟨SmallModel.{u} P.FullSubcategory, inferInstance, inferInstance, F,
    inferInstance, inferInstance, inferInstance, ?_⟩
  intro i
  let z : P.FullSubcategory := ⟨X i, ObjectProperty.le_limitsClosure _ _ _ ⟨i⟩⟩
  exact ⟨e.functor.obj z, ⟨P.ι.mapIso (e.unitIso.app z).symm⟩⟩

/-- Small full finite-limit-closed generators can be chosen compatibly with a left-exact functor.

Source: Stacks Project, Sites, Tags 03CI and 03A2
(blueprint: lem-weil-pbc-topos-compatible-generators).

Proof: Close the sheafified representables of the target under terminal objects and
pullbacks, using the essentially small limit closure. Its full subcategory has finite
limits created by its inclusion; pass to a small model. In the source repeat this with
the sheafified representables and the images of all objects of the first small model.
The functor therefore lifts through the second fully faithful inclusion. Its composite
with that inclusion is isomorphic to the original left-exact composite, so reflection
of limits proves that the lifted functor preserves finite limits. -/
theorem topos_compatibleGenerators
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : Sheaf K (Type u) ⥤ Sheaf J (Type u)) [PreservesFiniteLimits L] :
    ∃ (C' D' : Type u) (_ : SmallCategory C') (_ : SmallCategory D')
      (_ : HasFiniteLimits C') (_ : HasFiniteLimits D')
      (G : C' ⥤ Sheaf J (Type u)) (E : D' ⥤ Sheaf K (Type u)) (v : D' ⥤ C'),
      G.Full ∧ G.Faithful ∧ PreservesFiniteLimits G ∧
      E.Full ∧ E.Faithful ∧ PreservesFiniteLimits E ∧ PreservesFiniteLimits v ∧
      Nonempty (v ⋙ G ≅ E ⋙ L) ∧
      (∀ U : C, ∃ c, Nonempty
        (G.obj c ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U))) ∧
      (∀ U : D, ∃ d, Nonempty
        (E.obj d ≅ (presheafToSheaf K (Type u)).obj (yoneda.obj U))) := by
  obtain ⟨D', hD', hlimD', E, hEfull, hEfaith, hElim, hrepD⟩ :=
    generators (fun U : D ↦ (presheafToSheaf K (Type u)).obj (yoneda.obj U))
  let X : C ⊕ D' → Sheaf J (Type u) := Sum.elim
    (fun U ↦ (presheafToSheaf J (Type u)).obj (yoneda.obj U)) (fun d ↦ L.obj (E.obj d))
  obtain ⟨C', hC', hlimC', G, hGfull, hGfaith, hGlim, hX⟩ := generators X
  have hG : ∀ d, G.essImage ((E ⋙ L).obj d) := fun d ↦ hX (.inr d)
  let v := Functor.essImage.liftFunctor (E ⋙ L) G hG
  let a : v ⋙ G ≅ E ⋙ L := Functor.essImage.liftFunctorCompIso (E ⋙ L) G hG
  have : PreservesFiniteLimits (E ⋙ L) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (v ⋙ G) := preservesFiniteLimits_of_natIso a.symm
  have : PreservesFiniteLimits v := preservesFiniteLimits_of_reflects_of_preserves v G
  refine ⟨C', D', hC', hD', hlimC', hlimD', G, E, v,
    hGfull, hGfaith, hGlim, hEfull, hEfaith, hElim, inferInstance, ⟨a⟩, ?_, hrepD⟩
  intro U
  exact hX (.inl U)

end CategoryTheory
