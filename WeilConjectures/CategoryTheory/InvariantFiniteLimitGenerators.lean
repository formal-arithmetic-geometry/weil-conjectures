/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.LimitsClosure
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Small invariant finite-limit generators

Source: Stacks Project, Sites, Tag 03CI, with closure under both functors of an
adjoint equivalence (blueprint: lem-pur-invariant-finite-limit-generators).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private def invariantGeneratorShapes : Bool → Type
  | false => Discrete PEmpty
  | true => WalkingCospan

private instance (b : Bool) : SmallCategory (invariantGeneratorShapes b) := by
  cases b <;> dsimp [invariantGeneratorShapes] <;> infer_instance

private noncomputable instance (b : Bool) : FinCategory (invariantGeneratorShapes b) := by
  cases b <;> dsimp [invariantGeneratorShapes] <;> infer_instance

private def generatorWord {E : Type (u + 1)} [Category.{u} E]
    (σ : E ≌ E) (X : E) : List Bool → E
  | [] => X
  | true :: w => σ.functor.obj (generatorWord σ X w)
  | false :: w => σ.inverse.obj (generatorWord σ X w)

private theorem invariantClosure_map
    {E : Type (u + 1)} [Category.{u} E] [HasFiniteLimits E]
    {I : Type u} (X : I → E) (σ : E ≌ E) (b : Bool) :
    let P := (ObjectProperty.ofObj
      (fun wi : List Bool × I ↦ generatorWord σ (X wi.2) wi.1)).limitsClosure
        invariantGeneratorShapes
    ∀ Y, P Y → P ((if b then σ.functor else σ.inverse).obj Y) := by
  dsimp only
  intro Y hY
  induction hY with
  | of_mem Y hY =>
    obtain ⟨⟨w, i⟩⟩ := hY
    cases b
    · exact .of_mem _ ⟨(false :: w, i)⟩
    · exact .of_mem _ ⟨(true :: w, i)⟩
  | of_isoClosure e hY ih =>
    exact .of_isoClosure ((if b then σ.functor else σ.inverse).mapIso e) ih
  | of_limitPresentation pres h ih =>
    have : (if b then σ.functor else σ.inverse).IsEquivalence := by
      cases b <;> dsimp <;> infer_instance
    exact .of_limitPresentation (pres.map _) ih

/-- A small family in a locally small finite-limit category is contained in a small
full finite-limit subcategory invariant under a specified autoequivalence.

Source: Stacks Project, Sites, Tag 03CI, equivariant generator closure
(blueprint: lem-pur-invariant-finite-limit-generators).

Proof: take every finite word in the functor and its inverse applied to the given
family, then close under terminal objects and pullbacks. The closure is essentially
small by Mathlib's limit-closure theorem. Induction on this closure proves invariance:
words acquire an extra first letter, isomorphisms are mapped, and limit presentations
are mapped by the limit-preserving equivalence. The unit shows that membership after
the forward functor is equivalent to membership before it, so the equivalence restricts
to the full subcategory. Terminal objects and pullbacks give finite limits there,
created by the inclusion. Pass to a small model and conjugate the restricted equivalence.
The small-model counit identifies the inclusion of the conjugate with the original
ambient functor. The empty word includes every original generator.
-/
theorem invariantFiniteLimitGenerators
    {E : Type (u + 1)} [Category.{u} E] [HasFiniteLimits E]
    {I : Type u} (X : I → E) (σ : E ≌ E) :
    ∃ (A : Type u) (_ : SmallCategory A) (_ : HasFiniteLimits A)
      (H : A ⥤ E) (s : A ≌ A),
      H.Full ∧ H.Faithful ∧ PreservesFiniteLimits H ∧
      Nonempty (s.functor ⋙ H ≅ H ⋙ σ.functor) ∧
      ∀ i, ∃ a, Nonempty (H.obj a ≅ X i) := by
  let P := (ObjectProperty.ofObj
    (fun wi : List Bool × I ↦ generatorWord σ (X wi.2) wi.1)).limitsClosure
      invariantGeneratorShapes
  have hP (b : Bool) : P.IsClosedUnderLimitsOfShape (invariantGeneratorShapes b) :=
    inferInstance
  have : P.IsClosedUnderLimitsOfShape (Discrete PEmpty) := hP false
  have : P.IsClosedUnderLimitsOfShape WalkingCospan := hP true
  have : HasFiniteLimits P.FullSubcategory :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesFiniteLimits P.ι :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks P.ι
  have hp : P.inverseImage σ.functor = P := by
    funext Y
    apply propext
    constructor
    · intro h
      exact P.prop_of_iso (σ.unitIso.app Y).symm
        (invariantClosure_map X σ false _ h)
    · exact invariantClosure_map X σ true Y
  let t := σ.congrFullSubcategory hp
  let e := equivSmallModel.{u} P.FullSubcategory
  let H := e.inverse ⋙ P.ι
  let s := e.symm.trans (t.trans e)
  have : HasFiniteLimits (SmallModel.{u} P.FullSubcategory) :=
    ⟨fun _ _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence e.inverse⟩
  have : PreservesFiniteLimits H := comp_preservesFiniteLimits _ _
  have a : s.functor ⋙ H ≅ H ⋙ σ.functor :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e.unitIso.symm ≪≫
          (e.inverse ⋙ t.functor).rightUnitor) P.ι
  refine ⟨SmallModel.{u} P.FullSubcategory, inferInstance, inferInstance, H, s,
    inferInstance, inferInstance, inferInstance, ⟨a⟩, ?_⟩
  intro i
  let z : P.FullSubcategory := ⟨X i,
    ObjectProperty.le_limitsClosure _ _ _ ⟨([], i)⟩⟩
  exact ⟨e.functor.obj z, ⟨P.ι.mapIso (e.unitIso.app z).symm⟩⟩

end CategoryTheory
