/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.PicardTermwiseModels
import Sheaf.AlgebraicGeometry.PicardTermwiseSingleMapComposition

/-! # Coherence of the termwise source single
Source: Stacks Project, Tags 06YJ and 0D5S.
(blueprint: lem-sc-picard-termwise-source-coherence) -/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

/-- The canonical counit comparison for the source singles commutes with successive
pullback. This assertion concerns only the source, with no local perfect model.
Source: Stacks Project, Tags 06YJ and 0D5S.
(blueprint: lem-sc-picard-termwise-source-coherence)

Proof:
1. The degree-zero single of the structure sheaf is bounded above and termwise
   flat: tensor with the structure sheaf is the identity, and its other terms are
   zero. Its counit is invertible by the bounded-flat computation.
2. Compose singleFunctorIsoCompQ, the derived counit at this single,
   and the termwise single comparison. These give a_t, retaining the tensor-pulled
   structure sheaf, not replacing it with an unrelated isomorphic object.
3. Evaluate the defining leftDerivedLift counit equation of the pinned derived
   composition comparison at this single. Expand the complex quotient comparison
   and the singleMapHomologicalComplex comparison. The remaining underived map is
   precisely tensorPullbackCompositionIso. Naturality of the quotient comparison
   identifies the two sides of the displayed equation. Transport along ht; proof
   irrelevance identifies all proofs of the equality of the composite maps.
   This calculation also applies to empty schemes and the zero structure sheaf. -/
theorem picard_termwise_source_coherence (W : Scheme.{v}) :
    ∃ a : ∀ {T : Scheme.{v}} (t : T ⟶ W),
        (derivedPullback t).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj
            (SheafOfModules.unit (moduleRings W.toRingedSpace))) ≅
          DerivedCategory.Q.obj (picardTermwiseSource t),
      ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
        (ht : i ≫ t = t'),
      let c := (Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) i t ≪≫
          eqToIso (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) ht)
      (a t').hom ≫ DerivedCategory.Q.map (picardTermwiseSourceRestrictionIso i t t' ht).hom =
        c.inv.app _ ≫ (derivedPullback i).map (a t).hom ≫
          (picardTermwiseCounit i).app (picardTermwiseSource t) := by
  let M := SheafOfModules.unit (moduleRings W.toRingedSpace)
  have : SheafOfModules.IsInvertible.{v, v, v} M := by
    dsimp [M]
    exact SheafOfModules.instIsInvertibleUnit (R := W.ringCatSheaf)
  have hIso : ∀ {T : Scheme.{v}} (t : T ⟶ W),
      IsIso (picardTermwiseSingleMap t M) := by
    intro T t
    have := Modules.isIso_canonicalSinglePullbackMap t M
    unfold picardTermwiseSingleMap
    infer_instance
  let a : ∀ {T : Scheme.{v}} (t : T ⟶ W),
      (derivedPullback t).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj M) ≅
        DerivedCategory.Q.obj (picardTermwiseSource t) := fun t ↦
    @asIso _ _ _ _ (picardTermwiseSingleMap t M) (hIso t)
  refine ⟨a, ?_⟩
  intro T T' i t t' ht
  let c := (Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))) i t ≪≫
      eqToIso (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) ht)
  have h := picardTermwiseSingleMap_composition i t t' ht M
  change c.hom.app _ ≫ (a t').hom ≫
      DerivedCategory.Q.map (picardTermwiseSourceRestrictionIso i t t' ht).hom =
    (derivedPullback i).map (a t).hom ≫
      (picardTermwiseCounit i).app (picardTermwiseSource t) at h
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using
    congrArg (fun f ↦ c.inv.app _ ≫ f) h

end
end AlgebraicGeometry.Scheme
