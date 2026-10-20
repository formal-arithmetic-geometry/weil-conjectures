/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z5
-/
module

public import Sheaf.CategoryTheory.RingedPresentationData

/-! # Auxiliary ringed presentation comparisons -/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- Slicing a ringed equivalence gives ringed equivalences, and the induced
module inverse images commute with restriction and further restriction.

Source: Stacks Project, sites-modules.tex, Tags 04IE and 04J4.
(blueprint: lem-weil-pbc-ringed-equivalence-slices).

Proof: over A send an arrow X → A to e.inverse X → e.inverse A.
Its inverse uses e.direct and the invertible adjunction unit. The unit and
counit are the original ones on the objects of the arrows. Conjugate with the
two element-site fibre equivalences. Preservation of products identifies the
restricted source ring with the inverse image of the restricted target ring;
use the restricted structural isomorphism for its ring map. This gives q and
its structural equation. Construct the module direct image from this geometric
adjunction and ring map. Module inverse image is obtained by transporting the
module operations, since the ring map is invertible. Both ways around a
restriction square have the same underlying set inverse image and the same
scalar action; the product/fibre comparison is therefore linear. Its inverse
is linear by the inverse structural isomorphism. Naturality follows by
applying the underlying functors to each module arrow. For a map B → A the
same computation uses the product over A, giving the further restriction
square. Any of the specified module equivalences has inverse naturally
isomorphic to the specified induced direct image. Uniqueness of left adjoints
therefore transports these squares to any choices of whole and slice module
transport. This argument imposes no boundedness or representability on A. -/
theorem ringed_equivalence_slices
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] [IsIso e.ringMap]
    (sourceSlices : ∀ A : Sheaf K (Type u),
      RingedSheafSliceAdjunctionData (localCoefficientRings S) A)
    (targetSlices : ∀ A : Sheaf J (Type u),
      RingedSheafSliceAdjunctionData (localCoefficientRings R) A) :
    ∃ (s : ∀ A : Sheaf K (Type u),
        RingedToposMorphism
          (localCoefficientRings (presentationElementRing R (e.inverse.obj A)))
          (localCoefficientRings (presentationElementRing S A)))
      (h : ∀ A : Sheaf K (Type u), (s A).inverse.IsEquivalence)
      (k : ∀ A : Sheaf K (Type u), IsIso (s A).ringMap)
      (q : ∀ A : Sheaf K (Type u),
        e.inverse ⋙ elementSheafPullback (e.inverse.obj A) ≅
          elementSheafPullback A ⋙ (s A).inverse),
      (∀ A : Sheaf K (Type u), Nonempty ((s A).inverse ≅
        (sourceSlices A).fibreEquivalence.functor ⋙ Over.post e.inverse ⋙
          (targetSlices (e.inverse.obj A)).fibreEquivalence.inverse)) ∧
      (∀ A : Sheaf K (Type u),
        (q A).hom.app ((sheafCompose K (forget RingCat)).obj (localCoefficientRings S)) ≫
          (s A).ringMap = (elementSheafPullback (e.inverse.obj A)).map e.ringMap) ∧
      ∀ (whole : RingedPresentationAt e)
        (T : ∀ A : Sheaf K (Type u), RingedPresentationAt (s A))
        (rs : RingedPresentationRestrictions S) (rt : RingedPresentationRestrictions R),
        (∀ A : Sheaf K (Type u),
          Nonempty (whole.transport.modules.functor ⋙
            elementModulePullback.{u, u} (localCoefficientRings R) (e.inverse.obj A) ≅
              elementModulePullback.{u, u} (localCoefficientRings S) A ⋙
                (T A).transport.modules.functor)) ∧
        ∀ {A B : Sheaf K (Type u)} (b : B ⟶ A),
          Nonempty ((T A).transport.modules.functor ⋙
            elementModulePullbackOver.{u, u} (localCoefficientRings R) (e.inverse.map b)
              (rt.overContinuous (e.inverse.map b)) ≅
            elementModulePullbackOver.{u, u} (localCoefficientRings S) b
              (rs.overContinuous b) ⋙ (T B).transport.modules.functor) := by
  sorry

end CategoryTheory
