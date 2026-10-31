/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedPresentationData

import WeilConjectures.CategoryTheory.RingedGeneralizedCompletenessCriterion
import WeilConjectures.CategoryTheory.RingedGeneralizedTestTransport

/-! # Auxiliary ringed presentation comparisons -/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private theorem transportedIdeal_section
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    (w : RingedPresentationAt e) (I : PresentationModules S)
    (ι : I ⟶ SheafOfModules.unit (localCoefficientRings S))
    {B : Sheaf J (Type u)}
    (b : B ⟶ (presentationForget R).obj (w.transport.modules.functor.obj I)) :
    b ≫ (presentationForget R).map
        (w.transport.modules.functor.map ι ≫ w.transport.forward.unit.hom) =
      (b ≫ w.underlying.hom.app I) ≫
        e.inverse.map ((presentationForget S).map ι) ≫ e.ringMap := by
  have hn : (presentationForget R).map (w.transport.modules.functor.map ι) ≫
        w.underlying.hom.app (SheafOfModules.unit (localCoefficientRings S)) =
      w.underlying.hom.app I ≫ e.inverse.map ((presentationForget S).map ι) :=
    w.underlying.hom.naturality ι
  rw [Functor.map_comp, Category.assoc, w.structural]
  simpa only [Category.assoc] using congrArg (fun f ↦ b ≫ f ≫ e.ringMap) hn

/-- Local derived ideal-completeness is invariant under an exact ringed
module equivalence tied to the underlying geometric equivalence.

Source: Stacks Project, algebraization.tex, Tag 099J, opening presentation
reduction, and Tag 0999, definition-derived-complete.
(blueprint: lem-weil-pbc-ringed-equivalence-local-tests).

Proof: first replace the family of site-object tests by tests on arbitrary
sheaves A and generalized ideal sections A → I. Restrict such a test to every
(U,s) in the element site of A. Restriction of derived Hom and localization
identifies it with the original test on U. Thus all its cohomology sheaves
have zero sections at every (U,s); every cohomology sheaf, and therefore the
derived test object, is zero. Conversely use the underlying sheaf of I with
its identity generalized ideal section. Its elements include every ordinary
ideal section. This includes empty sites and empty coverings.
For A = e.inverse A', full faithfulness identifies generalized sections of I'
with those of e.inverse I'. The structural rank-one equation identifies the
image of the ideal inclusion with F(ι) followed by the given rank-one map.
The slice module equivalence and its internal Hom and localization comparisons
identify the associated tests. An equivalence preserves and reflects zero.
Every sheaf on the source is isomorphic to e.inverse A' for some A', so this
compares all generalized tests on both sides. Apply the preceding equivalence
of testing conventions in each presentation to obtain the displayed iff. -/
theorem ringed_equivalence_local_tests
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] [IsIso e.ringMap]
    (w : RingedPresentationAt e)
    (N : PresentationDerived S) (I : PresentationModules S)
    (ι : I ⟶ SheafOfModules.unit (localCoefficientRings S)) [Mono ι] :
    presentationComplete S I ι N ↔
      presentationComplete R (w.transport.modules.functor.obj I)
        (w.transport.modules.functor.map ι ≫ w.transport.forward.unit.hom)
        (w.transport.forward.derived.obj N) := by
  rw [presentation_complete_iff_generalized_tests,
    presentation_complete_iff_generalized_tests]
  constructor
  · intro h B b
    let A := e.inverse.objPreimage B
    let p := e.inverse.objObjPreimageIso B
    let c := p.hom ≫ b ≫ w.underlying.hom.app I
    let d := e.inverse.preimage c
    apply (presentation_generalized_test_transport e w N A B p
      (d ≫ (presentationForget S).map ι)
      (b ≫ (presentationForget R).map
        (w.transport.modules.functor.map ι ≫ w.transport.forward.unit.hom)) ?_).mp
      (h A d)
    rw [transportedIdeal_section e w I ι b]
    simp only [← Category.assoc]
    rw [Functor.map_comp, e.inverse.map_preimage]
    rfl
  · intro h A a
    let b := e.inverse.map a ≫ w.underlying.inv.app I
    apply (presentation_generalized_test_transport e w N A (e.inverse.obj A) (Iso.refl _)
      (a ≫ (presentationForget S).map ι)
      (b ≫ (presentationForget R).map
        (w.transport.modules.functor.map ι ≫ w.transport.forward.unit.hom)) ?_).mpr
      (h (e.inverse.obj A) b)
    simp only [Iso.refl_hom, Category.id_comp]
    rw [transportedIdeal_section e w I ι b]
    dsimp only [b]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]

end CategoryTheory
