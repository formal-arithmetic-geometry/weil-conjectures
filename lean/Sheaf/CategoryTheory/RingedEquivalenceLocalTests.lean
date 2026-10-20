/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z5
-/
module

public import Sheaf.CategoryTheory.RingedPresentationData

import Sheaf.CategoryTheory.RingedEquivalenceModuleHom
import Sheaf.CategoryTheory.ElementRestrictionHom
import Sheaf.CategoryTheory.RingedEquivalenceSlices

/-! # Auxiliary ringed presentation comparisons -/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

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
derived test object, is zero. Conversely choose the sheafified representable
of U and use the fibre equivalence for the site-object slice. This includes
empty sites and empty coverings.
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
  sorry

end CategoryTheory
