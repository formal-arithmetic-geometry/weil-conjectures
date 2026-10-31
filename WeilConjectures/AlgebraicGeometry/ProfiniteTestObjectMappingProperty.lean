/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapComparison

/-! # The mapping property of absolute profinite test objects

Source: Hemo--Richarz--Scholbach, Example 3.1 and the construction before (4.1).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Maps from an affine pro-étale object into `X[S]` are characterized by their
continuous profinite coordinate.

Source: Hemo--Richarz--Scholbach, Example 3.1 and the construction before (4.1)
(blueprint: lem-zl-profinite-test-object-mapping-property).

Proof: on affine schemes a continuous map to `S` gives the ring homomorphism
from locally constant integer functions, using the canonical integer scalars.
The spectrum correspondence gives a map into `Spec LC(S, ℤ)`. Pair it with the
structure map to `X` and use the pullback over `Spec ℤ` to obtain the required
map into `X[S]`. Equality of the profinite coordinates determines the ring maps,
and the second pullback projection is already fixed over `X`, giving uniqueness. -/
theorem profinite_test_object_mapping_property (X : Scheme.{u})
    {V : X.ProEt} [IsAffine V.left] {S : Profinite.{u}} (c : C(V.left, S)) :
    ∃! f : V ⟶ profiniteTestObject X S,
      ∀ y, profiniteTestObjectProj X S (f.left.base y) = c y := by
  obtain ⟨f, hf⟩ := exists_hom_profiniteTestObject X c
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact hom_ext_profiniteTestObject X (fun y ↦ (hg y).trans (hf y).symm)

end AlgebraicGeometry.ProEtale
