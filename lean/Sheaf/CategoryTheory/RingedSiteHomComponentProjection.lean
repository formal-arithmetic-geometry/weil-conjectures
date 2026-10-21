/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The SHEAF contributors
-/
module

public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.HomComplexComponents

/-! # Compatibility of the coefficient Hom projection presentations

Source: Stacks Project, Tag 0A8X (blueprint: lem-sfb-ringed-site-duality-maps).
The compatibility is checked separately so clients can use the projection API
without unfolding the Hom-complex existence specification at each use.
-/

@[expose] public section
set_option autoImplicit false
universe c v r
open CategoryTheory
namespace WeilConjectures

/-- The coefficient component is the named product projection of the same Hom complex.
Source: Stacks 0A8X (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: unfold the projection definitions. The existence specifications select the same
projection family by proof irrelevance. -/
theorem coefficientHomComponent_eq_homComplexπ
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
    (R : Sheaf J CommRingCat.{max c v r})
    (L M : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (n p q : ℤ) (h : p + n = q) :
    coefficientHomComponent.{r, c, v} J R L M n p q h =
      homComplexπ.{c, v, max c v r, max c v r} (R := R) L M n p q h := by
  with_unfolding_all rfl

end WeilConjectures
