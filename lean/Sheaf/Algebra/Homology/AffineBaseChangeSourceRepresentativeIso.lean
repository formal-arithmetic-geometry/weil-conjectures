/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.Algebra.Homology.AffineBaseChangeIntoPullback

/-! # Independence of the source-only stalk comparison from its representative

Source: Stacks Project, Tags 06Y6, 08IB and 0DJ8, equation-bc.
(blueprint: lem-pc-affine-base-change-source-representative-iso).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The source-only comparison is unchanged under K-flat representative change.
Source: Stacks Project, Tags 06Y6, 08IB and perfect.tex, equation-bc before Tag 0DJ8.
(blueprint: lem-pc-affine-base-change-source-representative-iso).

Proof: the exact stalk functor sends eQ followed by eP inverse to an isomorphism
between the derived stalk complexes. The universal derived extension functors
of the baseDerivedTensorCohomologyModel are uniquely isomorphic through their
counits. Apply their cohomology functors to this isomorphism. The cohomologyIso_smul
equations show that it respects both commuting scalar actions, hence the tensor
algebra action. Extend to the fourth stalk ring and forget scalars to obtain t.
Naturality of the universal counit makes the comparison_eq squares commute;
transposition through the extension/restriction adjunction and localized_eq gives
the same equation for localizedComparison. Naturality of tensorStalkIso and of
the exact representative/stalk comparison identifies the target with the stalk
of H(Lg'^*K). Finally cancel the invertible pullback counits and use their
naturality with eQ and eP. The resulting equation is the one displayed here.
No termwise quasi-coherence is assumed, and this argument applies on arbitrary
schemes, to zero complexes and in every integer degree. -/
theorem exists_affineBaseChangeIntoPullback_representativeIso
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (K : schemeDerivedCategory X)
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlat) (hQ : Q.IsKFlat)
    (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ K)
    (hcP : IsIso ((SingleComplexBaseChange.counit g').app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (hcQ : IsIso ((SingleComplexBaseChange.counit g').app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj Q))) (p : X') (i : ℤ) :
    ∃ t : (Arrow.mk (affineBaseChangeIntoPullback f f' g g' sq K Q eQ hcQ p i)).left ≃+
        (Arrow.mk (affineBaseChangeIntoPullback f f' g g' sq K P eP hcP p i)).left,
      ∀ x, affineBaseChangeIntoPullback f f' g g' sq K Q eQ hcQ p i x =
        affineBaseChangeIntoPullback f f' g g' sq K P eP hcP p i (t x) := by
  sorry

end AlgebraicGeometry
