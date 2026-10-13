/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction

/-! # Existence of an augmentation quotient in one degree

Source: Stacks Project, Tag 01EQ, proof of Lemma 20.11.2.
(blueprint: new-abelian-cech-comparison-core)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
/-- A quotient comparison exists in one degree, without a normalization assertion.

Source: Stacks Project, Tag 01EQ, proof of Lemma 20.11.2, the quotient of beta by
alpha; resolution independence expands the functoriality verification there.
(blueprint: new-abelian-cech-comparison-core)

Proof: Fix an injective resolution I of F. Evaluation at 1 in the constant-sheaf
adjunction gives an additive bijection from maps out of the constant integer
sheaf to global sections, commuting with the resolution differentials. Passing
to cocycles modulo coboundaries and using I.extAddEquivCohomologyClass gives an
additive isomorphism e from Ext in degree q to homology of abelianCechSections I.
It sends I.extMk a to homologyπ z whenever iCycles z is the section of a.
Define c by H(beta), inverse H(alpha), and inverse e, in that order; hα I makes
the middle map invertible. This gives the required equality on I.

For another resolution J, lift the identity of F to a chain map I -> J. Apply
sections and the Čech double-complex construction to this lift. Restriction
naturality and the augmentation identity give commuting alpha and beta squares.
The cocycle formula I.extMk_comp_mk₀ shows that e commutes with the induced
section homology map. This map is invertible since both e maps are isomorphisms;
the alpha square and hα imply that the total homology map is invertible too.
Transport the equality on I along these squares and cancel the total map. This
proves the equation on J for any representative a and section cycle z.

The argument uses neither hcover nor a finite-cover assumption: the supplied
quasi-isomorphisms suffice. If F is zero, or the space and cover are empty, the
same quotient construction uses the zero groups and still applies. -/
theorem exists_abelianCechComparison_core
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hα : ∀ I : InjectiveResolution F, QuasiIso (abelianCechAlpha U I)) (q : ℕ) :
    ∃ c : (TopCat.Sheaf.cechCohomologyFunctor U q).obj F ⟶
      (Sheaf.functorH (Opens.grothendieckTopology X) q).obj F,
      IsAbelianCechComparison U F q c := by sorry
end AlgebraicGeometry.Scheme.Modules
