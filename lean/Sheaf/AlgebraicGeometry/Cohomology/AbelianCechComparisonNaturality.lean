/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction
import Sheaf.AlgebraicGeometry.Cohomology.AbelianCechAlphaQuasiIso

/-! # Naturality of the augmentation quotient

Source: Stacks Project, Tag 01EQ, functoriality omitted in the proof,
and Tag 01FD, augmented comparison diagram.
(blueprint: lem-pc-abelian-cech-comparison-naturality)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
/-- Canonical comparison maps commute with coefficient morphisms.

Source: Stacks Project, Tags 01EQ and 01FD, augmentation squares.
(blueprint: lem-pc-abelian-cech-comparison-naturality)

Proof: Choose injective resolutions I of F and J of G and a lift of f between
them. Apply the Čech functor degreewise and totalize. Restrictions commute with
the lift by presheaf naturality, and coefficient augmentations commute with it
by the lifting equation, giving the alpha and beta squares. Apply homology.
The constant-sheaf adjunction takes a representing Ext cocycle a on I to its
section cycle, and takes a composed with the lift to the image section cycle
on J. Mathlib's extMk_comp_mk0 identifies the latter cocycle with the image of
the Ext class under H(f). For every input Čech class, apply the two defining
comparison equations to these representatives. The augmentation squares imply
that both proposed images agree after H(alpha on J) and the section-complex
identification. The row-augmentation quasi-isomorphism makes H(alpha on J)
injective, and Ext computed from J makes the identification injective. Cancel
both maps. Ext representatives exist by extMk_surjective. This proves equality
on every class and hence equality of the two additive morphisms. Empty spaces,
zero sheaves, and infinite covers are included by the same constructions. -/
theorem abelianCechComparison_naturality
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (f : F ⟶ G)
    (q : ℕ)
    (c : (TopCat.Sheaf.cechCohomologyFunctor U q).obj F ⟶
      (Sheaf.functorH (Opens.grothendieckTopology X) q).obj F)
    (d : (TopCat.Sheaf.cechCohomologyFunctor U q).obj G ⟶
      (Sheaf.functorH (Opens.grothendieckTopology X) q).obj G)
    (hc : IsAbelianCechComparison U F q c) (hd : IsAbelianCechComparison U G q d) :
    (TopCat.Sheaf.cechCohomologyFunctor U q).map f ≫ d =
      c ≫ (Sheaf.functorH (Opens.grothendieckTopology X) q).map f := by
  sorry
end AlgebraicGeometry.Scheme.Modules
