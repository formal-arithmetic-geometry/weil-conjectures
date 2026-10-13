/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSheafConstruction

/-! # Ordered insertion contracts the alternating Čech augmentation locally

Source: Stacks Project, Tags 02FU (local insertion) and 01FM (alternating comparison);
the ordered local insertion argument in
lem-pc-s3-alternating-cech-sheaf-local-contraction.
(blueprint: lem-pc-s3-alternating-cech-sheaf-insertion-homotopy).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- On a member of the family, the extended augmentation is a homotopy equivalence.
Source: Stacks Project, Tag 02FU (insertion contraction), adapted to increasing
tuples as in Tag 01FM, and the local contraction paragraph of
lem-pc-s3-alternating-cech-sheaf-local-contraction.
(blueprint: lem-pc-s3-alternating-cech-sheaf-insertion-homotopy).

Proof: On an open contained in U_i, project degree zero to the singleton i to define
the inverse of the augmentation. For a tuple t not containing i, insert i in its
unique increasing position a and take that coordinate with coefficient (-1)^a;
use zero when i already occurs. Since the test open lies in U_i, adjoining i does
not change its intersection with t, so the two section modules are canonically
identified. These operators are
linear and commute with restrictions, hence define morphisms of module presheaves.
In dh+hd the face deleting the inserted i is the identity; every other face cancels
with the same composite restriction bearing the opposite sign. When i is already
present, its deletion is the sole nonzero insertion contribution. The degree-zero
identity includes the singleton projection and the augmentation, whose reverse
composite is the identity. Sheafification and restriction are additive and preserve
these identities. This gives the inverse and the two homotopies for the augmentation
restricted to U_i. Extending by zero to integer degrees extends the inverse and both
homotopies and leaves the identities intact. No cover condition is used; if r=0
there is no index i and the assertion has no instances. -/
theorem alternatingCechSheafAugmentation_restrict_homotopyEquivalence
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r) :
    HomologicalComplex.homotopyEquivalences (U i).toScheme.Modules (ComplexShape.up ℤ)
      (((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (HomologicalComplex.extendMap
          (alternatingCechSheafAugmentation U G) ComplexShape.embeddingUpNat)) := by sorry

end AlgebraicGeometry
