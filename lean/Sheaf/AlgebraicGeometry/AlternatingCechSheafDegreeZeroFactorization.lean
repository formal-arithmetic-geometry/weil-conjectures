/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSheafConstruction

/-! # Local alternating Čech cancellation

Source: Stacks Project, Tags 02FU and 01FM.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Every degree-zero endomorphism killed by the first differential factors
through the local augmentation.
Source: Stacks Project, Tag 02FU, exactness at the first Čech term;
Tag 01FM for the ordered alternating convention.
(blueprint: lem-pc-s3-alternating-cech-sheaf-degree-zero-factorization).

Proof: A degree-zero cocycle is a family of sections on the singleton
intersections whose restrictions agree on pairwise intersections. On a test open
V contained in U i, take its i coordinate, which is a section of G(V).
The pairwise agreement with that coordinate shows that its augmentation recovers
every coordinate of the cocycle. The projection is linear and natural in V.
After sheafification, work locally where a section of the sheafified finite
product is represented by presheaf sections. The vanishing differential becomes
local pairwise agreement; taking the i coordinate then gives local sections of
G, and uniqueness glues them. Thus the augmentation identifies G with the
kernel of the first differential on U i. Transport this kernel property through
integer extension and restriction. Apply its universal property to the given
endomorphism f killed by the differential to obtain π, with π ≫ a.f 0 = f.
Empty opens have zero modules, r=0 has no i, and for r=1 the augmentation is
an isomorphism while the first differential has zero target.
-/
theorem alternatingCechSheafAugmentation_restrict_degreeZero_factorization
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r) :
    let F := Scheme.Modules.restrictFunctor (U i).ι
    let A := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((CochainComplex.single₀ X.Modules).obj G).extend ComplexShape.embeddingUpNat)
    let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)
    let a : A ⟶ C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap (alternatingCechSheafAugmentation U G)
        ComplexShape.embeddingUpNat)
    ∀ f : C.X 0 ⟶ C.X 0, f ≫ C.d 0 1 = 0 →
      ∃ π : C.X 0 ⟶ A.X 0, π ≫ a.f 0 = f := by sorry

end AlgebraicGeometry
