/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSheafConstruction

/-! # Signed insertion identities on the local alternating complex

Source: Stacks Project, Tag 02FU, the insertion cancellation computation;
Tag 01FM for the ordered alternating convention.
(blueprint: lem-pc-s3-alternating-cech-sheaf-insertion-identities).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Signed insertion contracts the complement of any chain retraction.
Source: Stacks Project, Tag 02FU, insertion and cancellation, adapted to increasing
indices as in Tag 01FM. The adjustment to an arbitrary retraction is elementary.
(blueprint: lem-pc-s3-alternating-cech-sheaf-insertion-identities).

Proof: First use the singleton projection p₀. On an open V contained in U i,
insert i in the increasing target tuple in its unique position b and multiply
by (-1)^b, or use zero if i already occurs. V intersect U i equals V, so insertion
uses the canonical identification of sections on equal intersections. The maps
are linear and natural. In dh+hd, deleting the inserted index gives the identity;
each other deletion pairs with insertion after deletion, with the same restriction
and opposite sign. If i was already present, only its deletion contributes.
In degree zero the identity is d₀h₀ = id - p₀a₀. Sheafification and restriction
are additive, so these equations remain valid for the constructed sheaf complex.
Extension by zero gives the same equations in integer degrees, with zero maps
in negative degrees. Now let q be any chain retraction and put p=q.f 0 and
δ=p-p₀. The retraction identities imply a₀δ=0. Therefore
δ=(id-p₀a₀)δ=d₀h₀δ. Replace h₀ by h₀-h₀δa₀, keeping every other h unchanged.
Then d₀h₀ becomes id-pa₀; h₀d₀ is unchanged because a₀d₀=0. Outside degree zero
q has zero components since its target is supported in degree zero. These are
exactly the displayed identities for all integer k. Empty intersections and an
empty U i cause no exception: the same linear identities hold in zero modules;
when r=0 there is no index i. -/
theorem alternatingCechSheafAugmentation_restrict_insertion_identities
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r) :
    let F := Scheme.Modules.restrictFunctor (U i).ι
    let A := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((CochainComplex.single₀ X.Modules).obj G).extend ComplexShape.embeddingUpNat)
    let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)
    let a := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap (alternatingCechSheafAugmentation U G)
        ComplexShape.embeddingUpNat)
    ∀ q : C ⟶ A, a ≫ q = 𝟙 A →
      ∃ h : ∀ k : ℤ, C.X (k + 1) ⟶ C.X k,
        ∀ k : ℤ, (q ≫ a).f k + C.d k (k + 1) ≫ h k +
          (C.XIsoOfEq (show k = k - 1 + 1 by omega)).hom ≫
            h (k - 1) ≫ C.d (k - 1) k = 𝟙 (C.X k) := by sorry

end AlgebraicGeometry
