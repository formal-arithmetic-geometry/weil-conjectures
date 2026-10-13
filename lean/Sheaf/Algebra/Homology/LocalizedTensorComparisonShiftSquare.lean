/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.Algebra.Homology.LocalizedTensorComparisonProperty

/-! # Shift square for localized tensor comparison

Source: Stacks Project, Tag 0DJA(1), using Tag 0BYJ.
(blueprint: lem-pc-localized-tensor-comparison-shift-square).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

/-- The comparison arrows for U and its inverse shift are conjugate.
Source: Stacks Project, Tag 0DJA(1), via Tag 0BYJ and the tensor shift maps.

Proof: put V = U[-n]. Use the first-variable tensor shift isomorphism
V tensor Q = (U tensor Q)[-n] and the scalar-extension shift isomorphism.
Keep the derived functor and universal counit of mU. Its canonical shift
comparison is obtained by uniqueness of the left-derived functor of the
additive extension-of-scalars functor. Reindex cohomology by j -> j-n:
transport the A tensor_R B action using the cohomology shift isomorphism.
Naturality in multiplication by a in A proves cohomologyIso_smul. Transport
ordinaryIso and ordinaryToLocalized through the termwise scalar-extension
shift maps; on tensors their specified formulas are unchanged. Define the
comparison by the counit formula comparison_eq and define its localization
by the extension/restriction adjunction, proving localized_eq. This constructs
mV without any choice of a witness of model existence. At degree i+n the
cohomology shift map gives eS after scalar extension to C; the target shift
map for F(U) tensor N gives eT. Naturality of the first-variable tensor shift
map in Q -> N and monoidality of F identifies the ordinary comparison square.
The counit shift compatibility gives its derived source square; transposing
localized_eq through the scalar adjunction gives the displayed conjugacy.
The first-variable tensor shift involves no extra signs. For n=0
use identity reindexing; zero complexes and arbitrary t are included. Neither
flatness of C nor K-flatness of U or Q is used by this transport statement.
(blueprint: lem-pc-localized-tensor-comparison-shift-square). -/
theorem exists_localizedTensorComparison_shift_square
    (U : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C) (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    ∃ (mV : BaseDerivedTensorCohomologyModel R A B ((U⟦-n⟧) ⊗ Q) C)
      (eS : (extendScalars (algebraMap (A ⊗[R] B) C)).obj (mV.cohomology (i + n)) ≅
        (extendScalars (algebraMap (A ⊗[R] B) C)).obj (mU.cohomology i))
      (eT : (F.obj (U⟦-n⟧) ⊗ N).homology (i + n) ≅ (F.obj U ⊗ N).homology i),
    mU.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i =
    eS.inv ≫ (mV.localizedComparison (i + n) ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F (U⟦-n⟧) Q).inv ≫ (F.obj (U⟦-n⟧) ◁ t)) (i + n)) ≫
        eT.hom := by sorry

end ModuleCat
