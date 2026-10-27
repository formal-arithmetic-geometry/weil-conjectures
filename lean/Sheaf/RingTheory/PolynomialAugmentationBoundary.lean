/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Sheaf.AlgebraicTopology.TrivialKanFibration
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.Logic.Relation
import Sheaf.AlgebraicTopology.SurjectiveQuasiIsoTrivialKan
import Sheaf.CategoryTheory.AdjunctionStandardSimplicialHomotopy
import Sheaf.AlgebraicTopology.SimplicialAbelianSetHomotopyQuasiIso

/-!
# Standard polynomial augmentations and boundary lifting

Source: Stacks Project, Cotangent Complex, Tags 08PM, 08PT (first proof), 08QI;
Simplicial, Tags 0197, 08ND, 08P2 and 08P1
(blueprint: lem-trf-polynomial-augmentation-boundary).

The existing cotangent-resolution definitions specify actual iterated polynomial rings,
evaluation faces, unit degeneracies and the iterated evaluation augmentation. The additive
augmentation uses the alternating-face complex extended along `n ↦ -n`. The homotopy inverse
below is a map of simplicial sets and carries no additivity or multiplicativity condition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite Simplicial

namespace Algebra.CotangentResolution

/-- The constant comparison, the boundary-lifting criterion, and the standard polynomial
resolution, with all its augmentation properties.

Source: Stacks Project, Cotangent Complex, Tags 08PM, 08PT (first proof) and 08QI;
Simplicial, Tags 0197, 08ND, 08P2 and 08P1
(blueprint: lem-trf-polynomial-augmentation-boundary).

Proof: (1) For the constant simplicial additive group of B, each face is the identity.
The alternating differential out of degree -n is zero for odd n and the identity for even
n > 0. Thus H^0 is B and all other cohomology groups vanish. The augmentation, identity
in degree zero and zero elsewhere, induces precisely these isomorphisms.
(2) The additive augmentation of Q factors through the alternating complex of constant B.
By (1) and two-out-of-three its simplicial additive augmentation is a quasi-isomorphism.
Apply lem-trf-simplicial-abelian-surjective-quasi-iso-boundary-lifting, reindexing cochain
degree -n as integer chain degree n. This gives every boundary filler; for n = 0 it is
exactly a preimage under the surjective degree-zero augmentation.
(3) The polynomial universal property gives F_A left adjoint to the forgetful functor U.
Its unit sends e to X_e, and its counit evaluates X_b at b. The triangle identities hold
on coefficients and variables. Apply lem-trf-adjunction-standard-simplicial-homotopy.
Its standard terms and operators are exactly standardTerm, standardFace and
standardDegeneracy, with standardBase and standardAugmentation; hence IsStandard holds.
The right-adjoint contraction gives a homotopy inverse and homotopies on underlying sets.
(4) Each standard term is A[E] for E the underlying set of the preceding term (B initially).
Starting with b, iteratively insert a polynomial variable indexed by the preceding
preimage. Iterated evaluation returns b, proving surjectivity in every degree. Arbitrary
sets of variables are permitted, so no finiteness condition is used.
(5) Apply lem-trf-simplicial-abelian-set-homotopy-quasi-iso to the additive augmentation:
the inverse and homotopies from (3) need only be maps of sets. Compose its quasi-isomorphism
with (1) to obtain the augmentation to B[0]. Together with (4) this gives
IsPolynomialResolution. Apply (2) for the asserted trivial Kan fibration in every dimension.
-/
theorem polynomial_augmentation_boundary (f : Arrow CommRingCat.{u}) :
    QuasiIso (HomologicalComplex.extendMap
      (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
        (⟨(SimplicialObject.const AddCommGrpCat.{u}).obj
            ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj f.right),
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj f.right,
          𝟙 _⟩)) ComplexShape.embeddingDownNat) ∧
    (∀ Q : Augmentation f,
      (∀ n : ℕ, Function.Surjective (Q.augmentation.app (op ⦋n⦌))) →
      QuasiIso (additiveAugmentation Q) →
      SSet.Enhanced.trivialKanFibration
        (Functor.whiskerRight Q.augmentation (forget CommRingCat.{u}))) ∧
    ∃ P : Augmentation f, IsStandard P ∧ IsPolynomialResolution P ∧
      (∃ g : (SimplicialObject.const CommRingCat.{u}).obj f.right ⋙
          forget CommRingCat.{u} ⟶ P.algebra ⋙ forget CommRingCat.{u},
        Relation.EqvGen (fun a b ↦ Nonempty (SSet.Homotopy a b))
          (Functor.whiskerRight P.augmentation (forget CommRingCat.{u}) ≫ g)
          (𝟙 (P.algebra ⋙ forget CommRingCat.{u})) ∧
        Relation.EqvGen (fun a b ↦ Nonempty (SSet.Homotopy a b))
          (g ≫ Functor.whiskerRight P.augmentation (forget CommRingCat.{u}))
          (𝟙 ((SimplicialObject.const CommRingCat.{u}).obj f.right ⋙
            forget CommRingCat.{u}))) ∧
      SSet.Enhanced.trivialKanFibration
        (Functor.whiskerRight P.augmentation (forget CommRingCat.{u})) := by
  sorry

end Algebra.CotangentResolution
