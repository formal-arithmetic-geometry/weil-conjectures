/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y5
-/
module

public import Sheaf.Paper.FiniteFreeScalarCalculusData

/-! # Normalized finite-free scalar constructions

Source: Stacks Project, Tags 03CZ, 05V4, 06YU and 05RT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
  [Algebra A B] (r : ℕ) (basis : Module.Basis (Fin r) A B)

/-- The normalized ordinary scalar balancing maps descend on K-flat cochain models.
Source: Stacks 06YU and 05V4; step 7 of lem-sf-finite-free-derived-scalar-calculus.
(blueprint: lem-sf-finite-free-scalar-derived-tensor-models).

Proof: let P and Q be K-flat A- and B-complexes. Exact extension and cancellation show
that UQ is K-flat: for acyclic H, its tensor with UQ is the restriction of EH tensor Q,
which is acyclic. Extension preserves K-flatness by the supplied descent. Restriction
preserves the coproducts in each total degree. Apply the sheaf balancing maps on each
homogeneous summand; the normalized formulas commute with both differentials, including
the sign in the second one, since the coefficient b has degree zero. The inverse formulas
give inverse chain maps. Naturality holds on pure tensors and hence after sheafification
and totalization. Descend this natural isomorphism through the two K-flat localization
equivalences. The defining localization equation is the tensor_normalized square with
the canonical mapDerivedCategoryFactors and localization tensorators. Its component
formula on each summand is precisely the first clause of that normalization. The same
localization equation proves independence of representatives and joint naturality. -/
theorem finiteFreeScalarDerivedTensorModels (s : FiniteFreeScalarTensorCalculus J r basis) :
    letI := s.extension_limits
    letI := s.extension_colimits
    letI := s.restriction_limits
    letI := s.restriction_colimits
    Nonempty (FiniteScalarDerivedTensorModels
      (finiteScalarExtension J (algebraMap A B)) (Sheaf.restrictScalars J (algebraMap A B))
      s.sheaf_balance) := by sorry

end AlgebraicGeometry
