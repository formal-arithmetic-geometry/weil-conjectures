/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FieldProjectionSystemData

/-! # Canonical tensor comparisons for field systems

Source: latest blueprint, field-extension-towers proof (2)
(blueprint: lem-sp-field-projection-tensor-construction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

variable (P : PurityFiniteSetting.{u}) (D : Models P)

/-- Construct the signed symmetry and strong scalar tensor comparison on the fixed models.
Source: Stacks 06YU, 07A4 and blueprint field-extension-towers proof (2)
(blueprint: lem-sp-field-projection-tensor-construction).

Proof: on the total tensor of two K-flat complexes interchange the homogeneous
summands with sign (-1)^(ab). The two differential contributions transform with
exactly this sign, so this is a chain isomorphism, natural in both complexes.
Restriction to the resolving subcategory and the two-variable localization
universal property descend it to the supplied derived tensor. For a coefficient
map use extension of scalars on ordinary sheaf tensors: (x tensor y) tensor b
maps to (x tensor b) tensor (y tensor 1), with inverse given by multiplying the
two scalar factors. Sheafification preserves the balancing equations. Apply this
map in each total summand. It preserves the signed differential and flat-term
K-flat complexes, and the scalar universal counits identify its localization
with the derived tensor comparison. These constructions give all four fields,
simultaneously for every coefficient inclusion and scheme. -/
theorem field_projection_tensor_construction :
    Nonempty (ProjectionTensorComparisons P D) := by sorry

end AlgebraicGeometry.ProEtale.FieldShriekSystem
