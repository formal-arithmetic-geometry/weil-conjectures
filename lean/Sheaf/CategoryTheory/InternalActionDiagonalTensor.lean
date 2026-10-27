/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.CategoryTheory.InternalRestrictionModuleTensorData

/-! # Diagonal tensor on internal-action module sheaves

Source: Stacks 03EK and the unit-compatible action-site sheafification comparisons.
(blueprint: lem-sfb-internal-action-diagonal-tensor).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open SheafOfModules

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C]

attribute [local irreducible] SheafOfModules.monoidalCategory

/-- Sheafifying the sectionwise tensor with diagonal action agrees with the
existing tensor on the action site, compatibly with its pure tensors.

Source: Stacks Project, Modules on Sites, Tag 03EK; step 4 of
lem-sfb-internal-restriction-module-tensor.
(blueprint: lem-sfb-internal-action-diagonal-tensor).

Proof: on U, give M(U) tensor_R(U) N(U) the operation a(x tensor y) = ax tensor ay.
The operation is well defined by bilinearity and balancing because the two actions
are R(U)-linear. Tensor generation proves its identity and multiplication laws;
a⁻¹ supplies its inverse. Naturality of both actions proves compatibility with
base restriction. Thus these tensors form an equivariant module presheaf.
Apply P.equivariantSheafification to obtain H. P.baseComparison identifies its
underlying sheaf with the existing base tensor sheaf, giving b. P.siteComparison
identifies its image on the action site with the sheafification of the twisted
presheaf tensor, giving e. The presheaf section equivalences induce the tensor
identification: twisted restriction sends x tensor y to (a f*x) tensor (a f*y).
Both comparisons commute with sheafification units by P.base_unit and P.site_unit.
Hence the action formula and the equation on action-site pure tensors are exactly
the two required equations. No assertion of sectionwise surjectivity of the
sheafification unit is used; uniqueness is its universal property. The construction
also works for the zero ring, the trivial group, and sites with empty covers. -/
theorem internalActionDiagonalTensor [HasFiniteLimits C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings) (K : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) (P : Presentation K J hJ R) :
    InternalDiagonalTensor J hJ K R P := by
  sorry

end CategoryTheory.InternalActionSite
