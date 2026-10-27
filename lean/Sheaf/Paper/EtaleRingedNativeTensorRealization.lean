/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Paper.EtaleRingedDerivedIdentificationData

/-! # The normalized native tensor realization on lifted étale sites -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConstantScalarRestriction CategoryTheory.ConstantModuleDerivedProjection
namespace AlgebraicGeometry.Etale.RingedProjectionIdentification

/-- Literal constant scalar restriction and site transport have their normalized
ordinary tensor comparison.
Source: Stacks Project, sites-modules.tex, Tag 0GMW, and sites-cohomology.tex,
Tags 06YU and 07A4
(blueprint: lem-pur-etale-ringed-native-tensor-realization).
Proof: on the lifted site use constant scalar restriction's normalized braided
structure. Precomposition by the canonical site equivalence transports sheaf tensor
products: sheafification commutes with this equivalence, and the comparison is the
identity on each local pure tensor and on each constant scalar in the unit. Its
inverse is precomposition in the other direction. The unit and counit of the site
equivalence are identities on sections. This gives the stated ordinary braided
structure and its pure-tensor and unit normalizations. The argument is
unchanged for zero coefficients or an empty site. -/
theorem etale_ringed_native_tensor_realization (T : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :
    Nonempty (NativeOrdinaryTensorData T Λ) := by
  sorry

end AlgebraicGeometry.Etale.RingedProjectionIdentification
