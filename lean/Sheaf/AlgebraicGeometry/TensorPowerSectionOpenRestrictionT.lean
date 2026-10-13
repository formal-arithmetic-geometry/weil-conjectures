/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestrictionN

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical numerator comparisons intertwine the transition morphisms as sheaf maps.
Source: Stacks Project, Modules, Tag 01CD; Properties, Tag 01PW, restriction paragraph.
(blueprint: lem-sc-tensor-power-section-open-restriction-T).

Proof: The inverse tensor comparison is uniquely characterized on all pure tensor
sections. Apply the sheaf tensor universal property to prove its naturality, associator
and unitor coherence: both composites carry a pure tensor to the same ambient tensor,
by tensorHom_app_tmulSection, associator_hom_app_tmulSection and the unitor formulas.
Induct on the first exponent in tensorPowAddIso. The zero case uses the unit comparison
and left unitor; the successor uses the recursive tensor comparison and associator.
This proves compatibility of the recursive power comparisons with tensorPowAddIso.
The section-power compatibility is openRestrictionTensorPowIso_inv_section. Expand
mulTensorPowSection into the inverse right unitor, tensoring with tensorPowSection,
the associator, and the inverse tensorPowAddIso. The previous compatibilities give the
displayed equality. The section-power comparison determines the section morphism since
homOfGlobalSection is determined by its value on 1. Equality is of sheaf morphisms;
there is no assumption that arbitrary sections are pure tensors. -/
theorem openRestrictionNumeratorIso_mul (X : Scheme.{u}) (L F : X.Modules)
    (s : Γ(L, ⊤)) (U : X.Opens) (n b : ℕ) :
    let sU : Γ(L.restrict U.ι, ⊤) :=
      (L.restrictAppIso U.ι ⊤).inv (L.presheaf.map (homOfLE le_top).op s)
    (restrictFunctor U.ι).map (mulTensorPowSection (homOfGlobalSection L s) F n b) ≫
        (openRestrictionNumeratorIso U.ι F L (n + b)).hom =
      (openRestrictionNumeratorIso U.ι F L n).hom ≫
        mulTensorPowSection (homOfGlobalSection (L.restrict U.ι) sU)
          (F.restrict U.ι) n b := by
  sorry

end AlgebraicGeometry.Scheme.Modules
