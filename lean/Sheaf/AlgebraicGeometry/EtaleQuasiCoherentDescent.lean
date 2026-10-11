/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.AlgebraicGeometry.EtaleTensorSections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Étale descent for sections of quasi-coherent modules

Source: Stacks Project, Descent, Section 35.8, Tags 03DR and 03DT
(blueprint: lem-sc-etale-qcoherent-descent).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- The presheaf `u : U ⟶ X ↦ Γ(U, u^*F)`, with pullback restrictions, is a sheaf on
`X.smallEtaleTopology` when `F` is quasi-coherent.
Source: Stacks Project, Descent, Section 35.8, equation (35.8.1) and Lemma 35.8.1,
Tags 03DR and 03DT (blueprint: lem-sc-etale-qcoherent-descent).

Proof:
1. A covering family of the small étale site is an fpqc covering of its target, by
   `lem-weil-pbc-fpqc-finer-than-etale` and `def-weil-pbc-etale-site`.
2. Apply `lem-sc-etale-qcoherent-descent-fpqc-sections` to the pullback of `F` on that
   target: compatible sections on the covering family descend to a unique section.
   In Stacks Tag 03DT this follows from descent of morphisms between quasi-coherent
   modules (Proposition 35.5.2), identifying sections with maps from the structure sheaf.
3. The restriction maps are those of `lem-sc-etale-qcoherent-presheaf-functorial`.
   Thus the existence and uniqueness in step 2 are precisely the sheaf condition for
   `etaleTensorSectionsPresheaf F` on `X.smallEtaleTopology`. -/
theorem isSheaf_etaleTensorSectionsPresheaf {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] :
    Presheaf.IsSheaf X.smallEtaleTopology (etaleTensorSectionsPresheaf F) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
