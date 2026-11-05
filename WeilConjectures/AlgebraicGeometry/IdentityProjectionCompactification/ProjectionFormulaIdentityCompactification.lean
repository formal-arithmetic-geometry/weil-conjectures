/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaBaseChangeNaturality
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectPackageOnSiteSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Projection.ProjectionFormulaCompactified

/-!
# Identity compactification and the projection formula

Source: Weil conjectures blueprint, proper base change, order 1272, identity
compactification lemma; detailed proper_base_change.tex, lines 5600--5616
(blueprint: lemma-weil-pbc-projection-formula-identity-compactification).

We use the normalized presentation of the identity open immersion: its extension
by zero and its restriction are the identity functor, with identity unit and counit.
Thus the definition Rp_* j_! is the actual composite (identity functor) followed by
Rp_*, and the open tensor comparison and composition constraint are identities.
These definitions describe this specific compactification, not arbitrary shriek data.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.IdentityProjectionCompactification

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
  (aY : ProEtaleTensorModel Y R) (aX : ProEtaleTensorModel X S)
  (E : DerivedCategory (proEtaleRingModules X S))
  (Q : DerivedCategory (proEtaleRingModules Y R))

variable [hf : IsProper f]

end AlgebraicGeometry.Scheme.IdentityProjectionCompactification
