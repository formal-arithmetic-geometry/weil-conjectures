/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Locally Noetherian regular schemes

Source: Stacks Project, Properties, Tag 02IT, and the scheme clause of the Weil
conjectures blueprint (blueprint: def-weil-regular-scheme).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- A regular scheme is locally Noetherian and has regular local rings at every point.
The ring notions are Mathlib's `IsRegularLocalRing` and `IsRegularRing`; the stalkwise
scheme condition is the upstream `IsRegular`. Local Noetherianity is included explicitly,
as required by the node, rather than inferred from regularity of individual stalks.
Source: Stacks Project, Lemma 02IT (blueprint: def-weil-regular-scheme). -/
def IsRegularScheme (X : Scheme.{u}) : Prop :=
  IsLocallyNoetherian X ∧ IsRegular X

end AlgebraicGeometry
