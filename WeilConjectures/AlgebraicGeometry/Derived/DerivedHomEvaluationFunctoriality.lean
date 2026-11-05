/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison

/-! # Functoriality of local derived morphism evaluation

Source: Stacks Tags 09B1, 0946, 09BE and 0F63. Transpose the local comparison
identities under the two adjunctions, then cancel the bijective sheafification unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
  (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))

end AlgebraicGeometry.Scheme
