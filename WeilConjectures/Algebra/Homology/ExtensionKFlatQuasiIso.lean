/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
import all WeilConjectures.Algebra.Homology.KFlatScalarExtensionDerivedIso

/-! # Extension of scalars on K-flat complexes

Extension of scalars preserves quasi-isomorphisms between K-flat complexes.

## References

* Stacks Project, More on Algebra, Tags 064L and 06Y0
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory

namespace ModuleCat

/-- Extension of scalars preserves quasi-isomorphisms between K-flat complexes,
without a flatness assumption on the ring map.
-/
theorem extendScalars_preservesKFlatQuasiIso {R B : Type u} [CommRing R] [CommRing B]
    (ρ : R →+* B) [(ModuleCat.extendScalars.{u, u, u} ρ).Additive] :
    (ModuleCat.extendScalars.{u, u, u} ρ).PreservesKFlatQuasiIso := by
  constructor
  intro P Q hP hQ α hα
  exact CochainComplex.scalarExtension_quasiIso_of_kFlat ρ α hα hP hQ

end ModuleCat
