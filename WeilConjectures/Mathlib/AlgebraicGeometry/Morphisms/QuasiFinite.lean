/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# Unramified morphisms locally of finite type are locally quasi-finite

Both `AlgebraicGeometry.FormallyUnramified` and `AlgebraicGeometry.LocallyOfFiniteType` are
affine-local on source and target, so the implication reduces to the corresponding statement
for ring homomorphisms, `RingHom.QuasiFinite.of_formallyUnramified_of_finiteType`.

In particular an étale morphism is locally quasi-finite, which combined with Zariski's main
theorem (`AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`) shows that a proper
étale morphism is finite.

## Main results

- `AlgebraicGeometry.locallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType`: a
  formally unramified morphism locally of finite type is locally quasi-finite.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A formally unramified morphism locally of finite type is locally quasi-finite. -/
instance (priority := low) locallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f :=
  (HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)).mpr fun U V e ↦
    .of_formallyUnramified_of_finiteType
      (HasRingHomProperty.appLE @FormallyUnramified f ‹_› U V e)
      (HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_› U V e)

example [Etale f] : LocallyQuasiFinite f := inferInstance

end AlgebraicGeometry
