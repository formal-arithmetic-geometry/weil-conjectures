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
# Locally quasi-finite morphisms of schemes

This file records two facts about `AlgebraicGeometry.LocallyQuasiFinite`.

First, that an unramified morphism locally of finite type is locally quasi-finite. Both
`AlgebraicGeometry.FormallyUnramified` and `AlgebraicGeometry.LocallyOfFiniteType` are
affine-local on source and target, so this reduces to the corresponding statement for ring
homomorphisms, `RingHom.QuasiFinite.of_formallyUnramified_of_finiteType`. In particular an étale
morphism is locally quasi-finite, which combined with Zariski's main theorem
(`AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`) shows that a proper étale
morphism is finite.

Second, that the fibre rings of a locally quasi-finite morphism are Artinian, hence zero
dimensional: this is the stalkwise transport of `RingHom.QuasiFinite.isArtinianRing_fiberRing`.

## Main results

- `AlgebraicGeometry.locallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType`: a
  formally unramified morphism locally of finite type is locally quasi-finite.
- `AlgebraicGeometry.Scheme.Hom.isArtinianRing_fiberRing_stalkMap`: the fibre rings of a locally
  quasi-finite morphism are Artinian.
- `AlgebraicGeometry.Scheme.Hom.ringKrullDim_fiberRing_stalkMap_eq_zero`: the fibre rings of a
  locally quasi-finite morphism are zero dimensional.
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

/-- The fibre rings of a **locally quasi-finite** morphism, in particular of a finite morphism,
are Artinian. -/
instance Scheme.Hom.isArtinianRing_fiberRing_stalkMap [LocallyQuasiFinite f] (x : X) :
    IsArtinianRing (f.stalkMap x).hom.fiberRing :=
  (f.quasiFiniteAt x).isArtinianRing_fiberRing

/-- The fibre rings of a **locally quasi-finite** morphism, in particular of a finite morphism,
are zero dimensional. -/
theorem Scheme.Hom.ringKrullDim_fiberRing_stalkMap_eq_zero [LocallyQuasiFinite f] (x : X) :
    ringKrullDim (f.stalkMap x).hom.fiberRing = 0 :=
  (f.quasiFiniteAt x).ringKrullDim_fiberRing_eq_zero

end AlgebraicGeometry
