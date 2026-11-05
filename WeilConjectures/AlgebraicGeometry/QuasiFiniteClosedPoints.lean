/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!

# Preimages of closed points under quasi-finite morphisms

For a locally quasi-finite morphism of schemes `f : X ⟶ Y`, a point of `X` lying over a closed
point of `Y` is closed (`AlgebraicGeometry.Scheme.Hom.isClosed_singleton_of_isClosed_singleton`),
since the fibres of `f` are discrete. If `f` is moreover quasi-compact, the preimage of a finite
set of closed points is a finite set of closed points
(`AlgebraicGeometry.Scheme.Hom.exists_finset_preimage_of_isClosed_singleton`).

This is used in the finite-support step of Gabber's Künneth formula (blueprint
`sk-prop-tf-nearby-external-kunneth`): the support of the cone of the Künneth map is contained in
the preimage, under a quasi-finite coordinate map, of a finite set of closed points.

-/

@[expose] public section

namespace AlgebraicGeometry

variable {X Y : Scheme} (f : X ⟶ Y)

end AlgebraicGeometry
