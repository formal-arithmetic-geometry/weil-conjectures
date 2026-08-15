/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!

# Scheme-theoretically dense compactifications

A compactification `X ⟶ Z ⟶ Y` of `f : X ⟶ Y` is scheme-theoretically dense if the
kernel ideal sheaf of its open immersion `i : X ⟶ Z` is trivial, i.e. if
`IsSchemeTheoreticallyDominant c.i` holds (blueprint:
`def:nagata-dense-compactification`). When `i` is quasi-compact — equivalently, by
`Compactification.quasiCompact_openImmersion_iff`, when `f` is — this says precisely
that the sheaf morphism `𝒪_Z ⟶ i_* 𝒪_X` is injective; in general `Scheme.Hom.ker` is
only the largest quasi-coherent ideal sheaf contained in that kernel.

We characterize this condition by the requirement that the inclusion of the
scheme-theoretic image of the open immersion into the compactification is an
isomorphism.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Compactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- A compactification is scheme-theoretically dense (i.e. its open immersion `c.i` is
scheme-theoretically dominant, blueprint: `def:nagata-dense-compactification`) if and
only if the inclusion of the scheme-theoretic image of its open immersion is an
isomorphism. This is the special case of
`AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_isIso_imageι` for `c.i`. -/
theorem isSchemeTheoreticallyDominant_iff_isIso_imageι (c : Compactification f) :
    IsSchemeTheoreticallyDominant c.i ↔ IsIso c.i.imageι :=
  _root_.AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_isIso_imageι c.i

end AlgebraicGeometry.Compactification
