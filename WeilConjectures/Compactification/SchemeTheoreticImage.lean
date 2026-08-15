/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.Defs

/-!

# Scheme-theoretically dense compactifications

A compactification `X ⟶ Z ⟶ Y` of `f : X ⟶ Y` is scheme-theoretically dense if the
sheaf morphism `𝒪_Z ⟶ i_* 𝒪_X` is injective, i.e. if the kernel ideal sheaf of the
open immersion `i : X ⟶ Z` is trivial. This is `IsSchemeTheoreticallyDominant c.i` in
terms of Mathlib's `AlgebraicGeometry.IsSchemeTheoreticallyDominant` (blueprint labels
`def:nagata-scheme-theoretically-dense-open` and `def:nagata-dense-compactification`).

We characterize this by the condition that the inclusion of the scheme-theoretic image
of the open immersion into the compactification is an isomorphism
(`lemma:nagata-dense-compactification-characterization`). Under the resulting
identification the factor map `c.i.toImage` is identified with `c.i` by the
factorization `Scheme.Hom.toImage_imageι`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Compactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- A compactification is scheme-theoretically dense (i.e. its open immersion `c.i` is
scheme-theoretically dominant, `def:nagata-dense-compactification`) if and only if the
inclusion of the scheme-theoretic image of its open immersion is an isomorphism.
(Blueprint: `lemma:nagata-dense-compactification-characterization`.) -/
theorem isSchemeTheoreticallyDominant_iff_isIso_imageι (c : Compactification f) :
    IsSchemeTheoreticallyDominant c.i ↔ IsIso c.i.imageι :=
  (isSchemeTheoreticallyDominant_iff c.i).trans
    (Scheme.isIso_subschemeι_iff_eq_bot c.i.ker).symm

end AlgebraicGeometry.Compactification
