/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.Defs

/-!

# Scheme-theoretically dense compactifications

An open immersion `j : U ⟶ X` is scheme-theoretically dense if the sheaf morphism
`𝒪_X ⟶ j_* 𝒪_U` is injective, i.e. if the kernel ideal sheaf of `j` is trivial. This is
Mathlib's `AlgebraicGeometry.IsSchemeTheoreticallyDominant` (blueprint label
`def:nagata-scheme-theoretically-dense-open`).

We define the corresponding predicate `Compactification.IsSchemeTheoreticallyDense` on
compactifications (`def:nagata-dense-compactification`) and characterize it by the
condition that the inclusion of the scheme-theoretic image of the open immersion into
the compactification is an isomorphism
(`lemma:nagata-dense-compactification-characterization`). Under the resulting
identification the factor map `c.i.toImage` is identified with `c.i` by the
factorization `Scheme.Hom.toImage_imageι`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Compactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- A compactification `X ⟶ Z ⟶ Y` of `f : X ⟶ Y` is scheme-theoretically dense if
`𝒪_Z ⟶ i_* 𝒪_X` is injective, i.e. if the open immersion `i : X ⟶ Z` into the
compactification is scheme-theoretically dominant.
(Blueprint: `def:nagata-dense-compactification`.) -/
def IsSchemeTheoreticallyDense (c : Compactification f) : Prop :=
  IsSchemeTheoreticallyDominant c.i

/-- A compactification is scheme-theoretically dense if and only if the inclusion of
the scheme-theoretic image of its open immersion is an isomorphism.
(Blueprint: `lemma:nagata-dense-compactification-characterization`.) -/
theorem isSchemeTheoreticallyDense_iff (c : Compactification f) :
    c.IsSchemeTheoreticallyDense ↔ IsIso c.i.imageι :=
  (isSchemeTheoreticallyDominant_iff c.i).trans
    (Scheme.isIso_subschemeι_iff_eq_bot c.i.ker).symm

end Compactification

end AlgebraicGeometry
