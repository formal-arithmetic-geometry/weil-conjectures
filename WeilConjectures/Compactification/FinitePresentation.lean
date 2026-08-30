/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!

# Nagata compactification for a morphism of finite presentation

This file proves **Nagata's compactification theorem for a separated, quasi-compact morphism of
finite presentation over a quasi-compact quasi-separated base**
(`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`): such a morphism
factors as an open immersion followed by a proper morphism.

The Noetherian hypothesis on the base of
`AlgebraicGeometry.nagataCompactification_of_isNoetherian` is removed by absolute Noetherian
approximation. Writing the qcqs base `S` as a cofiltered limit `S = lim Dᵢ` of Noetherian
stages with affine transition maps (Stacks Tag 01ZA,
`AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`), a separated, quasi-compact
morphism `f : X ⟶ S` of finite presentation descends to a morphism `p : Y ⟶ Dᵢ` with the same
three properties over one of the stages (Stacks Tag 01ZQ,
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`). The stage
`Dᵢ` is Noetherian, so `p` has a compactification; base changing it back along `S ⟶ Dᵢ`
(`AlgebraicGeometry.HasCompactification.of_isPullback`) compactifies `f`.

## Main results

- `AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`: a separated,
  quasi-compact morphism of finite presentation to a quasi-compact quasi-separated scheme
  admits a compactification.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Nagata compactification for a morphism of finite presentation**: a separated,
quasi-compact morphism `f : X ⟶ S` of finite presentation over a quasi-compact
quasi-separated scheme `S` factors as an open immersion followed by a proper morphism.

The base is written as a cofiltered limit of Noetherian stages by absolute Noetherian
approximation, `f` is descended to one of the stages, compactified there by
`AlgebraicGeometry.nagataCompactification_of_isNoetherian` and the compactification is base
changed back to `S`.
(blueprint: `lemma:nagata-final-basechanged-compactification`) -/
theorem nagataCompactification_of_locallyOfFinitePresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] : HasCompactification f := by
  obtain ⟨N⟩ := S.nonempty_noetherianApproximation
  obtain ⟨i, Y, p, hp₁, hp₂, hp₃, h, H⟩ :=
    Scheme.exists_isPullback_of_finitePresentation_of_isSeparated N.isLimit f
  have := hp₁; have := hp₂; have := hp₃
  have : HasCompactification p := nagataCompactification_of_isNoetherian p
  exact HasCompactification.of_isPullback H

end AlgebraicGeometry
