/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks

/-!

# Transport of scheme-theoretic images through admissible blow-ups

This file records the transport of scheme-theoretic images through an admissible blow-up
(Stacks Project Tag 0F3Y; blueprint `thm:0F3Y`,
`lemma:nagata-scheme-image-strict-transform`,
`lemma:nagata-scheme-image-transport-strict-transform`; proof order item 31):

- `AlgebraicGeometry.Scheme.Hom.ker_lift_admissibleBlowup`: the scheme-theoretic image of
  a lift along a `U`-admissible blow-up is the strict transform of the scheme-theoretic
  image.

It is consumed by the graph extension of
`WeilConjectures.Compactification.GraphExtension`.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section ImageTransport

variable {S X Y V : Scheme.{u}} {x : X ⟶ S} {y : Y ⟶ S}

end ImageTransport

end AlgebraicGeometry
