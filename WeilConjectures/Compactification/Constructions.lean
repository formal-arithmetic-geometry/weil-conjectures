/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Compactification.Defs

/-!

# Compactifications constructed from immersions

If `g : X ⟶ Y` is a quasi-compact immersion and `p : Y ⟶ S` is proper, then closing up `X`
inside `Y` compactifies `g ≫ p`: the factorization
```
X ⟶ g.image ⟶ Y ⟶ S
```
through the scheme-theoretic image of `g` exhibits a compactification of `g ≫ p`, since
`X ⟶ g.image` is an open immersion (`g` being a quasi-compact immersion) and
`g.image ⟶ S` is the composite of a closed immersion with the proper morphism `p`.

## Main definitions

- `AlgebraicGeometry.Compactification.ofIsImmersion`: the compactification of `g ≫ p`
  described above.

## Main results

- `AlgebraicGeometry.HasCompactification.of_isImmersion`: a quasi-compact morphism that
  factors as an immersion into a scheme proper over the base admits a compactification.

## Blueprint

This file implements `def:nagata-immersion-compactification` and
`lemma:nagata-immersion-into-proper` of the Nagata compactification blueprint.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/-- **Compactification constructed from an immersion**: for a quasi-compact immersion
`g : X ⟶ Y` and a proper morphism `p : Y ⟶ S`, the factorization of `g ≫ p` through the
scheme-theoretic image of `g` is a compactification of `g ≫ p`.
(blueprint: `def:nagata-immersion-compactification`,
`lemma:nagata-immersion-into-proper`) -/
noncomputable def Compactification.ofIsImmersion (g : X ⟶ Y) (p : Y ⟶ S)
    [IsImmersion g] [QuasiCompact g] [IsProper p] : Compactification (g ≫ p) where
  Z := g.image
  g := g.imageι ≫ p
  i := g.toImage
  comm := (g.toImage_imageι_assoc p).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- A quasi-compact morphism that factors as an immersion into a scheme proper over the
base admits a compactification.
(blueprint: `lemma:nagata-immersion-into-proper`) -/
theorem HasCompactification.of_isImmersion {u : X ⟶ S} (g : X ⟶ Y) (p : Y ⟶ S)
    [IsImmersion g] [IsProper p] [QuasiCompact u] (fac : g ≫ p = u) :
    HasCompactification u := by
  subst fac
  have : QuasiCompact g := .of_comp g p
  exact (Compactification.ofIsImmersion g p).hasCompactification

end AlgebraicGeometry
