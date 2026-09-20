/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-!
# The unit section of a monoid scheme over a base

Let `S` be a scheme and let `G` be a monoid object of the cartesian monoidal category `Over S`,
that is, a monoid scheme over `S`. The unit `η[G] : 𝟙_ (Over S) ⟶ G` is a morphism out of the
monoidal unit, which is `S` itself seen as an `S`-scheme, so on underlying schemes it is a
*section* `e := η[G].left` of the structure morphism of `G`:

```
              e
    S ───────────────▶ G.left
     ╲                ╱
       ╲            ╱  G.hom
  𝟙 S    ╲        ╱
           ▼     ▼
              S
```

Consequently the trivial `W`-point `1 : W ⟶ G` of `G` is, on underlying schemes, the constant
morphism at `e`, i.e. the structure morphism of `W` followed by `e`.

Mathlib has no file on monoid schemes over a base, so this file is not a mirror of any Mathlib
file and lives outside `WeilConjectures/Mathlib/`.

## Main results

- `AlgebraicGeometry.MonObj.one_left_comp_hom`: the unit of `G` is a section of `G.hom`.
- `AlgebraicGeometry.MonObj.one_left`: the trivial `W`-point of `G` is, on underlying schemes,
  the constant morphism at the unit.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

open scoped MonObj

namespace AlgebraicGeometry.MonObj

variable {S : Scheme.{u}} {W : Over S} (G : Over S) [MonObj G]

/-- **The unit of a monoid scheme over `S` is a section of the structure morphism**, i.e. an
`S`-rational point of `G`:

```
             η[G].left
    S ───────────────────▶ G.left
     ╲                    ╱
       ╲                ╱  G.hom
  𝟙 S    ╲            ╱
            ▼        ▼
                 S
```

This is `CategoryTheory.Over.w` applied to the unit; it is stated separately because it is the
side condition that every slice inclusion through the unit has to be handed. -/
@[reassoc]
theorem one_left_comp_hom : η[G].left ≫ G.hom = 𝟙 S :=
  Over.w η[G]

variable {G}

/-- **The trivial `W`-point of a monoid scheme `G` over `S` is the constant morphism at the
unit**: on underlying schemes it is the structure morphism of `W` followed by `η[G].left`.

```
                (1 : W ⟶ G).left
    W.left ──────────────────────▶ G.left
       ╲                          ↗
  W.hom  ╲                      ╱  η[G].left
           ▼                  ╱
              S ────────────╱
```

This is not a `simp` lemma: the `simp`-normal form of a Picard class pulled back along the
constant morphism at the unit is given by `AlgebraicGeometry.Scheme.Pic.map_one_left`. -/
theorem one_left : (1 : W ⟶ G).left = W.hom ≫ η[G].left :=
  rfl

end AlgebraicGeometry.MonObj
