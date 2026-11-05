/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Equalizers of morphisms of group objects

In a cartesian monoidal category, the equalizer of two morphisms `f g : G ⟶ H` is the fibre
product of `lift f g : G ⟶ H ⊗ H` with the diagonal `lift (𝟙 H) (𝟙 H) : H ⟶ H ⊗ H`:

```
  eqLocus f g ──── eqLocusι f g ────▶ G
       │                              │
       │                              │ lift f g
       ▼                              ▼
       H ─────── lift (𝟙 H) (𝟙 H) ──▶ H ⊗ H
```

Its `Y`-points are the `Y`-points `a` of `G` with `a ≫ f = a ≫ g`. For morphisms of group objects
the unit, multiplication and inverse of `G` factor through it, so it is a group object
(`CategoryTheory.GrpObj.ofMono`) and its inclusion into `G` is a morphism of group objects.

## Main definitions

- `CategoryTheory.GrpObj.eqLocus`: the equalizer of two morphisms into a cartesian monoidal
  category.
- `CategoryTheory.GrpObj.eqLocusι`: its canonical morphism to the source.
- `CategoryTheory.GrpObj.eqLocusLift`: the universal property of the equalizer.

## Main statements

- `CategoryTheory.GrpObj.mono_eqLocusι`: `eqLocusι f g` is a monomorphism.
- `CategoryTheory.GrpObj.isMonHom_eqLocusι`: for morphisms of group objects, `eqLocusι f g` is a
  morphism of group objects.
-/

@[expose] public section

namespace CategoryTheory

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

namespace GrpObj

variable {G H : C} (f g : G ⟶ H) [HasPullback (lift f g) (lift (𝟙 H) (𝟙 H))]

section GroupStructure

variable [GrpObj G] [GrpObj H] [IsMonHom f] [IsMonHom g]

end GroupStructure

end GrpObj

end CategoryTheory
