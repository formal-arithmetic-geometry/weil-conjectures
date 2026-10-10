/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.Compactification.Defs

/-!

# Base change of compactifications

Fix a Cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : IsPullback g' f' f g`, and a compactification `X ⟶[i] Z ⟶[p] Y` of
`f`. Base-changing the compactification along `g` yields a compactification

`X' ⟶[i'] Z ×_Y Y' ⟶[snd] Y'`

of `f'`: the structure morphism `pullback.snd` is proper since properness is stable under
base change, and the induced morphism `i'` is an open immersion since it is the base
change of `i` along the projection `pullback.fst : Z ×_Y Y' ⟶ Z`.

This is the geometric input for the base-change morphism of the lower shriek: both
squares of the pasting

```
X' --g'--> X            Z ×_Y Y' --fst--> Z
|          |            |                 |
i'         i            snd               p
v          v            v                 v
Z ×_Y Y' --fst--> Z     Y' --g----------> Y
```

are Cartesian, which is recorded in `Compactification.baseChange_isPullback_i` and
`Compactification.baseChange_isPullback_g`.

## Main definitions

- `AlgebraicGeometry.Compactification.baseChange`: the base change of a compactification
  of `f` along a Cartesian square, a compactification of `f'`.
- `AlgebraicGeometry.Compactification.baseChange_isPullback_i`: the open-immersion
  square of the base-changed compactification is Cartesian.
- `AlgebraicGeometry.Compactification.baseChange_isPullback_g`: the proper square of the
  base-changed compactification is Cartesian.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Compactification

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
variable (c : Compactification f) (sq : IsPullback g' f' f g)

/-- The open immersion of a compactification of `f`, base-changed along a Cartesian
square: the morphism `X' ⟶ Z ×_Y Y'` induced by `g' ≫ i` and `f'`. It is the base
change of `i` along `pullback.fst : Z ×_Y Y' ⟶ Z`, see `baseChange_isPullback_i`. -/
noncomputable def baseChangeOpenImmersion : X' ⟶ pullback c.g g :=
  pullback.lift (g' ≫ c.i) f' (by rw [Category.assoc, ← c.comm]; exact sq.w)

/-- The open-immersion square of a base-changed compactification is Cartesian: `X'` is
the preimage of the open `X ⊆ Z` under `pullback.fst : Z ×_Y Y' ⟶ Z`. This follows from
the Cartesian squares for `f'` and for `pullback.snd` by cancellation of vertical
pasting. -/
theorem isPullback_baseChangeOpenImmersion :
    IsPullback g' (c.baseChangeOpenImmersion sq) c.i (pullback.fst c.g g) := by
  refine IsPullback.of_bot ?_ (by rw [baseChangeOpenImmersion, pullback.lift_fst])
    (IsPullback.of_hasPullback c.g g)
  rw [baseChangeOpenImmersion, pullback.lift_snd, ← c.comm]
  exact sq

/-- The base change of a compactification `X ⟶[i] Z ⟶[p] Y` of `f` along a Cartesian
square `sq : IsPullback g' f' f g`: the compactification

`X' ⟶[i'] Z ×_Y Y' ⟶[snd] Y'`

of `f'`, where `i'` is induced by `g' ≫ i` and `f'`. Properness of the structure
morphism and the open-immersion property of `i'` hold since both are stable under base
change. -/
noncomputable def baseChange : Compactification f' where
  Z := pullback c.g g
  g := pullback.snd c.g g
  i := c.baseChangeOpenImmersion sq
  comm := (pullback.lift_snd _ _ _).symm
  isProper := inferInstance
  isOpenImmersion :=
    MorphismProperty.of_isPullback (c.isPullback_baseChangeOpenImmersion sq)
      c.isOpenImmersion

@[simp] lemma baseChange_Z : (c.baseChange sq).Z = pullback c.g g := rfl

@[simp] lemma baseChange_g : (c.baseChange sq).g = pullback.snd c.g g := rfl

@[simp] lemma baseChange_i : (c.baseChange sq).i = c.baseChangeOpenImmersion sq := rfl

/-- The scheme of the base-changed compactification is noetherian as soon as the fiber product
`Z ×_Y Y'` is: the two are the same scheme. This lets noetherianity hypotheses be stated on
either form. -/
instance noetherianSpace_baseChange_Z [h : TopologicalSpace.NoetherianSpace ↥(pullback c.g g)] :
    TopologicalSpace.NoetherianSpace (c.baseChange sq).Z :=
  h

/-- The open-immersion square of the base-changed compactification is Cartesian, stated
for the fields of `Compactification.baseChange`. -/
theorem baseChange_isPullback_i :
    IsPullback g' (c.baseChange sq).i c.i (pullback.fst c.g g) :=
  c.isPullback_baseChangeOpenImmersion sq

/-- The proper square of the base-changed compactification is Cartesian, stated for the
fields of `Compactification.baseChange`. -/
theorem baseChange_isPullback_g :
    IsPullback (pullback.fst c.g g) (c.baseChange sq).g c.g g :=
  IsPullback.of_hasPullback c.g g

end Compactification

end AlgebraicGeometry
