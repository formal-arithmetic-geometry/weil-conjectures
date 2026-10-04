/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BaseChange

/-!
# Compactification of a composite

Let `h : X ⟶ W`. A compactification `e = (X ⟶[e.i] e.Z ⟶[e.g] W)` of `h` and a proper morphism
`p : W ⟶ S` give the compactification `X ⟶[e.i] e.Z ⟶[e.g ≫ p] S` of `h ≫ p`, since a
composite of proper morphisms is proper. In particular, for `f : X ⟶ Y` and `g : Y ⟶ S`, a
compactification `d = (Y ⟶[d.i] d.Z ⟶[d.g] S)` of `g` and a compactification `e` of `f ≫ d.i`
give the compactification `X ⟶[e.i] e.Z ⟶[e.g ≫ d.g] S` of `f ≫ g`.

Conversely, a compactification `e` of `f ≫ m` for a monomorphism `m : Y ⟶ W` restricts to a
compactification of `f`: since `m` is a monomorphism, the square
`IsPullback (𝟙 X) f (f ≫ m) m` is cartesian, and base changing `e` along it gives the
compactification `X ⟶ e.Z ×_W Y ⟶ Y` of `f`. For `m = d.i` this is the compactification of `f`
used in the proof of the composition law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`, which rests on the
cartesian square
```
  e.Z ×_W Y ---fst---> e.Z
  |                     |
  snd                  e.g
  ↓                     ↓
  Y --------m--------> W
```

## Main definitions

- `AlgebraicGeometry.Compactification.compProper`: the compactification `(e.i, e.g ≫ p)` of
  `h ≫ p`, for `p` proper.
- `AlgebraicGeometry.Compactification.comp`: the compactification `(e.i, e.g ≫ d.g)` of
  `f ≫ g`.
- `AlgebraicGeometry.Compactification.restrict`: the compactification of `f` with compactifying
  scheme `e.Z ×_W Y`, for `e` a compactification of `f ≫ m` and `m` a monomorphism.

## Main results

- `AlgebraicGeometry.Compactification.isPullback_restrict`: the cartesian square above.

## Blueprint

The constructions of this file are ingredients of the proof of `sk-thm-sf-comp-composition`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Compactification

section CompProper

variable {X W S : Scheme.{u}} {h : X ⟶ W}

/-- **Postcomposing a compactification with a proper morphism**: if `e` compactifies
`h : X ⟶ W` and `p : W ⟶ S` is proper, then `X ⟶[e.i] e.Z ⟶[e.g ≫ p] S` compactifies `h ≫ p`.
```
  X --e.i--> e.Z
  |           |
  h          e.g
  ↓           ↓
  W ===h===  W
              |
              p
              ↓
              S
```
-/
@[simps]
noncomputable def compProper (e : Compactification h) (p : W ⟶ S) [IsProper p] :
    Compactification (h ≫ p) where
  Z := e.Z
  g := e.g ≫ p
  i := e.i
  comm := by rw [← Category.assoc, ← e.comm]
  isProper := inferInstance
  isOpenImmersion := e.isOpenImmersion

end CompProper

section Comp

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
  (d : Compactification g) (e : Compactification (f ≫ d.i))

include d e

/-- **The compactification of a composite**: if `d` compactifies `g : Y ⟶ S` and `e`
compactifies `f ≫ d.i`, then `X ⟶[e.i] e.Z ⟶[e.g ≫ d.g] S` compactifies `f ≫ g`. This is
`Compactification.compProper e d.g`, transported along `f ≫ g = (f ≫ d.i) ≫ d.g`.

Note that `d` must come first since the type of `e` depends on `d.i`.
```
  X --e.i--> e.Z
  |           |
  f          e.g
  ↓           ↓
  Y --d.i--> d.Z
  |           |
  g          d.g
  ↓           ↓
  S ========  S
```
-/
@[simps! Z g i]
noncomputable def comp : Compactification (f ≫ g) :=
  (e.compProper d.g).copy (by rw [Category.assoc, ← d.comm])

end Comp

section Restrict

variable {X Y W : Scheme.{u}} {f : X ⟶ Y} {m : Y ⟶ W} [Mono m] (e : Compactification (f ≫ m))

/-- **Restricting a compactification to a subobject**: for a monomorphism `m : Y ⟶ W` and a
compactification `e` of `f ≫ m`, the compactification of `f` with compactifying scheme
`e.Z ×_W Y`, obtained by base changing `e` along the cartesian square
```
  X ---𝟙 X---> X
  |            |
  f          f ≫ m
  ↓            ↓
  Y -----m---> W
```
-/
@[simps! Z g]
noncomputable def restrict : Compactification f :=
  e.ofIsPullback (IsPullback.of_horiz_isIso_mono ⟨by simp⟩ : IsPullback (𝟙 X) f (f ≫ m) m)

/-- The open immersion of `e.restrict` followed by the projection to `e.Z` is `e.i`:
```
  X --e.restrict.i--> e.Z ×_W Y
    \                    |
     e.i                fst
       \                 ↓
        ------------->  e.Z
```
-/
@[reassoc (attr := simp)] lemma restrict_i_comp_fst : e.restrict.i ≫ pullback.fst e.g m = e.i :=
  (pullback.lift_fst _ _ _).trans (Category.id_comp _)

/-- The cartesian square comparing the compactification `e.restrict` of `f` with `e`:
```
  e.Z ×_W Y ---fst---> e.Z
  |                     |
  e.restrict.g         e.g
  ↓                     ↓
  Y --------m--------> W
```
-/
theorem isPullback_restrict : IsPullback e.restrict.g (pullback.fst e.g m) m e.g :=
  (IsPullback.of_hasPullback e.g m).flip

end Restrict

end Compactification

/-! ### Axiom census

The constructions of this file are unconditional; the checks below are run by the build, so a
`sorry` reappearing beneath them breaks compilation rather than going unnoticed. -/

/--
info: 'AlgebraicGeometry.Compactification.comp' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Compactification.comp

/--
info: 'AlgebraicGeometry.Compactification.restrict' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Compactification.restrict

end AlgebraicGeometry
