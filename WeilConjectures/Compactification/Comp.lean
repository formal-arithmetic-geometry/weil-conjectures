/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BaseChange

/-!
# Compactification of a composite

Let `f : X ⟶ Y` and `g : Y ⟶ S`. Given a compactification `d = (Y ⟶[d.i] d.Z ⟶[d.g] S)` of `g`
and a compactification `e = (X ⟶[e.i] e.Z ⟶[e.g] d.Z)` of `f ≫ d.i`, the composite
`X ⟶[e.i] e.Z ⟶[e.g ≫ d.g] S` is a compactification of `f ≫ g`, since a composite of proper
morphisms is proper.

Moreover, `e` induces a compactification of `f` itself: since `d.i` is a monomorphism, the
square with sides `𝟙 X`, `f`, `f ≫ d.i` and `d.i` is cartesian, and base changing `e` along it
gives the compactification
```
X ⟶ V := e.Z ×_{d.Z} Y ⟶ Y
```
of `f`, whose open immersion composed with the projection `V ⟶ e.Z` is `e.i`. This is the
compactification of `f` used in the proof of the composition law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`,
which rests on the cartesian square
```
  V ---fst---> e.Z
  |             |
  snd          e.g
  ↓             ↓
  Y ---d.i---> d.Z
```

## Main definitions

- `AlgebraicGeometry.Compactification.comp`: the compactification `e.i, e.g ≫ d.g` of `f ≫ g`.
- `AlgebraicGeometry.Compactification.compRestrict`: the compactification of `f` with
  compactifying scheme `e.Z ×_{d.Z} Y`.

## Main results

- `AlgebraicGeometry.Compactification.isPullback_compRestrict`: the cartesian square above.

## Blueprint

This file implements the compactifications used in the proof of `sk-thm-sf-comp-composition`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Compactification

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}

/-- **The compactification of a composite**: if `d` compactifies `g : Y ⟶ S` and `e`
compactifies `f ≫ d.i`, then `X ⟶[e.i] e.Z ⟶[e.g ≫ d.g] S` compactifies `f ≫ g`.
(blueprint: `sk-thm-sf-comp-composition`) -/
@[simps]
noncomputable def comp (d : Compactification g) (e : Compactification (f ≫ d.i)) :
    Compactification (f ≫ g) where
  Z := e.Z
  g := e.g ≫ d.g
  i := e.i
  comm := by rw [← Category.assoc, ← e.comm, Category.assoc, ← d.comm]
  isProper := inferInstance
  isOpenImmersion := e.isOpenImmersion

/-- **The compactification of `f` induced by a compactification of `f ≫ d.i`**: the base
change of `e` along the cartesian square with sides `𝟙 X`, `f`, `f ≫ d.i` and `d.i`, with
compactifying scheme `e.Z ×_{d.Z} Y`.
(blueprint: `sk-thm-sf-comp-composition`) -/
noncomputable def compRestrict (d : Compactification g) (e : Compactification (f ≫ d.i)) :
    Compactification f :=
  e.ofIsPullback (IsPullback.of_horiz_isIso_mono ⟨by simp⟩ : IsPullback (𝟙 X) f (f ≫ d.i) d.i)

variable (d : Compactification g) (e : Compactification (f ≫ d.i))

@[simp] lemma compRestrict_Z : (compRestrict d e).Z = pullback e.g d.i := rfl

@[simp] lemma compRestrict_g : (compRestrict d e).g = pullback.snd e.g d.i := rfl

@[reassoc (attr := simp)] lemma compRestrict_i_comp_fst :
    (compRestrict d e).i ≫ pullback.fst e.g d.i = e.i :=
  (e.isPullback_i_ofIsPullback _).w.symm.trans (Category.id_comp _)

/-- The cartesian square comparing the compactification `compRestrict d e` of `f` with `d`:
```
  e.Z ×_{d.Z} Y ---fst---> e.Z
  |                         |
  snd                      e.g
  ↓                         ↓
  Y -----------d.i-------> d.Z
```
-/
theorem isPullback_compRestrict :
    IsPullback (pullback.snd e.g d.i) (pullback.fst e.g d.i) d.i e.g :=
  (IsPullback.of_hasPullback e.g d.i).flip

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
info: 'AlgebraicGeometry.Compactification.compRestrict' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Compactification.compRestrict

end AlgebraicGeometry
