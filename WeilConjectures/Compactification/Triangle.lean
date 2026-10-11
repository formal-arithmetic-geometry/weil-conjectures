/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.Comp
public import WeilConjectures.Compactification.Refinement

/-!
# Triangles of compactifications

For composable morphisms `f : X ⟶ Y` and `g : Y ⟶ S`, a *triangle of compactifications* consists
of compactifications `cf`, `cg`, `cfg` of `f`, `g`, `f ≫ g`, together with an open immersion
`q : cf.Z ⟶ cfg.Z` and a morphism `p : cfg.Z ⟶ cg.Z` such that `cf.i ≫ q = cfg.i`,
`p ≫ cg.g = cfg.g` and the square
```
cf.Z --cf.g--> Y
 |q            |cg.i
cfg.Z ---p---> cg.Z
```
is cartesian. This is the configuration on which the composition isomorphism
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` is built (blueprint `sk-thm-sf-comp-composition`): extension by zero
along `cg.i` commutes with the proper pushforward along `p`.

## Main definitions

- `AlgebraicGeometry.Compactification.Triangle`: a triangle of compactifications.
- `AlgebraicGeometry.Compactification.Triangle.ofRestrict`: the triangle attached to a
  compactification `d` of `g` and a compactification `e` of `f ≫ d.i`.
- `AlgebraicGeometry.Compactification.Triangle.Hom`: a morphism of triangles, i.e. compatible
  refinements of the three compactifications with cartesian squares.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}

variable (f g) in
/-- **A triangle of compactifications** of composable morphisms `f : X ⟶ Y`, `g : Y ⟶ S`:
compactifications `cf`, `cg`, `cfg` of `f`, `g`, `f ≫ g` and maps `q : cf.Z ⟶ cfg.Z` (an open
immersion) and `p : cfg.Z ⟶ cg.Z` with `cf.i ≫ q = cfg.i`, `p ≫ cg.g = cfg.g`, such that the
square `cf.g ≫ cg.i = q ≫ p` is cartesian. -/
structure Triangle where
  /-- The compactification of `f`. -/
  cf : Compactification f
  /-- The compactification of `g`. -/
  cg : Compactification g
  /-- The compactification of `f ≫ g`. -/
  cfg : Compactification (f ≫ g)
  /-- The open immersion `cf.Z ⟶ cfg.Z`. -/
  q : cf.Z ⟶ cfg.Z
  /-- The proper map `cfg.Z ⟶ cg.Z`. -/
  p : cfg.Z ⟶ cg.Z
  [isOpenImmersion_q : IsOpenImmersion q]
  i_q : cf.i ≫ q = cfg.i
  p_g : p ≫ cg.g = cfg.g
  isPullback : IsPullback cf.g q cg.i p

namespace Triangle

attribute [instance] isOpenImmersion_q

variable (T : Triangle f g)

instance isProper_p : IsProper T.p :=
  have : IsProper (T.p ≫ T.cg.g) := by rw [T.p_g]; infer_instance
  .of_comp T.p T.cg.g

/-- The triangle of compactifications attached to a compactification `d` of `g` and a
compactification `e` of `f ≫ d.i`: the compactifications `e.restrict` of `f`, `d` of `g` and
`d.comp e` of `f ≫ g`. -/
@[simps]
noncomputable def ofRestrict (d : Compactification g) (e : Compactification (f ≫ d.i)) :
    Triangle f g where
  cf := e.restrict
  cg := d
  cfg := d.comp e
  q := pullback.fst e.g d.i
  p := e.g
  i_q := e.restrict_i_fst
  p_g := rfl
  isPullback := e.isPullback_restrict

/-- **A morphism of triangles** `T' ⟶ T`: refinements of the three compactifications of `T` by
those of `T'`, compatible with `q` and `p`, whose squares over `X` and `Y` are cartesian. -/
structure Hom (T' T : Triangle f g) where
  /-- The refinement of the compactifications of `f`. -/
  rf : T'.cf.Refinement T.cf
  /-- The refinement of the compactifications of `g`. -/
  rg : T'.cg.Refinement T.cg
  /-- The refinement of the compactifications of `f ≫ g`. -/
  rfg : T'.cfg.Refinement T.cfg
  q_comm : rf.hom ≫ T.q = T'.q ≫ rfg.hom
  p_comm : T'.p ≫ rg.hom = rfg.hom ≫ T.p
  isPullback_rf : IsPullback T'.cf.i (𝟙 X) rf.hom T.cf.i
  isPullback_rg : IsPullback T'.cg.i (𝟙 Y) rg.hom T.cg.i

namespace Hom

variable {T' T : Triangle f g} (φ : T'.Hom T)

/-- The square `T'.cf.g ≫ T.cg.i = T'.q ≫ (T'.p ≫ φ.rg.hom)` is cartesian. -/
theorem isPullback_big : IsPullback T'.cf.g T'.q T.cg.i (T'.p ≫ φ.rg.hom) := by
  simpa using T'.isPullback.paste_horiz φ.isPullback_rg.flip

/-- The square `φ.rf.hom ≫ T.q = T'.q ≫ φ.rfg.hom` is cartesian. -/
theorem isPullback_q : IsPullback φ.rf.hom T'.q T.q φ.rfg.hom := by
  refine IsPullback.of_right (h₁₂ := T.cf.g) (h₂₂ := T.p) ?_ φ.q_comm T.isPullback
  rw [φ.rf.hom_g, ← φ.p_comm]
  exact φ.isPullback_big

/-- The square of the refinement of the compactifications of `f ≫ g` is cartesian. -/
theorem isPullback_rfg : IsPullback T'.cfg.i (𝟙 X) φ.rfg.hom T.cfg.i := by
  have := φ.isPullback_rf.flip.paste_vert φ.isPullback_q
  rw [T'.i_q, T.i_q] at this
  exact this.flip

end Hom

end Triangle

end AlgebraicGeometry.Compactification
