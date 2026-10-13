/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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

namespace AlgebraicGeometry

variable {X Y S T : Scheme.{u}} {u : X ⟶ S} {p : Y ⟶ T} {h : X ⟶ Y} {t : S ⟶ T}

namespace Compactification

/-- **The open immersion of a base-changed compactification is a base change of the
original open immersion.**

The square is obtained by cancelling the defining square of `c.Z ×_T S` off the bottom of
the given square `IsPullback h u p t`. -/
theorem isPullback_of_isPullback (hsq : IsPullback h u p t) (c : Compactification p)
    {i : X ⟶ pullback c.g t} (hfst : i ≫ pullback.fst c.g t = h ≫ c.i)
    (hsnd : i ≫ pullback.snd c.g t = u) :
    IsPullback h i c.i (pullback.fst c.g t) :=
  .of_bot (by rw [hsnd, ← c.comm]; exact hsq) hfst.symm (.of_hasPullback c.g t)

/-- **Base change construction for a compactification** (blueprint:
`def:nagata-compactification-base-change`,
`lemma:nagata-compactification-base-change`). -/
@[simps]
noncomputable def ofIsPullback (hsq : IsPullback h u p t) (c : Compactification p) :
    Compactification u where
  Z := pullback c.g t
  g := pullback.snd c.g t
  i := pullback.lift (h ≫ c.i) u (by rw [Category.assoc, ← c.comm, hsq.w])
  comm := (pullback.lift_snd _ _ _).symm
  isProper := inferInstance
  isOpenImmersion :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_of_isPullback hsq c (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _))
      c.isOpenImmersion

/-- **The open immersion of a base-changed compactification is a base change of the
original open immersion**, for the compactification `c.ofIsPullback hsq`:

```
  X ----h----------------> Y
  |                        |
  (c.ofIsPullback hsq).i   c.i
  ↓                        ↓
  c.Z ×_T S --fst-------> c.Z
```
-/
theorem isPullback_i_ofIsPullback (hsq : IsPullback h u p t) (c : Compactification p) :
    IsPullback h (c.ofIsPullback hsq).i c.i (pullback.fst c.g t) :=
  isPullback_of_isPullback hsq c (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- The open immersion of `c.ofIsPullback hsq` followed by the projection to `c.Z` is
`h ≫ c.i`. -/
@[reassoc (attr := simp)]
lemma ofIsPullback_i_fst (hsq : IsPullback h u p t) (c : Compactification p) :
    (c.ofIsPullback hsq).i ≫ pullback.fst c.g t = h ≫ c.i :=
  pullback.lift_fst _ _ _

/-- **The proper morphism of a base-changed compactification is a base change of the original
proper morphism**, for the compactification `c.ofIsPullback hsq`:

```
  c.Z ×_T S --------fst-------> c.Z
  |                              |
  (c.ofIsPullback hsq).g        c.g
  ↓                              ↓
  S ------------t-------------> T
```
-/
theorem isPullback_g_ofIsPullback (hsq : IsPullback h u p t) (c : Compactification p) :
    IsPullback (c.ofIsPullback hsq).g (pullback.fst c.g t) t c.g :=
  (IsPullback.of_hasPullback c.g t).flip

/-- **Base change of a compactification** along a morphism `t : T ⟶ S` of bases: if `c` is a
compactification of `f : X ⟶ S`, then `c.Z ×_S T ⟶ T` together with `X ×_S T ⟶ c.Z ×_S T`
is a compactification of the base change `pullback.snd f t`.
(blueprint: `def:nagata-compactification-base-change`,
`lemma:nagata-compactification-base-change`) -/
noncomputable def baseChangePullback {f : X ⟶ S} (c : Compactification f) (t : T ⟶ S) :
    Compactification (pullback.snd f t) :=
  ofIsPullback (.of_hasPullback f t) c

@[simp] lemma baseChangePullback_Z {f : X ⟶ S} (c : Compactification f) (t : T ⟶ S) :
    (c.baseChangePullback t).Z = pullback c.g t := rfl

@[simp] lemma baseChangePullback_g {f : X ⟶ S} (c : Compactification f) (t : T ⟶ S) :
    (c.baseChangePullback t).g = pullback.snd c.g t := rfl

@[reassoc (attr := simp)] lemma baseChange_i_fst {f : X ⟶ S} (c : Compactification f)
    (t : T ⟶ S) :
    (c.baseChangePullback t).i ≫ pullback.fst c.g t = pullback.fst f t ≫ c.i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] lemma baseChange_i_snd {f : X ⟶ S} (c : Compactification f)
    (t : T ⟶ S) :
    (c.baseChangePullback t).i ≫ pullback.snd c.g t = pullback.snd f t :=
  pullback.lift_snd _ _ _

/-- **Flat base change preserves scheme-theoretic density of a compactification.**

If the open immersion `c.i` of a compactification of `p` is scheme-theoretically dominant
and quasi-compact, then so is the open immersion of the base changed compactification along
a flat morphism `t`.

Flatness is essential: along an arbitrary base change the pulled back open need not be
dense. -/
theorem isSchemeTheoreticallyDominant_i_ofIsPullback (hsq : IsPullback h u p t)
    (c : Compactification p) (hc : IsSchemeTheoreticallyDominant c.i) [QuasiCompact c.i]
    [Flat t] :
    IsSchemeTheoreticallyDominant (c.ofIsPullback hsq).i :=
  have := hc
  .of_isPullback (c.isPullback_i_ofIsPullback hsq)

/-- **Flat base change preserves scheme-theoretic density of a compactification**, stated for
the literal fibre product, i.e. for `Compactification.baseChangePullback`. -/
theorem isSchemeTheoreticallyDominant_i_baseChange {f : X ⟶ S} (c : Compactification f)
    (t : T ⟶ S) (hc : IsSchemeTheoreticallyDominant c.i) [QuasiCompact c.i] [Flat t] :
    IsSchemeTheoreticallyDominant (c.baseChangePullback t).i :=
  isSchemeTheoreticallyDominant_i_ofIsPullback _ c hc

/-- If the proper morphism of a compactification of `p` is locally of finite presentation,
then so is the proper morphism of the base changed compactification. No flatness is needed:
finite presentation is stable under arbitrary base change. -/
theorem locallyOfFinitePresentation_g_ofIsPullback (hsq : IsPullback h u p t)
    (c : Compactification p) [LocallyOfFinitePresentation c.g] :
    LocallyOfFinitePresentation (c.ofIsPullback hsq).g :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.snd c.g t))

end Compactification

/-- **Compactifiability is stable under base change**: if `p : Y ⟶ T` admits a
compactification and `IsPullback h u p t`, then the base change `u : X ⟶ S` of `p` along
`t` admits one too.
(blueprint: `lemma:nagata-compactification-base-change`) -/
theorem HasCompactification.of_isPullback (hsq : IsPullback h u p t) [HasCompactification p] :
    HasCompactification u :=
  (Compactification.ofIsPullback hsq (HasCompactification.compactification p)).hasCompactification

/-- The second projection of a fibre product is a base change of the first leg of the
cospan, so it inherits compactifiability. -/
instance HasCompactification.pullback_snd {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasCompactification f] : HasCompactification (pullback.snd f g) :=
  .of_isPullback (IsPullback.of_hasPullback f g)

/-- The first projection of a fibre product is a base change of the second leg of the
cospan, so it inherits compactifiability. -/
instance HasCompactification.pullback_fst {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasCompactification g] : HasCompactification (pullback.fst f g) :=
  .of_isPullback (IsPullback.of_hasPullback f g).flip

/-! ### Axiom census

The flat base change statement is unconditional; the check below is run by the build, so a
`sorry` reappearing anywhere beneath it breaks compilation rather than going unnoticed. -/

/--
info: 'AlgebraicGeometry.Compactification.isSchemeTheoreticallyDominant_i_ofIsPullback' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Compactification.isSchemeTheoreticallyDominant_i_ofIsPullback

end AlgebraicGeometry
