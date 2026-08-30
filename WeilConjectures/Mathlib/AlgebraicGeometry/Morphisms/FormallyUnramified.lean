/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The locus where two morphisms into an unramified scheme agree

Unramified morphisms are *rigid*: two morphisms `a b : T ⟶ W` into a scheme `W` that is
unramified over a base `Z` and that agree after composing with `p : W ⟶ Z` agree on an open
subscheme of `T`, and that open subscheme is universal among the schemes over `T` on which
they agree. In particular two such morphisms that agree at a single point agree on a whole
neighbourhood of that point.

The whole content is Mathlib's `AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal`:
the diagonal `Limits.pullback.diagonal p : W ⟶ W ×[Z] W` of a formally unramified morphism
locally of finite type is an open immersion, and `AlgebraicGeometry.FormallyUnramified.eqLocus`
is the preimage of its range under `Limits.pullback.lift a b h : T ⟶ W ×[Z] W`.

## Main results

- `AlgebraicGeometry.FormallyUnramified.eqLocus` — the open subscheme of `T` on which `a`
  and `b` agree;
- `AlgebraicGeometry.FormallyUnramified.eqLocus_ι_comp_eq` — the two morphisms do agree on it;
- `AlgebraicGeometry.FormallyUnramified.liftEqLocus` — every morphism `c : S ⟶ T` with
  `c ≫ a = c ≫ b` factors through it, uniquely since `Scheme.Opens.ι` is a monomorphism;
- `AlgebraicGeometry.FormallyUnramified.exists_opens_isEqualizer` — the two previous statements
  packaged as an existence statement, and
  `AlgebraicGeometry.FormallyUnramified.exists_opens_lift` its pointed form: given a single
  `s : S ⟶ T` with `s ≫ a = s ≫ b` there is an open `U ⊆ T` on which `a` and `b` agree and
  through which `s` factors. This is the form in which a geometric point `S = Spec Ω` of `T`
  is moved into a neighbourhood on which two parallel maps are equalised;
- `AlgebraicGeometry.Etale.exists_opens_isEqualizer` and
  `AlgebraicGeometry.Etale.exists_opens_lift` — the same two statements for an étale `p`,
  which is both formally unramified and locally of finite type.

## Implementation notes

`eqLocus` is stated as a `Scheme.Opens` of `T` rather than as an abstract
`IsOpenImmersion e` with the two properties, or as a `Limits.HasEqualizer a b` together with
`IsOpenImmersion (Limits.equalizer.ι a b)`. The three carry the same information: an open
immersion into `T` with open image is the same thing as an open of `T` up to a unique
isomorphism over `T`, and `eqLocus_ι_comp_eq` together with `liftEqLocus` and the fact that
`Scheme.Opens.ι` is a monomorphism exhibit `(eqLocus p a b h).ι` as an equaliser of `a` and
`b`. The `Scheme.Opens` form is chosen because the intended use — cofilteredness of the
category of pointed étale neighbourhoods of a geometric point — needs to intersect the
resulting open with other opens of `T`.

The two étale corollaries live in this file rather than in a mirror of
`Mathlib.AlgebraicGeometry.Morphisms.Etale`, which `#find_home` would suggest, only to keep
them beside the unramified statements they are one-liners from.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace FormallyUnramified

variable {T W Z : Scheme.{u}} (p : W ⟶ Z) [FormallyUnramified p] [LocallyOfFiniteType p]
  (a b : T ⟶ W) (h : a ≫ p = b ≫ p)

/-- The open subscheme of `T` on which two morphisms `a b : T ⟶ W` agree, for `p : W ⟶ Z`
formally unramified and locally of finite type and `a ≫ p = b ≫ p`.

It is the preimage under `Limits.pullback.lift a b h : T ⟶ W ×[Z] W` of the range of the
diagonal `Limits.pullback.diagonal p`, which is open since `p` is unramified. -/
noncomputable def eqLocus : T.Opens :=
  pullback.lift a b h ⁻¹ᵁ (pullback.diagonal p).opensRange

omit [FormallyUnramified p] [LocallyOfFiniteType p] in
/-- A morphism `c : S ⟶ T` equalising `a` and `b` sends `Limits.pullback.lift a b h` into the
diagonal. -/
theorem comp_lift_eq_comp_diagonal {S : Scheme.{u}} (c : S ⟶ T) (hc : c ≫ a = c ≫ b) :
    c ≫ pullback.lift a b h = (c ≫ a) ≫ pullback.diagonal p := by
  refine pullback.hom_ext ?_ ?_ <;> simp [hc]

theorem range_subset_eqLocus {S : Scheme.{u}} (c : S ⟶ T) (hc : c ≫ a = c ≫ b) :
    Set.range c.base ⊆ (eqLocus p a b h : Set T) := by
  rw [Set.range_subset_iff]
  intro s
  exact ⟨(c ≫ a).base s, by
    simp only [← Scheme.Hom.comp_apply, comp_lift_eq_comp_diagonal p a b h c hc]⟩

/-- `a` and `b` agree on `eqLocus p a b h`. -/
@[reassoc]
theorem eqLocus_ι_comp_eq : (eqLocus p a b h).ι ≫ a = (eqLocus p a b h).ι ≫ b := by
  have hrange : Set.range ((eqLocus p a b h).ι ≫ pullback.lift a b h).base ⊆
      Set.range (pullback.diagonal p).base := by
    rintro _ ⟨x, rfl⟩
    exact x.2
  have hfac := IsOpenImmersion.lift_fac (pullback.diagonal p)
    ((eqLocus p a b h).ι ≫ pullback.lift a b h) hrange
  have h₁ := congr($hfac ≫ pullback.fst p p)
  have h₂ := congr($hfac ≫ pullback.snd p p)
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
    pullback.lift_fst, pullback.lift_snd] at h₁ h₂
  rw [← h₁, ← h₂]

/-- The factorisation of a morphism `c : S ⟶ T` equalising `a` and `b` through the open
subscheme `eqLocus p a b h`. It is the unique such factorisation, `Scheme.Opens.ι` being a
monomorphism. -/
noncomputable def liftEqLocus {S : Scheme.{u}} (c : S ⟶ T) (hc : c ≫ a = c ≫ b) :
    S ⟶ (eqLocus p a b h : Scheme) :=
  IsOpenImmersion.lift (eqLocus p a b h).ι c <| by
    simpa using range_subset_eqLocus p a b h c hc

@[reassoc (attr := simp)]
theorem liftEqLocus_ι {S : Scheme.{u}} (c : S ⟶ T) (hc : c ≫ a = c ≫ b) :
    liftEqLocus p a b h c hc ≫ (eqLocus p a b h).ι = c :=
  IsOpenImmersion.lift_fac _ _ _

include p h in
/-- `(eqLocus p a b h).ι` is an equaliser of `a` and `b`: `a` and `b` agree on it, and every
morphism into `T` equalising `a` and `b` factors uniquely through it. -/
theorem exists_opens_isEqualizer :
    ∃ U : T.Opens, U.ι ≫ a = U.ι ≫ b ∧ ∀ (S : Scheme.{u}) (c : S ⟶ T), c ≫ a = c ≫ b →
      ∃! t : S ⟶ (U : Scheme), t ≫ U.ι = c :=
  ⟨eqLocus p a b h, eqLocus_ι_comp_eq p a b h, fun _ c hc ↦
    ⟨liftEqLocus p a b h c hc, liftEqLocus_ι p a b h c hc, fun _ ht ↦ by
      rw [← cancel_mono (eqLocus p a b h).ι, ht, liftEqLocus_ι]⟩⟩

include p h in
/-- The pointed form: a morphism `s : S ⟶ T` equalising `a` and `b` — in the application a
geometric point `S = Spec Ω` of `T` — factors through an open subscheme of `T` on which `a`
and `b` agree. -/
theorem exists_opens_lift {S : Scheme.{u}} (s : S ⟶ T) (hs : s ≫ a = s ≫ b) :
    ∃ (U : T.Opens) (t : S ⟶ (U : Scheme)), U.ι ≫ a = U.ι ≫ b ∧ t ≫ U.ι = s :=
  ⟨eqLocus p a b h, liftEqLocus p a b h s hs, eqLocus_ι_comp_eq p a b h,
    liftEqLocus_ι p a b h s hs⟩

end FormallyUnramified

namespace Etale

variable {T W Z : Scheme.{u}} (p : W ⟶ Z) [Etale p] (a b : T ⟶ W) (h : a ≫ p = b ≫ p)

include p h in
/-- Two morphisms into a scheme étale over `Z` that agree over `Z` agree on an open subscheme,
and that open subscheme is an equaliser of the two. -/
theorem exists_opens_isEqualizer :
    ∃ U : T.Opens, U.ι ≫ a = U.ι ≫ b ∧ ∀ (S : Scheme.{u}) (c : S ⟶ T), c ≫ a = c ≫ b →
      ∃! t : S ⟶ (U : Scheme), t ≫ U.ι = c :=
  FormallyUnramified.exists_opens_isEqualizer p a b h

include p h in
/-- Two morphisms into a scheme étale over `Z` that agree over `Z` and agree at a point — more
precisely, whose restrictions along some `s : S ⟶ T` agree — agree on an open neighbourhood of
that point, that is, on an open subscheme of `T` through which `s` factors. -/
theorem exists_opens_lift {S : Scheme.{u}} (s : S ⟶ T) (hs : s ≫ a = s ≫ b) :
    ∃ (U : T.Opens) (t : S ⟶ (U : Scheme)), U.ι ≫ a = U.ι ≫ b ∧ t ≫ U.ι = s :=
  FormallyUnramified.exists_opens_lift p a b h s hs

end Etale

end AlgebraicGeometry
