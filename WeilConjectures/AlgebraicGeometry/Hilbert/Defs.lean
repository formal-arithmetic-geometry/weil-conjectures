/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier

/-!
# The Hilbert functor

For a morphism of schemes `f : X ⟶ S` and `d : ℕ`, the Hilbert functor `Hilb^d_{X/S}` sends an
`S`-scheme `T` to the set of closed subschemes `Z ⊆ X_T = X ×[S] T` such that the projection
`Z ⟶ T` is finite, flat and locally of finite presentation of degree `d`. Closed subschemes of
`X_T` are encoded by quasi-coherent ideal sheaves, i.e. by
`AlgebraicGeometry.Scheme.IdealSheafData`, and the degree is the rank function
`AlgebraicGeometry.Scheme.Hom.finrank` of a finite flat morphism. Functoriality is base change
of ideal sheaves, `AlgebraicGeometry.Scheme.IdealSheafData.comap`, along the base-change maps
`AlgebraicGeometry.baseChangeMap` of the fibre products `X ×[S] T`.

We then state that `Hilb^d_{X/S}` is a sheaf for the fppf topology. Representability of
`Hilb^d_{X/S}` in general is proved in
`WeilConjectures.AlgebraicGeometry.Hilbert.Representability`, and the Hilbert schemes of curves
are in `WeilConjectures.AlgebraicGeometry.Hilbert.Curve`.

## Implementation notes

That the defining condition is stable under base change — `IsHilbertSubscheme.comap` — is the
one obligation in the construction of `hilbertPresheaf`. Finiteness, flatness and local finite
presentation are `MorphismProperty.IsStableUnderBaseChange` in Mathlib; the invariance of
`Scheme.Hom.finrank` is not, and is what the `sorry` on that lemma stands for.

## Main definitions

- `AlgebraicGeometry.IsHilbertSubscheme`: the condition cutting out the Hilbert functor.
- `AlgebraicGeometry.hilbertPresheaf`: the Hilbert functor `Hilb^d_{X/S}`
  (blueprint `sk-the-hilbert-functor--definition-1`).

## Main statements

- `AlgebraicGeometry.IsHilbertSubscheme.comap`: the defining condition is stable under base
  change.
- `AlgebraicGeometry.IsHilbertSubscheme.isInvertible`: for a smooth curve, the points of the
  Hilbert functor are relative effective Cartier divisors.
- `AlgebraicGeometry.IsHilbertSubscheme.eq_of_le`: two points of `Hilb^d_{X/S}(T)` one of
  which contains the other are equal.
- `AlgebraicGeometry.isSheaf_hilbertPresheaf`: `Hilb^d_{X/S}` is an fppf sheaf
  (blueprint `sk-cor-picard-hilb-sheaf`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The condition cutting out the Hilbert functor: the closed subscheme of `X_T = X ×[S] T`
described by the ideal sheaf `I` is finite, flat and locally of finite presentation of
degree `d` over `T`. -/
def IsHilbertSubscheme (f : X ⟶ S) (d : ℕ) (T : Over S)
    (I : (Limits.pullback f T.hom).IdealSheafData) : Prop :=
  IsFinite (I.subschemeι ≫ Limits.pullback.snd f T.hom) ∧
    Flat (I.subschemeι ≫ Limits.pullback.snd f T.hom) ∧
      LocallyOfFinitePresentation (I.subschemeι ≫ Limits.pullback.snd f T.hom) ∧
        ∀ t, (I.subschemeι ≫ Limits.pullback.snd f T.hom).finrank t = d

/-- The defining condition of the Hilbert functor is stable under base change along a morphism
`φ : T' ⟶ T` of `S`-schemes.

Finiteness, flatness and local finite presentation are stable under base change in Mathlib; the
remaining content is that `AlgebraicGeometry.Scheme.Hom.finrank` is unchanged, which is a
statement about `finrank` alone and should move next to it once proved. -/
theorem IsHilbertSubscheme.comap {f : X ⟶ S} {d : ℕ} {T T' : Over S} (φ : T' ⟶ T)
    {I : (Limits.pullback f T.hom).IdealSheafData} (hI : IsHilbertSubscheme f d T I) :
    IsHilbertSubscheme f d T' (I.comap (baseChangeMap f φ)) :=
  sorry

/-- **The points of the Hilbert functor of a smooth curve are divisors.** If `f : X ⟶ S` is
smooth of relative dimension `1`, then every point of `Hilb^d_{X/S}(T)` is a relative effective
Cartier divisor on `X_T/T`; in particular its ideal is invertible. This is
`AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat` for the base change
`X_T ⟶ T`, which is again smooth of relative dimension `1`. -/
theorem IsHilbertSubscheme.isInvertible {f : X ⟶ S} [SmoothOfRelativeDimension 1 f] {d : ℕ}
    {T : Over S} {I : (Limits.pullback f T.hom).IdealSheafData}
    (hI : IsHilbertSubscheme f d T I) : I.IsInvertible :=
  have : SmoothOfRelativeDimension 1 (Limits.pullback.snd f T.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f T.hom) ‹_›
  Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat _ hI.1 hI.2.1 hI.2.2.1

/-- **Nested points of the Hilbert functor are equal.** If `Z ⊆ Z'` are closed subschemes of
`X_T` which are both finite locally free of degree `d` over `T`, i.e. their ideals `I' ≤ I`
both lie in `Hilb^d_{X/S}(T)`, then `Z = Z'`: the surjection `𝒪_{Z'} ⟶ 𝒪_Z` of finite locally
free `𝒪_T`-modules of the same rank `d` is an isomorphism. -/
theorem IsHilbertSubscheme.eq_of_le {f : X ⟶ S} {d : ℕ} {T : Over S}
    {I J : (Limits.pullback f T.hom).IdealSheafData} (hI : IsHilbertSubscheme f d T I)
    (hJ : IsHilbertSubscheme f d T J) (h : I ≤ J) : I = J :=
  sorry

/-- The Hilbert functor. For `f : X ⟶ S` and `d : ℕ`, `Hilb^d_{X/S}` sends an `S`-scheme `T` to
the set of closed subschemes `Z ⊆ X_T = X ×[S] T`, encoded as quasi-coherent ideal sheaves `I`
on `X_T`, such that the projection `Z ⟶ T` is finite, flat, locally of finite presentation and
of degree `d`, the last condition meaning that its rank function `Scheme.Hom.finrank` is
constantly `d`.

An `S`-morphism `φ : T' ⟶ T` acts by pulling back the ideal sheaf along the base-change map
`X_{T'} ⟶ X_T`.

(blueprint: `sk-the-hilbert-functor--definition-1`) -/
noncomputable def hilbertPresheaf (f : X ⟶ S) (d : ℕ) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := { I : (Limits.pullback f T.unop.hom).IdealSheafData // IsHilbertSubscheme f d T.unop I }
  map φ := TypeCat.ofHom fun I ↦ ⟨I.1.comap (baseChangeMap f φ.unop),
    IsHilbertSubscheme.comap φ.unop I.2⟩
  map_id T := congrArg TypeCat.ofHom (funext fun I ↦ Subtype.ext (by
    simp [baseChangeMap_id, Scheme.IdealSheafData.comap_id]))
  map_comp φ ψ := congrArg TypeCat.ofHom (funext fun I ↦ Subtype.ext (by
    simp only [unop_comp, baseChangeMap_comp, Scheme.IdealSheafData.comap_comp]
    rfl))

/-- **The Hilbert functor is an fppf sheaf.** `Hilb^d_{X/S}` is a sheaf for the fppf topology on
`S`-schemes, hence in particular for the coarser Zariski topology.

(blueprint: `sk-cor-picard-hilb-sheaf`) -/
theorem isSheaf_hilbertPresheaf (f : X ⟶ S) (d : ℕ) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (hilbertPresheaf f d) :=
  sorry

end AlgebraicGeometry
