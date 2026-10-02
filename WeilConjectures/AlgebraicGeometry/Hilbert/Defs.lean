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

We then state that `Hilb^d_{X/S}` is a sheaf for the fppf topology, that it is representable
under a hypothesis of "enough affine opens" on the fibres, and, over a field, that the Hilbert
functor of a smooth proper geometrically integral curve is represented by a smooth proper
geometrically integral `k`-scheme of dimension `d` carrying a universal effective Cartier
divisor, together with the addition morphisms between these Hilbert schemes.

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
- `AlgebraicGeometry.isSheaf_hilbertPresheaf`: `Hilb^d_{X/S}` is an fppf sheaf
  (blueprint `sk-cor-picard-hilb-sheaf`).
- `AlgebraicGeometry.isRepresentable_hilbertPresheaf`: representability of `Hilb^d_{X/S}`
  (blueprint `sk-thm-picard-hilb-general`).
- `AlgebraicGeometry.hilbertPresheaf_curve_representable`,
  `AlgebraicGeometry.hilbertPresheaf_curve_points`,
  `AlgebraicGeometry.hilbertPresheaf_curve_add`: the Hilbert schemes of a smooth proper curve
  (blueprint `sk-thm-picard-hilb-curves`).
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

/-- **Representability of `Hilb^d`, general case.** Assume that for every point `s` of `S` and
every finite set of at most `d` points of the fibre `X_s` there is an affine open of `X`
containing all of them; this holds for instance when `X ⟶ S` is quasi-projective, or when `X`
carries an ample invertible module. If moreover `X ⟶ S` is separated, then `Hilb^d_{X/S}` is
representable by a scheme.

Separatedness cannot be dropped: for the line with doubled origin over a field and `d = 1`,
every finite set of at most one point lies in an affine open, but `Hilb^1_{X/S}` is not
representable.

(blueprint: `sk-thm-picard-hilb-general`) -/
theorem isRepresentable_hilbertPresheaf (f : X ⟶ S) [IsSeparated f] (d : ℕ)
    (hf : ∀ (s : S) (t : Finset (f.fiber s)), t.card ≤ d →
      ∃ U : X.affineOpens, ∀ x ∈ t, (f.fiberι s).base x ∈ U.1) :
    (hilbertPresheaf f d).IsRepresentable :=
  sorry

section Curve

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The Hilbert scheme of a smooth projective curve.** For a geometrically integral smooth
proper curve `X` over `k` and `d : ℕ`, the functor `Hilb^d_{X/k}` is represented by a smooth
proper geometrically integral `k`-scheme `H` of dimension `d`, and `H ×[k] X` carries an
effective Cartier divisor `D` which is universal, in the sense that the point of `Hilb^d_{X/k}`
classified by a `k`-morphism `h : T ⟶ H` is the pullback of `D` along the induced morphism
`X_T ⟶ H ×[k] X`:

```
        X_T ──────────────▶ H ×[k] X ─────▶ X
         │  ⟨pr_T ≫ h, pr_X⟩    │            │
         │                      │            f
         ▼                      ▼            ▼
         T ─────── h ─────────▶ H ─── p ──▶ Spec k
```

The separatedness hypothesis of `isRepresentable_hilbertPresheaf` is part of
`IsProper f`.

(blueprint: `sk-thm-picard-hilb-curves`, parts (1) and (3)) -/
theorem hilbertPresheaf_curve_representable [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] (d : ℕ) :
    ∃ (H : Scheme.{u}) (p : H ⟶ Spec (.of k)), SmoothOfRelativeDimension d p ∧ IsProper p ∧
      GeometricallyIntegral p ∧ ∃ e : (hilbertPresheaf f d).RepresentableBy (Over.mk p),
        ∃ D : (Limits.pullback p f).IdealSheafData, IsEffectiveCartierCenter D.subschemeι ∧
          ∀ (T : Over (Spec (.of k))) (h : T.left ⟶ H) (hh : h ≫ p = T.hom),
            D.comap (Limits.pullback.lift (Limits.pullback.snd f T.hom ≫ h)
                (Limits.pullback.fst f T.hom)
                (by rw [Category.assoc, hh, Limits.pullback.condition])) =
              (e.homEquiv (Over.homMk h hh)).1 :=
  sorry

/-- **The points of the Hilbert scheme of a curve.** For a field extension `k'` of `k`, the
`k'`-points of `Hilb^d_{X/k}` are exactly the effective Cartier divisors of degree `d` on
`X_{k'}`. Since both sides are described by ideal sheaves on `X_{k'}`, the bijection is the
identity on underlying ideal sheaves, which is the naturality in `k'`.

`Scheme.Hom.finrank` is junk-valued away from the finite flat case, so the right-hand side
carries the finiteness and flatness of the projection explicitly.

The separatedness hypothesis of `isRepresentable_hilbertPresheaf` is part of
`IsProper f`.

(blueprint: `sk-thm-picard-hilb-curves`, part (2)) -/
theorem hilbertPresheaf_curve_points [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] (d : ℕ) (k' : Type u) [Field k'] [Algebra k k']
    (T : Over (Spec (.of k))) (hT : T = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (I : (Limits.pullback f T.hom).IdealSheafData) :
    (∃ Z : (hilbertPresheaf f d).obj (op T), Z.1 = I) ↔
      IsEffectiveCartierCenter I.subschemeι ∧
        IsFinite (I.subschemeι ≫ Limits.pullback.snd f T.hom) ∧
        Flat (I.subschemeι ≫ Limits.pullback.snd f T.hom) ∧
        ∀ t, (I.subschemeι ≫ Limits.pullback.snd f T.hom).finrank t = d :=
  sorry

/-- **The addition morphism of the Hilbert schemes of a curve.** If `H₁`, `H₂` and `H`
represent `Hilb^{d₁}_{X/k}`, `Hilb^{d₂}_{X/k}` and `Hilb^{d₁ + d₂}_{X/k}`, then there is a
`k`-morphism `H₁ ×[k] H₂ ⟶ H`, which on points is addition of effective Cartier divisors —
i.e. the product of the corresponding ideal sheaves — and which is finite, flat and locally of
finite presentation of degree `(d₁ + d₂).choose d₁`.

The last clause is what identifies `α`: without it any finite flat morphism of the right degree
would do, and the descent argument of the blueprint needs to know which morphism it is.

The separatedness hypothesis of `isRepresentable_hilbertPresheaf` is part of
`IsProper f`.

(blueprint: `sk-thm-picard-hilb-curves`, part (3)) -/
theorem hilbertPresheaf_curve_add [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] (d₁ d₂ : ℕ) (H₁ H₂ H : Over (Spec (.of k)))
    (e₁ : (hilbertPresheaf f d₁).RepresentableBy H₁)
    (e₂ : (hilbertPresheaf f d₂).RepresentableBy H₂)
    (e : (hilbertPresheaf f (d₁ + d₂)).RepresentableBy H) :
    ∃ α : Limits.pullback H₁.hom H₂.hom ⟶ H.left,
      α ≫ H.hom = Limits.pullback.fst H₁.hom H₂.hom ≫ H₁.hom ∧
        IsFinite α ∧ Flat α ∧ LocallyOfFinitePresentation α ∧
          (∀ t, α.finrank t = (d₁ + d₂).choose d₁) ∧
          ∀ (T : Over (Spec (.of k))) (t₁ : T ⟶ H₁) (t₂ : T ⟶ H₂) (t : T ⟶ H),
            t.left = Limits.pullback.lift t₁.left t₂.left
                (by rw [Over.w, Over.w]) ≫ α →
              (e.homEquiv t).1 = (e₁.homEquiv t₁).1 * (e₂.homEquiv t₂).1 :=
  sorry

end Curve

end AlgebraicGeometry
