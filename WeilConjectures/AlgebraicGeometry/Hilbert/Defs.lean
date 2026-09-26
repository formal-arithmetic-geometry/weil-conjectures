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

@[expose] public section

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

## Main definitions

- `AlgebraicGeometry.hilbertPresheaf`: the Hilbert functor `Hilb^d_{X/S}`
  (blueprint `sk-the-hilbert-functor--definition-1`).

## Main statements

- `AlgebraicGeometry.isSheaf_hilbertPresheaf`: `Hilb^d_{X/S}` is an fppf sheaf
  (blueprint `sk-cor-picard-hilb-sheaf`).
- `AlgebraicGeometry.isRepresentable_hilbertPresheaf`: representability of `Hilb^d_{X/S}`
  (blueprint `sk-thm-picard-hilb-general`).
- `AlgebraicGeometry.hilbertPresheaf_curve_representable`,
  `AlgebraicGeometry.hilbertPresheaf_curve_points`,
  `AlgebraicGeometry.hilbertPresheaf_curve_add`: the Hilbert schemes of a smooth proper curve
  (blueprint `sk-thm-picard-hilb-curves`).
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- Blueprint `sk-the-hilbert-functor--definition-1`: Hilbert functor.

For `f : X ⟶ S` and `d : ℕ`, `Hilb^d_{X/S}` sends an `S`-scheme `T` to the set of closed
subschemes `Z ⊆ X_T = X ×[S] T`, encoded as quasi-coherent ideal sheaves `I` on `X_T`, such
that the projection `Z ⟶ T` is finite, flat, locally of finite presentation and of degree `d`,
the last condition meaning that its rank function `Scheme.Hom.finrank` is constantly `d`.

An `S`-morphism `φ : T' ⟶ T` acts by pulling back the ideal sheaf along the base-change map
`X_{T'} ⟶ X_T`. -/
noncomputable def hilbertPresheaf (f : X ⟶ S) (d : ℕ) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := { I : (pullback f T.unop.hom).IdealSheafData //
    IsFinite (I.subschemeι ≫ pullback.snd f T.unop.hom) ∧
      Flat (I.subschemeι ≫ pullback.snd f T.unop.hom) ∧
      LocallyOfFinitePresentation (I.subschemeι ≫ pullback.snd f T.unop.hom) ∧
      ∀ t, (I.subschemeι ≫ pullback.snd f T.unop.hom).finrank t = d }
  map φ := TypeCat.ofHom fun I ↦ ⟨I.1.comap (baseChangeMap f φ.unop), sorry⟩
  map_id T := congrArg TypeCat.ofHom (funext fun I ↦ Subtype.ext (by
    simp [baseChangeMap_id, Scheme.IdealSheafData.comap_id]))
  map_comp φ ψ := congrArg TypeCat.ofHom (funext fun I ↦ Subtype.ext (by
    simp only [unop_comp, baseChangeMap_comp, Scheme.IdealSheafData.comap_comp]
    rfl))

/-- Blueprint `sk-cor-picard-hilb-sheaf`: Hilbert functor is the fppf sheaf.

`Hilb^d_{X/S}` is a sheaf for the fppf topology on `S`-schemes, hence in particular for the
coarser Zariski topology. -/
theorem isSheaf_hilbertPresheaf (f : X ⟶ S) (d : ℕ) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (hilbertPresheaf f d) :=
  sorry

/-- Blueprint `sk-thm-picard-hilb-general`: Representability of `Hilb^d` — general case.

Assume that for every point `s` of `S` and every finite set of at most `d` points of the fibre
`X_s` there is an affine open of `X` containing all of them; this holds for instance when
`X ⟶ S` is quasi-projective, or when `X` carries an ample invertible module. Then
`Hilb^d_{X/S}` is representable by a scheme. -/
theorem isRepresentable_hilbertPresheaf (f : X ⟶ S) (d : ℕ)
    (hf : ∀ (s : S) (t : Finset (f.fiber s)), t.card ≤ d →
      ∃ U : X.affineOpens, ∀ x ∈ t, (f.fiberι s).base x ∈ U.1) :
    (hilbertPresheaf f d).IsRepresentable :=
  sorry

section Curve

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Blueprint `sk-thm-picard-hilb-curves`: Hilbert schemes of smooth projective curves.

Part (1), together with the universal effective Cartier divisor of part (3): for a
geometrically integral smooth proper curve `X` over `k` and `d : ℕ`, the functor
`Hilb^d_{X/k}` is represented by a smooth proper geometrically integral `k`-scheme `H` of
dimension `d`, and `H ×[k] X` carries an effective Cartier divisor `D` which is universal, in
the sense that the point of `Hilb^d_{X/k}` classified by a `k`-morphism `h : T ⟶ H` is the
pullback of `D` along the induced morphism `X_T ⟶ H ×[k] X`. -/
theorem hilbertPresheaf_curve_representable [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] (d : ℕ) :
    ∃ (H : Scheme.{u}) (p : H ⟶ Spec (.of k)), SmoothOfRelativeDimension d p ∧ IsProper p ∧
      GeometricallyIntegral p ∧ ∃ e : (hilbertPresheaf f d).RepresentableBy (Over.mk p),
        ∃ D : (pullback p f).IdealSheafData, IsEffectiveCartierCenter D.subschemeι ∧
          ∀ (T : Over (Spec (.of k))) (h : T.left ⟶ H) (hh : h ≫ p = T.hom),
            D.comap (pullback.lift (pullback.snd f T.hom ≫ h) (pullback.fst f T.hom)
                (by rw [Category.assoc, hh, pullback.condition])) =
              (e.homEquiv (Over.homMk h hh)).1 :=
  sorry

/-- Blueprint `sk-thm-picard-hilb-curves`: Hilbert schemes of smooth projective curves.

Part (2): for a field extension `k'` of `k`, the `k'`-points of `Hilb^d_{X/k}` are exactly the
effective Cartier divisors of degree `d` on `X_{k'}`. Since both sides are described by ideal
sheaves on `X_{k'}`, the bijection is the identity on underlying ideal sheaves, which is the
naturality in `k'`. -/
theorem hilbertPresheaf_curve_points [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] (d : ℕ) (k' : Type u) [Field k'] [Algebra k k']
    (T : Over (Spec (.of k))) (hT : T = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (I : (pullback f T.hom).IdealSheafData) :
    (∃ Z : (hilbertPresheaf f d).obj (op T), Z.1 = I) ↔
      IsEffectiveCartierCenter I.subschemeι ∧
        ∀ t, (I.subschemeι ≫ pullback.snd f T.hom).finrank t = d :=
  sorry

/-- Blueprint `sk-thm-picard-hilb-curves`: Hilbert schemes of smooth projective curves.

Part (3), the addition morphism: if `H₁`, `H₂` and `H` represent `Hilb^{d₁}_{X/k}`,
`Hilb^{d₂}_{X/k}` and `Hilb^{d₁ + d₂}_{X/k}`, then there is a `k`-morphism
`H₁ ×[k] H₂ ⟶ H`, given on points by addition of effective Cartier divisors, which is finite,
flat and locally of finite presentation of degree `(d₁ + d₂).choose d₁`. -/
theorem hilbertPresheaf_curve_add [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] (d₁ d₂ : ℕ) (H₁ H₂ H : Over (Spec (.of k)))
    (e₁ : (hilbertPresheaf f d₁).RepresentableBy H₁)
    (e₂ : (hilbertPresheaf f d₂).RepresentableBy H₂)
    (e : (hilbertPresheaf f (d₁ + d₂)).RepresentableBy H) :
    ∃ α : pullback H₁.hom H₂.hom ⟶ H.left,
      α ≫ H.hom = pullback.fst H₁.hom H₂.hom ≫ H₁.hom ∧
        IsFinite α ∧ Flat α ∧ LocallyOfFinitePresentation α ∧
          ∀ t, α.finrank t = (d₁ + d₂).choose d₁ :=
  sorry

end Curve

end AlgebraicGeometry
