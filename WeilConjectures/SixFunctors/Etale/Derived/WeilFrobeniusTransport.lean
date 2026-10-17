/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius

/-!
# Transport of Weil data and of Weil equivariance

Let `h : Y ⟶ Y` be an endomorphism of a scheme, in the `ℓ`-adic formalism the geometric
Frobenius `g_{Y,γ}` of `Y = Y₀ ×_{k₀} k`, and let `ψ : Lh^* M ⟶ M` be Weil data
(`WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius`). This file records two formal
properties of the equivariance squares `IsWeilMorphism h ψ_M ψ_N u`, i.e. of the commutative
squares
```
  Lh^* M ──Lh^* u──▶ Lh^* N
    │ψ_M               │ψ_N
    ▼                  ▼
    M ───────u───────▶ N
```

* **Scheme-Frobenius forms.** If `κ : LΦ^* ⟶ Lh^*` is a natural transformation (in the
  blueprint the comparison isomorphism `κ_Y` between the derived pullbacks along the scheme
  Frobenius `Φ_Y` and along the geometric Frobenius `g_{Y,γ}`), then precomposing the vertical
  maps with `κ` turns every equivariance square for `h` into one for `Φ`, for the data
  `u_N = ψ_N ∘ κ_N` (`AlgebraicGeometry.Etale.IsWeilMorphism.precomp`). For an isomorphism `κ`
  the two kinds of squares are equivalent (`AlgebraicGeometry.Etale.isWeilMorphism_precomp_iff`).
* **Transport along an operation.** A functor `F : D(Y_ét, Λ) ⥤ D(Y'_ét, Λ')` together with an
  exchange `e : Lh'^* ∘ F ⟶ F ∘ Lh^*` carries Weil data to Weil data,
  `ψ ↦ e_M ≫ F(ψ)` (`AlgebraicGeometry.Etale.transportWeilDatum`), and equivariance squares to
  equivariance squares (`AlgebraicGeometry.Etale.IsWeilMorphism.transport`). The compactly
  supported direct image with its exchange `Ex_!` is the compact-support transport of Weil data
  (`AlgebraicGeometry.Etale.lowerShriekWeilDatum_eq_transportWeilDatum`); finite reduction,
  scalar extension and base change are other instances, and transport is compatible with
  composition of operations (`AlgebraicGeometry.Etale.transportWeilDatum_comp`).

## Main statements

- `AlgebraicGeometry.Etale.IsWeilMorphism.precomp`
  (`prop-pur-weil-equivariance-scheme-frobenius`).
- `AlgebraicGeometry.Etale.IsWeilMorphism.transport`,
  `AlgebraicGeometry.Etale.IsWeilMorphism.comp` (`prop-pur-weil-equivariance-compatibilities`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section SchemeFrobenius

variable {Λ : Type (u + 1)} [CommRing Λ] {Y : Scheme.{u}} {h Φ : Y ⟶ Y}
  {M N : DerivedCategoryModule Λ Y}
  {ψM : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M}
  {ψN : (L((h)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ N}

/-- Blueprint `prop-pur-weil-equivariance-scheme-frobenius`: Scheme-Frobenius forms of Weil
equivariance.

Let `κ : LΦ^* ⟶ Lh^*` be a natural transformation between derived pullbacks; in the blueprint
`h = g_{Y,γ}` is the geometric Frobenius, `Φ = Φ_Y` the scheme Frobenius and `κ = κ_Y` the
comparison isomorphism of `def-pur-scheme-geometric-frobenius`. Precomposing the vertical maps
of an equivariance square for `h`,
```
  Lh^* M ──Lh^* u──▶ Lh^* N
    │ψ_M               │ψ_N
    ▼                  ▼
    M ───────u───────▶ N
```
with `κ_M` and `κ_N` gives the same square for the scheme-Frobenius maps `u_M = ψ_M ∘ κ_M` and
`u_N = ψ_N ∘ κ_N`. Applied to the purity, counit and trace squares of
`thm-pur-weil-equivariance-of-purity-and-trace`, these are the three scheme-Frobenius squares
of the blueprint. The proof is the naturality of `κ`. -/
theorem IsWeilMorphism.precomp (κ : L((Φ)^*[ModuleCat.{u + 1} Λ]) ⟶ L((h)^*[ModuleCat.{u + 1} Λ]))
    {f : M ⟶ N} (hf : IsWeilMorphism h ψM ψN f) :
    IsWeilMorphism Φ (κ.app M ≫ ψM) (κ.app N ≫ ψN) f := by
  unfold IsWeilMorphism at *
  rw [← Category.assoc, κ.naturality f, Category.assoc, hf, Category.assoc]

/-- Blueprint `prop-pur-weil-equivariance-scheme-frobenius`: Scheme-Frobenius forms of Weil
equivariance.

For an isomorphism `κ : LΦ^* ≅ Lh^*` (the comparison `κ_Y` of
`def-pur-scheme-geometric-frobenius`), a square is equivariant for the geometric-Frobenius data
`ψ` if and only if it is equivariant for the scheme-Frobenius data `κ ≫ ψ`. -/
theorem isWeilMorphism_precomp_iff
    (κ : L((Φ)^*[ModuleCat.{u + 1} Λ]) ≅ L((h)^*[ModuleCat.{u + 1} Λ])) {f : M ⟶ N} :
    IsWeilMorphism Φ (κ.hom.app M ≫ ψM) (κ.hom.app N ≫ ψN) f ↔ IsWeilMorphism h ψM ψN f := by
  refine ⟨fun hf ↦ ?_, IsWeilMorphism.precomp κ.hom⟩
  have := hf.precomp κ.inv
  simpa only [Iso.inv_hom_id_app_assoc] using this

end SchemeFrobenius

section Transport

variable {Λ Λ' Λ'' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] [CommRing Λ'']
  {Y Y' Y'' : Scheme.{u}} {h : Y ⟶ Y} {h' : Y' ⟶ Y'} {h'' : Y'' ⟶ Y''}
  (F : DerivedCategoryModule Λ Y ⥤ DerivedCategoryModule Λ' Y')
  (e : F ⋙ L((h')^*[ModuleCat.{u + 1} Λ']) ⟶ L((h)^*[ModuleCat.{u + 1} Λ]) ⋙ F)

/-- The *transport* of a Weil datum `ψ : Lh^* M ⟶ M` along an operation
`F : D(Y_ét, Λ) ⥤ D(Y'_ét, Λ')` with an exchange `e : Lh'^* ∘ F ⟶ F ∘ Lh^*`:
```
                 e_M                     F ψ
  Lh'^* F M ──────────▶ F Lh^* M ──────────▶ F M
```
For `F = Ra_!` and `e = Ex_!` this is the compact-support transport
(`AlgebraicGeometry.Etale.lowerShriekWeilDatum`), for `F = Ra_*` and `e = Ex_*` the transport to
the direct image (`AlgebraicGeometry.Etale.lowerStarWeilDatum`). -/
noncomputable def transportWeilDatum {M : DerivedCategoryModule Λ Y}
    (ψ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M) :
    (L((h')^*[ModuleCat.{u + 1} Λ'])).obj (F.obj M) ⟶ F.obj M :=
  e.app M ≫ F.map ψ

variable {M N : DerivedCategoryModule Λ Y}
  {ψM : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M}
  {ψN : (L((h)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ N}

/-- Blueprint `prop-pur-weil-equivariance-compatibilities`: Compatibilities of Weil
equivariance.

An operation `F` with an exchange `e : Lh'^* ∘ F ⟶ F ∘ Lh^*` carries equivariance squares to
equivariance squares: if `u : M ⟶ N` is a morphism of Weil objects for `ψ_M` and `ψ_N`, then
`F u` is one for the transported data (`AlgebraicGeometry.Etale.transportWeilDatum`). The
operations of the blueprint are instances: finite reduction `- ⊗ᴸ A_m` and scalar extension
with their commutation with derived pullback, base change `Lf^*` with the pullback-composition
identifications, and the direct images with their exchange maps. Compatibility with composition
is `AlgebraicGeometry.Etale.IsWeilMorphism.comp` for composites of squares and
`AlgebraicGeometry.Etale.transportWeilDatum_comp` for composites of operations. The proof is the
naturality of `e`. -/
theorem IsWeilMorphism.transport {f : M ⟶ N} (hf : IsWeilMorphism h ψM ψN f) :
    IsWeilMorphism h' (transportWeilDatum F e ψM) (transportWeilDatum F e ψN) (F.map f) := by
  have := e.naturality f
  simp only [Functor.comp_map] at this
  unfold IsWeilMorphism transportWeilDatum at *
  rw [reassoc_of% this, ← F.map_comp, hf, F.map_comp, Category.assoc]

/-- Blueprint `prop-pur-weil-equivariance-compatibilities`: Compatibilities of Weil
equivariance (composition of operations).

Transporting a Weil datum along `F` and then along `G` is transporting it along `F ⋙ G`, with
the pasted exchange `Lh''^* G F ⟶ G Lh'^* F ⟶ G F Lh^*`. -/
lemma transportWeilDatum_comp (G : DerivedCategoryModule Λ' Y' ⥤ DerivedCategoryModule Λ'' Y'')
    (e' : G ⋙ L((h'')^*[ModuleCat.{u + 1} Λ'']) ⟶ L((h')^*[ModuleCat.{u + 1} Λ']) ⋙ G)
    (ψ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M) :
    transportWeilDatum G e' (transportWeilDatum F e ψ) =
      transportWeilDatum (F ⋙ G)
        (Functor.whiskerLeft F e' ≫ Functor.whiskerRight e G) ψ := by
  simp [transportWeilDatum]

end Transport

section Exchange

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} {a : X ⟶ Y}
  [HasCompactification a] {g : X ⟶ X} {h : Y ⟶ Y}

/-- The compact-support transport `AlgebraicGeometry.Etale.lowerShriekWeilDatum` of
`def-pur-compact-support-transport` is the transport of Weil data along `Ra_!` with the
exchange `Ex_!`. -/
lemma lowerShriekWeilDatum_eq_transportWeilDatum [QuasiCompact a] (sq : IsPullback g a a h)
    {K : DerivedCategoryModule Λ X} (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    lowerShriekWeilDatum sq φ =
      transportWeilDatum (R(a)_![ModuleCat.{u + 1} Λ]) (rightDerivedLowerShriekBaseChangeMap Λ sq)
        φ :=
  rfl

omit [Finite Λ] [HasCompactification a] in
/-- The transport `AlgebraicGeometry.Etale.lowerStarWeilDatum` to the direct image is the
transport of Weil data along `Ra_*` with the exchange `Ex_*`. -/
lemma lowerStarWeilDatum_eq_transportWeilDatum (sq : CommSq g a a h)
    {M : DerivedCategoryModule Λ X} (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M) :
    lowerStarWeilDatum sq ψ =
      transportWeilDatum (R((a)_*[ModuleCat.{u + 1} Λ])) (derivedBaseChangeMap _ sq) ψ :=
  rfl

end Exchange

end Etale

end AlgebraicGeometry
