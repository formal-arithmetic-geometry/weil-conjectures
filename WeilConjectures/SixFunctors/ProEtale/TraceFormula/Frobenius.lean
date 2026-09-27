/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence

/-!
# Weil complexes, relative Frobenius and topological invariance

A *Weil datum* on the geometric base change `X` of a separated finite type
`𝐅_q`-scheme `X₀` is a complex `K ∈ Dᵇctf(X, A)` together with an isomorphism
`φ : Φ₁^* K ≃ K`, where `Φ₁` is the geometric `q`-power Frobenius. Its iterates give the
graph correspondences `c_m = (id, Φ_m)` and the global Frobenius operators.

The `q^m`-power Frobenius of a scheme is not formalised anywhere in Mathlib or in this
project, so `AlgebraicGeometry.ProEtale.WeilComplex` carries it as data: an `s`-morphism
`Φ₁ : X ⟶ X`. The properties of it that the trace formula uses — being finite and a
universal homeomorphism — appear as hypotheses where they are needed.

## Main definitions

- `AlgebraicGeometry.ProEtale.WeilComplex` (blueprint `sk-d-weil`)
- `AlgebraicGeometry.ProEtale.relativeFrobenius` (blueprint `sk-d-relative-frob`)
- `AlgebraicGeometry.ProEtale.WeilComplex.lowerShriekPush` (blueprint `sk-d-weil-push`)

## Main results

- `AlgebraicGeometry.ProEtale.isFinite_relativeFrobenius_and_isUniversalHomeomorphism`
  (blueprint `sk-i-relative-frob`)
- `AlgebraicGeometry.ProEtale.isEquivalence_leftDerivedUpperStar_of_isFinite`
  (blueprint `sk-i-topology`)
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {s X Y : Scheme.{u}}

/-- Blueprint `sk-d-weil`: Frobenius and Weil data.

For `X₀/𝐅_q` separated of finite type and `X = X₀ ×_{𝐅_q} k`, the blueprint takes
`Φ₁ : X ⟶ X` to be the base change of the `q`-power scheme Frobenius of `X₀`; it fixes the
scalar field, so it is a morphism over `s`. A *Weil datum* is a complex
`K ∈ Dᵇctf(X, A)` with `φ : Φ₁^* K ≃ K`; for the coefficient continuation of the argument
one also allows a *Frobenius coefficient morphism*, an arbitrary map `Φ₁^* K ⟶ K` with no
invertibility requirement.

A `WeilComplex` is the latter, more general notion: the field `coeff` is a plain morphism,
and a Weil datum in the strict sense is a `WeilComplex` with `IsIso W.coeff`. The scheme
Frobenius does not exist in this project, so `frobenius` is carried as data. -/
structure WeilComplex (aX : X ⟶ s) where
  /-- the geometric `q`-power Frobenius `Φ₁ : X ⟶ X`. -/
  frobenius : X ⟶ X
  /-- `Φ₁` is a morphism over the base: it fixes the scalar field `k`. -/
  frobenius_comp : frobenius ≫ aX = aX
  /-- the coefficient complex `K`. -/
  obj : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)
  /-- the Frobenius coefficient morphism `φ : Φ₁^* K ⟶ K`. -/
  coeff : ((upperStar A frobenius).leftDerivedFunctor).obj obj ⟶ obj

namespace WeilComplex

variable {aX : X ⟶ s} (W : WeilComplex (A := A) aX)

/-- The `m`-th iterate `Φ_m = Φ₁^m : X ⟶ X` of the geometric Frobenius. -/
noncomputable def frobeniusIterate (m : ℕ) : X ⟶ X := (show End X from W.frobenius) ^ m

/-- The iterate `φ_m : Φ_m^* K ⟶ K` of the Frobenius coefficient morphism, obtained by
composing the pulled back copies of `φ` along the composition isomorphisms for `Φ^*`. -/
noncomputable def coeffIterate (m : ℕ) :
    ((upperStar A (W.frobeniusIterate m)).leftDerivedFunctor).obj W.obj ⟶ W.obj :=
  sorry

/-- The graph correspondence `c_m = (id_X, Φ_m)` of a Weil complex, with coefficient map
`φ_m`. Its ordinary-pullback leg is `Φ_m` and its exceptional leg is the identity. -/
noncomputable def graph (m : ℕ) : Correspondence aX aX W.obj W.obj where
  supp := X
  str := aX
  fst := 𝟙 X
  snd := W.frobeniusIterate m
  fst_comp := Category.id_comp aX
  snd_comp := sorry
  coeff := sorry

end WeilComplex

/-- Blueprint `sk-d-relative-frob`: The relative Frobenius factorization.

For `f : X ⟶ Y` and Frobenius morphisms `Φ_X : X ⟶ X`, `Φ_Y : Y ⟶ Y` with
`f ≫ Φ_Y = Φ_X ≫ f`, the blueprint forms `X'_m = Y ×_{Φ_{Y,m}, Y, f} X` with the two
projections `p_m : X'_m ⟶ X` and `f'_m : X'_m ⟶ Y`, and the *relative Frobenius*
`r_m = (f, Φ_{X,m}) : X ⟶ X'_m`. It satisfies `p_m ≫ r_m = Φ_{X,m}` and `r_m ≫ f'_m = f`.

Here `X'_m` is `CategoryTheory.Limits.pullback Φ_Y f`, with `f'_m = pullback.fst` and
`p_m = pullback.snd`. -/
noncomputable def relativeFrobenius (f : X ⟶ Y) (frobX : X ⟶ X) (frobY : Y ⟶ Y)
    (h : f ≫ frobY = frobX ≫ f) : X ⟶ pullback frobY f :=
  pullback.lift f frobX h

/-- Blueprint `sk-i-relative-frob`: Relative Frobenius.

The relative Frobenius `r_m` of the factorization is a finite universal homeomorphism.

The `q^m`-power Frobenius itself is not available, so the hypotheses record the two
properties of it that the argument uses: `Φ_X` and `Φ_Y` are finite universal
homeomorphisms. Since `relativeFrobenius f Φ_X Φ_Y h` composed with the projection
`p_m`, itself a base change of `Φ_Y`, is `Φ_X`, cancellation gives the conclusion. -/
theorem isFinite_relativeFrobenius_and_isUniversalHomeomorphism (f : X ⟶ Y) (frobX : X ⟶ X)
    (frobY : Y ⟶ Y) (h : f ≫ frobY = frobX ≫ f) [IsFinite frobX] [IsFinite frobY]
    [IsUniversalHomeomorphism frobX] [IsUniversalHomeomorphism frobY] :
    IsFinite (relativeFrobenius f frobX frobY h) ∧
      IsUniversalHomeomorphism (relativeFrobenius f frobX frobY h) :=
  sorry

/-- Blueprint `sk-i-topology`: Topological invariance.

For a finite universal homeomorphism `r : X ⟶ Y`, pullback is an equivalence
`r^* : Dᵇctf(Y, A) ≃ Dᵇctf(X, A)`, with inverse `Rr_* = Rr_!` and invertible unit and
counit. Reduction of a scheme is a finite universal homeomorphism, so the statement
includes it.

This is the derived, pro-étale form of the topological invariance of the small étale
topos, which this project already has at the sheaf level on the étale site as
`AlgebraicGeometry.Etale.isEquivalence_upperStar`. The stability of `Dᵇctf` is the second
clause, stated through the coefficient stage `G`. -/
theorem isEquivalence_leftDerivedUpperStar_of_isFinite (G : GeometricCoefficients A)
    (r : X ⟶ Y) [IsFinite r] [IsUniversalHomeomorphism r] :
    ((upperStar A r).leftDerivedFunctor).IsEquivalence ∧
      ∀ K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A),
        G.ctf Y K ↔ G.ctf X (((upperStar A r).leftDerivedFunctor).obj K) :=
  sorry

/-- Blueprint `sk-d-weil-push`: Weil `!`-pushforward.

For a Weil complex `(K, φ)` on `X` and `f : X ⟶ Y` compatible with the Frobenius
morphisms, Cartesian `!`-base change for `X'_m` together with topological invariance for
the relative Frobenius `r_m` gives the comparison

`θ_{f,m} : Φ_{Y,m}^* Rf_! K ≃ Rf'_{m!} p_m^* K ⟶ Rf'_{m!} Rr_{m!} r_m^* p_m^* K ≃
  Rf_! Φ_{X,m}^* K`,

whose middle unit is invertible. The pushed forward Weil complex on `Y` is `L = Rf_! K`
with `ψ = Rf_! φ ∘ θ_{f,1}`, and its iterates are `ψ_m = Rf_! φ_m ∘ θ_{f,m}`. The same
definition applies to an arbitrary Frobenius coefficient morphism.

The comparison `θ` is built from base change and topological invariance, which the package
only postulates, so the `coeff` field of the result carries a `sorry`. -/
noncomputable def WeilComplex.lowerShriekPush {aX : X ⟶ s} {aY : Y ⟶ s}
    (W : WeilComplex (A := A) aX) (f : X ⟶ Y) [HasCompactification f] (frobY : Y ⟶ Y)
    (hY : frobY ≫ aY = aY) (_h : f ≫ frobY = W.frobenius ≫ f) : WeilComplex (A := A) aY where
  frobenius := frobY
  frobenius_comp := hY
  obj := (rightDerivedLowerShriek A f).obj W.obj
  coeff := sorry

end AlgebraicGeometry.ProEtale
