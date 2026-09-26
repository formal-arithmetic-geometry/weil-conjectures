/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Operations
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar

/-!

# Weil complexes and their Frobenius normalization

A *strict Weil complex* on the geometric fibre `X = X₀ ×_{k₀} k` is a pair `(K, φ_K)` with `K`
an object of `D(X_proét)` and `φ_K : L g_γ^* K ≅ K` an isomorphism, where `g_γ` is the
geometric Frobenius of `X` over `k₀`
(`AlgebraicGeometry.PoincareDualitySetting.geometricFrobenius`). Such a datum induces a
Frobenius endomorphism `F` of every cohomology group of `K`, ordinary or compactly supported.

The naive dual `K^∨` carries the *contragredient* datum, and the Tate twist `K(r)` carries the
datum twisted by `τ_r`, on which the geometric Frobenius acts by `q^{-r}`; this normalization
is what turns the Poincaré pairing into a similitude of factor `q^d` in its untwisted form.

## Main definitions

- `AlgebraicGeometry.ProEtale.WeilComplex`: a strict Weil complex `(K, φ_K)`.
- `AlgebraicGeometry.ProEtale.WeilComplex.dual`: the contragredient datum on `K^∨`.
- `AlgebraicGeometry.ProEtale.WeilComplex.twist`: the twisted datum on `K(r)`.
- `AlgebraicGeometry.ProEtale.WeilComplex.cohomologyFrobenius` and
  `AlgebraicGeometry.ProEtale.WeilComplex.compactlySupportedCohomologyFrobenius`: the induced
  Frobenius endomorphisms of `H^i(X, K)` and of `H^i_c(X, K)`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

variable {X : Scheme.{u}} (g : X ⟶ X)

/-- Blueprint `sk-def-weil`: Weil structures and their Frobenius normalization.

A *strict Weil complex* along an endomorphism `g` of `X` — in the applications the geometric
Frobenius `g_γ` — is a pair `(K, φ_K)` consisting of an object `K` of `D(X_proét)` and an
isomorphism `φ_K : L g^* K ≅ K`. -/
structure WeilComplex where
  /-- The underlying complex. -/
  obj : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)
  /-- The Frobenius structure `φ_K : L g^* K ≅ K`. -/
  frobenius : (L((g)^*[A])).obj obj ≅ obj

namespace WeilComplex

/-- Blueprint `sk-def-weil`: Weil structures and their Frobenius normalization.

The constant sheaf `Λ_X = 𝟙_ D(X_proét)` with its canonical Weil structure, coming from the
fact that `L g^*` is monoidal, hence preserves the unit. -/
noncomputable def unit : WeilComplex A g where
  obj := 𝟙_ _
  frobenius := sorry

variable {A g}

/-- Blueprint `sk-def-weil`: Weil structures and their Frobenius normalization.

The *contragredient datum* on the naive dual `K^∨` of a strict Weil complex `K`. -/
noncomputable def dual (K : WeilComplex A g) : WeilComplex A g where
  obj := (derivedDual A X).obj (op K.obj)
  frobenius := sorry

/-- Blueprint `sk-def-weil`: Weil structures and their Frobenius normalization.

The Tate twist `K(r)` of a strict Weil complex, whose Frobenius datum is `φ_K ⊗ τ_r`; the
geometric Frobenius acts on the twisting line `Λ(r)` by `q^{-r}`, hence by `q^r` on
`Λ(-r)`. -/
noncomputable def twist (K : WeilComplex A g) (r : ℤ) : WeilComplex A g where
  obj := (tateTwist A X r).obj K.obj
  frobenius := sorry

/-- Blueprint `sk-def-weil`: Weil structures and their Frobenius normalization.

The geometric Frobenius endomorphism `F` of the ordinary cohomology `H^i(X, K)` induced by
the Weil structure of `K`. -/
noncomputable def cohomologyFrobenius (K : WeilComplex A g) (i : ℤ) :
    (cohomology A X i).obj K.obj ⟶ (cohomology A X i).obj K.obj :=
  sorry

/-- Blueprint `sk-def-weil`: Weil structures and their Frobenius normalization.

The `r`-th power `F^r` of the Frobenius endomorphism of `H^i(X, K)`: the geometric Frobenius
of the degree `r` extension of the base field inside `k`. -/
noncomputable def cohomologyFrobeniusPow (K : WeilComplex A g) (i : ℤ) (r : ℕ) :
    (cohomology A X i).obj K.obj ⟶ (cohomology A X i).obj K.obj :=
  (show End ((cohomology A X i).obj K.obj) from K.cohomologyFrobenius i) ^ r

/-- Blueprint `sk-def-weil`: Weil structures and their Frobenius normalization.

The geometric Frobenius endomorphism `F_c` of the compactly supported cohomology
`H^i_c(X, K)` induced by the Weil structure of `K`. The geometric Frobenius of `X` is not a
morphism over the base `Y = Spec k`, only over `Spec k₀`; the compatibility it does satisfy is
`g ≫ a = a ≫ b` for the Frobenius `b` of the base, and `RΓ(Y, Rb_* -) ≅ RΓ(Y, -)` is what
turns that into an endomorphism of `H^i_c(X, K)`. -/
noncomputable def compactlySupportedCohomologyFrobenius (K : WeilComplex A g)
    {Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a] (b : Y ⟶ Y)
    (hab : g ≫ a = a ≫ b) (i : ℤ) :
    (H_c(a)[A](i)).obj K.obj ⟶ (H_c(a)[A](i)).obj K.obj :=
  sorry

end WeilComplex

end ProEtale

end AlgebraicGeometry
