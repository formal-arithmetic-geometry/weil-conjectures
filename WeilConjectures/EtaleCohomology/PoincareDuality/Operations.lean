/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek

/-!

# The dualizing complex and the two duals

The six operations on the small pro-étale site are already available: `Lg^*` and `Rg_*`
(`WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar`), `Rf_!` and `Rf^!`
(`…Derived.LowerShriek`, `…Derived.UpperShriek`), `- ⊗ᴸ -` and `RHom(-, -)`
(`…Derived.Tensor`, `…Derived.Hom`), together with `RΓ(X, -)` and `RΓ_c(X/Y, -)`. This file
adds the three objects the duality chapter builds out of them: the dualizing complex
`ω_{X,Λ} = Ra_X^! Λ`, the Verdier dual `𝔻_X K = RHom(K, ω_{X,Λ})` and the naive dual
`K^∨ = RHom(K, Λ_X)`, plus the ordinary cohomology functors `H^i(X, -)` completing the
compactly supported ones.

## Main definitions

- `AlgebraicGeometry.ProEtale.derivedDual`: the naive dual `K ↦ K^∨ = RHom(K, Λ_X)`.
- `AlgebraicGeometry.ProEtale.dualizingComplex`: `ω_{X,Λ} = Ra_X^! Λ`.
- `AlgebraicGeometry.ProEtale.verdierDual`: `𝔻_X K = RHom(K, ω_{X,Λ})`.
- `AlgebraicGeometry.ProEtale.cohomology`: `H^i(X, -)`.

## Implementation notes

The constant sheaf `Λ_X` is the monoidal unit `𝟙_ D(X_proét)` of the derived tensor product,
and the coefficient object `Λ` at the point is the monoidal unit `𝟙_ A` of the coefficient
category.

The *Tate twist* `K ↦ K(r)` belongs to the coefficient conventions of the six-functor
chapter (blueprint `sk-def-sf-setting`, `def:coefficient-twists`) and is not constructed
here; `AlgebraicGeometry.ProEtale.tateTwist` and
`AlgebraicGeometry.ProEtale.coefficientTateTwist` are placeholders for it, to be replaced by
the real construction once that chapter is formalised. The same goes for the bounded
constructible finite-Tor category `D^b_ctf(X, Λ)`, whose placeholder is
`AlgebraicGeometry.ProEtale.boundedConstructibleFiniteTor`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

section Twist

/-- The Tate twist `K ↦ K(r)` on `D(X_proét)`.

This is a placeholder for the twist fixed by the coefficient conventions of the six-functor
chapter (blueprint `sk-def-sf-setting`, `def:coefficient-twists`), which is not yet
formalised. -/
-- TODO(unify): sk-def-sf-setting
noncomputable def tateTwist (X : Scheme.{u}) (r : ℤ) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  sorry

/-- The Tate twist `M ↦ M(r)` on the coefficient category `A`; in particular the twisted
coefficient object `Λ(r) = (𝟙_ A)(r)`, the value line of the trace–cup pairing.

This is a placeholder for the twist fixed by the coefficient conventions of the six-functor
chapter (blueprint `sk-def-sf-setting`, `def:coefficient-twists`), which is not yet
formalised. -/
-- TODO(unify): sk-def-sf-setting
noncomputable def coefficientTateTwist (r : ℤ) : A ⥤ A :=
  sorry

/-- The twisted coefficient object `Λ(r)`, the value line of the trace–cup pairing. -/
noncomputable abbrev twistedCoefficients (r : ℤ) : A :=
  (coefficientTateTwist A r).obj (𝟙_ A)

/-- The bounded constructible finite-Tor category `D^b_ctf(X, Λ)` inside `D(X_proét)`, as an
object property.

This is a placeholder for the coefficient conventions of the six-functor chapter (blueprint
`sk-def-sf-setting`, `def:weil-finite-torsion-constructibility` and
`def:weil-finite-tor-amplitude`), which are not yet formalised. -/
-- TODO(unify): sk-def-sf-setting
noncomputable def boundedConstructibleFiniteTor (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  sorry

end Twist

variable (X : Scheme.{u})

/-- Blueprint `sk-def-ops`: The six operations, the dualizing complex, the duals.

The naive dual `K ↦ K^∨ = RHom_{Λ_X}(K, Λ_X)` on `D(X_proét)`, the internal hom into the
constant sheaf `Λ_X = 𝟙_ D(X_proét)`. -/
noncomputable def derivedDual :
    (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))ᵒᵖ ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  (RHom(X)[A]).flip.obj (𝟙_ _)

/-- Blueprint `sk-def-ops`: The six operations, the dualizing complex, the duals.

The ordinary cohomology `H^i(X, K) = H^i(RΓ(X, K))`, the companion of the compactly
supported `AlgebraicGeometry.ProEtale.compactlySupportedCohomology`. -/
noncomputable def cohomology (i : ℤ) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤ A :=
  rightDerivedGlobalSections A X ⋙ DerivedCategory.homologyFunctor A i

variable {X} {Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a]

/-- Blueprint `sk-def-ops`: The six operations, the dualizing complex, the duals.

The dualizing complex `ω_{X,Λ} = Ra_X^! Λ` of a scheme `X` with structure morphism
`a_X : X ⟶ Y`, the exceptional inverse image of the constant sheaf `Λ_Y = 𝟙_ D(Y_proét)`. -/
noncomputable def dualizingComplex : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  (R(a)^![A]).obj (𝟙_ _)

/-- Blueprint `sk-def-ops`: The six operations, the dualizing complex, the duals.

The Verdier dual `𝔻_X K = RHom_{Λ_X}(K, ω_{X,Λ})` on `D(X_proét)`. -/
noncomputable def verdierDual :
    (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))ᵒᵖ ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  (RHom(X)[A]).flip.obj (dualizingComplex A a)

end ProEtale

end AlgebraicGeometry
