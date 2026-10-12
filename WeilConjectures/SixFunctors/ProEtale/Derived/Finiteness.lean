/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage
public import WeilConjectures.SixFunctors.ProEtale.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekComparison

/-!
# Finite-level bounded constructibility of compactly supported direct images, pro-étale

At a finite coefficient stage `Λ` (in the blueprint `A_{E,n} = 𝒪_E/ϖⁿ`) whose exponent is
invertible on the base field, the compactly supported direct image on the pro-étale site
preserves bounded constructibility (of étale origin), and shifts the cohomological interval
`[a, b]` of a complex to `[a, b + 2e]` when the geometric fibres have dimension at most `e`.
This is deduced from the étale finiteness theorems through the comparison
`Rf_!^{proét} ∘ ν^* ≅ ν^* ∘ Rf_!^{ét}`.

## Main statements

- `AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerShriek` and
  `AlgebraicGeometry.ProEtale.constructibleIn_rightDerivedLowerShriek`
  (`prop-finite-compact-support-constructibility`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]

/-- Blueprint `prop-finite-compact-support-constructibility`: Finite-level bounded
constructibility for proper support (bounded constructibility).

Let `f : X ⟶ Y` be a separated finite-type morphism (here: one admitting a compactification)
between finite-type schemes over a field `k`, and let `Λ` be a finite ring whose exponent is
invertible in `k` (in the blueprint `Λ = A_{E,n}`). Then the compactly supported direct image on
the pro-étale site restricts to `Dᵇc_proét(X, Λ) ⥤ Dᵇc_proét(Y, Λ)`. It is triangulated, being
the restriction of a triangulated functor to triangulated subcategories. -/
theorem boundedConstructible_rightDerivedLowerShriek [HasInvertibleExponent Λ (Spec (.of k))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (hf : f ≫ aY = aX)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K) :=
  sorry

/-- Blueprint `prop-finite-compact-support-constructibility`: Finite-level bounded
constructibility for proper support (amplitude).

In the situation of `AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerShriek`,
if every geometric fibre of `f` has dimension at most `e`, then the compactly supported direct
image sends `D_c^{[a, b]}(X, Λ)` into `D_c^{[a, b + 2e]}(Y, Λ)`; the bounds only depend on
`a`, `b` and `e`, not on the compactification, nor on the finite coefficient ring. -/
theorem constructibleIn_rightDerivedLowerShriek [HasInvertibleExponent Λ (Spec (.of k))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (hf : f ≫ aY = aX) (e : ℕ)
    (he : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (Limits.pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞)) (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) X a b K) :
    DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * e)
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K) :=
  sorry

end ProEtale

end AlgebraicGeometry
