/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek

/-!
# The compact-support candidate attached to a compactification

Blueprint `def-weil-compact-support-candidate`: for a separated finite-type morphism
`f : X ⟶ Y`, a compactification `c = (j, f̄)` of `f` (an object of the compactification category
`Comp(f)`, `AlgebraicGeometry.Compactification f`) and finite-torsion coefficients `A = A_{E,n}`,
the *compact-support candidate* is

`Rf^c_{!,n} = R f̄_{*,n} ∘ j_! : D(X_proét, A) ⥤ D(Y_proét, A)`,

with `j_!` the exact extension by zero and `R f̄_*` computed by K-injective resolutions. In the
project this functor is `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`
(notation `Rf_!(c)[A]`), defined for every Grothendieck abelian coefficient category; at the
finite-torsion stages `A = ModuleCat A_{E,n}`.

The full subcategory `D⁺_et(X, A)` of complexes coming from the étale site is
`AlgebraicGeometry.ProEtale.DerivedCategory.plusEtaleOrigin`; it contains the finite-torsion
constructible complexes (`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`,
blueprint `def-weil-finite-torsion-constructibility`), see
`AlgebraicGeometry.ProEtale.compactSupportCandidate_spec`.
-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A]

/-- Blueprint `def-weil-compact-support-candidate`: Compact-support candidate attached to a
compactification.

For a compactification `c = (j, f̄)` of `f : X ⟶ Y` (`c.i` the open immersion `j`, `c.g` the
proper morphism `f̄`), the compact-support candidate `Rf^c_! = R f̄_* ∘ j_!` is the functor
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification A c`: the functor `D(j_!)`
induced by the exact extension by zero, followed by the total right derived direct image
`R f̄_*`. Moreover the subcategory `D⁺_et(X, A)` of complexes of étale origin
(`AlgebraicGeometry.ProEtale.DerivedCategory.plusEtaleOrigin`) contains the bounded
constructible complexes. -/
theorem compactSupportCandidate_spec {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Rf_!(c)[A] = D((c.i)_!open[A]) ⋙ R((c.g)_*[A]) ∧
      DerivedCategory.boundedConstructible A X ≤ DerivedCategory.plusEtaleOrigin A X :=
  ⟨rfl, fun _ hK ↦ hK.plusEtaleOrigin⟩

end AlgebraicGeometry.ProEtale
