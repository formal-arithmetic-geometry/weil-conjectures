/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimensionAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint

/-!
# The ambient exceptional right adjoint datum and exceptional-adjoint admissibility

Blueprint `sk-def-sf-admissible` names two hypotheses of different strength for a separated
finite-type `f : X ⟶ Y` with a compactification `X → X̄ → Y` whose proper part is `p`:

* clause (1), the *ambient exceptional right adjoint datum*
  `AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint`: a uniform
  cohomological-dimension bound `FullCD(p, A; c)` for some `c`, together with a right adjoint
  of `Rf_!` on the unbounded derived categories of the small pro-étale sites
  (`AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint.isLeftAdjoint`);
* clauses (1)–(3), *exceptional-adjoint admissibility*
  `AlgebraicGeometry.ProEtale.IsExceptionalAdjointAdmissible`: clause (1) together with the
  preservation clauses, that a right adjoint `Rf^×` of `Rf_!` carries each constructible interval
  `D_c^[a, b](Y, A)` into `D_c^[a + c₁, b + c₂](X, A)` for constants `c₁, c₂` independent of
  `a, b` (2), and `Dctf(Y, A)` into `Dctf(X, A)` (3).

Both are *hypotheses*, and they **fail in general** (`sk-rem-sf-fullcd-scope`). Let `E` be an
elliptic curve over `𝔽̄_p`, `r ≠ p` a prime and `A` the category of `𝔽_r`-modules. Evaluating at
the pro-étale geometric generic point `T = Spec k(E)^sep` and taking the right adjoint, one
builds a pro-étale sheaf `F` with `Hⁿ(E_proét, F) ≅ Hⁿ(⊕_ℕ ℤ, 𝔽_r) ≠ 0` for all `n ≥ 1`. So
`FullCD` fails for the structure morphism `p` of `E`. Moreover countable products and coproducts
of pro-étale sheaves are exact, so `⊕ F[n] ≅ ∏ F[n]`, while `Rp_*` sends this to the
non-surjective `⊕ Hⁿ(E, F) → ∏ Hⁿ(E, F)` in degree `0`: `Rp_! = Rp_*` does not preserve
coproducts and has no right adjoint on `D`. A separate `t`-structure argument rules out a right
adjoint on `D⁺` as well. The sheaf `F` is not of étale origin. The blueprint's proof chain never
assumes these data: it uses the constructible `Rf^!` of `det-def-sf-operations`(vi) instead, and
the data survive only as optional hypotheses of `sk-lem-sf-mate`(a), of the second half of
`sk-thm-sf-package`(1), and of `sk-prop-sf-existence`(b).

On the *étale-origin* class the bound is a theorem, with `c = 2 dim X̄`: it follows from the
finiteness of proper direct images in ordinary étale cohomology together with the pro-étale
comparison. This does not give clause (1), which quantifies over all pro-étale sheaves.

## Implementation notes

The data are `structure`s, not `class`es: they are meant to be named and passed explicitly.

Clauses (2) and (3) are stated for *every* right adjoint `G` of `Rf_!`: the ambient right
adjoint `Rf^×` is not defined in this repository, since it does not exist in general. It is not
`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`, which is the constructible `Rf^!` of
`det-def-sf-operations` (vi). Both predicates are closed under isomorphism, so this is no
stronger than stating them for one right adjoint.

The blueprint's "compatibly with refinements" clause of `sk-def-sf-admissible` is not among
the fields: the repository has no refinement relation between compactifications to state it
against.

The constructible intervals and `Dctf` are those of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude`, whose bounded
constructibility is étale origin; these agree with the blueprint's only at the finite coefficient
stages.

The purity chapter itself is stated on the small *étale* site, with
`AlgebraicGeometry.Etale.rightDerivedUpperShriek`, while the data here are about the pro-étale
`Rf^!`. The bridge between the two is the comparison of
`WeilConjectures.SixFunctors.ProEtale.Comparison`: the pro-étale constructible `Rf^!` is by
definition `ν_X^* ∘ f^× ∘ Rν_{Y,*}` (`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`).

## Main definitions

- `AlgebraicGeometry.ProEtale.HasUniformCohomologicalDimensionLE`: the uniform
  cohomological-dimension bound, stable under base change along the pro-étale site.
- `AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint`: the ambient exceptional right
  adjoint datum, clause (1).
- `AlgebraicGeometry.ProEtale.IsExceptionalAdjointAdmissible`: exceptional-adjoint
  admissibility, clauses (1)–(3).

## Main statements

- `AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint.isLeftAdjoint`: under clause (1),
  `Rf_!` is a left adjoint.
- `AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedLowerStar_comparisonUpperStar`, in
  `WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension`: the bound on the
  étale-origin class (blueprint `sk-prop-sf-fullcd-etale-origin`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}}

section Admissibility

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

end Admissibility

end ProEtale

end AlgebraicGeometry
