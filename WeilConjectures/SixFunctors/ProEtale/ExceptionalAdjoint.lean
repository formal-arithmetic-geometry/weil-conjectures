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

Consider a separated finite-type `f : X ⟶ Y` with a compactification `X → X̄ → Y` whose proper
part is `p`. This file defines two hypotheses of different strength:

* the *ambient exceptional right adjoint datum*
  `AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint`: a uniform
  cohomological-dimension bound `FullCD(p, A; c)` for some `c`, together with a right adjoint
  of `Rf_!` on the unbounded derived categories of the small pro-étale sites
  (`AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint.isLeftAdjoint`);
* *exceptional-adjoint admissibility*
  `AlgebraicGeometry.ProEtale.IsExceptionalAdjointAdmissible`: the datum together with the
  preservation clauses, that a right adjoint `Rf^×` of `Rf_!` carries each constructible interval
  `D_c^[a, b](Y, A)` into `D_c^[a + c₁, b + c₂](X, A)` for constants `c₁, c₂` independent of
  `a, b`, and `Dctf(Y, A)` into `Dctf(X, A)`.

Both are *hypotheses*, and they **fail in general**. Let `E` be an
elliptic curve over `𝔽̄_p`, `r ≠ p` a prime and `A` the category of `𝔽_r`-modules. Evaluating at
the pro-étale geometric generic point `T = Spec k(E)^sep` and taking the right adjoint, one
builds a pro-étale sheaf `F` with `Hⁿ(E_proét, F) ≅ Hⁿ(⊕_ℕ ℤ, 𝔽_r) ≠ 0` for all `n ≥ 1`. So
`FullCD` fails for the structure morphism `p` of `E`. Moreover countable products and coproducts
of pro-étale sheaves are exact, so `⊕ F[n] ≅ ∏ F[n]`, while `Rp_*` sends this to the
non-surjective `⊕ Hⁿ(E, F) → ∏ Hⁿ(E, F)` in degree `0`: `Rp_! = Rp_*` does not preserve
coproducts and has no right adjoint on `D`. A separate `t`-structure argument rules out a right
adjoint on `D⁺` as well. The sheaf `F` is not of étale origin. The constructible `Rf^!` is used
instead, and the data survive only as optional hypotheses.

On the *étale-origin* class the bound is a theorem, with `c = 2 dim X̄`: it follows from the
finiteness of proper direct images in ordinary étale cohomology together with the pro-étale
comparison. This does not give the datum, which quantifies over all pro-étale sheaves.

## Implementation details

The data are `structure`s, not `class`es: they are meant to be named and passed explicitly.

The preservation clauses are stated for *every* right adjoint `G` of `Rf_!`: the ambient right
adjoint `Rf^×` is not defined in this repository, since it does not exist in general. It is not
`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`, which is the constructible `Rf^!`. Both
predicates are closed under isomorphism, so this is no stronger than stating them for one right
adjoint.

The constructible intervals and `Dctf` are those of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude`, whose bounded
constructibility is étale origin.

The purity chapter itself is stated on the small *étale* site, with
`AlgebraicGeometry.Etale.rightDerivedUpperShriek`, while the data here are about the pro-étale
`Rf^!`. The bridge between the two is the comparison of
`WeilConjectures.SixFunctors.ProEtale.Comparison`: the pro-étale constructible `Rf^!` is by
definition `ν_X^* ∘ f^× ∘ Rν_{Y,*}` (`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`).

## Main definitions

- `AlgebraicGeometry.ProEtale.HasUniformCohomologicalDimensionLE`: the uniform
  cohomological-dimension bound, stable under base change along the pro-étale site.
- `AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint`: the ambient exceptional right
  adjoint datum.
- `AlgebraicGeometry.ProEtale.IsExceptionalAdjointAdmissible`: exceptional-adjoint
  admissibility.

## Main statements

- `AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint.isLeftAdjoint`: under the datum,
  `Rf_!` is a left adjoint.
- `AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedLowerStar_comparisonUpperStar`, in
  `WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension`: the bound on the
  étale-origin class.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}}

/-- The uniform cohomological-dimension bound `FullCD(p, A; c)`: `p : X ⟶ Y` *has uniform
cohomological dimension at most `c` at `A`* if the higher direct images of `p`, and of all its base
changes along objects of `Y_proét`, vanish above `c` on every pro-étale sheaf of `A`-modules. -/
def HasUniformCohomologicalDimensionLE (p : X ⟶ Y) (c : ℕ) : Prop :=
  ∀ (V : Y.ProEt) ⦃X' : Scheme.{u}⦄ (g' : X' ⟶ X) (p' : X' ⟶ V.left),
    IsPullback g' p' p V.hom →
      ∀ (F : Sheaf (Scheme.ProEt.topology X') A) (r : ℤ), (c : ℤ) < r →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
          ((R((p')_*[A])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))

/-- The ambient exceptional right adjoint datum for a morphism `f : X ⟶ Y` with a chosen
compactification: a uniform cohomological-dimension bound `FullCD(p, A; c)` for the proper part `p`
of the compactification, for some `c`, and a right adjoint `Rf^×` of `Rf_!` on the unbounded
derived categories of the small pro-étale sites. Not satisfied in general. -/
structure HasAmbientExceptionalRightAdjoint (f : X ⟶ Y) [HasCompactification f] : Prop where
  /-- A uniform cohomological-dimension bound for the proper part of the compactification. -/
  exists_hasUniformCohomologicalDimensionLE :
    ∃ c : ℕ, HasUniformCohomologicalDimensionLE A (HasCompactification.compactification f).g c
  /-- The derived lower shriek `Rf_!` has a right adjoint `Rf^×`. -/
  isLeftAdjoint_rightDerivedLowerShriek : (R(f)_![A]).IsLeftAdjoint

/-- Under the ambient exceptional right adjoint datum, the derived lower shriek `Rf_!` is a left
adjoint on the unbounded derived categories of the small pro-étale sites. -/
theorem HasAmbientExceptionalRightAdjoint.isLeftAdjoint {f : X ⟶ Y} [HasCompactification f]
    (h : HasAmbientExceptionalRightAdjoint A f) : (R(f)_![A]).IsLeftAdjoint :=
  h.isLeftAdjoint_rightDerivedLowerShriek

section Admissibility

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The exceptional-adjoint admissibility of `f`, at a finite coefficient stage: the ambient
exceptional right adjoint datum, together with the preservation clauses for every right adjoint `G`
of `Rf_!`: `G` preserves bounded constructibility, carries each constructible interval
`D_c^[a, b](Y, A)` into `D_c^[a + c₁, b + c₂](X, A)` for constants `c₁, c₂` independent of `a, b`,
and carries `Dctf(Y, A)` into `Dctf(X, A)`. Not satisfied in general. -/
structure IsExceptionalAdjointAdmissible (f : X ⟶ Y) [HasCompactification f] : Prop
    extends HasAmbientExceptionalRightAdjoint A f where
  /-- A right adjoint of `Rf_!` preserves bounded constructibility. -/
  boundedConstructible_le_inverseImage :
    ∀ ⦃G : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
        _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)⦄, (R(f)_![A] ⊣ G) →
      DerivedCategory.boundedConstructible A Y ≤
        (DerivedCategory.boundedConstructible A X).inverseImage G
  /-- A right adjoint of `Rf_!` shifts the constructible intervals by constants independent of
  the interval. -/
  exists_homologyConcentratedIn_le_inverseImage :
    ∃ c₁ c₂ : ℤ, ∀ ⦃G : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
        _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)⦄, (R(f)_![A] ⊣ G) →
      ∀ a b : ℤ, DerivedCategory.boundedConstructible A Y ⊓
          _root_.DerivedCategory.homologyConcentratedIn a b ≤
        (_root_.DerivedCategory.homologyConcentratedIn (a + c₁) (b + c₂)).inverseImage G
  /-- A right adjoint of `Rf_!` preserves `Dctf`. -/
  constructibleFiniteTor_le_inverseImage :
    ∀ ⦃G : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
        _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)⦄, (R(f)_![A] ⊣ G) →
      DerivedCategory.constructibleFiniteTor A Y ≤
        (DerivedCategory.constructibleFiniteTor A X).inverseImage G

end Admissibility

end ProEtale

end AlgebraicGeometry
