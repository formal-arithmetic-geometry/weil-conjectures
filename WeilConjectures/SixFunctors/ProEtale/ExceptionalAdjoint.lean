/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek

/-!
# The ambient exceptional right adjoint datum and exceptional-adjoint admissibility

Blueprint `sk-def-sf-admissible` names two data of different strength for a separated
finite-type `f : X ⟶ Y` with a compactification `X → X̄ → Y` whose proper part is `p`:

* clause (1), the *ambient exceptional right adjoint datum*
  `AlgebraicGeometry.ProEtale.AmbientExceptionalAdjointData`: a uniform cohomological-dimension
  bound `FullCD(p, A; c)` for some `c`, and the existence of a right adjoint `Rf^×` of `Rf_!` on
  the unbounded derived categories of the small pro-étale sites;
* clauses (1)–(3), *exceptional-adjoint admissibility*
  `AlgebraicGeometry.ProEtale.ExceptionalAdjointAdmissibilityData`: clause (1) together with
  the preservation clauses, that `Rf^×` carries each constructible interval `D_c^[a, b](Y, A)`
  into `D_c^[a + c⁻, b + c⁺](X, A)` for constants independent of `a, b` (2), and `Dctf(Y, A)`
  into `Dctf(X, A)` (3).

Both are *hypotheses*, and they **fail in general**: for an elliptic curve `E` over `𝔽̄_p` and
`A` the category of `𝔽_r`-modules there is a pro-étale sheaf `F` with `Hⁿ(E_proét, F) ≠ 0` for
all `n ≥ 1`, so `Rp_*` does not preserve the coproduct `⊕ F[n]` and `Rp_*` has no right adjoint
on `D` or `D⁺` (`sk-rem-sf-fullcd-scope`). The blueprint's proof chain does not use these data:
it works with the constructible `Rf^!` of `sk-def-sf-operations`(vi) instead.

On the *étale-origin* class the bound is a theorem, with `c = 2 dim X̄`: it follows from the
finiteness of proper direct images in ordinary étale cohomology together with the pro-étale
comparison.

## Implementation notes

The data are `structure`s, not `class`es: they are meant to be named and passed explicitly.

The field `AmbientExceptionalAdjointData.isLeftAdjoint` duplicates the global instance
`AlgebraicGeometry.ProEtale.isLeftAdjoint_rightDerivedLowerShriek`; it is recorded so that the
datum still carries the existence of the right adjoint should that instance be removed.

The blueprint's "compatibly with refinements" clause of `sk-def-sf-admissible` is not among
the fields: the repository has no refinement relation between compactifications to state it
against.

The constructible intervals and `Dctf` are those of
`WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude`, whose bounded constructibility is
étale origin; these agree with the blueprint's only at the finite coefficient stages.

The purity chapter itself is stated on the small *étale* site, with
`AlgebraicGeometry.Etale.rightDerivedUpperShriek`, while the data here are about the pro-étale
`Rf^!`. The bridge between the two is the comparison of
`WeilConjectures.SixFunctors.ProEtale.Comparison`; that `ν^*` intertwines the two exceptional
inverse images is not stated anywhere yet, and is a TODO of the block.

## Main definitions

- `AlgebraicGeometry.ProEtale.HasUniformCohomologicalDimensionLE`: the uniform
  cohomological-dimension bound, stable under base change along the pro-étale site.
- `AlgebraicGeometry.ProEtale.AmbientExceptionalAdjointData`: the ambient exceptional right
  adjoint datum, clause (1).
- `AlgebraicGeometry.ProEtale.ExceptionalAdjointAdmissibilityData`: exceptional-adjoint
  admissibility, clauses (1)–(3).

## Main statements

- `AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedLowerStar_comparisonUpperStar`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}}

/-- Blueprint `sk-def-sf-admissible`: the bound `FullCD(p, A; c)`.

`p : X ⟶ Y` *has uniform cohomological dimension at most `c` at `A`* if the higher direct
images of `p`, and of all its base changes along objects of `Y_proét`, vanish above `c` on
*every* pro-étale sheaf of `A`-modules:

```
  X' --g'--> X
  |          |          R^r p'_* F = 0 for r > c, all F on X'_proét
  p'         p
  |          |
  v          v
  V.left --V.hom--> Y        V an object of Y_proét
```

This is the uniform bound that makes `Rp_*` preserve coproducts on the unbounded derived
category. The base changes are taken along the pro-étale site of `Y`, as in the blueprint, and
not along arbitrary morphisms of schemes: the latter is a strictly stronger hypothesis than
`sk-prop-sf-fullcd-etale-origin` can deliver.

*Not satisfied in general*, even for proper smooth `p`: for an elliptic curve `E` over `𝔽̄_p`
and `A` the category of `𝔽_r`-modules, there is a pro-étale sheaf `F` on `E` with
`Hⁿ(E_proét, F) ≠ 0` for all `n ≥ 1` (`sk-rem-sf-fullcd-scope`). -/
def HasUniformCohomologicalDimensionLE (p : X ⟶ Y) (c : ℕ) : Prop :=
  ∀ (V : Y.ProEt) ⦃X' : Scheme.{u}⦄ (g' : X' ⟶ X) (p' : X' ⟶ V.left),
    IsPullback g' p' p V.hom →
      ∀ (F : Sheaf (Scheme.ProEt.topology X') A) (r : ℤ), (c : ℤ) < r →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
          ((R((p')_*[A])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))

/-- Blueprint `sk-def-sf-admissible`, clause (1): the ambient exceptional right adjoint datum.

For a morphism `f : X ⟶ Y` with a chosen compactification: a uniform cohomological-dimension
bound `FullCD(p, A; c)` for the proper part `p` of the compactification, for some `c`, and the
existence of a right adjoint `Rf^×` of `Rf_!` on the unbounded derived categories of the small
pro-étale sites. It asserts only existence, nothing about the values of `Rf^×`.

This is a *hypothesis*, and it is *not satisfied in general*: for an elliptic curve over `𝔽̄_p`
and `A` the category of `𝔽_r`-modules, `Rp_*` does not preserve coproducts and has no right
adjoint on `D` or `D⁺` (`sk-rem-sf-fullcd-scope`). The blueprint's proof chain uses the
constructible `Rf^!` of `sk-def-sf-operations`(vi) instead. -/
structure AmbientExceptionalAdjointData (f : X ⟶ Y) [HasCompactification f] : Prop where
  /-- A uniform cohomological-dimension bound for the proper part of the compactification. -/
  exists_hasUniformCohomologicalDimensionLE :
    ∃ c : ℕ, HasUniformCohomologicalDimensionLE A (HasCompactification.compactification f).g c
  /-- `Rf_!` has a right adjoint on the unbounded derived categories. -/
  isLeftAdjoint : (R(f)_![A]).IsLeftAdjoint

section Admissibility

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- Blueprint `sk-def-sf-admissible`: exceptional-adjoint admissibility, clauses (1)–(3).

The ambient exceptional right adjoint datum (1), together with the preservation clauses: the
exceptional inverse image `Rf^!` carries each constructible interval `D_c^[a, b](Y, A)` into
`D_c^[a + c⁻, b + c⁺](X, A)` for constants `c⁻, c⁺` independent of `a, b` (2), and carries
`Dctf(Y, A)` into `Dctf(X, A)` (3).

This is a *hypothesis*, and it is *not satisfied in general*, since already clause (1) fails for
an elliptic curve over `𝔽̄_p` with `A` the category of `𝔽_r`-modules
(`sk-rem-sf-fullcd-scope`). The blueprint's proof chain uses the constructible `Rf^!` of
`sk-def-sf-operations`(vi) instead. -/
structure ExceptionalAdjointAdmissibilityData (f : X ⟶ Y) [HasCompactification f] : Prop
    extends AmbientExceptionalAdjointData A f where
  /-- `Rf^!` shifts the constructible intervals by constants independent of the interval. -/
  exists_rightDerivedUpperShriek_mem_constructibleInterval :
    ∃ c₁ c₂ : ℤ, ∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)),
      DerivedCategory.boundedConstructible A Y K →
        _root_.DerivedCategory.homologyConcentratedIn a b K →
          DerivedCategory.boundedConstructible A X ((R(f)^![A]).obj K) ∧
            _root_.DerivedCategory.homologyConcentratedIn (a + c₁) (b + c₂)
              ((R(f)^![A]).obj K)
  /-- `Rf^!` preserves `Dctf`. -/
  rightDerivedUpperShriek_mem_constructibleFiniteTor :
    ∀ K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A),
      DerivedCategory.constructibleFiniteTor A Y K →
        DerivedCategory.constructibleFiniteTor A X ((R(f)^![A]).obj K)

end Admissibility

/-- Blueprint `sk-prop-sf-fullcd-etale-origin`: `FullCD` on the étale-origin class

**The cohomological-dimension bound on the étale-origin class.** Let `k` be separably closed,
let `p : X' ⟶ Y` be a proper morphism of finite-type `k`-schemes with `dim X' ≤ d`, and let
`Λ` be a finite coefficient ring whose exponent is invertible on `X'` — so that every sheaf of
`Λ`-modules is torsion, which is the first line of the blueprint proof. Then for every étale
sheaf `F` of `Λ`-modules on any base change `X''` of `X'`,

`H^r(Rp'_{proét,*} ν_{X''}^* F) = 0` for `r > 2d`.

Quantifying over the base changes is what turns the statement into the bound
`HasUniformCohomologicalDimensionLE` on the essential image of `ν^*`, which is the point of
the subsection; without it the theorem would not imply admissibility.

The bound covers étale-origin sheaves only: for general pro-étale module sheaves it is false
(for an elliptic curve over `𝔽̄_p` and `A` the category of `𝔽_r`-modules;
`sk-rem-sf-fullcd-scope`), so the étale-origin class is the natural domain. -/
theorem isZero_homology_rightDerivedLowerStar_comparisonUpperStar (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k] {X' : Scheme.{u}}
    (p : X' ⟶ Y) [IsProper p] (aX' : X' ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX'] [LocallyOfFiniteType aY] (hp : p ≫ aY = aX')
    [HasInvertibleExponent Λ X'] (d : ℕ) (hd : topologicalKrullDim X' ≤ (d : WithBot ℕ∞))
    {X'' Y'' : Scheme.{u}} (g' : X'' ⟶ X') (p' : X'' ⟶ Y'') (g : Y'' ⟶ Y)
    (sq : IsPullback g' p' p g)
    (F : Sheaf X''.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (r : ℤ) (hr : (2 * d : ℤ) < r) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
      ((R((p')_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X'').obj F)))) :=
  sorry

end ProEtale

end AlgebraicGeometry
