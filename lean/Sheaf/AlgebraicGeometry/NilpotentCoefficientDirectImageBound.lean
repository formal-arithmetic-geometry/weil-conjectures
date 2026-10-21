/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives

/-!
# Nilpotent coefficient extensions preserve a higher direct-image bound

Source: Stacks Project, Derived Categories, Tag 015B, lemma-higher-derived-functors,
part (1); the nilpotent coefficient application is the agent-written annihilator-filtration
argument in the DAG, motivated by Bhatt--Scholze, Lemma 6.5.11.
(blueprint: lem-sf-nilpotent-coefficient-direct-image-bound)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- A common higher direct-image vanishing bound for quotient coefficients remains a bound
for the original coefficients when the coefficient ideal is nilpotent. The same integer
`N` is retained for every positive nilpotency exponent and every module sheaf.

Source: Stacks Project, Tag 015B, lemma-higher-derived-functors, part (1), applied to the
agent-written annihilator filtration, motivated by Bhatt--Scholze, Lemma 6.5.11.
(blueprint: lem-sf-nilpotent-coefficient-direct-image-bound)

Proof:
1. For an arbitrary module sheaf `M`, take the subsheaf `M_j` of sections annihilated
by `I ^ j`. Restrictions preserve the equations defining it, and gluing in `M` preserves
them by uniqueness, so this is an actual subsheaf of modules
(`def-weil-sheaf-of-modules-category`). Commutativity makes it an `R`-submodule.
The inclusions `I ^ (j + 1) ≤ I ^ j` give the increasing filtration
`0 = M_0 ≤ M_1 ≤ ... ≤ M_t = M`: `I ^ 0` contains `1` and `I ^ t = 0`.
2. Form the sheaf cokernels `Q_j = M_(j+1) / M_j` for `j < t`, giving short exact
sequences `0 → M_j → M_(j+1) → Q_j → 0`
(`def-weil-sheaf-of-modules-category`). If `a ∈ I` and `s ∈ M_(j+1)`, then
`r * (a * s) = (r * a) * s = 0` for every `r ∈ I ^ j`. Thus multiplication by `a`
factors through `M_j` and is zero on the cokernel. Consequently `Q_j` has its canonical
`R / I`-action, independent of the chosen lift of a scalar. The constant-sheaf construction
and sheafification universal property (`def-weil-pbc-constant-sheaf`,
`def-weil-pbc-sheafification`) extend the action from constant sections to the constant
ring sheaf. Restricting this action to `R` recovers the original cokernel action.
3. Fix `q ≥ 0` with `q > N`. The hypothesis annihilates the higher direct image of
each `Q_j` over `R / I`. Apply `lem-sbc-coefficient-higher-direct-image-zero` to
`Ideal.Quotient.mk I` and the given qcqs morphism. This gives the same vanishing after
restriction to `R`, without any flatness assumption or claim about preserving injectives.
4. Module sheaves are abelian (`def-weil-sheaf-of-modules-category`), have enough
injectives (`lem-weil-pbc-module-sheaves-enough-injectives`), and direct image is additive
and left exact (`lem-weil-pbc-module-direct-image-left-exact`). Hence
`lem-weil-pbc-derived-functor-long-exact` supplies, for each short exact sequence in step 2,
the exact segment `R^q f_* M_j → R^q f_* M_(j+1) → R^q f_* Q_j`, including `q = 0`.
If both outer objects vanish, exactness makes the middle one vanish.
5. Induct on `j` from zero to `t`. The base is the higher direct image of zero,
computed by the zero injective resolution (`def-weil-pbc-direct-image`). Step 3 and
the exact segment in step 4 give the successor. At `j = t` the result is the vanishing
for `M`. The degree never changes, so the bound stays `N`, also when `N < 0` and
`q = 0` occurs. No finiteness or flatness of `M` enters the argument. -/
theorem isZero_higherDirectImage_of_nilpotent_quotient_bound
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (R : Type (u + 1)) [CommRing R] (I : Ideal R) (t : ℕ)
    (ht : 1 ≤ t) (hI : I ^ t = ⊥) (N : ℤ)
    (hN : ∀ (Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (R ⧸ I)))
      (q : ℤ), 0 ≤ q → N < q → IsZero (higherDirectImage (R ⧸ I) f q Q)) :
    ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
      (q : ℤ), 0 ≤ q → N < q → IsZero (higherDirectImage R f q M) := by
  sorry

end AlgebraicGeometry.Etale
