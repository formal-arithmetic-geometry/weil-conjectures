/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Complete.CompletedPullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange

/-!
# Completed compact-support base change on the pro-étale site

Let `Λ` be a commutative ring and `I` an ideal of `Λ`. On derived `I`-complete pro-étale
complexes the extension by zero along an open immersion has to be *completed*: the adic
extension by zero (Bhatt–Scholze) is
```
j_!^comp K = (j_! K)^∧ = R lim_n (j_! K ⊗ᴸ Λ/Iⁿ)
```
(`AlgebraicGeometry.ProEtale.completedOpenImmersionLowerShriek`). The plain `j_!` does not
preserve derived completeness, see the docstring of
`AlgebraicGeometry.ProEtale.completedPullbackOpenImmersionLowerShriekIso`.

This file proves the completed extension-by-zero base change (blueprint
`lem-cbc-completed-extension-zero-comparison`, corrected) and constructs the completed
compact-support exchange map (blueprint `def-cbc-completed-exchange-map`, corrected), both from
maps of towers of reductions and the homotopy limit machinery of
`WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Existence`.

## Main definitions

- `AlgebraicGeometry.ProEtale.completedOpenImmersionLowerShriek`: `j_!^comp K = (j_! K)^∧`.
- `AlgebraicGeometry.ProEtale.completedPullbackOpenImmersionLowerShriekIso`:
  `Lg^*_comp (j_! K) ≅ j'_!^comp (Lg_U^* K)`.
- `AlgebraicGeometry.ProEtale.completedRightDerivedLowerShriekBaseChangeMap`: the completed
  exchange map `Lg^*_comp Rf_! K ⟶ (Rf'_! Lg'^*_comp K)^∧`.

## Main statements

- `AlgebraicGeometry.ProEtale.isIso_completedRightDerivedLowerShriekBaseChangeMap`: the completed
  exchange map is an isomorphism when the exchange map `Ex_!` at `K` followed by `Rf'_!` of the
  completion map of `Lg'^* K` is.
- `AlgebraicGeometry.ProEtale.isIso_completedRightDerivedLowerShriekBaseChangeMap_of_finite`: for
  a finite coefficient ring and `K` of étale origin, it is an isomorphism as soon as the
  completion map of `Lg'^* K` is.

## Implementation notes

Homotopy limits in a triangulated category are only unique up to non-unique isomorphism, and
maps between them induced by maps of towers are only unique up to phantom maps. The derived
completions and the maps between them used here are choices
(`CategoryTheory.Pretriangulated.homotopyLimitMap`); they are made so that a levelwise
isomorphism of towers induces an isomorphism
(`CategoryTheory.Pretriangulated.isIso_homotopyLimitMap`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ)

section OpenImmersion

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

variable (j) in
/-- The completed extension by zero `j_!^comp K = (j_! K)^∧ = R lim_n (j_! K ⊗ᴸ Λ/Iⁿ)` along an
open immersion `j`, the extension by zero of the adic formalism: the derived completion
(`DerivedCategory.derivedCompletion`) of `j_! K`. It is a chosen homotopy limit. -/
noncomputable def completedOpenImmersionLowerShriek
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)) :=
  _root_.DerivedCategory.derivedCompletion (Scheme.ProEt.topology Z) I
    (D((j)_!open[ModuleCat.{u + 1} Λ]).obj K)

variable (Λ) in
/-- The base change isomorphism `Lg^*(j_! K) ≅ j'_!(Lg_U^* K)` of the extension by zero on the
unbounded derived categories, for a cartesian square `g' ≫ j = j' ≫ g''` with `j`, `j'` open
immersions: the derived pullbacks are computed degreewise
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory`) and the extension by
zero commutes with base change
(`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekBaseChangeIso`, blueprint
`lem-cbc-proetale-extension-zero-base-change`). -/
noncomputable def leftDerivedUpperStarOpenImmersionLowerShriekIso
    (hsq : IsPullback g' j' j g'')
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))) :
    (L((g'')^*[ModuleCat.{u + 1} Λ])).obj (D((j)_!open[ModuleCat.{u + 1} Λ]).obj K) ≅
      D((j')_!open[ModuleCat.{u + 1} Λ]).obj ((L((g')^*[ModuleCat.{u + 1} Λ])).obj K) :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g'').app _ ≪≫
    ((derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) hsq).app K).symm ≪≫
    D((j')_!open[ModuleCat.{u + 1} Λ]).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g').app K).symm

/-- Blueprint `lem-cbc-completed-extension-zero-comparison` (corrected): Completed
extension-by-zero base change.

For a cartesian square `g' ≫ j = j' ≫ g''` of schemes with `j : U ⟶ Z`, `j' : U' ⟶ Z'` open
immersions and `K` in `D(U_proét, Λ)`, the completed pullback of the extension by zero is the
completed extension by zero of the pullback:
```
Lg''^*_comp (j_! K) ≅ j'_!^comp (Lg'^* K) = (j'_! Lg'^* K)^∧.
```
Both sides are homotopy limits of the towers of reductions of `Lg''^*(j_! K)` and of
`j'_!(Lg'^* K)`, which are isomorphic through the finite-level base change isomorphism
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarOpenImmersionLowerShriekIso`; the isomorphism is
the induced map of the chosen homotopy limits (`DerivedCategory.derivedCompletionMap`). No
completeness hypothesis on `K` is needed.

The type of this declaration is inferred: it is
`derivedCompletion Z' I (Lg''^*(j_! K)) ≅ derivedCompletion Z' I (j'_!(Lg'^* K))`, which is
definitionally
`completedPullback I g'' (j_! K) ≅ completedOpenImmersionLowerShriek I j' (Lg'^* K)`;
stating it in the latter form makes the kernel time out on the comparison of the proofs nested
in the two elaborations of the derived pullback.

**The literal blueprint statement is false.** It asserts
`Lg''^*_comp (j_! K) ≅ j'_!(Lg'^*_comp K)` for derived complete `K`, with the plain extension by
zero on the right. For `g'' = 𝟙` this says that `j_!` preserves derived completeness, which
fails: let `Z` be the spectrum of a strictly henselian discrete valuation ring `R` with fraction
field `F`, `U` its generic point, `Λ = ℤ_ℓ`, `I = (ℓ)` and `K = ℤ_ℓ` (derived complete), and let
`T` be the spectrum of the ring of finitely-valued sequences in `F` which lie in `R` from some
index on (ind-Zariski over `R`, hence in `Z_proét`). The clopen subsets of `T` lying over `U`
are the finite unions of the components `Spec F`, so `(j_! ℤ_ℓ)(T) = ⊕_ℕ ℤ_ℓ`, whereas
`(R lim_n j_!(ℤ/ℓⁿ))(T)` is the `ℓ`-adic completion of `⊕_ℕ ℤ_ℓ`. The step of the blueprint proof
that fails is that `j_!` commutes with countable products. -/
noncomputable def completedPullbackOpenImmersionLowerShriekIso (hsq : IsPullback g' j' j g'')
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))) :=
  asIso (_root_.DerivedCategory.derivedCompletionMap (Scheme.ProEt.topology Z') I
    (leftDerivedUpperStarOpenImmersionLowerShriekIso Λ hsq K).hom)

end OpenImmersion

section Exchange

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The map `Lg^* Rf_!(c) K ⟶ Rf'_!(c') Lg'^*_comp K` whose reductions modulo `Iⁿ` induce the
completed exchange map: the pro-étale exchange map `Ex_!(c)` at `K`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap`) followed
by `Rf'_!(c')` of the completion map `Lg'^* K ⟶ Lg'^*_comp K`
(`DerivedCategory.derivedCompletionUnit`, a choice). -/
noncomputable def rightDerivedLowerShriekBaseChangeCompletionMap (sq : IsPullback g' f' f g)
    (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :=
  (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq c).app K ≫
    (Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1} Λ]).map
      (_root_.DerivedCategory.derivedCompletionUnit (Scheme.ProEt.topology X') I _)

/-- Blueprint `def-cbc-completed-exchange-map` (corrected): Completed compact-support exchange
map.

For a cartesian square `g' ≫ f = f' ≫ g`, a compactification `c` of `f` with base change
`c' = c ×_Y Y'` and `K` in `D(X_proét, Λ)`, the completed compact-support exchange map
```
Ex_!^comp(K) : Lg^*_comp Rf_!(c) K ⟶ (Rf'_!(c') Lg'^*_comp K)^∧
```
is the map of homotopy limits induced by the tower of reductions modulo `Iⁿ` of the finite-level
maps `Lg^* Rf_! K ⟶ Rf'_! Lg'^* K ⟶ Rf'_! Lg'^*_comp K`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekBaseChangeCompletionMap`).

As in the corrected `lem-cbc-completed-extension-zero-comparison`
(`AlgebraicGeometry.ProEtale.completedPullbackOpenImmersionLowerShriekIso`), the target is
completed: `Rf'_! = Rp'_* j'_!` need not preserve derived completeness, because `j'_!` does not.
The map is a choice: the derived completions, the completion map and the induced map of
homotopy limits (`DerivedCategory.derivedCompletionMap`) are only determined up to non-unique
isomorphism and phantom maps; the choice is made so that the map is an isomorphism whenever
the finite-level map is (`isIso_completedRightDerivedLowerShriekBaseChangeMap`). Its type is
inferred (as for `completedPullbackOpenImmersionLowerShriekIso`); it is definitionally
`completedPullback I g (Rf_!(c) K) ⟶
  derivedCompletion Y' I (Rf'_!(c') (completedPullback I g' K))`. -/
noncomputable def completedRightDerivedLowerShriekBaseChangeMap (sq : IsPullback g' f' f g)
    (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :=
  _root_.DerivedCategory.derivedCompletionMap (Scheme.ProEt.topology Y') I
    (rightDerivedLowerShriekBaseChangeCompletionMap I sq c K)

/-- The completed exchange map is an isomorphism when the finite-level map
`Lg^* Rf_! K ⟶ Rf'_! Lg'^*_comp K` is. -/
lemma isIso_completedRightDerivedLowerShriekBaseChangeMap (sq : IsPullback g' f' f g)
    (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    [IsIso (rightDerivedLowerShriekBaseChangeCompletionMap I sq c K)] :
    IsIso (completedRightDerivedLowerShriekBaseChangeMap I sq c K) :=
  _root_.DerivedCategory.isIso_derivedCompletionMap _ _ _

/-- For a finite coefficient ring `Λ` and `K` bounded below of étale origin, the completed
exchange map is an isomorphism as soon as the completion map `Lg'^* K ⟶ Lg'^*_comp K` is (for
instance when `Lg'^* K` is derived complete and the chosen completion map is the comparison of
homotopy limits): the exchange map `Ex_!(c)` at `K` is an isomorphism by finite-level pro-étale
compact-support base change
(`AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app`,
blueprint `thm-cbc-finite-level-proetale`). -/
lemma isIso_completedRightDerivedLowerShriekBaseChangeMap_of_finite [Finite Λ]
    (sq : IsPullback g' f' f g) (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K)
    [IsIso (_root_.DerivedCategory.derivedCompletionUnit (Scheme.ProEt.topology X') I
      ((L((g')^*[ModuleCat.{u + 1} Λ])).obj K))] :
    IsIso (completedRightDerivedLowerShriekBaseChangeMap I sq c K) := by
  have := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app Λ sq c K hK
  have : IsIso (rightDerivedLowerShriekBaseChangeCompletionMap I sq c K) := by
    rw [rightDerivedLowerShriekBaseChangeCompletionMap]
    infer_instance
  exact isIso_completedRightDerivedLowerShriekBaseChangeMap I sq c K

end Exchange

end AlgebraicGeometry.ProEtale
