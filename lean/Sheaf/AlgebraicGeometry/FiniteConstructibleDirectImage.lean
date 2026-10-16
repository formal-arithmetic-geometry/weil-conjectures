/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import Sheaf.Paper.ConstantSheafSectionsLocallyConstant
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Finite direct images of constructible module sheaves

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-morphism.md`,
order 1580 (blueprint: lem-fin-finite-morphism).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- For a finite morphism with target of finite type over a field, direct image preserves
constructible module sheaves and its positive higher direct images vanish.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-morphism.md`, order 1580
(blueprint: lem-fin-finite-morphism).

Proof plan:
1. Spec k is Noetherian; finite type makes S Noetherian
   (`lem-weil-pbc-finite-type-over-noetherian`). Forgetting scalars makes F a finite
   constructible abelian sheaf (`def-weil-pbc-constructible-abelian-sheaf`).
2. Apply `lem-weil-pbc-finite-pushforward-constructible-noetherian` to that abelian sheaf.
   The forgetful compatibility in `lem-weil-pbc-module-direct-image-left-exact` identifies
   the result with the underlying abelian sheaf of f_*F. Choose its finite partition and
   finite constant abelian trivializations.
3. On a trivialization with finite fibre M, transport each scalar action to M. By
   `lem-weil-pbc-constant-sheaf-sections-locally-constant`, its values on constant sections
   are Zariski locally constant. The coefficient convention makes both Lambda and M finite,
   so refine by all fibres of the finitely many action-table entries simultaneously.
   On each nonempty piece the constant values satisfy the module relations. Applying the
   section description again to arbitrary etale objects and using the sheaf axiom shows
   that the abelian trivialization is a constant-module trivialization.
4. These open refinements are etale by `lem-weil-pbc-etale-composition-cancellation`.
   The original finite constructible stratification now gives exactly
   `def-weil-pbc-etale-constructible-sheaf` for f_*F.
5. Forget a short exact module sequence to abelian sheaves, use
   `lemma-weil-pbc-finite-direct-image-exact`, and use the forgetful compatibility again.
   Sectionwise kernels and sheafified cokernels (`def-weil-sheaf-of-modules-category`)
   detect exactness, so module direct image is exact.
6. Choose an injective resolution of F as in `def-weil-pbc-direct-image`. Exactness in
   step 5 preserves the short exact sequences of cycles of the resolution. In every
   positive degree the image of the preceding pushed-forward differential therefore
   equals the kernel of the next differential. Its cohomology sheaf, R^q f_*F, is zero. -/
theorem finite_directImage_constructible_and_higher_vanishing
    (k : Type u) [Field k] {X S : Scheme.{u}}
    [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (f : X ⟶ S) [IsFinite f] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]
    (hcoeff : IsSmoothBaseChangeCoefficients N Λ S)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : @Scheme.IsConstructibleEtaleModuleSheaf X Λ _ hcoeff.2.1 F) :
    @Scheme.IsConstructibleEtaleModuleSheaf S Λ _ hcoeff.2.1
      ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ∧
    ∀ q : ℤ, 0 < q → IsZero
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  sorry

end AlgebraicGeometry.Etale
