/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.AlgebraicGeometry.FiniteConstructibleDirectImage
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact

/-!
# Constructibility under finite morphisms

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/
`fin4-thm-finite-morphisms-constructible.md` (blueprint: fin4-thm-finite-morphisms-constructible).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- For a finite morphism to a finite-type scheme over a field, every nonnegative
higher direct image of a constructible finite-coefficient module sheaf is constructible,
and all positive higher direct images vanish.

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/
`fin4-thm-finite-morphisms-constructible.md`, node order 1773
(blueprint: fin4-thm-finite-morphisms-constructible).

Proof plan:
1. Apply `lem-fin-finite-morphism` with the same finite commutative coefficient ring,
   annihilated by the positive integer N invertible on S (and hence on X). It gives
   constructibility of f_*F and vanishing of R^q f_*F for q > 0, in the module category
   of `def-weil-pbc-direct-image`.
2. Choose an injective resolution of F, zero in negative degrees, as specified in
   `def-weil-pbc-direct-image`. By `lem-weil-pbc-module-direct-image-left-exact`,
   applying f_* preserves its initial kernel sequence. Thus H^0(f_*I) is f_*F,
   so its constructibility from step 1 transports to R^0 f_*F.
3. In every positive degree use step 1's zero-object isomorphism. On the same finite
   constructible locally closed partition and etale trivializations that witness
   constructibility of f_*F in `def-weil-pbc-etale-constructible-sheaf`, the zero
   sheaf is constant with value the zero finite Lambda-module. These trivializations
   give constructibility of R^q f_*F. For empty S the empty partition works. Together
   with step 2 this covers all q >= 0 and gives vanishing above 2 * 0 = 0. -/
theorem finiteMorphisms_constructible
    (k : Type u) [Field k] {X S : Scheme.{u}}
    [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (f : X ⟶ S) [IsFinite f] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]
    (hcoeff : IsSmoothBaseChangeCoefficients N Λ S)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : @Scheme.IsConstructibleEtaleModuleSheaf X Λ _ hcoeff.2.1 F) :
    (∀ q : ℕ, @Scheme.IsConstructibleEtaleModuleSheaf S Λ _ hcoeff.2.1
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) ∧
    (∀ q : ℕ, q > 0 → IsZero ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := by
  sorry

end AlgebraicGeometry.Etale
