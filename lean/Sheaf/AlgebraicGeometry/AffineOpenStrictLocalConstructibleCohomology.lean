/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Data.ZMod.Basic
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ConstructibleFiniteOpenConstantGeneration
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.RingTheory.FiniteRingMapQuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import Sheaf.RingTheory.QuasiFiniteIntegralClosureOpen
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.IntegralExtensionDimension
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.RingTheory.StrictlyHenselianQuotient
import Sheaf.AlgebraicGeometry.OpenClosedRecollement
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import Sheaf.AlgebraicGeometry.AffineOpenStrictLocalConstantBound

/-!
# Constructible sheaf cohomology on affine opens of an excellent strictly local scheme

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XV, Corollary 1.2.2,
printed p. 219, applied to an affine open immersion; the constructible coefficient
case is the direct affine-open specialization.
(blueprint: lem-per-affine-open-strict-local-cd-constructible).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option linter.style.haveILetI false

/-- Gabber's affine-open cohomological-dimension bound for constructible finite
prime-power coefficient sheaves. The cohomology is computed after forgetting the
module structure to the underlying abelian sheaf and placing it in degree zero.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XV, Corollary 1.2.2,
printed p. 219, for an affine open immersion of a Noetherian excellent strictly
henselian local affine scheme (blueprint: lem-per-affine-open-strict-local-cd-constructible).

Proof outline, following the node's ten steps:
1. Filter `C` by the images of multiplication by powers of `ℓ`. The successive quotients
   are constructible `F_ℓ`-module sheaves by `thm-constructible-serre`. Exact forgetting
   (`lem-weil-pbc-module-sheaves-colimits-forgetful`) and the long exact cohomology sequence
   (`lem-weil-pbc-pullback-cohomology-long-exact-ladder`) reduce to these quotients.
2. The class of sheaves with vanishing above `d` is closed under finite sums, extensions
   and retracts, by additivity of derived cohomology
   (`lem-weil-pbc-right-derived-universal-delta-functor`), enough injectives
   (`lem-weil-pbc-site-sheaves-enough-injectives`) and evaluation global sections
   (`def-weil-pbc-global-sections-functor`). The affine open is Noetherian
   (`pqf-lem-affine-open-locnoeth`), so
   `lem-per-constructible-finite-open-constant-generation` reduces to `π_* k_! F_ℓ`,
   with `π : T → V` finite, `T` integral and `k : W → T` nonempty open.
3. Write the affine rings as `R`, `R_V`, `E`. The open immersion `V → X` is quasi-compact
   (`lem-weil-pbc-affine-scheme-qcqs`) and finite type
   (`lem-weil-pbc-qc-open-immersion-finite-type`). The finite map `T → V` is finite type
   (`lem-weil-pbc-finite-ring-map-quasi-finite`), as is its composite to `X`
   (`lem-sfb-finite-type-composition-base-change`). Finite fibres
   (`lem-weil-pbc-finite-closed-map-finite-fibres`, `pqf-lem-qf-finitefibres`)
   make the composite quasi-finite.
4. Translate this using `pqf-def-quasifinite` and
   `def-weil-pbc-ring-map-quasi-finite-at-prime`. Clause (3) of
   `lem-weil-pbc-quasi-finite-ring-map-integral-closure-open` gives a finite subalgebra
   `A ⊆ E` with `T` a dense open of the integral scheme `Y = Spec A`.
5. In fact `T = Y ×_X V`: the induced open immersion is finite because `E` is finite
   over `A ⊗[R] R_V` (`def-weil-finite-integral-morphism`). Its image is closed
   (`lem-weil-pbc-finite-closed-map-finite-fibres`) and dense, so it is an isomorphism
   (`def-weil-open-immersion`). Thus `T` is an affine open of `Y`.
6. The finite domain `A` is henselian local
   (`lem-weil-pbc-finite-over-henselian-local-product`) with separably closed residue field
   (`lem-kun-sep-closed-finite-extension-sep-closed`), excellent
   (`lem-exc-finite-type-localization-excellent`), and has dimension `e ≤ d`
   (`lem-weil-pbc-integral-extension-dimension`). It is strictly local, and `ℓ` is a unit.
7. Close the reduced boundary `F = T ∖ W` in `Y` to obtain `Z`
   (`lem-weil-pbc-reduced-induced-closed-subscheme`), with `F = Z ×_Y T` affine open.
   Since `Z` misses the generic point, it has dimension at most `e - 1`, or is empty
   when `e = 0`. A nonempty `Z` is strictly local
   (`lem-weil-pbc-strictly-henselian-quotient`) and excellent
   (`lem-exc-finite-type-localization-excellent`).
8. Apply `lem-per-affine-open-strict-local-constant-bound` to `T ⊆ Y` and `F ⊆ Z`.
   For `q > d`, this gives `H^q(T, F_ℓ) = 0` and `H^(q-1)(F, F_ℓ) = 0`.
   When `Z` is empty the latter vanishing holds directly.
9. The open-closed triangle (`lem-cbc-open-closed-recollement`), constant inverse image
   (`lem-pe-constant-left-module-inverse-image`) and exact forgetting yield
   `0 → k_! F_ℓ → F_ℓ → i_* F_ℓ → 0`. The closed immersion is finite
   (`lem-weil-pbc-closed-immersion-finite`); finite pushforward cohomology
   (`lem-weil-pbc-finite-pushforward-cohomology`) and the long exact sequence give
   `H^q(T, k_! F_ℓ) = 0` between the two zero groups of step 8.
10. Finite pushforward cohomology identifies this with `H^q(V, π_* k_! F_ℓ)`.
    The underlying abelian direct image agrees sectionwise (`def-weil-pbc-direct-image`).
    The closure properties of step 2 and the generator theorem give the bound over `F_ℓ`;
    descending induction through step 1 gives it for `C`. Empty `V` and the zero sheaf
    are included. -/
theorem isZero_cohomology_affineOpen_of_strictlyHenselian_constructible
    (X : Scheme.{u}) [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    [IsStrictlyHenselianLocalRing Γ(X, ⊤)] (hX : IsExcellent Γ(X, ⊤))
    (ℓ n d : ℕ) (hℓ : ℓ.Prime) (hn : 1 ≤ n)
    (hunit : IsUnit (ℓ : Γ(X, ⊤)))
    (hd : ringKrullDim Γ(X, ⊤) = (d : WithBot ℕ∞))
    {V : Scheme.{u}} [IsAffine V] (j : V ⟶ X) [IsOpenImmersion j]
    (C : Sheaf V.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n)))))
    (hC : @Scheme.IsConstructibleEtaleModuleSheaf V
      (ULift.{u + 1} (ZMod (ℓ ^ n))) _ (by
        letI : NeZero (ℓ ^ n) := ⟨pow_ne_zero n hℓ.ne_zero⟩
        letI : Fintype (ZMod (ℓ ^ n)) :=
          ZMod.fintype (ℓ ^ n)
        exact Finite.of_equiv (ZMod (ℓ ^ n)) Equiv.ulift.symm) C)
    (q : ℕ) (hq : d < q) :
    IsZero ((cohomology AddCommGrpCat.{u + 1} V (q : ℤ)).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((sheafCompose V.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))
            AddCommGrpCat.{u + 1})).obj C))) := by
  sorry

end AlgebraicGeometry.Etale
