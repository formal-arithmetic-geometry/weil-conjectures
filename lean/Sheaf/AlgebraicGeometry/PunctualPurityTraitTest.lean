/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.AlgebraicGeometry.PunctualPurity
public import Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
public import Sheaf.AlgebraicGeometry.StalkRegularClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.AlgebraicGeometry.Sites.EtaleSheavesGsetsPoint
import Sheaf.RingTheory.CompleteMixedRegularPairApproximation

/-!
# Testing punctual purity over complete mixed-characteristic traits

Source: ILO, Exposé XVI, Definitions 3.2.1--3.2.2, Propositions 3.2.4--3.2.5,
pp. 244--245, and §3.7, first paragraph, p. 254
(blueprint: lem-per-punctual-purity-trait-test).

Punctual purity uses the published predicate `IsPunctuallyPure`: the transpose of the
actual Kummer class is an isomorphism. The supported class is the unique normalized
family of the published class-calculus theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Abelian

namespace AlgebraicGeometry.Etale

/-- Testing over integral regular flat quasi-projective schemes of finite type over
complete strictly henselian mixed-characteristic traits suffices for punctual purity
of every regular Noetherian scheme. No excellence assumption is made.

Source: ILO XVI §3.7, first paragraph, p. 254, together with Propositions 3.2.4--3.2.5
(blueprint: lem-per-punctual-purity-trait-test).

Proof:
1. Fix a point of W. By lem-per-punctual-strict-completion-test, replace its regular
local ring by the completion of its strict henselization, with the same dimension.
This test does not require excellence.
2. If this ring contains a prime field, apply lem-per-prime-field-punctual-purity.
Otherwise lem-sc-regular-local-domain gives a domain and the characteristic split
is mixed (0,p); invertibility of ℓ gives ℓ ≠ p.
3. Choose regular parameters and apply lem-per-complete-mixed-regular-pair-approximation.
It gives compatible affine regular pairs over a complete strictly henselian trait,
with integral regular flat finite-type ambient schemes. Their affine presentations
make them quasi-projective, so the testing hypothesis makes them punctually pure.
4. Their regular F_p closed subschemes are pure by lem-per-prime-field-punctual-purity.
Conditions (b) and (c) of lem-per-punctual-purity-two-of-three imply that the actual
supported Kummer class of each finite-stage pair is an isomorphism after transposition.
5. Apply lem-per-transverse-gysin-limit to the compatible regular parameters. In every
integer degree, supported cohomology and ordinary cohomology are the colimits of
the finite stages, and their Kummer maps are the actual limiting Kummer map.
6. The limiting residue field is separably closed. By lem-exc-etale-sheaves-gsets-point,
its small-etale topos is sets, so global sections detect the isomorphism in every degree.
The strict-completion test gives purity at the original point; quantify over all points.
-/
theorem punctual_purity_of_complete_mixed_trait_test (ℓ : ℕ) (hℓ : ℓ.Prime)
    (htest : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [IsStrictlyHenselianLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
      [CharZero R],
      (∃ p : ℕ, p.Prime ∧ CharP (IsLocalRing.ResidueField R) p) → IsUnit (ℓ : R) →
      ∀ (V : Scheme.{u}) [IsNoetherian V] [IsIntegral V]
        (f : V ⟶ Spec (.of R)),
        IsRegularScheme V → Flat f → LocallyOfFiniteType f → QuasiCompact f →
        (∃ (N : ℕ) (i : V ⟶ ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of R))),
          IsImmersion i ∧
            i ≫ ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of R)) ↘ Spec (.of R) = f) →
        IsPunctuallyPure ℓ hℓ V) :
    ∀ (W : Scheme.{u}) [IsNoetherian W], IsRegularScheme W →
      IsUnit (ℓ : Γ(W, ⊤)) → IsPunctuallyPure ℓ hℓ W := by
  sorry

end AlgebraicGeometry.Etale
