/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.AlgebraicGeometry.PunctualPurity
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.KrullDimension.Basic

import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.AlgebraicGeometry.OpenClosedRecollement
import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.AlgebraicGeometry.RegularLCIGeometricCalculus
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations
import Mathlib.RingTheory.Localization.Submodule
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Punctual purity and the two-of-three criterion

Source: ILO, Exposé XVI, Definitions 3.1.4, 3.2.1--3.2.2 and Proposition 3.2.3,
printed pp. 243--244 (blueprint: lem-per-punctual-purity-two-of-three).

The three conditions use the published canonical supported Kummer map and punctual
purity predicates on ordinary small-etale D+ with coefficients F_ell.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Among purity of a regular closed pair, punctual purity of its closed scheme, and
punctual purity of the ambient scheme on the closed support, any two imply the third.
All schemes are arbitrary Noetherian regular schemes; in particular localizations of
such pairs are included. The constant-codimension statement is applied separately on
regions where the locally constant codimension has a fixed value.

Source: ILO XVI Proposition 3.2.3, printed p. 244
(blueprint: lem-per-punctual-purity-two-of-three).

Proof plan, following the eight DAG steps:
1. At z localize the pair to S = Spec O_(Z,z) inside T = Spec O_(X,i(z)). The local
   dimensions are d and d+c, by lem-per-regular-lci-geometric-calculus. Noetherianity
   survives localization. The localization is ind-etale, as the filtered colimit of
   principal open localizations (lem-weil-pbc-localization-colimit-principal-localizations
   and lem-weil-pbc-open-immersion-etale). Restrict the class by class calculus and
   identify closed support by lem-per-ind-etale-closed-support-base-change.
2. Fundamental-class composition gives eta_b = a^!(eta_i)(d)[2d] after eta_a. The
   transitivity is the canonical adjunction comparison (lem-cat-right-adjoint-composition);
   lem-asd-etale-finite-twist-pullback gives the normalized Tate comparisons.
3. On D+ the compact-support adjoint is the derived supported kernel, by the closed
   adjunction (def-per-closed-support-plus-adjunction, lem-pur-etale-supported-kernel-adjunction,
   def-amb-etale-compact-support). Derive on injectives using enough injectives and
   lem-weil-pbc-dplus-injective-representative. It is triangulated by
   lem-pc-right-derived-functor-triangulated, and the cone detects invertibility by
   lem-sf-derived-homology-long-exact.
4. If the pair is pure, cancel its exceptional restriction in the composition identity.
   This proves each of the first two implications at every z.
5. If both punctual conditions hold, cancel eta_a and eta_b to obtain a^!C = 0 for
   a cone C of the local pair class.
6. Induct strongly on d over all regular local pairs. Proper generizations have smaller
   local dimension, hence the cone restricts to zero off the closed point. Use
   lem-weil-pbc-inverse-image-stalk-germ and lem-weil-pbc-derived-stalk-conservative.
   At d=0 the punctured spectrum is empty.
7. Open-closed recollement (lem-cbc-open-closed-recollement) makes C supported at the
   closed point: C = a_*a^*C. The adjunction of lem-exc-closed-ambient, restricted to
   D+, identifies Hom(C,C) with Hom(a^*C,a^!C)=0. Thus C=0.
8. The local class is therefore an isomorphism at every z, and stalk conservativity
   gives the global assertion. The proof applies unchanged to localized pairs.
   Empty support makes both pointwise conditions vacuous; c=0 uses the clopen class.
-/
theorem punctual_purity_two_of_three (ℓ : ℕ) (hℓ : ℓ.Prime)
    {Z X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian X]
    (hZ : IsRegularScheme Z) (hX : IsRegularScheme X)
    (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ)
    (hi : IsStalkRegularClosedImmersion i c)
    (hℓX : IsUnit ((ℓ ^ 1 : ℕ) : Γ(X, ⊤))) :
    (IsIso (punctualPurityClassMap ℓ hℓ i c hi hℓX) → IsPunctuallyPure ℓ hℓ Z →
      ∀ z : Z, IsPunctuallyPureAt ℓ hℓ X (i z)) ∧
    (IsIso (punctualPurityClassMap ℓ hℓ i c hi hℓX) →
      (∀ z : Z, IsPunctuallyPureAt ℓ hℓ X (i z)) → IsPunctuallyPure ℓ hℓ Z) ∧
    (IsPunctuallyPure ℓ hℓ Z →
      (∀ z : Z, IsPunctuallyPureAt ℓ hℓ X (i z)) →
      IsIso (punctualPurityClassMap ℓ hℓ i c hi hℓX)) := by
  sorry

end AlgebraicGeometry.Etale
