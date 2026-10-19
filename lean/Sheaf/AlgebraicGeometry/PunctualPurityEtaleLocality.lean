/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.AlgebraicGeometry.PunctualPurity
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange
import Sheaf.RingTheory.Etale.LocalDimension
import Sheaf.RingTheory.StrictHenselizationLocalMaximalIdeal
import Sheaf.RingTheory.StrictHenselizationDimension
import Sheaf.RingTheory.StrictHenselizationNoetherian
import Sheaf.RingTheory.StrictHenselizationRegular
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedImmersionCartesian
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-!
# Étale locality of punctual cohomological purity

Source: ILO, Exposé XVI, Definitions 3.2.1--3.2.2, printed p.244, and the reduction
following Proposition 3.6.5, printed p.253
(blueprint: lem-per-punctual-purity-etale-locality).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Punctual purity is invariant at points of an étale morphism and descends along every
jointly surjective étale family. No surjectivity is required for the pointwise assertion.
Source: ILO XVI 3.2.1--3.2.2 and the reduction after 3.6.5
(blueprint: lem-per-punctual-purity-etale-locality).

Proof, following the seven steps of the node:
1. Set R = O_{X,x}, S = O_{Y,y}. The étale local-dimension theorem makes their dimensions
   equal to d; the residue extension k'/k is finite separable. Regular local rings give
   closed-point regular immersions of codimension d, by regular-lci geometric calculus.
2. Ind-étale strict-local invariance and affine strict-local-ring comparison identify
   the strict localizations at compatible geometric points with the same scheme C.
   This includes the residue embeddings, not an identification of the ordinary local rings.
3. Strict henselization preserves Noetherianity, regularity and dimension. Its maps to
   Spec R and Spec S are ind-étale. The closed-immersion strict-localization Cartesian theorem
   and the strict-henselian maximal-ideal calculation give the same closed point c of C.
4. Ind-étale closed-support base change, finite Tate pullback and the regular-immersion
   class calculus identify both pulled-back Kummer maps with the same normalized class
   on c inside C. The adjoint and supported-kernel formulations agree by uniqueness.
5. Exact inverse image and exact geometric stalks identify all cohomology maps. Derived
   geometric-stalk conservativity gives eta_S invertible iff the pullback of eta_R is.
6. Each geometric point of Spec k lifts to Spec k': the algebraic extension embeds into
   its algebraically closed geometric residue field. Stalk conservativity therefore reflects
   invertibility along Spec k' → Spec k. Functors preserve inverses in the other direction.
7. Apply this pointwise equivalence at every point of each family member. Conversely,
   joint surjectivity supplies a point upstairs over each point downstairs. Empty families
   covering the empty scheme and dimension zero are included without exceptions. -/
theorem punctual_cohomological_purity_etale_locality (ℓ : ℕ) (hℓ : ℓ.Prime) :
    (∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y],
      IsRegularScheme X → IsRegularScheme Y →
      ∀ (f : Y ⟶ X) [Etale f], IsUnit (ℓ : Γ(X, ⊤)) → IsUnit (ℓ : Γ(Y, ⊤)) →
      ∀ y : Y, IsPunctuallyPureAt ℓ hℓ Y y ↔
        IsPunctuallyPureAt ℓ hℓ X (f y)) ∧
    (∀ {X : Scheme.{u}} [IsNoetherian X], IsRegularScheme X →
      IsUnit (ℓ : Γ(X, ⊤)) → ∀ (I : Type v) (Y : I → Scheme.{u})
      [∀ a : I, IsNoetherian (Y a)], (∀ a : I, IsRegularScheme (Y a)) →
      ∀ (f : ∀ a : I, Y a ⟶ X) [∀ a : I, Etale (f a)],
      (∀ x : X, ∃ (a : I) (y : Y a), f a y = x) →
      (IsPunctuallyPure ℓ hℓ X ↔
        ∀ a : I, IsPunctuallyPure ℓ hℓ (Y a))) := by
  sorry

end AlgebraicGeometry.Etale
