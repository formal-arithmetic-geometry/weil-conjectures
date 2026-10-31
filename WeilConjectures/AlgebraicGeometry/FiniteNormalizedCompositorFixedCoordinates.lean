/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSupportCoordinates
public import WeilConjectures.AlgebraicGeometry.FiniteAdjointCompositorTransposes
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.FiniteType
import WeilConjectures.SecSmoothPurity.ReductionExceptionalObjects
import WeilConjectures.AlgebraicGeometry.FiniteSiteWordRefinement
import WeilConjectures.AlgebraicGeometry.FiniteCompactSiteCoherence
import WeilConjectures.AlgebraicGeometry.CompactSupportSiteCoherence

/-! # Finite normalized compositors in fixed module coordinates

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/
`sk-prop-sp-composition-comparisons.proof.md`, (3), first sentence
(blueprint: lem-sp-finite-normalized-compositor-fixed-coordinates).

The equality is in the ambient fixed-coefficient derived category. The intrinsic
input is in the full bounded constructible finite-Tor subcategory, and its specified
bounded-below etale antecedent is retained. All comparisons are the published ones.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale



/-- A finite compositor normalized on all etale witnesses agrees with the canonical
fixed-module compositor under the section-normalized finite support coordinates.
Source: blueprint, composition comparisons proof (3), first sentence
(blueprint: lem-sp-finite-normalized-compositor-fixed-coordinates).

Proof:
1. Finite-type schemes over k are Noetherian, using finite affine covers and
   lem-weil-pbc-finite-type-algebra-noetherian. The proper compactifying schemes are
   finite type over k by lem-sfb-finite-type-composition-base-change, hence Noetherian.
   Keep all three supplied compactifications.
2. Write Q for inverse realization, N for site comparison, U for forward realization
   after N, and S for finiteAdjointSiteSupportIso. Apply forward realization to the
   retained witness and then the realization counit to obtain v : U L ≅ K. The full
   constructible finite-Tor property transports across v, so D.normalization applies.
3. By lem-sp-finite-site-word-refinement the etale intermediate G_f L is bounded below.
   With tau : Q U ≅ N the inverse realization unit, put q_c = Q(S_c) followed by tau.
   The single-support square lem-sp-single-support-site-coordinate-square gives
   q_c followed by C_c = s_c followed by Fhat_c(tau), for f,L; g,G_f L; and h,L.
4. Apply Q to D.normalization and use naturality of tau. Finite compact-site coherence
   (lem-sp-finite-compact-site-coherence) identifies the etale compositor transported
   through C with finiteCanonicalComposition. The chosen-compactification changes
   are precisely def-pur-chosen-compactification-compositors, so this holds for the
   arbitrary supplied compactifications.
5. Substitute these two equations in the single-support square for h. Replace the
   g square and use naturality of s_g at S_f. Replace the f square, use naturality
   of the fixed compositor at tau, and cancel the invertible factor Fhat_h(tau).
   This gives the displayed equation at U L.
6. Both sides are natural in the intrinsic input. Apply naturality to v : U L ≅ K
   and cancel its image under Q F_g F_f, obtaining the equality at the original K.
   No tower evaluation, smoothness, or normalized-tower hypothesis is used.
-/
theorem finiteNormalizedCompositorFixedCoordinates
    (l p : ℕ) [Fact l.Prime] [Fact p.Prime] (_hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (z : SpTowerCalculus.FiniteCoordinates l E)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g))
    (D : FiniteAdjointCompositorDatum (SpTowerShriek.R l E n) cf cg ch)
    (K : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n))
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n)))))
    (w : (comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) X).mapDerivedCategory.obj
          L.obj ≅ (sfIntrinsicDerivedEquivalence X (SpTowerShriek.R l E n)).inverse.obj K.obj) :
    (sfIntrinsicDerivedEquivalence Z (SpTowerShriek.R l E n)).inverse.map
        ((D.alpha.hom.app K).hom) ≫
      (SpTowerCalculus.fixedSupportCoordinatesFinite l E z ch n).hom.app K.obj =
    (SpTowerCalculus.fixedSupportCoordinatesFinite l E z cg n).hom.app
        ((reductionCompactSupport (SpTowerShriek.R l E n) cf.i cf.g).obj K.obj) ≫
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) cg).map
          ((SpTowerCalculus.fixedSupportCoordinatesFinite l E z cf n).hom.app K.obj) ≫
      (SpTowerCalculus.finiteCanonicalComposition
        (ULift.{u + 1} (SpTowerShriek.R l E n)) f g cf cg ch).hom.app
          ⟨(sfIntrinsicDerivedEquivalence X (SpTowerShriek.R l E n)).inverse.obj K.obj,
            ⟨L.obj, L.property, ⟨w⟩⟩⟩ := by
  sorry

end AlgebraicGeometry.ProEtale
