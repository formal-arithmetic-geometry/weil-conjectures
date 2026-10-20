/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.EtaleCompactSupportCoefficientChange
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons

import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
import Sheaf.AlgebraicGeometry.ProperOpenComparison
import Sheaf.AlgebraicGeometry.OpenSectionClopen
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.Paper.UnboundedProperOpenInterchange
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization
import Sheaf.AlgebraicGeometry.ClopenSectionDirectImage
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle
import Sheaf.Paper.ProjectionMateExact
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.Compactification.NagataCompactification
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import Sheaf.Paper.BoundedBelowCtfReflection
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.FiniteCoefficientDirectImage
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.Paper.FiniteCoefficientReductionFlatModel
import Sheaf.Paper.FiniteTensorConstructibleCohomology
import Sheaf.Paper.OpenExtensionFiniteTor
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage
import Sheaf.Paper.ProperOpenCoefficientRefinement
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Finite coefficient comparison and compact-support composition

Source: Stacks Project, more-etale.tex, Tags 0F7J and 0GL6
(blueprint: lem-sf-compact-coefficient-composition).
The two statements use the actual small-etale and pro-etale compact-support functors,
the specified canonical compositors, and universal B-linear coefficient comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

/-- Positive-level coefficient rings in the standard coefficient universe are finite.
This only registers the recorded coefficient finiteness theorem at positive levels.
Source: Serre, Local Fields, Chapter II, section 2; Stacks Tag 0GL6
(blueprint: lem-sf-compact-coefficient-composition). -/
instance finiteCompositionCoefficient (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ+) : Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) :=
  Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n n.property)

/-- The specified quotient coefficient homomorphism, with only the standard universe lift.
Source: Stacks Tag 0GL6 (blueprint: lem-sf-compact-coefficient-composition). -/
def finiteCompositionReduction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ+) (hmn : n ≤ m) :
    ULift.{u + 1} (Padic.coefficientExtensionRing l E m) →+*
      ULift.{u + 1} (Padic.coefficientExtensionRing l E n) :=
  RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E m)
    (T := Padic.coefficientExtensionIdeal l E n) (Ideal.pow_le_pow_right hmn))

/-- Register the existing Nagata construction for a separated finite-type morphism
whose target is separated and quasi-compact over the fixed field. The two topological
instances are consequences of its structure morphism, not hypotheses on the theorem.
Source: Stacks Tags 0F41 and 0F7J
(blueprint: lem-sf-compact-coefficient-composition). -/
noncomputable def finiteCompositionCompactification
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k))]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Compactification f :=
  letI := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k))
  letI := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (CommRingCat.of k))
  NagataCompactification f

/-- The canonical B-linear coefficient comparison respects geometric composition on finite
constructible pro-etale realizations, for every universal tensor presentation.
Source: Stacks Project, Tags 0F7J and 0GL6
(blueprint: lem-sf-compact-coefficient-composition).

Proof (the ten steps of the node):
1. Finite-type schemes over k are Noetherian and qcqs. Choose compatible compactifications
   by Nagata and lem-weil-pbc-compatible-compactification-triangle. Open extension and
   proper pushforward preserve the finite-Tor constructible domain (lem-trf-open-ctf,
   cor-sf-direct-image-ctf-proetale), so q_g is defined at F_f K.
2. Use lem-sf-flat-model and lem-sf-reduction-flat-model: bounded flat representatives
   stay bounded and flat under nonflat reduction. Finite tensor preserves constructible
   cohomology; constructible origin and full faithfulness of thm-weil-pbc-site-comparison
   reflect etale constructibility and lem-sf-comparison-tor-amplitude reflects the interval.
3. Normalize q as the proper counit mate followed by the open unit mate, as in
   lem-fix-compact-support-coefficient-change. The maps are B-linear universal adjuncts.
4. Inverse-image coefficient identifications compose on K-flat pure tensors. Apply
   lem-weil-pbc-mate-pasting to obtain the proper and open composition identities.
5. Paste the same coefficient squares with the cartesian proper/open inverse-image
   square. Taking mates gives the mixed-interchange coefficient identity.
6. Transpose that identity under the open adjunction, use the open unit identities,
   and cancel the invertible restriction exchange (lem-amb-unbounded-proper-open-interchange).
7. For noncartesian refinements use def-weil-pbc-proper-open-comparison: its exchange,
   open base-change and clopen-section factors all commute with coefficients. Transpose
   and use the universal tensor bijection to obtain refinement compatibility in D(B).
8. Expand the canonical compositor using lem-amb-unbounded-compact-support-comparisons
   or lem-amb-etale-compact-comparisons. Substitute the proper, open and mixed identities
   of steps 4--6, and cancel the refinement factors from step 7.
9. The remaining two paths are exactly the displayed equality with the stated endpoints.
10. Transport through the unit/counit-normalized compactification site comparison,
   lem-sf-class-compact-support-comparison and lem-sf-proper-open-comparison-site-normalization.
   Its three factors respect the same coefficient squares; full faithfulness reflects
   the ordinary-etale equation. No exceptional adjunction or faithfulness of scalar
   restriction in the derived category is used.
-/
theorem finiteCoefficient_compactSupport_composition
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ+) (hmn : n ≤ m)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [Z.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (CommRingCat.of D.k))] [g.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :
    letI := (ProEtale.finiteCompositionCompactification D.k f).hasCompactification
    letI := (ProEtale.finiteCompositionCompactification D.k g).hasCompactification
    letI := (ProEtale.finiteCompositionCompactification D.k (f ≫ g)).hasCompactification
    ∀ (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)))))
    (K₀ : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)))))
    (hK₀ : WeilConjectures.finiteTorConstructibleEtale l E m m.property X K₀.obj)
    (e : (comparisonUpperStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E m))) X).mapDerivedCategory.obj K₀.obj ≅ K)
    (M : CoefficientTensorModel (finiteCompositionReduction l E m n hmn) X K)
    (N : CoefficientTensorModel (finiteCompositionReduction l E m n hmn) Y
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m))) f).obj K))
    (P : CoefficientTensorModel (finiteCompositionReduction l E m n hmn) Z
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m))) g).obj ((rightDerivedLowerShriek (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E m))) f).obj K)))
    (S : CoefficientTensorModel (finiteCompositionReduction l E m n hmn) Z
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m))) (f ≫ g)).obj K)),
    P.map S ((originCompositionAmbient (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m)) f g).hom.app
        ⟨K, ⟨K₀.obj, K₀.property, ⟨e⟩⟩⟩) ≫
        compactSupportCoefficientComparison (HasCompactification.compactification (f ≫ g)) M S =
      compactSupportCoefficientComparison (HasCompactification.compactification g) N P ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E n))) g).map
          (compactSupportCoefficientComparison (HasCompactification.compactification f) M N) ≫
        (originCompositionAmbient (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E n)) f g).hom.app
          ⟨M.obj, M.origin_of_etale_finiteTor l E m n n.property hmn K₀ hK₀ e⟩ := by
  sorry

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale

/-- The same composition square on the small ordinary-etale site. All tensor units
are universal in the ambient derived categories, so nonflat reductions are included.
Source: Stacks Project, Tags 0F7J and 0GL6
(blueprint: lem-sf-compact-coefficient-composition).

Proof (the ten steps of the node):
1. Finite-type schemes over k are Noetherian and qcqs. Choose compatible compactifications
   by Nagata and lem-weil-pbc-compatible-compactification-triangle. Open extension and
   proper pushforward preserve the finite-Tor constructible domain (lem-trf-open-ctf,
   cor-sf-direct-image-ctf-proetale), so q_g is defined at F_f K.
2. Use lem-sf-flat-model and lem-sf-reduction-flat-model: bounded flat representatives
   stay bounded and flat under nonflat reduction. Finite tensor preserves constructible
   cohomology; constructible origin and full faithfulness of thm-weil-pbc-site-comparison
   reflect etale constructibility and lem-sf-comparison-tor-amplitude reflects the interval.
3. Normalize q as the proper counit mate followed by the open unit mate, as in
   lem-fix-compact-support-coefficient-change. The maps are B-linear universal adjuncts.
4. Inverse-image coefficient identifications compose on K-flat pure tensors. Apply
   lem-weil-pbc-mate-pasting to obtain the proper and open composition identities.
5. Paste the same coefficient squares with the cartesian proper/open inverse-image
   square. Taking mates gives the mixed-interchange coefficient identity.
6. Transpose that identity under the open adjunction, use the open unit identities,
   and cancel the invertible restriction exchange (lem-amb-unbounded-proper-open-interchange).
7. For noncartesian refinements use def-weil-pbc-proper-open-comparison: its exchange,
   open base-change and clopen-section factors all commute with coefficients. Transpose
   and use the universal tensor bijection to obtain refinement compatibility in D(B).
8. Expand the canonical compositor using lem-amb-unbounded-compact-support-comparisons
   or lem-amb-etale-compact-comparisons. Substitute the proper, open and mixed identities
   of steps 4--6, and cancel the refinement factors from step 7.
9. The remaining two paths are exactly the displayed equality with the stated endpoints.
10. Transport through the unit/counit-normalized compactification site comparison,
   lem-sf-class-compact-support-comparison and lem-sf-proper-open-comparison-site-normalization.
   Its three factors respect the same coefficient squares; full faithfulness reflects
   the ordinary-etale equation. No exceptional adjunction or faithfulness of scalar
   restriction in the derived category is used.
-/
theorem finiteCoefficient_compactSupport_composition
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ+) (hmn : n ≤ m)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [Z.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (CommRingCat.of D.k))] [g.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :
    letI := (ProEtale.finiteCompositionCompactification D.k f).hasCompactification
    letI := (ProEtale.finiteCompositionCompactification D.k g).hasCompactification
    letI := (ProEtale.finiteCompositionCompactification D.k (f ≫ g)).hasCompactification
    ∀ (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m)))))
    (_hK : WeilConjectures.finiteTorConstructibleEtale l E m m.property X K.obj)
    (M : CoefficientTensorModel (ProEtale.finiteCompositionReduction l E m n hmn) X K)
    (N : CoefficientTensorModel (ProEtale.finiteCompositionReduction l E m n hmn) Y
      ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m))) f).obj K))
    (P : CoefficientTensorModel (ProEtale.finiteCompositionReduction l E m n hmn) Z
      ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m))) g).obj
        ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m))) f).obj K)))
    (S : CoefficientTensorModel (ProEtale.finiteCompositionReduction l E m n hmn) Z
      ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m))) (f ≫ g)).obj K)),
    P.map S ((rightDerivedLowerShriekPlusCompIso (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E m)) f g).hom.app K) ≫
        compactSupportCoefficientComparisonPlus
          (HasCompactification.compactification (f ≫ g)) M S =
      compactSupportCoefficientComparisonPlus (HasCompactification.compactification g) N P ≫
        (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E n))) g).map
          (compactSupportCoefficientComparisonPlus
            (HasCompactification.compactification f) M N) ≫
        (rightDerivedLowerShriekPlusCompIso (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E n)) f g).hom.app M.obj := by
  sorry

end AlgebraicGeometry.Etale
