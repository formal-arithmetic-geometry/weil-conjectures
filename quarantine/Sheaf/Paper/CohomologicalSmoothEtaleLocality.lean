/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Sheaf.Paper.CohomologicalSmoothnessComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

import Sheaf.Paper.PurityFiniteSetting
import WeilConjectures.Compactification.NagataCompactification
import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Paper.PbcActualScalarPullback
import Sheaf.Paper.PurityAffineChartBounds
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.FiniteCoefficientTensorCtf
import Sheaf.Algebra.Homology.DerivedTensor
import Sheaf.Paper.FiniteFieldFiber
import Sheaf.Paper.FiniteTorAmplitude
import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.Paper.SfDerivedComplete
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.Paper.ComparisonTorAmplitude
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.ConstructibleSheaf.Defs
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact
import Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.FiniteConstructibleHom
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import WeilConjectures.SixFunctors.Etale.Derived.Hom
import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.ProEtaleStalkConservative
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.EtaleIsoDescent
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.FiniteTorStability
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver

/-!
# Source-etale locality of cohomological smoothness

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-etale-locality (blueprint: lem-pur-co-smooth-etale-locality).

The two statements give descent from a surjective etale source cover and the
cohomological smoothness and untwisted dualizing object of every etale map in the setting.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale

/-- Source-etale locality of cohomological smoothness in the finite purity setting.
Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-etale-locality, first assertion
(blueprint: lem-pur-co-smooth-etale-locality).

Proof:
1. Work with the finite ring A_{E,n} of P. Finite-type schemes over its field are
Noetherian. Nagata gives compactifications. The constructible exceptional functors
are transported from the ordinary etale adjoints, and their images and all tensors
and pullbacks occurring below have the stated bounded constructible finite-Tor domains.
This uses finite-type exceptional preservation, constructible etale origins, site
comparison, finite compact-support projection, finite-level base change, flat models,
and the dimension bound, exactly as in Step 1 of the DAG proof. No separatedness of Y
or of an arbitrary change-of-base scheme is used.
2. Normalize etale compact supports by the canonical sum-extension comparison of
lem-sfb-quasifinite-compact-support-exact. The graph-normalized compatibility of
lem-pur-etale-support-map-compatibility identifies the actual exchange and projection
maps with sum-extension exchange and projection. Transfer the sum/evaluation adjunction:
its right adjoint is restriction, its counit is evaluation, and its dualizing object
is the coefficient unit. The counit equations give the canonical tensor and base-change
mates, including evaluation after restriction to each pulled-back lift.
3. Compose this adjunction with that of f. The normalized compact-support compositor
and etale compact-support comparisons give canonical rho_K: u* f!K = (fu)!K,
with composite counit epsilon_f composed with Rf! epsilon_u. At the unit this gives
rho_A: u* omega_f = omega_fu. Here exclamation marks in f!K denote exceptional inverse
image, and Rf! denotes compact-support direct image.
4. Expand the transpose defining theta, using projection composition and mate pasting.
Both transposes are inverse projection followed by the composite counit; the etale
sum-projection identity gives rho_K composed with u*theta_f,K equal to theta_fu,K
composed with (1 tensor rho_A). Surjectivity and etale isomorphism detection descend
the invertibility of theta_fu,K to that of theta_f,K.
5. Set M = omega_f and Mdual = RHom(M,A_X), with its canonical evaluation.
Finite constructible Hom puts Mdual in Dctf. Restriction commutes with RHom and tensor,
so evaluation pulls back to evaluation for the invertible omega_fu, hence is an
isomorphism there. Etale isomorphism detection descends evaluation; tensor symmetry
gives its reverse ordering. Thus Mdual is a global two-sided tensor inverse.
6. After any base change Y' to Y, the pulled-back singleton cover u' is surjective
etale. Pasting of the actual compact-support exchanges and the composite counit gives
rho'_A composed with u'* beta_f,g equal to beta_fu,g composed with h_U* rho_A.
The latter is invertible. Cover detection for pro-etale complexes descends this to
beta_f,g, even when X' or Y' is nonseparated.
7. Steps 5, 4 and 6 give the three clauses of IsCohomologicallySmooth for f.
The empty scheme is allowed: its module category is zero and its unit is zero;
a surjective map with empty source also has empty target. No object is descended.
-/
theorem isCohomologicallySmooth_of_surjective_etale
    (P : WeilConjectures.PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))] [U.IsSeparated] [X.IsSeparated]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))] [Etale e]
    [QuasiCompact e] [Surjective e]
    (h : IsCohomologicallySmoothCompared P (e ≫ f)) : IsCohomologicallySmoothCompared P f := by
  sorry

/-- Every etale map in the finite purity setting is cohomologically smooth and has
untwisted relative dualizing object.
Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-etale-locality, final assertion
(blueprint: lem-pur-co-smooth-etale-locality).

Proof: use Step 2 of the node proof. Canonical compact-support comparison identifies
Re_! with exact etale sum extension, including its specified projection and base-change
maps by lem-pur-etale-support-map-compatibility. Transfer its sum/evaluation adjunction
to identify Re^! with e*. Its value on the coefficient unit is the coefficient unit,
which is tensor-invertible with itself as inverse. Substituting the sum counit and
projection into the defining transpose of theta gives the unit isomorphism; at each
lift the composite is scalar multiplication. Substituting the sum exchange and
counit into the transpose of beta gives the canonical pullback identification of the
unit. These calculations remain valid after every allowed base change. Etale-origin
comparison transports the actual maps and their counits, so all three clauses of
IsCohomologicallySmooth hold for the specified pro-etale functors. Surjectivity,
absolute separatedness of the schemes, and nonemptiness are not required.
-/
theorem isCohomologicallySmooth_etale_and_dualizing
    (P : WeilConjectures.PurityFiniteSetting.{u}) {U X : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))] [Etale e]
    [IsSeparated e] [QuasiCompact e] :
    IsCohomologicallySmoothCompared P e ∧
      Nonempty (@comparedDualizing P U X e
        (P.comparedCompactification e (X ↘ Spec (.of P.field.k))).hasCompactification ≅
        𝟙_ (_root_.DerivedCategory
          (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} P.Coefficient)))) := by
  sorry

end AlgebraicGeometry.ProEtale
