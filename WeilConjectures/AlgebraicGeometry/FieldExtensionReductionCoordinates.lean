/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystemModels
public import WeilConjectures.AlgebraicGeometry.FieldExtensionIntegralCoordinates
public import WeilConjectures.AlgebraicGeometry.FieldScalarNormalizedData
public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerData
public import WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison

import WeilConjectures.NumberTheory.Padics.LocalFieldIntegralBasis
import WeilConjectures.AlgebraicGeometry.FieldScalarSystemData
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.AlgebraicGeometry.CofinalCoefficientProjectionCocone
import WeilConjectures.CategoryTheory.SystemRingedSequenceSite
import WeilConjectures.CategoryTheory.SystemScalarModel
import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.ConstantFiniteFreePresentationExtension
import WeilConjectures.CategoryTheory.SiteConstantModuleHomSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIsoSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherenceSupplement
import WeilConjectures.CategoryTheory.FiniteFreeScalarCoordinates
import WeilConjectures.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
import WeilConjectures.AlgebraicGeometry.FiniteFreeScalarExtension
import WeilConjectures.AlgebraicGeometry.SiteDerivedTensorRestriction
import WeilConjectures.AlgebraicGeometry.FiniteFreeTensorCtf
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.ProEtalePointPullbackSupplement
import WeilConjectures.Topology.ContinuousMapCondensedRingSupplement
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.FintypeCat
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Monoidal.Mon
import WeilConjectures.AlgebraicGeometry.FieldScalarReductionData
import WeilConjectures.Algebra.Homology.ScalarHomExtensionKFlat

/-! # Canonical integral coordinates for an arbitrary reduction presentation

Source:
literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.proof.md,
paragraph (1), first sentence after the finite-free reduction formula
(blueprint: lem-route-field-extension-reduction-coordinates)

## Main statement

This theorem constructs the normalized integral-coordinate data for the supplied reduction
presentations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExtensionTowers

/-- Canonical integral coordinates for the supplied arbitrary reduction presentations.
Source:
literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.proof.md,
paragraph (1), first sentence after the finite-free reduction formula.
(blueprint: lem-route-field-extension-reduction-coordinates).

Proof plan for stage 3:
Step 1:
  Write A=O_E, B=O_F, r=[F:E], A_n=A/(ell^(n+1)), B_n=B/(ell^(n+1)), and write R_A,R_B for
  the two section-ring sheaves. Choose a single integral basis b_1,...,b_r of B over A. Its
  reductions form an A_n-basis of B_n: the basis isomorphism A^r→B carries ell^(n+1)A^r
  exactly onto ell^(n+1)B, so it descends to A_n^r≅B_n. In particular this uses ell-powers
  on both sides, not independently chosen uniformizer powers. The inclusion induces
  i_n:A_n→B_n by [a]↦[i(a)]; every quotient square commutes by evaluation on a residue
  class.
  Uses: lem-sfb-local-field-integral-basis.

Step 2:
  Let a: R_A≅Rhat_E and b:R_B≅Rhat_F be the supplied coefficient isomorphisms. Put
  c.integral = a.hom followed by the actual completed inclusion ι̂ followed by b.inv, and
  c.tower_n=(i_n)_T. By the definition of the reduction data, the ell-power projections of
  RA,RB are a.hom (resp. b.hom) followed by the canonical ell-power projections
  β^E_N:Rhat_E→(A_{N-1})_T, β^F_N:Rhat_F→(B_{N-1})_T (N=n+1). The completed inclusion ι̂ is
  fixed by the UNIFORMIZER-level squares δ^F_j∘ι̂ = (O_E/ϖ_E^j→O_F/ϖ_F^j)_T∘δ^E_j, so the
  ell-power square needs the cofinality bridge. Write ell=u_Eϖ_E^{e_E}=u_Fϖ_F^{e_F} (DVR
  factorization, e_E,e_F≥1). Take j=e_F N. Since ell^N O_F=ϖ_F^{j}O_F, the cocone map
  q^F_{N,j}:(B_{N-1})_T→(O_F/ϖ_F^j)_T is an isomorphism with q^F_{N,j}β^F_N=δ^F_j. Hence
  β^F_N∘ι̂ = (q^F_{N,j})^{-1}∘δ^F_j∘ι̂ = (q^F_{N,j})^{-1}∘(O_E/ϖ_E^j→O_F/ϖ_F^j)_T∘δ^E_j.
  Since j=e_F N≥e_E N=:k and ell^N O_E=ϖ_E^k O_E, the cocone map q^E_{N,k} is an isomorphism
  and the cocone equalities give β^E_N=(q^E_{N,k})^{-1}∘d^E_{j,k}∘δ^E_j, and the composite
  ring maps O_E/ϖ_E^j→O_F/ell^N through either path send [x] to [ι(x)]; so
  β^F_N∘ι̂=(i_{N-1})_T∘β^E_N. Conjugating by a and b gives
  projection_n∘c.integral=(i_n)_T∘projection_n, the integral_projection field. Thus the
  quotient, quotient_mk, tower, tower_app and integral_projection fields of Coefficients
  hold. Commutativity for all quotient transitions follows on residue classes, and then by
  constant sheafification.
  Uses: def-sp-reduction-tower-data, def-sp-field-scalar-system-data,
  lem-weil-finite-free-completed-scalar-comparison, lem-weil-l-adic-extension-integers-dvr,
  lem-sp-cofinal-coefficient-projection-cocone.

Step 3:
  Use the ringed sequence site and its explicit equivalence with strict systems. The base
  small pro-etale site and this sequence site are essentially small in the module universe
  u+1 (scheme morphisms may lie in u). Apply the normalized scalar model to c.tower on that
  site, and transport along the supplied DA,DB strict-system equivalences. On local
  generators the resulting ordinary functor H sends M_n to M_n⊗_(A_n)B_n and a transition
  n→m to x⊗s↦t_nm(x)⊗q_nm(s). This respects balancing because the coefficient quotient
  squares commute; identities and composites hold on generators. Use the given level scalar
  models by the unique adjunction comparison carrying their units 1⊗x to 1⊗x. Its inverse
  has the same generator formula, so H.level and every H.transition have precisely the
  recorded normalization.
  Uses: lem-pur-system-ringed-sequence-site, lem-pur-system-scalar-model,
  lem-coef-semilinear-derived-sections.

Step 4:
  Define H.restriction by keeping every module section and transition and restricting its
  coefficient action along c.tower. It is additive and exact: restriction of sheaf
  coefficients is exact, and exactness of systems is componentwise. Sheafify the chosen
  isomorphisms A_n^r≅B_n, using exact constant-module sheafification and its finite-power
  comparison. The finite-free scalar-coordinate lemma then gives
  M^r≅H.restriction(H.ordinary M), with column i equal to x↦x⊗bar(b_i). Its inverse takes
  x⊗s to (q_i(s)x)_i. Since q_nm(bar(b_i))=bar(b_i), these maps commute with every
  transition and define a natural isomorphism of WHOLE systems. Restriction is faithful and
  reflects exactness, so this finite-power formula proves H.ordinary additive and exact as
  well.
  Uses: lem-pur-sheaf-ring-coefficient-ordinary-adjunction, lem-coef-semilinear-derived-sections,
  lem-sfb-constant-finite-free-presentation-extension, lem-sfb-finite-free-scalar-coordinates.

Step 5:
  Take H.derived to be the exact induced derived functor of H.ordinary, with its termwise
  localization factor as H.counit. Exact localization is a universal left-derived pair and
  its comparison is invertible for EVERY complex. The derived level isomorphisms are those
  of the scalar model, identified with H.derived by uniqueness of universal left-derived
  functors. Localizing the whole-system coordinate isomorphism of step 4 yields H.derived
  followed by derived restriction ≅ the finite-power functor. No evaluation functor is being
  used to detect equality of morphisms.
  Uses: lem-weil-pbc-exact-functor-derived-factorization,
  lem-weil-pbc-exact-functor-derived-functor, lem-sfb-exact-derived-natural-iso,
  lem-coef-semilinear-derived-sections.

Step 6:
  For a normalized K and n≥m the normalization map for H.derived(K) is the composite
  (K_n⊗^L_(A_n)B_n)⊗^L_(B_n)B_m ≅ K_n⊗^L_(A_n)B_m ≅ (K_n⊗^L_(A_n)A_m)⊗^L_(A_m)B_m →
  K_m⊗^L_(A_m)B_m. Its last arrow is scalar extension of the normalization isomorphism for
  K. This is the actual transition adjunct: on K-flat representatives both routes multiply
  coefficients and insert one, and the successive-scalar normalization identifies their
  units and iterated comparisons. The maps originate on whole systems in step 3, so this
  proves normalization without claiming evaluation detects equality.
  Uses: lem-sfb-successive-derived-quotient-normalization, lem-coef-semilinear-derived-sections.

Step 7:
  The same prescribed cohomological interval [a,b] is retained: after exact faithful
  restriction, each extended level complex is the r-fold power of the original one, so its
  homology vanishes wherever the original homology vanishes. The same prescribed Tor
  interval is retained: for any B_n-module N, the derived tensor-restriction isomorphism
  identifies K_n⊗^L_(A_n)Res(N) with Res((K_n⊗^L_(A_n)B_n)⊗^L_(B_n)N) in D(A_n), naturally
  in N; since restriction is exact and faithful, the homology of the latter vanishes outside
  [a,b] by the original Tor bound. Finite quotient rings and the basis of step 1 satisfy the
  finite-free constructibility lemma on ANY scheme T, so each extended level remains bounded
  constructible of finite Tor amplitude. Together with step 6 and these unchanged common
  intervals this gives H.normalized, H.support_preserved and H.tor_preserved. No qcqs,
  Noetherian or finite-type assumption on T has been introduced.
  Uses: lem-pur-finite-free-scalar-extension, lem-trf-site-derived-tensor-restriction,
  lem-sfb-successive-derived-quotient-normalization, lem-coef-finite-free-tensor-ctf,
  def-sp-field-scalar-system-data.

Step 8:
  Construct the completed basis from the SAME b_i, rather than selecting a second finite-
  free presentation. In each coefficient field ell=u·varpi^e with e>0: use the DVR
  factorization of ell, its nonzero image and |ell|<1. Thus the ell-power ideals are cofinal
  with uniformizer powers. The completed ring identification gives Rhat_E≅lim_n(A_n)_T and
  Rhat_F≅lim_n(B_n)_T, with the ell-power projections β as limit projections (cocone lemma,
  as in step 2). Explicitly a compatible family over the cofinal ell-powers gives its
  component at varpi^m by choosing e(n+1)≥m and reducing; compatibility makes this
  independent of n. The basis maps (A_n)_T^r≅(B_n)_T commute with reduction, so their
  inverse limits give Rhat_E^r≅Res Rhat_F, the restriction being along ι̂ because ι̂ is the
  limit of the (i_n)_T by the square of step 2; finite powers commute with these limits by
  their tuple universal property. Conjugate by a,b to obtain R_A^r≅Res_c R_B. Column i sends
  1 to b.inv of the completed constant b_i, exactly integralConstant in the record. This
  supplies Coordinates.integral; step 5 supplies Coordinates.derived.
  Uses: lem-weil-l-adic-extension-integers-dvr, det-prop-sfb-qlbar-colimit-x-integral-limit,
  lem-sfb-constant-finite-free-presentation-extension, def-sp-field-scalar-reduction-data,
  lem-sp-cofinal-coefficient-projection-cocone.

Step 9:
  Let C be the recorded normalized scalar model along c.integral. The completed basis of
  step 8 and finite-free scalar coordinates show that C is exact: its faithful restriction
  is a finite power. Consequently C.model.T and the exact derived functor of C.model.E are
  uniquely isomorphic preserving their universal counits. Its universal counit computes
  every cochain complex. The same holds for the ordinary/derived completed scalar model, by
  finite freeness of the actual completed inclusion. We shall retain these specified
  counits, not choose unrelated exact-localization factors.
  Uses: lem-pur-system-scalar-model, lem-sfb-finite-free-scalar-coordinates,
  lem-weil-finite-free-completed-scalar-comparison, lem-weil-pbc-exact-functor-derived-functor.

Step 10:
  Construct the ordinary reduction comparison C.E followed by RB.ordinary ≅ RA.ordinary
  followed by H.ordinary. At level n its forward map is (x⊗s)⊗b_n ↦ (x⊗1)⊗(p_B,n(s)b_n), and
  its inverse is (x⊗a_n)⊗b_n ↦ (x⊗1)⊗(i_n(a_n)b_n). The projection square of step 2 gives
  precisely the balancing relation over R_A. The two composites are identities: move s,
  respectively a_n, into the last factor using the tensor balancing relation. These are
  morphisms of sheafified tensors, by their tensor universal property; arbitrary tensor-
  sheaf sections need only be locally generated. Naturality in modules and vertical
  restrictions follows from the formulas. For n→m, reducing p_B,n(s)b_n gives
  p_B,m(s)q_nm(b_n), and reducing i_n(a_n)b_n gives i_m(q_nm(a_n))q_nm(b_n). Hence the maps
  commute with every transition BEFORE localization and give OrdinaryComparison with exactly
  both specified generator formulas.
  Uses: def-sp-reduction-tower-data, def-sp-field-scalar-reduction-data,
  lem-pur-sheaf-ring-coefficient-ordinary-adjunction,
  lem-sfb-successive-derived-quotient-normalization.

Step 11:
  Pass the comparison of step 10 termwise to cochains of WHOLE strict systems. For a K-flat
  R_A-complex P, C.E(P) is K-flat over R_B by scalar-extension preservation of K-flatness.
  Thus RA.counit_P, RB.counit_(C.E P), and C.model.ε_P are isomorphisms; H.counit is an
  isomorphism on every complex by step 5. These give two natural comparison transformations,
  one from C.T followed by RB.red and one from RA.red followed by H.derived, to the
  localized termwise ordinary composites of step 10. Both are invertible on K-flat P. Every
  input complex has a K-flat resolution; the source and target small-site and module
  universes are fixed as in step 3.
  Uses: lem-sfb-scalar-extension-kflat, lem-pc-kflat-resolution, def-sp-reduction-tower-data,
  def-sp-field-scalar-reduction-data.

Step 12:
  Here is the localization argument for these TWO composite functors, not just their
  evaluations. Let F be cochain ordinary C.E then RB.ordinary, localized in the target
  whole-system derived category. It factors through the homotopy category and is
  triangulated, since additive termwise functors commute with shifts and mapping cones. On a
  quasi-isomorphism between K-flat inputs, the first composite counit of step 11 is
  invertible; naturality and inversion by the derived composite imply that F inverts that
  quasi-isomorphism. Apply the K-flat-class left-derived criterion to F and K-flat
  resolutions, obtaining a universal pair (LF,ε). Identify the second ordinary composite
  with F by the inverse of step 10. Each comparison of step 11 induces a map from its
  derived composite to LF by universality. On a K-flat P this map is ε_P^(-1) times that
  composite counit, hence invertible. Every derived object is represented by a K-flat P, so
  both maps are natural isomorphisms everywhere. Inverting the second and composing with the
  first yields the required whole-system derived comparison. The universal counit equality
  says exactly: isoDerived_QP followed by H.derived(RA.counit_P) and H.counit_(RA.ordinary
  P) equals RB.red(C.ε_P), then RB.counit_(C.E P), then localization of the cochain map in
  step 10. In particular this gives ReductionComparison.representative for every K-flat P,
  with no separate levelwise equality argument.
  Uses: lem-pur-left-derived-from-kflat-class, lem-pc-kflat-resolution,
  def-sp-field-scalar-reduction-data.

Step 13:
  Assemble c from steps 1–2, H from steps 3–7, Coordinates from steps 5 and 8, and
  ReductionComparison from steps 10–12 into ScalarData. This is the record for ONE
  inclusion; neither the Family record nor any independent identity/successive choice is
  needed. Thus we have constructed all four components of IntegralCoordinates.data rather
  than assuming that a normalized-data definition asserts existence.
  Uses: def-sp-field-scalar-normalized-data, def-sp-field-scalar-system-data,
  def-sp-field-scalar-reduction-data.

Step 14:
  For a completed E-module M define integralOrdinary on local generators by s⊗x ↦
  b.inv(s)⊗x, where x on the right is restricted along a.hom. Its inverse sends t⊗x to
  b.hom(t)⊗x. The conjugation formula c.integral=b.inv∘inclusion∘a.hom proves balancing:
  moving a section z of R_A between factors has identical images, since
  b.inv(inclusion(a.hom(z)))=c.integral(z). The inverse identities follow from b.hom b.inv=1
  and b.inv b.hom=1. Sheafified tensor adjunctions therefore supply natural module-sheaf
  isomorphisms with exactly these formulas, which are the integralOrdinary_sections field.
  The equality for the coefficient field is the definition in step 2.
  Uses: lem-pur-sheaf-ring-coefficient-ordinary-adjunction,
  def-sp-field-extension-integral-coordinates.

Step 15:
  Both ordinary composite functors in step 14 are exact (step 9 and exact scalar
  restriction). Derive their natural isomorphism by exact localization. Identify its two
  sides with completedDerivedScalarExtension followed by derived restriction along b, and
  derived restriction along a followed by C.model.T, using their universal counits from step
  9. The defining exact-localization equation is valid on EVERY cochain Q. Written with
  these recorded factors, it says ordinaryDerived_QQ then C.T of restriction_a factor then
  C.ε_(restriction_a Q) equals restriction_b of completedScalarCounit_Q then the
  restriction_b factor then Q of the termwise integralOrdinary map. This is precisely
  ordinaryDerived_rep, in its specified direction and with its specified counits. Uniqueness
  of universal left-derived pairs makes the identifications respect these counits, so the
  equation is not inferred from evaluated components.
  Uses: lem-sfb-exact-derived-natural-iso, lem-weil-pbc-exact-functor-derived-functor,
  def-sp-field-extension-integral-coordinates.

Step 16:
  Use ScalarData of step 13 as data, the defining coefficient equality of step 2 as
  coefficient, the natural isomorphism and generator equation of step 14 as integralOrdinary
  and integralOrdinary_sections, and step 15 as ordinaryDerived and ordinaryDerived_rep.
  These are all fields of IntegralCoordinates P D E F h T RA RB. Their constructor supplies
  the required object for the given presentations and arbitrary scheme T.
  Uses: def-sp-field-extension-integral-coordinates.

The supplied presentations RA and RB are fixed, not existential; this theorem constructs
only the IntegralCoordinates object for the fixed P, D, E, F, h, T, RA and RB.
-/
theorem field_extension_reduction_coordinates (P : PurityFiniteSetting.{u})
    (D : FieldShriekSystem.Models P) (E F : FieldShriekSystem.Index P) (h : E ≤ F)
    (T : Scheme.{u})
    (RA : SpReductionTower P.coefficients.l E.val T ((D.coordinates E).abelian T))
    (RB : SpReductionTower P.coefficients.l F.val T ((D.coordinates F).abelian T)) :
    Nonempty (IntegralCoordinates P D E F h T RA RB) := by sorry

end AlgebraicGeometry.ProEtale.FieldExtensionTowers
