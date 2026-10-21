module

public import Sheaf.AlgebraicGeometry.FieldActionCoefficientTransportData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientBasic

import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.ProEtalePointPullback
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.Paper.SheafSliceDerivedComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.Paper.RingedComparisonTensorAdjunction
import Sheaf.CategoryTheory.CondensedActionModule
import Sheaf.Paper.FieldProfiniteGaloisSite
import Sheaf.Paper.CoefficientHeartStratificationDefs
import Sheaf.CategoryTheory.ActionToposGeometricRestriction
import Sheaf.CategoryTheory.InternalActionSitePresentation
import Sheaf.Paper.RingedProjectionFirstShift
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Paper.ProfiniteTestObjectFunctor
import Sheaf.CategoryTheory.RingedPresentationTransport
import Sheaf.Paper.DerivedAdjunctionShift
import Sheaf.Paper.RingedCoefficientProjectionCocycle
import Sheaf.CategoryTheory.RingedDerivedCompositionCocycle
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Field actions and normalized geometric derived sections

Source: Bhatt--Scholze Example 4.1.10, Definition 6.8.3 and Proposition 6.8.4;
main-20261015 direct-images paragraph (3), normalized ordinary derived sections
(blueprint: lem-sfb-field-action-derived-section-transport).

## Main definitions

* `Assertion`: existence of the full compatible field, scalar, geometric and lisse data.

## Main statements

* `field_action_derived_section_transport`: the normalized field-action theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FieldActionTransport

open CondensedGalois

variable (k ks : Type u) [Field k] [Field ks] [Algebra k ks] [IsSepClosure k ks]

/-- The complete field equivalence, all coefficient maps and geometric inputs, and the
finite norm-topology lisse restriction. All categorical structure in this proposition
is asserted to exist; no such data are chosen from mere existence in a definition.
Source: Bhatt--Scholze Example 4.1.10, Definition 6.8.3 and Proposition 6.8.4;
main-20261015, direct-images paragraph (3)
(blueprint: lem-sfb-field-action-derived-section-transport). -/
def Assertion : Prop := by
  refine ∃ h : ∀ R : Coefficients.{u},
    CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks), ?_
  letI (R : Coefficients.{u}) :
    CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks) := h R
  refine ∃ hf : ∀ R : Coefficients.{u}, ForgetData k ks R, ?_
  letI (R : Coefficients.{u}) : ForgetData k ks R := hf R
  refine ∃ e : ∀ R : Coefficients.{u}, FieldData k ks R, ?_
  letI (R : Coefficients.{u}) : (fieldFunctor k ks (e R)).Additive := (e R).geometric.additive
  letI (R : Coefficients.{u}) : (fieldFunctor k ks (e R)).IsEquivalence := (e R).equivalence
  refine ∃ c : ∀ (R R' : Coefficients.{u}) (φ : R ⟶ R'),
    ScalarTransport k ks φ (e R) (e R'), ?_
  refine (∀ R : Coefficients.{u},
    (fieldFunctor k ks (e R)).mapDerivedCategory.IsTExact
      DerivedCategory.TStructure.t DerivedCategory.TStructure.t) ∧ ?_
  refine (∀ (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], ?_) ∧ ?_
  · letI := Scheme.coefficientExtensionNormedField l E
    exact Nonempty (LisseTransport k ks E (e (normCoefficients E)))
  · refine ∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
      (a : X ⟶ Spec (.of k)), ?_
    refine ∃ hp : ∀ R : Coefficients.{u},
      PointAdjunctionData R (geometricScheme.{u} k ks X a), ?_
    letI (R : Coefficients.{u}) : PointAdjunctionData R (geometricScheme.{u} k ks X a) := hp R
    refine ∃ d : ∀ R : Coefficients.{u}, OrdinaryData k ks X a R, ?_
    letI (R : Coefficients.{u}) : (d R).geometric.functor.Additive := (d R).geometric.additive
    letI (R : Coefficients.{u}) {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
        (CondensedRing.upperStar.{u} R.X f).Additive := CondensedRing.upperStar_additive R.X f
    letI (R : Coefficients.{u}) {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
        PreservesFiniteLimits (CondensedRing.upperStar.{u} R.X f) :=
      CondensedRing.preservesFiniteLimits_upperStar R.X f
    letI (R : Coefficients.{u}) {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
        PreservesFiniteColimits (CondensedRing.upperStar.{u} R.X f) :=
      CondensedRing.preservesFiniteColimits_upperStar R.X f
    letI (R : Coefficients.{u}) {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
        (CondensedRing.lowerStar.{u} R.X f).Additive := CondensedRing.lowerStar_additive R.X f
    refine ∃ g : ∀ R : Coefficients.{u}, GeometricTransport k ks X a R (e R) (d R), ?_
    exact ∀ (R R' : Coefficients.{u}) (φ : R ⟶ R'),
      Nonempty (CoefficientTransport k ks X a φ (e R) (e R') (c R R' φ)
        (d R) (d R') (g R) (g R'))

/-- Field-action equivalence, normalized geometric derived sections and coefficient
projections, including the finite-rank norm-continuous lisse equivalence.
Source: Bhatt--Scholze Example 4.1.10, Definition 6.8.3 and Proposition 6.8.4;
main-20261015 direct-images paragraph (3), ordinary derived coefficient normalization
(blueprint: lem-sfb-field-action-derived-section-transport).

Proof plan, following the sixteen steps of the node:
1. Present the qcqs field site by profinite continuous Galois sets using
   lem-sfb-field-profinite-galois-site and lem-pc-fppf-dense-sheaf-equivalence.
   The geometric test is G times P and the arithmetic test is the trivial G-set P.
2. Restrict to free orbits: G times S maps onto S by (g,x) maps to gx. Arrows have the
   formula (g,t) maps to (g b(t),f(t)) and composition (fh,c h*b). Apply
   lem-sfb-action-topos-geometric-restriction to obtain the normalized action equivalence.
3. The kernel pair of G times P to P is G times G times P. Its equalizer identifies
   arithmetic sections with sections fixed after all profinite base changes. Adjoint
   uniqueness identifies point pullback with trivial inflation, including ring objects.
   Apply lem-weil-pbc-ringed-presentation-transport and
   lem-sfb-internal-action-site-presentation, using the recorded internal/section-module
   equivalence, to obtain the exact additive field module equivalence.
4. Forgetting creates kernels and cokernels and detects zero objects. Cohomology and
   cones then give derived conservativity. The exact field equivalence and its inverse
   commute with homology, so their termwise derived equivalence is t-exact.
5. Scalar restriction changes only the ring action. Its exact section comparison fixes
   both ordinary scalar adjunctions: transpose by m maps to 1 tensor m and evaluate by
   r' tensor m maps to r'f(m). The balanced tensor comparison preserves these formulas.
6. The tensor comparison preserves K-flatness, since the exact inverse identifies
   tensoring with every acyclic complex. Localize the same scalar transpositions to
   obtain the derived scalar adjunctions, including units and counits, with no flatness
   hypothesis on the ring map. This is the total-derived counit normalization.
7. By lem-weil-pbc-profinite-test-object-functor, X times_s sbar[P] is X^s[P], including
   all test maps. Thus E_R a_* is the existing equivariant geometric section functor.
   Apply both functors to one K-injective resolution, giving the normalized derived
   object comparison by sk-def-sfb-module-derived-pushpull.
8. Localize the field site at sbar, using lem-weil-proetale-weakly-etale-localization.
   Free objects over G are isomorphic to the projections G times P to G, and their maps
   are the maps of P. Slice restriction therefore forgets the G-action. The coefficient
   identification is lem-sfb-alpha-iso.
9. Apply lem-sbc-ringed-topos-sheaf-slice-derived-comparison at h_sbar and h_Xs.
   Its normalized counit and K-flat tensor comparison identify the slice restriction of
   Ra_* with Ra_s* u^*. The canonical derived composition comparison gives Rp_Xs* u^*.
10. Scalar restriction is ringed direct image on the identity underlying topos.
    lem-weil-pbc-ringed-topoi-derived-pushforward-composition for the identical composites
    fixes the comparisons rho by their derived units, even for nonflat coefficients.
11. Define beta by scalarProjection: transpose K(eta_M) followed by rho. On the field
    side this is the scalar transpose defining chi. Use
    lem-sfb-ringed-comparison-tensor-adjunction to identify rho as the conjugate of the
    derived pullback scalar exchange. The two adjunction triangles leave exactly the
    scalar extension of the geometric counit, the projection specified by
    lem-pur-ringed-coefficient-projection-cocycle. Transport gives chi equals beta.
12. Restrict this counit formula to the two slices. The normalized slice and composition
    comparisons preserve the counit and scalar exchange. By
    lem-sfb-derived-composition-adjunction-normalization and
    lem-weil-pbc-ringed-projection-mate-exact, forgotten beta is pointProjection.
    The scalar/geometric conjugacy also identifies the R-linear and R'-linear forms.
13. Every comparison is a restriction or an adjunction/derived-unit comparison. Their
    naturality gives all input-morphism squares; the composition cocycle gives all
    coefficient-restriction squares, by lem-pur-ringed-derived-composition-cocycle.
    Canonical right-derived shifts and lem-weil-pbc-derived-adjunction-shift give the
    shift squares, including the projection by lem-sfb-ringed-projection-first-shift.
14. For finite E/Q_l, Definition 6.8.3 gives the recorded finite locally free predicate.
    On the geometric field site, pull a trivialization back along a point of a nonempty
    profinite covering chart. Thus a lisse module is C(-,E)^n, also for n=0.
15. Evaluate the internal action on id_G and the finite basis to get a continuous matrix
    G to GL_n(E). Conversely such a representation acts pointwise on C(P,W), naturally
    in P. This is exactly the recorded norm-continuous representation category.
16. Morphisms are equivariant E-matrices, which are continuous by
    lem-sfb-finite-dimensional-linear-map-continuous. They act by postcomposition on
    every C(P,W), so the same E_R restricts to the stated lisse equivalence. All
    constructions include the zero module, empty test, and trivial Galois group.
-/
theorem field_action_derived_section_transport : Assertion k ks := by
  sorry


end AlgebraicGeometry.ProEtale.FieldActionTransport
