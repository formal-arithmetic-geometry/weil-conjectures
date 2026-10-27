/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Paper.PurityAffineLineDatum
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Sheaf.CategoryTheory.SiteCohomologyPullback
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.CategoryTheory.DeltaFunctor
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.AlgebraicGeometry.Sites.Gm
import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections
import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula
import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem
import Sheaf.AlgebraicGeometry.StrictlyHenselianConstantCohomology
import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.CohomologyPullbackCanonicalArrows
import WeilConjectures.AlgebraicGeometry.CohomologyPullbackDerivedUnit
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.Paper.KunBcMapOnCohomology
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ComparisonDirectImageCanonicalMate
import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomology
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
import Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
import Sheaf.AlgebraicGeometry.AffinePuncturedLineAlgebra
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.KummerCoefficientBaseChange
import Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.FiniteDirectImageComposition
import Sheaf.Paper.PurityFiniteKummerLevel
import Sheaf.Paper.PurityFiniteSetting
import Sheaf.Paper.SiteComparisonEdgeSection
import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
/-!
# Relative affine-line acyclicity and the actual Kummer generator

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer/prop-pur-gm-relative-kummer.md
(blueprint: prop-pur-gm-relative-kummer).

All objects below are actual finite-coefficient module sheaves on the small pro-etale
site. The maps are the units and canonical exchange mates of the published functors.
The generator is homology of the adjoint of the coordinate's actual Kummer boundary.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- Canonical pullback on constants, with comparison inverse images included.
Source: blueprint sk-def-purity-conv (blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def constantPullback (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj (P.constant Y) ⟶
      P.constant X :=
  (ProEtale.comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) f).hom.app (P.constantEtale Y) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) f).hom.app
          (ModuleCat.of P.Coefficient P.Coefficient))

/-- Canonical pullback on the finite twist, with comparison inverse images included.
Source: blueprint sk-def-purity-conv (blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def twistPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj (P.twist h Y) ⟶
      P.twist h X :=
  (ProEtale.comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) f).hom.app (P.twistEtale h Y) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
        (P.twistEtalePullback h f)

/-- Pullback of a coefficient object in the derived category. This is the standard
single-complex comparison followed by the canonical map on the actual sheaves.
Source: blueprint sk-def-purity-conv (blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def derivedCoefficientPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) (twisted : Bool) :
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor).obj
      (P.derivedSheaf h Y twisted) ⟶ P.derivedSheaf h X twisted :=
  (ProEtale.singleFunctorCompLeftDerivedUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) f).hom.app (P.coefficientSheaf h Y twisted) ≫
      (DerivedCategory.singleFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) 0).map
          (match twisted with
            | true => P.twistPullback h f
            | false => P.constantPullback f)

/-- The canonical unit with coefficients identified by their canonical pullback map.
Source: blueprint sk-prop-a1-kummer, clauses (1) and (2)
(blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def relativeUnit (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) (twisted : Bool) :
    P.derivedSheaf h Y twisted ⟶
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor.obj
        (P.derivedSheaf h X twisted) :=
  (ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} P.Coefficient) f).unit.app (P.derivedSheaf h Y twisted) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor.map
        (P.derivedCoefficientPullback h f twisted)

/-- The edge-section map, obtained by transposing the actual coordinate class and
taking H0, followed by the standard H0(K[1])=H1(K) comparison. It is the A-linear map
whose value on 1 is the Leray edge image of kappa(t).
Source: blueprint sk-prop-a1-kummer, clause (2)
(blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def kummerGenerator (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) :
    P.constant Y ⟶ (DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 1).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection Y)).rightDerivedFunctor.obj
            (P.derivedSheaf h (Punctured Y) true)) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).inv.app
      (P.constant Y) ≫
    (DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).map
      (((ProEtale.derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) (puncturedProjection Y)).homEquiv _ _
          (P.derivedCoefficientPullback h (puncturedProjection Y) false ≫
            (P.coordinateKummer h Y a).hom)) ≫
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection Y)).rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
            (P.derivedSheaf h (Punctured Y) true)) ≫
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).shiftIso
        (1 : ℤ) 0 1 (add_zero 1)).hom.app
      ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        (puncturedProjection Y)).rightDerivedFunctor.obj (P.derivedSheaf h (Punctured Y) true))

/-- The assertions in clauses (1)-(3), with the actual specified maps. No finite-type
condition is built into this predicate, so it also applies to geometric fibres.
Source: blueprint sk-prop-a1-kummer, clauses (1)-(3)
(blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def RelativeKummerConclusions (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) : Prop :=
  IsIso (P.relativeUnit h (lineProjection Y) false) ∧
  IsIso (P.relativeUnit h (lineProjection Y) true) ∧
  (∀ (m : ℕ), 0 < m → IsZero
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) (m : ℤ)).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (lineProjection Y)).rightDerivedFunctor.obj (P.derivedSheaf h (Line Y) true)))) ∧
  IsIso ((DerivedCategory.homologyFunctor
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).map
      (P.relativeUnit h (puncturedProjection Y) true)) ∧
  IsIso (P.kummerGenerator h Y a) ∧
  ∀ (m : ℕ), 2 ≤ m → IsZero
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) (m : ℤ)).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection Y)).rightDerivedFunctor.obj
            (P.derivedSheaf h (Punctured Y) true)))

/-- Clause (4): naturality of the actual coordinate class and invertibility of the
canonical exchange mates. Their targets use the canonical coefficient pullback
identifications; invertibility is equivalently tested before those identifications.
Source: blueprint sk-prop-a1-kummer, clause (4)
(blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def KummerBaseChangeConclusions (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {Y' Y : Scheme.{u}} (g : Y' ⟶ Y)
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) : Prop :=
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (puncturedMap g)).leftDerivedFunctor.map (P.coordinateKummer h Y a).hom ≫
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (puncturedMap g)).leftDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
        (P.derivedSheaf h (Punctured Y) true) ≫
    (P.derivedCoefficientPullback h (puncturedMap g) true)⟦(1 : ℤ)⟧' =
      P.derivedCoefficientPullback h (puncturedMap g) false ≫
        (P.coordinateKummer h Y' (g ≫ a)).hom ∧
  IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq).app
      (P.derivedSheaf h (Line Y) true)) ∧
  IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
    (puncturedSquare g)).app (P.derivedSheaf h (Punctured Y) true))

/-- The affine line and punctured line over a separated finite-type k-scheme, with
canonical units, the actual Kummer generator, higher vanishing and both kinds of
base change, including geometric points which need not be of finite type.
Source: blueprint sk-prop-a1-kummer, prop-pur-gm-relative-kummer
(blueprint: prop-pur-gm-relative-kummer).

Proof:
1. Put r=ell^(n/e). The finite Kummer level gives rA=0 and A finite free over Z/r.
Since ell differs from p, r is invertible on k-schemes. A primitive r-th root in k
identifies the root line with constant A, compatibly with pullback.
2. Use the natural module/abelian cohomology and higher-direct-image comparisons.
Injective module sheaves are acyclic after forgetting for global sections, so these
comparisons preserve maps, not only abstract isomorphism types. Scalar forgetting
also identifies the canonical exchange and reflects isomorphisms.
3. Inverse image of the Kummer exact sequence, followed by pullback of units, is a
morphism of exact sequences. Naturality of connecting maps proves naturality of the
boundary, and coefficient extension preserves it. In particular t pulls back to t'.
4. Over the algebraically closed base field, both curves have Pic=0. The Kummer long
exact sequence computes H1 as units modulo r-th powers. Affine-line units are k-units;
punctured-line units are k-units times integral powers of t. Thus H1 is zero on the
line and Z/r generated by the actual boundary of t on the punctured line.
5. Constant sections give H0. Affine curve cohomological dimension with exponent r,
not N, kills higher cohomology. Tensor with the finite free Z/r-module A, preserving
the boundary, to obtain the asserted finite-coefficient fibre calculations.
6. For a geometric point of any base B, the strict-henselization stalk formula gives
the cohomology of the curve over Spec O_B^sh. The presheaf description of higher
direct images identifies the germ of the edge section with restriction of kappa(t).
7. Rotate the product square: apply smooth base change to the curve over k and the
affine map Spec O_B^sh to Spec k. Strictly henselian constant cohomology and the
stalk formula show that the pullback unit along the other projection is an
isomorphism. Smoothness is used on the curve over k, not on the strict local base.
8. Composition of derived direct images and its unit identifies the resulting
cohomology comparison with actual restriction from the curve over k. It preserves
constants and, by step 3, the specified coordinate Kummer generator.
9. Geometric stalk conservativity gives the relative degree-zero units, the degree-one
Kummer map, and all the stated vanishing. Cohomological detection of derived
isomorphisms gives affine-line acyclicity. The same primitive-root trivialization
handles the untwisted unit. Restriction through j preserves these constants.
10. The exchange is the canonical adjunction mate. The triangle identity shows its
composite with pullback of the unit is the unit after base change; hence it preserves
constants and is an isomorphism in degree zero.
11. On injective resolutions and their etale restrictions the higher-image exchange
sends a cocycle to its restriction. Naturality of the actual boundary shows its
degree-one map preserves kappa(t), hence is invertible.
12. Both sides have the stated vanishing in all other degrees, including negative
ones. Exact pullback and detection by cohomology prove derived exchange invertible.
The same argument applies to geometric points without a finite-type assumption.
13. Exact etale/pro-etale comparison preserves the classes, and its canonical counit
mate identifies the units and exchanges. Transport all calculations to the small
pro-etale site. Over Spec of an algebraically closed field, the constant-sheaf
comparison with modules identifies these statements with the final fibre calculations. -/
theorem relative_kummer (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))] :
    P.RelativeKummerConclusions h Y (Y ↘ Spec (CommRingCat.of P.field.k)) ∧
    (∀ (Y' : Scheme.{u}) [Y'.Over (Spec (CommRingCat.of P.field.k))]
      [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of P.field.k))]
      [QuasiCompact (Y' ↘ Spec (CommRingCat.of P.field.k))]
      [IsSeparated (Y' ↘ Spec (CommRingCat.of P.field.k))]
      (g : Y' ⟶ Y) [g.IsOver (Spec (CommRingCat.of P.field.k))],
      P.KummerBaseChangeConclusions h g (Y ↘ Spec (CommRingCat.of P.field.k))) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (CommRingCat.of Ω) ⟶ Y),
      P.KummerBaseChangeConclusions h g (Y ↘ Spec (CommRingCat.of P.field.k)) ∧
      P.RelativeKummerConclusions h (Spec (CommRingCat.of Ω))
        (g ≫ Y ↘ Spec (CommRingCat.of P.field.k)) := by
  sorry

end WeilConjectures.PurityFiniteSetting
