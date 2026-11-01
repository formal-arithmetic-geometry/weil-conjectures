/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructure
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCohomologyHom
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.Open.OpenComplementCondition
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Kummer.PurityFiniteKummerLevel
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.Open.OpenComplementCondition
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit
import WeilConjectures.AlgebraicGeometry.SmoothPurity.SiteClosedCounitTransport

/-! # Realization of affine-line supported classes

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
thm-pur-affine-line-orientation.proof.md, first paragraph and final site comparison;
Milne, Etale Cohomology, Theorem 9.4 and Example 9.5
(blueprint: lem-pur-affine-line-boundary-realization).

The comparison maps below use the ordinary etale closed adjoint and the published
identity/proper compactification. All adjunction assertions remain on the etale site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- Finite presentation of the zero section follows by cancellation from its retraction.
Source: affine-line datum, zero section and projection
(blueprint: lem-pur-affine-line-boundary-realization). -/
instance boundaryClosedPresentation (Y : Scheme.{u}) :
    LocallyOfFinitePresentation (zeroSection Y) :=
  letI : LocallyOfFiniteType (lineProjection Y) :=
    inferInstanceAs (LocallyOfFiniteType
      ((AffineSpace (ULift.{u} (Fin 1)) Y) ↘ Y))
  letI : LocallyOfFinitePresentation (zeroSection Y ≫ lineProjection Y) :=
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y).symm ▸
      inferInstanceAs (LocallyOfFinitePresentation (𝟙 Y))
  locallyOfFinitePresentation_of_comp (zeroSection Y) (lineProjection Y)

/-- Exact closed direct image, using the existing finite direct-image theorem.
Source: affine-line orientation proof, closed direct image
(blueprint: lem-pur-affine-line-boundary-realization). -/
instance boundaryClosedExact (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) :
    PreservesFiniteColimits (lowerStar (Modules P) (zeroSection Y)) :=
  preservesFiniteColimits_lowerStar_of_isFinite P.Coefficient (zeroSection Y)

/-- The ordinary etale model of the shifted exceptional value.
Source: affine-line orientation proof, etale-origin qualification
(blueprint: lem-pur-affine-line-boundary-realization). -/
abbrev boundaryEtaleValue (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :=
  ((etClosed P (zeroSection Y)).obj (P.gysinEtaleInput h Y).obj)⟦(2 : ℤ)⟧

/-- The canonical comparison from the ordinary closed adjoint to the transported value,
including the displayed shift. Its unshifted factors are the retraction compositor,
uniqueness of etale right adjoints, and the site-comparison unit.
Source: affine-line orientation proof, site comparison
(blueprint: lem-pur-affine-line-boundary-realization). -/
def boundaryExceptionalComparison (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :
    (nu P Y).obj (P.boundaryEtaleValue h Y) ⟶ P.gysinValue h Y :=
  ((nu P Y).commShiftIso (2 : ℤ)).hom.app _ ≫
    ((nu P Y).map ((collapse P (lineProjection Y) (zeroSection Y)
        (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y)).inv.app _) ≫
      firstComparison P (lineProjection Y) (zeroSection Y)
        (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y)
        (P.gysinEtaleInput h Y))⟦(2 : ℤ)⟧'

/-- The canonical closed direct-image site mate in exact-functor coordinates.
Source: affine-line orientation proof, transported etale maps
(blueprint: lem-pur-affine-line-boundary-realization). -/
def boundaryImageComparison (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (B : DerivedCategory.Plus (EtSheaves P Y)) :
    (nu P (Line Y)).obj
        ((Etale.lowerStar (Modules P) (zeroSection Y)).mapDerivedCategory.obj B.obj) ⟶
      (lowerStar (Modules P) (zeroSection Y)).mapDerivedCategory.obj
        ((nu P Y).obj B.obj) :=
  (nu P (Line Y)).map
      ((Etale.lowerStar (Modules P)
        (zeroSection Y)).rightDerivedFunctorIsoMapDerivedCategory.inv.app B.obj) ≫
    imageComparison P (zeroSection Y) B ≫
    ((lowerStar (Modules P) (zeroSection Y)).rightDerivedFunctorIsoMapDerivedCategory).hom.app
      ((nu P Y).obj B.obj)

/-- The ordinary etale closed counit on the shifted twist, with exact direct-image
and shift comparisons displayed. No pro-etale adjunction is used.
Source: Milne, closed-support adjunction before Theorem 16.7
(blueprint: lem-pur-affine-line-boundary-realization). -/
def boundaryEtaleCounit (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :
    (Etale.lowerStar (Modules P) (zeroSection Y)).mapDerivedCategory.obj
        (P.boundaryEtaleValue h Y) ⟶ (P.gysinEtaleInput h Y).obj⟦(2 : ℤ)⟧ :=
  ((Etale.lowerStar (Modules P) (zeroSection Y)).mapDerivedCategory.commShiftIso
      (2 : ℤ)).hom.app _ ≫
    ((Etale.lowerStar (Modules P) (zeroSection Y)).rightDerivedFunctorIsoMapDerivedCategory.inv.app
        _ ≫
      (Adjunction.ofIsLeftAdjoint
        (Etale.lowerStar (Modules P) (zeroSection Y)).rightDerivedFunctor).counit.app
          (P.gysinEtaleInput h Y).obj)⟦(2 : ℤ)⟧'

/-- The supported-Hom functor isomorphism, with the underived closed image of the unit.
Source: Milne, Theorem 9.4 and Ext description, Example 9.5
(blueprint: lem-pur-affine-line-boundary-realization). -/
abbrev BoundarySupportedHom (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) :=
  (derivedSupportSections (zeroSection Y) P.Coefficient ⋙
      DerivedCategory.Plus.homologyFunctor (Modules P) 2 ⋙
      forget₂ (Modules P) AddCommGrpCat.{u + 1}) ≅
    (DerivedCategory.Plus.ι ⋙ shiftFunctor (ModuleDerivedCategory (Line Y) P.Coefficient) (2 : ℤ) ⋙
      preadditiveCoyoneda.obj
        (op ((DerivedCategory.singleFunctor (ProSheaves P (Line Y)) 0).obj
          ((lowerStar (Modules P) (zeroSection Y)).obj (P.constant Y)))))

/-- The realization and its normalizations. The section-to-support map is precisely the
one in GysinSupportIdentification: the inverse local-class edge followed by supportIso.
The exceptional comparison and counit are fixed by their actual etale maps, and every
realizing morphism has a unique ordinary etale antecedent.
Source: affine-line orientation proof, first paragraph and final site-comparison sentence
(blueprint: lem-pur-affine-line-boundary-realization). -/
def AffineLineBoundaryRealization (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) : Prop :=
  ∃ (χ : P.BoundarySupportedHom Y)
    (hb : DerivedCategory.TStructure.t.plus (P.boundaryEtaleValue h Y))
    (eK : (nu P Y).obj (P.boundaryEtaleValue h Y) ≅ P.gysinValue h Y)
    (d : (nu P (Line Y)).obj
        ((Etale.lowerStar (Modules P) (zeroSection Y)).mapDerivedCategory.obj
          (P.boundaryEtaleValue h Y)) ≅
      (lowerStar (Modules P) (zeroSection Y)).mapDerivedCategory.obj
        ((nu P Y).obj (P.boundaryEtaleValue h Y)))
    (ε : (lowerStar (Modules P) (zeroSection Y)).mapDerivedCategory.obj
        (P.gysinValue h Y) ⟶ (P.gysinInput h Y).obj⟦(2 : ℤ)⟧),
    eK.hom = P.boundaryExceptionalComparison h Y ∧
    d.hom = P.boundaryImageComparison Y ⟨P.boundaryEtaleValue h Y, hb⟩ ∧
    d.hom ≫ (lowerStar (Modules P) (zeroSection Y)).mapDerivedCategory.map eK.hom ≫ ε =
      (nu P (Line Y)).map (P.boundaryEtaleCounit h Y) ≫
        ((nu P (Line Y)).commShiftIso (2 : ℤ)).hom.app (P.gysinEtaleInput h Y).obj ∧
    Nonempty (Comparison P (lineProjection Y) (zeroSection Y) (openImmersion Y)
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y)) ∧
    ∀ c : Comparison P (lineProjection Y) (zeroSection Y) (openImmersion Y)
        (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y),
      ∃ (b : (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory.obj
            (P.gysinInput h Y).obj ≅ P.derivedSheaf h (Punctured Y) true)
        (edge : (hyper P Y 2).obj (P.gysinClosed h Y) ≅
          (localClasses P Y 2).obj (P.gysinClosed h Y))
        (e : (localClasses P Y 0).obj (P.gysinValue h Y) ≅ P.gysinSupport h Y),
        b.hom = P.gysinOpenCoefficient h Y ∧
        edge.hom = (c.edge 2).app (P.gysinClosed h Y) ∧
        e.hom = (globalSectionsFunctor (Modules P) Y).map
            (((DerivedCategory.homologyFunctor (ProSheaves P Y) 0).shiftIso
              (2 : ℤ) 0 2 (add_zero 2)).hom.app (P.gysinClosed h Y)) ≫
          edge.inv ≫ (c.supportIso 2).hom.app (P.gysinEtaleInput h Y) ∧
        (∀ α : P.gysinSupport h Y, ∃! m : P.derivedSheaf h Y false ⟶ P.gysinValue h Y,
          e.hom (P.gysinHomToSections h Y m) = α) ∧
        (∀ m : P.derivedSheaf h Y false ⟶ P.gysinValue h Y,
          (χ.hom.app (P.gysinInput h Y)) (e.hom (P.gysinHomToSections h Y m)) =
            ((lowerStar (Modules P) (zeroSection Y)).mapDerivedCategorySingleFunctor 0).inv.app
              (P.constant Y) ≫
              (lowerStar (Modules P) (zeroSection Y)).mapDerivedCategory.map m ≫ ε) ∧
        (∀ m : P.derivedSheaf h Y false ⟶ P.gysinValue h Y,
          ∃! f : (DerivedCategory.singleFunctor (EtSheaves P Y) 0).obj
              (P.constantEtale Y) ⟶ P.boundaryEtaleValue h Y,
            ((comparisonUpperStar (Modules P) Y).mapDerivedCategorySingleFunctor 0).inv.app
              (P.constantEtale Y) ≫ (nu P Y).map f ≫ eK.hom = m) ∧
        ∀ δ : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology (Line Y)) (Modules P)
            (supportRestrictionArrow (zeroSection Y)) ⊤,
          Sheaf.SupportSequenceExact (Scheme.ProEt.topology (Line Y)) (Modules P)
            (supportRestrictionArrow (zeroSection Y)) ⊤ δ →
          ∃! m : P.derivedSheaf h Y false ⟶ P.gysinValue h Y,
            e.hom (P.gysinHomToSections h Y m) =
              (δ 1).app ⟨P.gysinInput h Y, trivial⟩ (P.gysinKummerSection h Y a c b)

/-- Finite-Tor realization and exceptional transpose of every affine-line support class.
Source: blueprint main-20261015, thm-pur-affine-line-orientation.proof.md,
first paragraph, ambient qualifications, and final site-comparison sentence;
Milne, Theorem 9.4, Example 9.5, and closed-support adjunction before Theorem 16.7
(blueprint: lem-pur-affine-line-boundary-realization).

Proof (the seven steps of the node):
1. The zero-support retraction triangle supplies the finite Noetherian closed/open pair
and quasi-compact j. Finite-type dimension supplies d, with d=0 for the empty scheme.
The finite Kummer-level lemma gives ell^N A=0. OpenComplementKnown gives c=2d.
2. FiniteEtaleTwistLine and PurTwistSheafLocallyFree give the etale and pro-etale root
lines. On a root-trivializing cover both coefficient comparisons send zeta^a tensor b
to ab; their identical transition multipliers glue. Exact comparison preserves the
constant coefficient sheaf. Locally tensoring either line is tensoring A, so its Tor
interval is [0,0]. The constant unit has that interval and is constructible.
3. EtaleClosedAmbientAdjoint supplies the ordinary adjoint independently of step 1.
EtaleClosedSupportAmplitude and EtaleClosedSupportTorAmplitude, using the two open
conditions separately, give bounded constructibility and finite-Tor preservation.
4. The zero-support triangle and KummerTriangleConcentration give the classical support
value shifted by two, concentrated in degree zero and finite-Tor constructible.
SupportedClassEvaluationComparison compares it with the transported exceptional value
using the closed counit, and supplies the two evaluation isomorphisms.
5. Define u_alpha by these bijections. The normalized edge and supportIso are exactly
the Gysin section-to-support identification. The inverse adjunct is s_*u_alpha followed
by the exceptional counit, proving the displayed equality and uniqueness.
6. The finite twist has its actual etale model; step 3 puts its exceptional value in D+.
Full faithfulness of site comparison gives the unique etale representative of every
u_alpha. SiteClosedCounitTransport identifies the counit with the ordinary etale counit
through the closed image mate. Exact comparison commutes with the displayed shifts.
No adjunction on arbitrary pro-etale objects is used.
7. Substitute the exact support boundary of coordinateKummer. By the definition of
gysinHomToSections, evaluation is H^0(u)(1), giving the final assertion. -/
theorem affine_line_boundary_realization (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    (1 ≤ P.kummerLevel ∧ (P.exponent : P.Coefficient) = 0) ∧
    (∃ (d : ℕ) (hj : QuasiCompact (openImmersion Y)),
      topologicalKrullDim (Line Y) ≤ (d : WithBot ℕ∞) ∧
      @Scheme.HasOpenComplementCondition P.Coefficient inferInstance inferInstance
        (Punctured Y) (Line Y) (openImmersion Y) inferInstance hj (2 * d)) ∧
    ((Etale.lowerStar (Modules P) (zeroSection Y)).rightDerivedFunctor.IsLeftAdjoint) ∧
    (∀ M : DerivedCategory (EtSheaves P (Line Y)),
      Etale.DerivedCategory.isBoundedConstructible P.Coefficient (Line Y) M →
      Etale.DerivedCategory.isBoundedConstructible P.Coefficient Y
          ((etClosed P (zeroSection Y)).obj M) ∧
        (finiteTorConstructibleEtale P.coefficients.l P.extension P.level P.level_pos
            (Line Y) M →
          finiteTorConstructibleEtale P.coefficients.l P.extension P.level P.level_pos Y
            ((etClosed P (zeroSection Y)).obj M))) ∧
    (∃ V : Scheme.Cover.{u} Scheme.etalePrecoverage (Line Y), ∀ i : V.I₀,
      Nonempty ((Etale.upperStar (Modules P) (V.f i)).obj (P.twistEtale h (Line Y)) ≅
        P.constantEtale (V.X i)) ∧
      Nonempty ((upperStar (Modules P) (V.f i)).obj (P.twist h (Line Y)) ≅
        P.constant (V.X i))) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn P.Coefficient (Line Y) 0 0
      (P.gysinEtaleInput h Y).obj ∧
    Scheme.HasProEtaleTorAmplitude (Line Y) P.Ring
      ((finiteCoefficientIntrinsicRealization (Line Y) P.Ring).mapDerivedCategory.obj
        (P.gysinInput h Y).obj) 0 0 ∧
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((finiteCoefficientIntrinsicRealization Y P.Ring).mapDerivedCategory.obj
        (P.derivedSheaf h Y false)) ∧
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((finiteCoefficientIntrinsicRealization Y P.Ring).mapDerivedCategory.obj
        (P.gysinValue h Y)) ∧
    (∀ q : ℤ, q ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ProSheaves P Y) q).obj
        (P.gysinValue h Y))) ∧
    P.AffineLineBoundaryRealization h Y a := by
  sorry

end WeilConjectures.PurityFiniteSetting
