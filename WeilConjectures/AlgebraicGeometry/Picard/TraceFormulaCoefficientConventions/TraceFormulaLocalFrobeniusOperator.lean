/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusCohomologyTransport
public import WeilConjectures.TraceFormula.TraceFormulaCoefficientConventions.FrobeniusPullbackComparisonCoherence
public import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.IteratedWeilMap
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.SmoothPurity.TraceFormulaCoefficientConventions.TraceFormulaStrictWeilComplex
public import WeilConjectures.SmoothPurity.TraceFormulaCoefficientConventions.TraceFormulaCoefficientConventions
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.SchemeFrobenius
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.SelectedSchemeGaloisComparison
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusFactorization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius
public import WeilConjectures.AlgebraicGeometry.SixFunctors.AbsoluteFrobeniusSite
public import WeilConjectures.AlgebraicGeometry.SixFunctors.FrobeniusTrivializationPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.Topology.Homeomorph.Defs
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.Tactic.Ring
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalPullbackComposition
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.TraceFormula.PointTransportComposition
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtalePullbackStalkCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius

/-!
# The finite-coefficient local Frobenius operator

Source: Weil conjectures blueprint, main-20261015, def-trf-frobenius-operators, clause 2
(blueprint: def-trf-frobenius-operators).

This supplements the recorded etale cohomological operator with the local operator
on the intrinsic pro-etale ordinary-module complex, retaining rho, the specified kappa,
and the iterated Weil isomorphism separately. Point evaluation is exactly the ambient
functor whose constructible restriction is `pointFiniteFibre`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TraceFormulaCoefficientConventions

/-- Exact evaluation at the point, with precisely the localization universe of the
recorded point fibre. The sheaf category retains its standard larger localization.
Source: blueprint def-trf-frobenius-operators, clause 2, and def-weil-finite-coefficient-point
(blueprint: def-trf-frobenius-operators). -/
def finiteLocalSections (T : TraceFormulaCoefficientConventions.{u}) :
    proEtaleDerivedCategory (Spec (.of T.datum.k)) T.coefficientRing ⥤
      @DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian _) :=
  @Functor.mapDerivedCategory
    (proEtaleRingModules (Spec (.of T.datum.k))
      (proEtaleConstantRing (Spec (.of T.datum.k)) T.coefficientRing)) _ _
    (HasDerivedCategory.standard _)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointFiniteSections T.datum.k T.coefficientRing)
    (pointFiniteSectionsAdditive T.datum.k T.coefficientRing)
    (pointFibreFiniteLimits T.datum T.coefficientRing)
    (pointFibreFiniteColimits T.datum T.coefficientRing)

/-- The stalk complex `Fib_s(Lz^*K)`, using exact sections at `s`.
Source: blueprint def-trf-frobenius-operators, clause 2
(blueprint: def-trf-frobenius-operators). -/
def finiteLocalFibre (T : TraceFormulaCoefficientConventions.{u})
    (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange) :
    proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing ⥤
      @DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian _) :=
  proEtaleConstantRingDerivedPullback T.coefficientRing z ⋙
    T.finiteLocalSections

/-- The canonical fixed-point identification rho. Only equality of the scheme-Frobenius
translate is used; raw geometric Galois Frobenius need not fix z.
Source: blueprint def-trf-frobenius-operators, clause 2
(blueprint: def-trf-frobenius-operators). -/
def finiteLocalRho (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex) (m : ℕ)
    (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange)
    (hz : z ≫ T.datum.schemeFrobeniusIterate T.X₀ m = z) :
    (T.finiteLocalFibre z).obj K.obj.carrier ≅
      (T.finiteLocalFibre z).obj
        ((proEtaleConstantRingDerivedPullback T.coefficientRing
          (T.datum.schemeFrobeniusIterate T.X₀ m)).obj K.obj.carrier) :=
  T.finiteLocalSections.mapIso
    (eqToIso (congrArg
      (fun f ↦ (proEtaleConstantRingDerivedPullback T.coefficientRing f).obj K.obj.carrier)
      hz.symm) ≪≫
      (proEtaleConstantRingPullbackComposition z
        (T.datum.schemeFrobeniusIterate T.X₀ m) T.coefficientRing).symm.app K.obj.carrier)

/-- The local geometric Frobenius `Fib_s(Lz^* phi^[m])` after `Fib_s(Lz^* kappa)`
after rho, on the actual ordinary-module fibre complex. This formula applies to the
scalar-extended point of every rational point; no arbitrary transport is supplied.
Source: blueprint def-trf-frobenius-operators, clause 2
(blueprint: def-trf-frobenius-operators). -/
def finiteLocalFrobenius (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex) (m : ℕ) (hm : 1 ≤ m)
    (z : Spec (.of T.datum.k) ⟶ T.geometricBaseChange)
    (hz : z ≫ T.datum.schemeFrobeniusIterate T.X₀ m = z) :
    (T.finiteLocalFibre z).obj K.obj.carrier ⟶ (T.finiteLocalFibre z).obj K.obj.carrier :=
  (T.finiteLocalRho K m z hz).hom ≫
    (T.finiteLocalFibre z).map (T.iteratedWeilSchemeFrobenius K m hm).hom

/-- The actual functor `H = Fib_s Ra_X!` on the ambient intrinsic derived category,
represented by the geometric base change of the retained compactification.
Source: blueprint def-trf-frobenius-operators, clause 1
(blueprint: def-trf-frobenius-operators). -/
def finiteGlobalCompactSections (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom) :
    proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing ⥤
      @DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian _) :=
  sfIntrinsicCompactSupport (frobeniusCohomologyCompactification T.datum T.X₀ c₀)
    T.coefficientRing ⋙ T.finiteLocalSections

/-- Degree-one compact transport, in the canonical tensor-pullback coordinates.
Only the unit-normalized presentation comparison and `g^1 = g` are inserted.
Source: blueprint def-trf-frobenius-operators, clause 1
(blueprint: def-trf-frobenius-operators). -/
def finiteGlobalCompactStep (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom)
    (M : proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing) :
    (T.finiteGlobalCompactSections c₀).obj M ⟶
      (T.finiteGlobalCompactSections c₀).obj ((T.frobeniusPullbackPower 0).obj M) := by
  rcases T with ⟨D, C, E, n, hn, X, hft, hqc, hsep⟩
  cases n with
  | zero => omega
  | succ n =>
    exact frobeniusCompactTransportFinite D C.l C.different
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E) X c₀ n M ≫
      (finiteGlobalCompactSections ⟨D, C, E, n + 1, hn, X⟩ c₀).map
        ((pointPowerPullbackModel C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E) n
          (D.geometricGaloisFrobenius X)).hom.app M ≫
          eqToHom (congrArg
            (fun f ↦ (proEtaleConstantRingDerivedPullback
              (Padic.coefficientExtensionRing C.l
                (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E) (n + 1)) f).obj M)
            (pow_one (End.of (D.geometricGaloisFrobenius X))).symm))

-- The later composites use these interfaces, without unfolding their derived constructions.
attribute [local irreducible] finiteLocalSections finiteLocalFibre finiteLocalRho
  finiteLocalFrobenius finiteGlobalCompactSections finiteGlobalCompactStep

end WeilConjectures.TraceFormulaCoefficientConventions
