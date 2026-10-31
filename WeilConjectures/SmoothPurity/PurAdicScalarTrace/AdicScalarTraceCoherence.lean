/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.ZetaSeries
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SmoothPurity.Integral.Twist.IntegralTwistDerivedScalarCanonical
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.SmoothPurity.Integral.Twist.IntegralTwistScalarCoherence
import WeilConjectures.SmoothPurity.Supporting.TwistPreservesFiniteness

/-! # Scalar coherence of reconstructed integral traces

Source: blueprint `sec-smooth-purity/sk-thm-purity-transport/_section.md`, Step 3;
current `main-20261015`, `thm-pur-rational-and-qbar-purity.md`, coefficient transport
(blueprint: lem-pur-adic-scalar-trace-coherence).

Compact support is the published completed proper/open functor `PurCompactSupport.image`.
Its realization as the recorded integral compact-support functor is the normalized
`sfQcqsCompactSupportRealization`. Scalar extension is ordinary derived extension along
the actual completed coefficient inclusion; the finite-free comparison identifies this
with strict-tower extension. All comparison choices below are normalized to those maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

namespace PurAdicScalarTrace

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The completed coefficient unit in degree zero, with its actual module structure.
Source: purity conventions and scalar transport Step 3
(blueprint: lem-pur-adic-scalar-trace-coherence). -/
def unit (S : Scheme.{u}) : DerivedCategory (integralTowerModules l E S) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E S))

/-- The degree-zero coefficient-unit complex used to normalize multiplication.
Source: purity conventions and scalar transport Step 3
(blueprint: lem-pur-adic-scalar-trace-coherence). -/
def unitComplex (S : Scheme.{u}) : CochainComplex (integralTowerModules l E S) ℤ :=
  (HomologicalComplex.single _ (.up ℤ) 0).obj
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E S))

/-- The source's twisted shifted unit, formed using the published exact tensor twist.
Source: purity transport Step 3, T_L = 1_L(d)[2d]
(blueprint: lem-pur-adic-scalar-trace-coherence). -/
def twistedUnit (S : Scheme.{u}) [∀ x : S, Invertible (l : S.residueField x)]
    (d : ℕ) : DerivedCategory (integralTowerModules l E S) :=
  ((integralSheafTwist l E S (d : ℤ)).mapDerivedCategory.obj (unit l E S))⟦2 * (d : ℤ)⟧

/-- Transport the specified inverse of l in k to the residue fields. This is actual
structure obtained from l distinct from p, not an additional invertibility assumption.
Source: purity conventions (blueprint: lem-pur-adic-scalar-trace-coherence). -/
@[instance_reducible]
def residueInverse (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (S : Scheme.{u}) [S.Over (Spec (.of D.k))] :
    ∀ x : S, Invertible (l : S.residueField x) :=
  fun x ↦ (map_natCast ((S ↘ Spec (.of D.k)).residueFieldAlgebraMap x) l) ▸
    ((PurCompactSupport.coefficientPrimeUnit l D hl).map
      ((S ↘ Spec (.of D.k)).residueFieldAlgebraMap x)).invertible

/-- The same twisted shifted unit with its residue-field inverse constructed from
l distinct from p. Source: purity conventions and transport Step 3
(blueprint: lem-pur-adic-scalar-trace-coherence). -/
def overTwistedUnit (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (S : Scheme.{u}) [S.Over (Spec (.of D.k))] (d : ℕ) :
    DerivedCategory (integralTowerModules l E S) :=
  @twistedUnit l _ E _ _ _ S (residueInverse l D hl S) d

variable (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
  (ι : E →ₐ[Padic l] F)

/-- An interface for the canonical coefficient-unit multiplication, retaining its
full normalization. The complex map is determined by b tensor x maps to b iota(x)
in degree zero (all other terms vanish). Its derived map is exactly the universal
K-flat counit followed by that chain map; changing its sign violates these equations.
Source: purity transport Step 3, the unit multiplication convention
(blueprint: lem-pur-adic-scalar-trace-coherence). -/
structure UnitMultiplication (S : Scheme.{u}) where
  chain : (completedOrdinaryScalarComplex l E F ι S).obj (unitComplex l E S) ≅
    unitComplex l F S
  multiplication : ∀ (U : S.ProEtᵒᵖ)
    (b : (completedIntegralCommRingSheafUnrestricted l F S).obj.obj U)
    (x : (completedIntegralCommRingSheafUnrestricted l E S).obj.obj U),
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l F S))).hom).val.app U
      ((chain.hom.f 0).val.app U
          (completedScalarTensorSection l E F ι S _ U b
            (((HomologicalComplex.singleObjXSelf (.up ℤ) 0
              (SheafOfModules.unit
                (completedIntegralCoefficientSheafUnrestricted l E S))).inv).val.app U x))) =
      b * ((completedCoefficientMap l E F ι S).hom.app U).hom x
  iso : (completedDerivedScalarExtension l E F ι S).obj (unit l E S) ≅ unit l F S
  normalization : iso.hom =
    completedScalarCounit l E F ι S (unitComplex l E S) ≫ DerivedCategory.Q.map chain.hom

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]

/-- Only the specified coefficient-unit multiplications and compact-support comparison
are packaged here. In particular compact.hom is the actual published adjunction mate,
not a freely chosen comparison. These are presentations of canonical isomorphisms;
no geometric or trace compatibility equation is assumed.
Source: purity transport Step 3 and its explicit comparison conventions
(blueprint: lem-pur-adic-scalar-trace-coherence). -/
structure CoefficientComparison (c : Compactification f) (d : ℕ) where
  unitX : UnitMultiplication l E F ι X
  unitY : UnitMultiplication l E F ι Y
  compact :
    (completedDerivedScalarExtension l E F ι Y).obj
        ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj
          (overTwistedUnit l E D hl X d)) ≅
      (PurCompactSupport.image (PurCompactSupport.completed l F) c).obj
        ((completedDerivedScalarExtension l E F ι X).obj (overTwistedUnit l E D hl X d))
  normalization : compact.hom =
    (PurCompactSupport.comparison (PurCompactSupport.completedChange l E F ι) c).app
      (overTwistedUnit l E D hl X d)

/-- Build theta (and, for E to F, a) from the named canonical beta, coefficient-unit
multiplication and the canonical shift comparison. The unit is the zero signed twist,
hence the argument of beta is the recorded intrinsic constructible unit.
Source: node proof Step 2 and purity transport Step 3
(blueprint: lem-pur-adic-scalar-trace-coherence). -/
def twistComparison
    (S : Scheme.{u}) [S.Over (Spec (.of D.k))]
    (d : ℕ) (v : UnitMultiplication l E F ι S) :
    (completedDerivedScalarExtension l E F ι S).obj (overTwistedUnit l E D hl S d) ≅
      overTwistedUnit l F D hl S d :=
  letI := residueInverse l D hl S
  letI : (completedDerivedScalarExtension l E F ι S).CommShift ℤ :=
    PurCompactSupport.scalarCommShift (completedCoefficientMap l E F ι S)
  ((completedDerivedScalarExtension l E F ι S).commShiftIso (2 * (d : ℤ))).app
      ((integralSheafTwist l E S (d : ℤ)).mapDerivedCategory.obj (unit l E S)) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((integralTwistOrdinaryBeta l E F ι S (d : ℤ)).app
          (intrinsicIntegralCoefficientTwist D l hl E S 0) ≪≫
        (integralSheafTwist l F S (d : ℤ)).mapDerivedCategory.mapIso v.iso)

/-- The explicit scalar-extended trace, including the coefficient-unit identification
suppressed in the source's displayed formula. All factors are the specified constructions.
Source: purity transport Step 3 and node proof Step 1
(blueprint: lem-pur-adic-scalar-trace-coherence). -/
def trace
    (c : Compactification f) (d : ℕ) (a : CoefficientComparison l E F ι D hl c d)
    (t₀ : (PurCompactSupport.image (PurCompactSupport.completed l E) c).obj
      (overTwistedUnit l E D hl X d) ⟶ unit l E Y) :
    (PurCompactSupport.image (PurCompactSupport.completed l F) c).obj
      (overTwistedUnit l F D hl X d) ⟶ unit l F Y :=
  (PurCompactSupport.image (PurCompactSupport.completed l F) c).map
      (twistComparison l E F ι D hl X d a.unitX).inv ≫
    a.compact.inv ≫ (completedDerivedScalarExtension l E F ι Y).map t₀ ≫ a.unitY.iso.hom

variable (X Y : Scheme.{u}) (f : X ⟶ Y) (d : ℕ)
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))] [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))] [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  [fbase : f.IsOver (Spec (.of D.k))] [fs : IsSeparated f]
  [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f] [fsm : SmoothOfRelativeDimension d f]

include Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc fsm

end PurAdicScalarTrace
end WeilConjectures
