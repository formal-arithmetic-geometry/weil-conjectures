/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupMixed.CondensedMixedSupportCup
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeil.CondensedStrictWeilComplex
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
import WeilConjectures.AlgebraicGeometry.Native.NativeSignedLine
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupProper.CondensedProperComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSmoothTraceUnit
public import WeilConjectures.AlgebraicGeometry.CondensedPoincare.CondensedPoincareSetting
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeil.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.PoincareDualitySetting

/-! # Trace and trace--cup pairing with actual condensed coefficients

Source: latest blueprint sec-poincare-duality/sk-def-trace-cup/_section.md.
The orientation is the uniquely integration-normalized purity family. The proper
comparison uses the identity compactification. Every cup is the mixed-support cup
followed by coefficient multiplication, transported by that proper comparison.
(blueprint: sk-def-trace-cup)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj
open MonoidalCategory MonoidalClosed Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceCup

open PurityTransport

variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
set_option synthInstance.maxHeartbeats 0 in
-- The large cancellation composite needs unrestricted instance search.
set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Construct the required residue inverses from ell different from the characteristic.
Source: distinct primes in the fixed setting (blueprint: sk-def-trace-cup). -/
@[instance_reducible]
def residueInverse (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (T : Over (Spec (.of D.k))) : ∀ x : T.left, Invertible (ell : T.left.residueField x) :=
  fun x ↦ (map_natCast (T.hom.residueFieldAlgebraMap x) ell) ▸
    ((primeUnit D ell hEll).map (T.hom.residueFieldAlgebraMap x)).invertible

/-- Cohomology classes represented by scalar-unit maps to the shifted coefficient complex.
Source: representatives Lambda[-i] -> RΓ, equivalently Lambda -> RΓ[i]
(blueprint: sk-def-trace-cup). -/
abbrev Classes (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (M : DerivedCategory (ModuleCat.{u + 1} (Γ Λ))) (i : ℤ) :=
  (𝟙_ (DerivedCategory (ModuleCat.{u + 1} (Γ Λ)))) ⟶ M⟦i⟧

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Tensor two class representatives, extract their shifts, then apply the given
coefficient-complex product. Source: the representative prescription
(blueprint: sk-def-trace-cup). -/
def product {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ]
    {M N P : DerivedCategory (ModuleCat.{u + 1} (Γ Λ))}
    (mulMap : M ⊗ N ⟶ P) (i j : ℤ) (x : Classes Λ M i) (y : Classes Λ N j) :
    Classes Λ P (i + j) :=
  (λ_ _).inv ≫ (x ⊗ₘ y) ≫
    (DerivedCategory.shiftTensorShiftIso _ M N i j).hom ≫ mulMap⟦i + j⟧'

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The canonical h_r induced by the proper comparison on coefficient complexes.
Source: kappa and h_r (blueprint: sk-def-trace-cup). -/
def properClassComparison (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism] (i : ℤ) :
    Classes (c.obj ell)
      ((condensedRingCompactCoefficientComplex (c.obj ell)
        (Compactification.ofIsProper (G.structureMorphism D.k))).obj
          (unit ell c (G.geometricFiber D.k))) i ≃
    Classes (c.obj ell)
      ((condensedRingOrdinaryCoefficientComplex (c.obj ell)
        (G.structureMorphism D.k)).obj (unit ell c (G.geometricFiber D.k))) i :=
  (Iso.refl _).homCongr
    ((shiftFunctor _ i).mapIso
      ((Functor.isoWhiskerRight (TraceCupProper.comparison (c.obj ell)
        (G.structureMorphism D.k))
          (TraceCupPoint.fiber (c.obj ell) D.k)).app _))

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Ordinary cup is h_(i+j) of the mixed-support product of h_i inverse x and y,
followed by compact-support coefficient-unit multiplication. Source: cup display
(blueprint: sk-def-trace-cup). -/
def cupRepresentatives (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism]
    (i j : ℤ)
    (x : Classes (c.obj ell) ((condensedRingOrdinaryCoefficientComplex (c.obj ell)
      (G.structureMorphism D.k)).obj (unit ell c (G.geometricFiber D.k))) i)
    (y : Classes (c.obj ell) ((condensedRingOrdinaryCoefficientComplex (c.obj ell)
      (G.structureMorphism D.k)).obj (unit ell c (G.geometricFiber D.k))) j) :=
  let a := G.structureMorphism D.k
  let C := Compactification.ofIsProper a
  let K := unit ell c (G.geometricFiber D.k)
  let m : K ⊗ K ⟶ K :=
    ((DerivedCategory.singleFunctorObjUnitIso _).hom ⊗ₘ 𝟙 K) ≫ (λ_ K).hom
  properClassComparison ell c D d G (i + j)
    (product
      (TraceCupMixed.cup (c.bundled ell) D.k C K K ≫
        (condensedRingCompactCoefficientComplex (c.obj ell) C).map m) i j
      ((properClassComparison ell c D d G i).symm x) y)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Canonical identification of scalar-unit representatives with actual cohomology.
It first uses the projective scalar module and then evaluates a linear map at 1.
Source: the representative prescription (blueprint: sk-def-trace-cup). -/
def classEquiv {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ]
    (M : DerivedCategory (ModuleCat.{u + 1} (Γ Λ))) (i : ℤ) :
    Classes Λ M i ≃ ↥((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ Λ)) i).obj M) :=
  ((DerivedCategory.singleFunctorObjUnitIso _).symm.homCongr (Iso.refl _)).trans
    (((DerivedCategory.shiftFunctorCompPreadditiveCoyonedaObjSingleFunctorZeroIso
      (ModuleCat.of (Γ Λ) (Γ Λ)) i).app M).addCommGroupIsoToAddEquiv.toEquiv.trans
        ((ModuleCat.homLinearEquiv (R := Γ Λ) (S := ℤ)
          (M := ModuleCat.of (Γ Λ) (Γ Λ))
          (N := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ Λ)) i).obj M)).toEquiv.trans
          (LinearMap.ringLmapEquivSelf (Γ Λ) ℤ
            ↥((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ Λ)) i).obj M)).toEquiv))

/-- Actual ordinary cohomology with constant coefficients in degree i.
Source: H^i(X,Lambda) (blueprint: sk-def-trace-cup). -/
abbrev H (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) (i : ℤ) :=
  (condensedRingOrdinaryCohomology (c.obj ell) (G.structureMorphism D.k) i).obj
    (unit ell c (G.geometricFiber D.k))

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The cup on actual ordinary cohomology groups, through their canonical representatives.
Source: h_(i+j) H_c(m) mu_c(h_i inverse x,y) (blueprint: sk-def-trace-cup). -/
def cup (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism]
    (i j : ℤ) (x : H ell c D d G i) (y : H ell c D d G j) : H ell c D d G (i + j) :=
  let M := (condensedRingOrdinaryCoefficientComplex (c.obj ell)
    (G.structureMorphism D.k)).obj (unit ell c (G.geometricFiber D.k))
  classEquiv (Λ := c.obj ell) M (i + j) (cupRepresentatives ell c D d G i j
    ((classEquiv (Λ := c.obj ell) M i).symm x)
    ((classEquiv (Λ := c.obj ell) M j).symm y))

/-- The coefficient Tate line, defined as exactly H^0 Fib_s(Lambda_s(-d)).
Source: the displayed definition of Lambda(-d) (blueprint: sk-def-trace-cup). -/
abbrev TateLineValue (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ (c.obj ell))) 0).obj
    ((TraceCupPoint.fiber (c.obj ell) D.k).obj
      (StrictWeil.derivedTateLine ell c (Spec (.of D.k)) (-(d : ℤ))))

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The compact trace on actual cohomology, through the canonical projective-single
identification of representatives. Source: tau_X display (blueprint: sk-def-trace-cup). -/
def compactTrace (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (d : ℕ) (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism]
    (x : (condensedRingCompactCohomology (c.obj ell)
      (Compactification.ofIsProper (G.structureMorphism D.k)) (2 * (d : ℤ))).obj
        (unit ell c (G.geometricFiber D.k))) : TateLineValue ell c D d :=
  let M := (condensedRingCompactCoefficientComplex (c.obj ell)
    (Compactification.ofIsProper (G.structureMorphism D.k))).obj
      (unit ell c (G.geometricFiber D.k))
  let N := (TraceCupPoint.fiber (c.obj ell) D.k).obj
    (StrictWeil.derivedTateLine ell c (Spec (.of D.k)) (-(d : ℤ)))
  let t := compactTraceRepresentatives ell c D hEll d G
    ((classEquiv (Λ := c.obj ell) M (2 * (d : ℤ))).symm x)
  classEquiv (Λ := c.obj ell) N 0 (t ≫ (shiftFunctorZero _ ℤ).inv.app N)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The ordinary trace is exactly tau_X after the inverse cohomology proper comparison.
Source: tr_X^(-d) display (blueprint: sk-def-trace-cup). -/
def trace (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (d : ℕ) (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism]
    (x : H ell c D d G (2 * (d : ℤ))) : TateLineValue ell c D d :=
  compactTrace ell c D hEll d G
    (((TraceCupProper.cohomology (c.obj ell) (G.structureMorphism D.k)
      (2 * (d : ℤ))).inv.app (unit ell c (G.geometricFiber D.k))) x)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
end AlgebraicGeometry.ProEtale.CondensedRing.TraceCup
