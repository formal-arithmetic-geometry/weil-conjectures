/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import Mathlib.LinearAlgebra.Trace
public import WeilConjectures.PointCount
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# L² weights for actual condensed Weil coefficients

Source: latest blueprint, def-wf-l2-norm, squared trace sum and supremum formula
(blueprint: def-wf-l2-norm).

The rational-point sum is written in its closed-point form: a closed point of degree d
contributes d copies of the trace of F_x^(m/d) precisely when d divides m. This is the
ordinary point-count decomposition, including multiplicities, not a different norm.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale Filter
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2
open NativeCondensedModule

/-- Linear trace of an operator power, checked in the abstract bundled module category.
Source: latest blueprint, local Frobenius trace (blueprint: def-wf-l2-norm). -/
def traceOfPower {R : Type v} [CommRing R] {V : ModuleCat.{w} R}
    (f : End V) (r : ℕ) : R :=
  LinearMap.trace R V (f.hom ^ r)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- Choose a residue embedding into the specified algebraic closure by Mathlib's lift.
No sheaf or operator is chosen; local trace is independent of this geometric-point choice.
Source: latest blueprint, closed-point trace convention (blueprint: def-wf-l2-norm). -/
@[irreducible] def residueEmbedding (x : {x : X₀.left // x ∈ closedPoints X₀.left}) :
    letI := (X₀.hom.residueFieldAlgebraMap x.val).toAlgebra
    X₀.left.residueField x.val →ₐ[D.k₀] D.k :=
  letI := (X₀.hom.residueFieldAlgebraMap x.val).toAlgebra
  letI := X₀.hom.finite_residueField_of_isClosed x.val x.property
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  IsAlgClosed.lift

/-- Trace of the r-th power of closed-point geometric Frobenius on the actual scalar fibre.
Source: latest blueprint, trace-function convention (blueprint: def-wf-l2-norm). -/
@[irreducible] def closedPowerTrace (M : WeilModule D l X₀)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left}) (r : ℕ) : PadicAlgCl l :=
  letI := (X₀.hom.residueFieldAlgebraMap x.val).toAlgebra
  let i := residueEmbedding D X₀ x
  let hi := i.comp_algebraMap
  let f := closedOperator D l X₀ M x i.toRingHom hi
  (traceOfPower f r).down

/-- The displayed extended-real supremum; ENNReal limsup permits infinite growth.
Source: latest blueprint, second displayed formula (blueprint: def-wf-l2-norm). -/
def weightOfEnergy (q : ℕ) (energy : ℕ → ℝ) : EReal :=
  ⨆ (β : ℝ) (_ : 0 < limsup (fun m : ℕ ↦ ENNReal.ofReal
    (energy m / (q : ℝ) ^ ((m : ℝ) * (β + 1)))) atTop), (β : EReal)

/-- Cohomology of a bounded constructible complex with its canonical induced Weil structure.
This accepts a Weil pair in the underlying derived category, without a derived-Weil lift.
Source: latest blueprint, alternating cohomological trace (blueprint: def-wf-l2-norm). -/
def complexCohomology
    (K : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) (i : ℤ) : WeilModule D l X₀ :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk
    ((DerivedCategory.homologyFunctor _ i).obj K.obj.carrier)
    (((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom).mapDerivedCategoryHomologyFunctorIso i).app
        K.obj.carrier ≪≫ (DerivedCategory.homologyFunctor _ i).mapIso K.obj.str)

/-- Alternating trace of closed-point Frobenius on the Weil cohomology sheaves.
The complex is bounded, so the finsum has finite support.
Source: latest blueprint, alternating cohomological trace (blueprint: def-wf-l2-norm). -/
def complexClosedPowerTrace
    (K : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left}) (r : ℕ) : PadicAlgCl l :=
  ∑ᶠ i : ℤ, (-1 : PadicAlgCl l) ^ i *
    closedPowerTrace D l X₀ (complexCohomology D l X₀ K i) x r

/-- The squared trace sum for a bounded constructible Weil complex.
Source: latest blueprint, first displayed formula (blueprint: def-wf-l2-norm). -/
def complexTraceEnergy (iota : PadicAlgCl l →+* ℂ)
    (K : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom)
    (m : ℕ) : ℝ :=
  if m = 0 then 0 else
    ∑ᶠ x : {x : X₀.left // x ∈ closedPoints X₀.left},
      if localClosedPointDegree D X₀ x ∣ m then
        (localClosedPointDegree D X₀ x : ℝ) *
          ‖iota (complexClosedPowerTrace D l X₀ K x
            (m / localClosedPointDegree D X₀ x))‖ ^ 2
      else 0

/-- The L² parameter of a bounded constructible Weil complex.
Source: latest blueprint, second displayed formula (blueprint: def-wf-l2-norm). -/
def complexL2Weight (iota : PadicAlgCl l →+* ℂ)
    (K : condensedStrictWeilComplex (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom) :
    EReal :=
  weightOfEnergy D.q (complexTraceEnergy D l X₀ iota K)

end WeilConjectures.NativeL2
