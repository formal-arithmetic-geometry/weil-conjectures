/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.FieldCohomologyScalarExtension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
import Sheaf.Paper.PointSectionsScalarExtension
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Paper.IntegralPullbackComparisonRealization
import Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws
import Sheaf.Paper.SfWeilSheafComplex

/-!
# Local traces of isomorphic finite Weil models

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace/def-fd-trace-function.md,
displayed formula and representative independence
(blueprint: lem-fd-local-weil-model-trace-independence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  (E L : Padic.FiniteCoefficientFields c.l c.Qbar) (hEL : E ≤ L)

/-- Extend a Weil pair using the inverse of the specified pullback/scalar comparison.
Source: blueprint finite-model comparison, def-fd-trace-function.md
(blueprint: lem-fd-local-weil-model-trace-independence). -/
def localWeilModelScalar (V : sfWeilComplex D c.l c.different X₀ E.val) :
    sfWeilComplex D c.l c.different X₀ L.val :=
  letI := sfWeilPrimeInvertible D c.l c.different X₀
  CategoryTheory.Endofunctor.IsoAlgebra.mk
    ((sfRationalScalarExtension c.l E.val (D.geometricFiber X₀).left 0
      (Nat.Prime.ne_zero (Fact.out : c.l.Prime)) L.val
      (IntermediateField.inclusion hEL)).obj V.carrier)
    (((rationalPullbackScalarComparison c.l E.val L.val
      (IntermediateField.inclusion hEL) (D.geometricFrobenius X₀).hom).app V.carrier).symm ≪≫
      (sfRationalScalarExtension c.l E.val (D.geometricFiber X₀).left 0
        (Nat.Prime.ne_zero (Fact.out : c.l.Prime)) L.val
        (IntermediateField.inclusion hEL)).mapIso V.str)

/-- The required b_M: inverse sections/scalar comparison followed by the fibre of
pullback/scalar comparison. Source: blueprint finite-model comparison,
def-fd-trace-function.md (blueprint: lem-fd-local-weil-model-trace-independence). -/
def localWeilModelPointScalar (V : sfWeilComplex D c.l c.different X₀ E.val)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :
    (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion hEL).toRingHom).obj
        (localPointComplex c.l E.val D c.different X₀ V x) ≅
      localPointComplex c.l L.val D c.different X₀
        (localWeilModelScalar D c X₀ E L hEL V) x :=
  letI := frobeniusPointPrimeInvertible D c.l c.different
  letI := sfWeilPrimeInvertible D c.l c.different X₀
  ((pointRationalFibreScalarIso D c.l c.different E.val L.val
    (IntermediateField.inclusion hEL)).app
      (localDerivedStalk c.l E.val D c.different X₀ V x)).symm ≪≫
    (pointRationalFibre D c.l c.different L.val).mapIso
      ((rationalPullbackScalarComparison c.l E.val L.val
        (IntermediateField.inclusion hEL) x).app V.carrier)

variable (E' : Padic.FiniteCoefficientFields c.l c.Qbar) (hE'L : E' ≤ L)
  (V : sfWeilComplex D c.l c.different X₀ E.val)
  (V' : sfWeilComplex D c.l c.different X₀ E'.val)
  (u : localWeilModelScalar D c X₀ E L hEL V ≅
    localWeilModelScalar D c X₀ E' L hE'L V')

/-- The specified tilde-u_x is b_M, the point pullback of u, then inverse b_M'.
Source: blueprint finite-model comparison, def-fd-trace-function.md
(blueprint: lem-fd-local-weil-model-trace-independence). -/
def localWeilModelPointIso (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :=
  letI := frobeniusPointPrimeInvertible D c.l c.different
  letI := sfWeilPrimeInvertible D c.l c.different X₀
  localWeilModelPointScalar D c X₀ E L hEL V x ≪≫
    (pointRationalFibre D c.l c.different L.val).mapIso
      ((rationalDerivedPullback c.l L.val x).mapIso
        ((sfWeilForget D c.l c.different X₀ L.val).mapIso u)) ≪≫
    (localWeilModelPointScalar D c X₀ E' L hE'L V' x).symm

/-- Cohomology conjugacy uses the prescribed cohomology/scalar isomorphisms,
with tilde-u_x between them. Source: blueprint finite-model comparison,
def-fd-trace-function.md (blueprint: lem-fd-local-weil-model-trace-independence). -/
def localWeilModelCohomologyIso
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (j : ℤ) :=
  ((DerivedCategory.fieldDerivedHomologyIso
    (IntermediateField.inclusion hEL).toRingHom j).app
      (localPointComplex c.l E.val D c.different X₀ V x).obj).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} L.val) j).mapIso
      ((DerivedCategory.pointFiniteDimensional L.val).ι.mapIso
        (localWeilModelPointIso D c X₀ E L hEL E' hE'L V V' u x)) ≪≫
    (DerivedCategory.fieldDerivedHomologyIso
      (IntermediateField.inclusion hE'L).toRingHom j).app
        (localPointComplex c.l E'.val D c.different X₀ V' x).obj

/-- Ordinary degreewise linear trace, with the fixed local cohomology operator.
Source: blueprint displayed local trace, def-fd-trace-function.md
(blueprint: lem-fd-local-weil-model-trace-independence). -/
def localWeilModelDegreeTrace (F : Padic.FiniteCoefficientFields c.l c.Qbar)
    (W : sfWeilComplex D c.l c.different X₀ F.val)
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints X₀ n hn) (j : ℤ) : F.val :=
  LinearMap.trace F.val
    ((DerivedCategory.coefficientFdCohomology F.val j).obj
      (localPointComplex c.l F.val D c.different X₀ W (localExtensionPoint D X₀ n hn x)))
    (localExtensionFrobeniusCohomology c.l F.val D c.different X₀ W n hn x j).hom

/-- Local Frobenius operators are conjugate through exactly the specified b comparisons;
cohomology operators are conjugate through their canonical scalar comparisons, and
ordinary traces agree both in L and in the fixed algebraic closure.
Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace/def-fd-trace-function.md,
displayed formula and representative independence
(blueprint: lem-fd-local-weil-model-trace-independence).

Proof plan:
1. Form the natural b maps from the inverse point-sections scalar comparison and the
rationalized pullback/scalar comparison. Integral naturality extends linearly to all
rational morphisms. The distinct coefficient prime is invertible on both schemes.
2. Induct on the Weil-pair intertwining equation to intertwine all iterated Weil maps;
use naturality and associativity of the specified composition comparison at each step.
3. Induct on the point transports using frobeniusPointTransport_natural to prove
naturality of their iterates, then pass through the pullback-composition identification.
4. The return comparison uses g_X^n xbar = xbar g_s^n. Its naturality, step 3 and step 2
show that the point pullback of u intertwines the L-local operators.
5. Induct on iterated Weil maps and paste the composition/scalar squares from
integralPullbackComparisonRealization to identify scalar extension of theta^[n]
with theta_L^[n]. The normalization respects equality of morphisms and iterations.
6. Paste the n point-transport scalar squares. Intermediate scalar comparisons cancel;
the same composition/scalar identity at the return comparison gives b F^T = F_L b.
No integral Weil lattice or finite-reduction Tor condition is used.
7. Apply step 6 to each model and cancel b and b' in step 4 to get the asserted
conjugacy with b followed by the point pullback of u followed by inverse b'.
8. Apply cohomology and the natural fieldDerivedHomologyIso to obtain the displayed
conjugacy of the extended cohomology operators in every integer degree.
9. Apply LinearMap.trace_conj' to the linear equivalence in step 8, and apply
LinearMap.trace_baseChange separately to the finite-dimensional E and E' spaces.
Use the algebra structures induced by the two inclusions into L and the canonical
tensor symmetry to express ModuleCat.extendScalars in baseChange coordinates.
These are the ordinary field trace identities described by formal laws (1),(3),(4);
the recorded categorical laws (1),(3) themselves have finite quotient-ring sources,
so they are not instantiated at E or E'. Include L into Qbar; the composites are
the fixed inclusions. Zero cohomology contributes zero. -/
theorem localWeilModelTraceIndependence
    (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom]
    (E E' L : Padic.FiniteCoefficientFields c.l c.Qbar) (hEL : E ≤ L) (hE'L : E' ≤ L)
    (V : sfWeilComplex D c.l c.different X₀ E.val)
    (V' : sfWeilComplex D c.l c.different X₀ E'.val)
    (u : localWeilModelScalar D c X₀ E L hEL V ≅
      localWeilModelScalar D c X₀ E' L hE'L V')
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints X₀ n hn) :
    (localWeilModelPointIso D c X₀ E L hEL E' hE'L V V' u
      (localExtensionPoint D X₀ n hn x)).hom ≫
        (DerivedCategory.pointFdScalarExtension
          (IntermediateField.inclusion hE'L).toRingHom).map
          (localExtensionFrobenius c.l E'.val D c.different X₀ V' n hn x) =
      (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion hEL).toRingHom).map
        (localExtensionFrobenius c.l E.val D c.different X₀ V n hn x) ≫
          (localWeilModelPointIso D c X₀ E L hEL E' hE'L V V' u
            (localExtensionPoint D X₀ n hn x)).hom ∧
    ∀ j : ℤ,
      (localWeilModelCohomologyIso D c X₀ E L hEL E' hE'L V V' u
        (localExtensionPoint D X₀ n hn x) j).hom ≫
          (ModuleCat.extendScalars (IntermediateField.inclusion hE'L).toRingHom).map
            (localExtensionFrobeniusCohomology c.l E'.val D c.different X₀ V' n hn x j) =
        (ModuleCat.extendScalars (IntermediateField.inclusion hEL).toRingHom).map
          (localExtensionFrobeniusCohomology c.l E.val D c.different X₀ V n hn x j) ≫
            (localWeilModelCohomologyIso D c X₀ E L hEL E' hE'L V V' u
              (localExtensionPoint D X₀ n hn x) j).hom ∧
      (IntermediateField.inclusion hEL)
          (localWeilModelDegreeTrace D c X₀ E V n hn x j) =
        (IntermediateField.inclusion hE'L)
          (localWeilModelDegreeTrace D c X₀ E' V' n hn x j) ∧
      E.val.subtype (localWeilModelDegreeTrace D c X₀ E V n hn x j) =
        E'.val.subtype (localWeilModelDegreeTrace D c X₀ E' V' n hn x j) := by
  sorry

end WeilConjectures
