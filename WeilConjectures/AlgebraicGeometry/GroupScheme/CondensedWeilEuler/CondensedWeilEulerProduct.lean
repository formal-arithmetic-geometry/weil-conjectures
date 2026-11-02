/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedDerived.CondensedScalarDerivedLocalFrobenius
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Complex.Basic
public import Mathlib.Order.KrullDimension
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections

/-! # Euler product for condensed Weil complexes

Source: latest blueprint, thm-trf-l-function-euler-product, clauses (1)--(4)
and its proof Steps 0--6 (blueprint: thm-trf-l-function-euler-product).

Products are coefficientwise formal products. No lattice or finite-level datum is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilEuler
open WeilConjectures.NativeCondensedModule

/-- The ordinary scalar field of the allowed condensed coefficient.
Source: the initial coefficient convention (blueprint: thm-trf-l-function-euler-product). -/
abbrev Scalar {ell : ℕ} [Fact ell.Prime] : WeilCoefficient ell → Type
  | .finite E => E
  | .qbar => PadicAlgCl ell

/-- The existing field structure on the ordinary scalar field.
Source: the initial coefficient convention (blueprint: thm-trf-l-function-euler-product). -/
instance scalarField {ell : ℕ} [Fact ell.Prime] (c : WeilCoefficient ell) : Field (Scalar c) :=
  match c with
  | .finite _ => inferInstance
  | .qbar => inferInstance

/-- The canonical constant scalar action on condensed global sections.
Source: Lambda(*) = E or Qbar (blueprint: thm-trf-l-function-euler-product). -/
def scalarMap {ell : ℕ} [Fact ell.Prime] (c : WeilCoefficient ell) :
    Scalar c →+* MonObj.Γ (WeilCoefficient.ab.{u} c) :=
  match c with
  | .finite E => Profinite.continuousMapConstRingHom (E : Type)
  | .qbar => Profinite.PadicAlgCl.constRingHom ell

/-- The finite alternating determinant on a graded operator, inverted to give the
Euler factor; even degrees contribute inverse determinants.
Source: the two displayed definitions (blueprint: thm-trf-l-function-euler-product). -/
def inverseAlternating {R : Type v} [Field R] (V : ℤ → ModuleCat.{u + 1} R)
    (F : ∀ i, End (V i)) (e : ℕ) : PowerSeries R :=
  ∏ᶠ i : ℤ, if Even i then (determinantFactor (V i) (F i) e)⁻¹
    else determinantFactor (V i) (F i) e

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  (c : WeilCoefficient ell) (K : strictWeilComplexCategory D ell hEll X₀ c)

/-- Closed points carry the recorded scheme-theoretic meaning.
Source: the closed-point product (blueprint: thm-trf-l-function-euler-product). -/
abbrev ClosedPoint := {x : X₀.left // x ∈ closedPoints X₀.left}

/-- The local scalar stalk cohomology for any choice of compatible residue embedding.
Source: the displayed local determinant (blueprint: thm-trf-l-function-euler-product). -/
def localCohomology (x : ClosedPoint D X₀)
    (iota : X₀.left.residueField x.val →+* D.k)
    (hiota : iota.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (j : ℤ) : ModuleCat.{u + 1} (Scalar c) :=
  (ModuleCat.restrictScalars (scalarMap c)).obj
    ((NativeCondensedDerived.cohomology (WeilCoefficient.ab c) j).obj
      (NativeCondensedDerived.stalk (WeilCoefficient.ab c) D K.obj.carrier
        (localClosedPoint D X₀ x iota hiota)))

/-- The one-circuit local Frobenius, with the degree-minus-one convention of the
recorded positive-power operator (so degree one means one, not zero, iteration).
Source: the local Frobenius paragraph (blueprint: thm-trf-l-function-euler-product). -/
def localOperator (x : ClosedPoint D X₀)
    (iota : X₀.left.residueField x.val →+* D.k)
    (hiota : iota.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (j : ℤ) : End (localCohomology D ell hEll X₀ c K x iota hiota j) :=
  (ModuleCat.restrictScalars (scalarMap c)).map
    ((NativeCondensedDerived.cohomology (WeilCoefficient.ab c) j).map
      (NativeCondensedDerived.operator (WeilCoefficient.ab c) D
        (D.geometricFrobenius X₀).hom K.obj.carrier K.obj.str
        (localClosedPoint D X₀ x iota hiota) (localClosedPointDegree D X₀ x - 1)
        (localClosedPoint_return D X₀ x iota hiota)))

/-- The inverse alternating local determinant after a compatible choice at each point.
Source: the definition of L (blueprint: thm-trf-l-function-euler-product). -/
def localFactor
    (iota : ∀ x : ClosedPoint D X₀, X₀.left.residueField x.val →+* D.k)
    (hiota : ∀ x, (iota x).comp (X₀.hom.residueFieldAlgebraMap x.val) =
      algebraMap D.k₀ D.k) (x : ClosedPoint D X₀) : PowerSeries (Scalar c) :=
  inverseAlternating (localCohomology D ell hEll X₀ c K x (iota x) (hiota x))
    (localOperator D ell hEll X₀ c K x (iota x) (hiota x)) (localClosedPointDegree D X₀ x)

/-- Coefficient n of the Euler product uses just points of degree at most n.
The finite-product operation is total; the theorem includes finiteness of this index set.
Source: clause (1), proof Step 2 (blueprint: thm-trf-l-function-euler-product). -/
def lFunction
    (iota : ∀ x : ClosedPoint D X₀, X₀.left.residueField x.val →+* D.k)
    (hiota : ∀ x, (iota x).comp (X₀.hom.residueFieldAlgebraMap x.val) =
      algebraMap D.k₀ D.k) : PowerSeries (Scalar c) :=
  PowerSeries.mk fun n ↦ PowerSeries.coeff n
    (∏ᶠ x : {x : ClosedPoint D X₀ // localClosedPointDegree D X₀ x ≤ n},
      localFactor D ell hEll X₀ c K iota hiota x.val)

variable [IsSeparated X₀.hom] (c₀ : Compactification (D.geometricFiber X₀).hom)

/-- Actual compact cohomology, restricted along the canonical ordinary scalar inclusion.
Source: clause (2) (blueprint: thm-trf-l-function-euler-product). -/
def compactCohomology (j : ℤ) : ModuleCat.{u + 1} (Scalar c) :=
  (ModuleCat.restrictScalars (scalarMap c)).obj
    ((CondensedRing.condensedRingCompactCohomology (WeilCoefficient.ab c) c₀ j).obj
      K.obj.carrier)

/-- The recorded global geometric Frobenius acting on compact cohomology.
Source: clause (2), specified F (blueprint: thm-trf-l-function-euler-product). -/
def compactOperator (j : ℤ) : End (compactCohomology D ell hEll X₀ c K c₀ j) :=
  (ModuleCat.restrictScalars (scalarMap c)).map
    (GlobalGeometricFrobenius.globalGeometricFrobeniusOnCohomology
      D ell hEll X₀ c c₀ K j).2

/-- Coefficientwise transport of the finite determinant product. Only the algebraic
closure coefficient is asserted in clause (4); the finite-extension branch adds no clause.
Source: clause (4), proof Step 6 (blueprint: thm-trf-l-function-euler-product). -/
def complexEmbeddingIdentity {ell : ℕ} [Fact ell.Prime] :
    (c : WeilCoefficient ell) → PowerSeries (Scalar c) →
      (ℤ → PowerSeries (Scalar c)) → Prop
  | .finite _, _, _ => True
  | .qbar, L, P => ∀ iota : PadicAlgCl ell →+* ℂ,
      PowerSeries.map iota L =
        ∏ᶠ j : ℤ, if Even j then (PowerSeries.map iota (P j))⁻¹
          else PowerSeries.map iota (P j)

/-- Euler-product trace formula, all four clauses over the two allowed condensed fields.
Source: latest blueprint, thm-trf-l-function-euler-product, clauses (1)--(4).
Proof: Step 0 applies det(1-TG)^(-1) = exp(sum tr(G^r) T^r/r) degreewise.
Step 1 uses independent compact/stalk finiteness and the Weil cocycle and canonical
pullback comparisons to identify global powers and the conjugate local one-circuit powers.
Step 2 uses finiteness of closed points of bounded degree, so each coefficient depends
on finitely many factors, each congruent to 1 modulo T^degree. Step 3 applies the trace
formula over Qbar and descends its finite matrix expressions to E by injective scalar
extension; grouping rational points by closed points yields e_x copies of tr(F_x^(m/e_x)).
Step 4 multiplies by T^m/m, reindexes m=e_x r, and exponentiates the coefficientwise
locally finite logarithmic identity. Compact finiteness makes the global product finite.
Step 5 applies the compact cohomological bound [0,2 dim X] to a sheaf in degree zero;
base extension preserves dimension, so on curves only degrees 0,1,2 survive and their
signs give the displayed quotient. Step 6 applies a field embedding coefficientwise;
finite matrix determinants, inverses of constant-one series, and each finite truncation
of the Euler product commute with this ring homomorphism.
(blueprint: thm-trf-l-function-euler-product). -/
theorem eulerProduct
    (iota : ∀ x : ClosedPoint D X₀, X₀.left.residueField x.val →+* D.k)
    (hiota : ∀ x, (iota x).comp (X₀.hom.residueFieldAlgebraMap x.val) =
      algebraMap D.k₀ D.k) :
    let V := compactCohomology D ell hEll X₀ c K c₀
    let F := compactOperator D ell hEll X₀ c K c₀
    let A := localFactor D ell hEll X₀ c K iota hiota
    let L := lFunction D ell hEll X₀ c K iota hiota
    (∀ j, Module.Finite (Scalar c) (V j)) ∧
    (∀ x j, Module.Finite (Scalar c)
      (localCohomology D ell hEll X₀ c K x (iota x) (hiota x) j)) ∧
    (∃ S : Finset ℤ, ∀ j, j ∉ S → IsZero (V j)) ∧
    (∃ S : Finset ℤ, ∀ x j, j ∉ S →
      IsZero (localCohomology D ell hEll X₀ c K x (iota x) (hiota x) j)) ∧
    (∀ n : ℕ, Set.Finite {x : ClosedPoint D X₀ | localClosedPointDegree D X₀ x ≤ n}) ∧
    (∀ n : ℕ, Set.Finite {x : ClosedPoint D X₀ |
      ∃ m ≤ n, PowerSeries.coeff m (A x) ≠ PowerSeries.coeff m (1 : PowerSeries _)}) ∧
    PowerSeries.constantCoeff L = 1 ∧
    (∀ (n : ℕ) (s : Finset (ClosedPoint D X₀)),
      (∀ x, localClosedPointDegree D X₀ x ≤ n → x ∈ s) →
      PowerSeries.coeff n L = PowerSeries.coeff n (∏ x ∈ s, A x)) ∧
    L = inverseAlternating V F 1 ∧
    (∀ S : Finset ℤ, (∀ j, j ∉ S → IsZero (V j)) →
      L = ∏ j ∈ S, if Even j then (determinantFactor (V j) (F j) 1)⁻¹
        else determinantFactor (V j) (F j) 1) ∧
    ((topologicalKrullDim X₀.left ≤ 1 ∧
      (∀ j : ℤ, j ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ j).obj K.obj.carrier))) →
      (∀ j : ℤ, j ∉ ({0, 1, 2} : Finset ℤ) → IsZero (V j)) ∧
      L = determinantFactor (V 1) (F 1) 1 *
        (determinantFactor (V 0) (F 0) 1 * determinantFactor (V 2) (F 2) 1)⁻¹) ∧
    complexEmbeddingIdentity c L (fun j ↦ determinantFactor (V j) (F j) 1) := by
  sorry

end WeilConjectures.CondensedWeilEuler
