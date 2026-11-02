/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupPoint.PointFiberTensorSystem
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointTensorReduction.CondensedPointTensorReduction
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.IntrinsicCondensedCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedGeometricPointPerfect
import WeilConjectures.AlgebraicGeometry.FinitePointComparison.CondensedPointDerivedScalarComparison
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence

/-! # Native condensed point fibres preserve derived tensor

Source: latest blueprint, sec-six-functors/sk-thm-sf-kunneth-relative/_section.md,
compact-support specialization to Spec k, finite reduction and scalar extension
(blueprint: lem-sf-point-fibre-derived-tensor).

All maps use the ordinary unbounded module-derived categories. The tensor comparison
is the existing normalized section cup; the coherence assertions are restricted to
bounded constructible inputs of finite Tor amplitude. Scalar comparisons are normalized
on flat-term K-flat representatives, including the sheafification unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings

open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

attribute [local instance] Mod.extendScalarsMonoidal
attribute [local instance 20000]
  CategoryTheory.InternalAbelianSheafModule.comparison_essentiallySmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

namespace AlgebraicGeometry.ProEtale.CondensedRing.NativePointTensor

/-- Exactly the four native coefficient forms, with every positive uniformizer exponent.
Source: relative product theorem, compact-support specialization at Spec k
(blueprint: lem-sf-point-fibre-derived-tensor). -/
def IsCoefficient (ell : ℕ) [Fact ell.Prime] (Λ : ScalarSixRing.{u}) : Prop :=
  (∃ (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E)
      (_hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E))
      (n : ℕ),
    Λ = PointTensorReduction.finiteCoefficient ell E π n) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ell, Λ = latticeIntegralRing ell E) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ell, Λ = scalarSixFieldRing ell E) ∨
  Λ = latticeClosureRing ell

/-- The actual integral quotient map is specified on every profinite section. This
property determines the morphism uniquely and does not replace it by an arbitrary map.
Index n means the positive exponent n+1, including exponent one.
Source: relative product theorem, integral reduction clause
(blueprint: lem-sf-point-fibre-derived-tensor). -/
def IsIntegralReduction (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E) (n : ℕ)
    (a : latticeIntegralRing.{u} ell E ⟶ PointTensorReduction.finiteCoefficient ell E π n) :
    Prop :=
  ∀ (S : Profinite.{u}) (x : (latticeIntegralRing.{u} ell E).X.obj.obj (op S)) (s : S),
    ((a.hom.hom.hom.app (op S)) x).down s =
      Ideal.Quotient.mk ((Ideal.span {π}) ^ (n + 1)) (x.down s)

/-- The coefficient maps in the statement, including equal finite levels and equal
finite subextensions. Integral reduction is pinned sectionwise by its quotient formula.
Source: relative product theorem, finite-reduction and scalar-extension clause
(blueprint: lem-sf-point-fibre-derived-tensor). -/
inductive IsScalarMap (ell : ℕ) [Fact ell.Prime] :
    {Λ Λ' : ScalarSixRing.{u}} → (Λ ⟶ Λ') → Prop
  | finite (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E)
      (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E))
      {m n : ℕ} (h : n ≤ m) :
      IsScalarMap ell (PointTensorReduction.finiteCoefficientMap ell E π h)
  | reduction (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E)
      (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E))
      (n : ℕ) (a : latticeIntegralRing ell E ⟶ PointTensorReduction.finiteCoefficient ell E π n)
      (ha : IsIntegralReduction ell E π n a) : IsScalarMap ell a
  | localization (E : PadicAlgCl.FiniteIntermediateField ell) :
      IsScalarMap ell (scalarSixIntegralToField ell E)
  | integral {E E' : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ E') :
      IsScalarMap ell (latticeIntegralMap ell h)
  | field {E E' : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ E') :
      IsScalarMap ell
        (⟨⟨Profinite.padicSubfieldRingObjMap ell h⟩⟩ :
          scalarSixFieldRing ell E ⟶ scalarSixFieldRing ell E')
  | closure (E : PadicAlgCl.FiniteIntermediateField ell) :
      IsScalarMap ell
        (⟨⟨Profinite.padicSubfieldRingObjToPadicAlgCl ell E⟩⟩ :
          scalarSixFieldRing ell E ⟶ latticeClosureRing ell)

variable (Λ : ScalarSixRing.{u}) (k : Type u) [Field k] [IsAlgClosed k]

/-- Coherence of the fixed section cup. Invertibility makes its inverse unique;
these equations also express naturality, associativity, signed symmetry and both
unit laws for that inverse. Tensor products in these equations are ambient tensors.
Source: relative product theorem, tensor coherence at Spec k
(blueprint: lem-sf-point-fibre-derived-tensor). -/
structure TensorCoherence : Prop where
  invertible (M N : CondensedGeometricPoint.Complexes Λ.X k)
    (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M)
    (hN : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) N) :
    IsIso (TraceCupPoint.tensor Λ.X k M N)
  unit_invertible : IsIso (TraceCupPoint.pointFiberUnit (Λ := Λ) k)
  naturality {M M' N N' : CondensedGeometricPoint.Complexes Λ.X k}
    (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M)
    (hM' : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M')
    (hN : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) N)
    (hN' : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) N')
    (f : M ⟶ M') (g : N ⟶ N') :
    ((TraceCupPoint.fiber Λ.X k).map f ⊗ₘ (TraceCupPoint.fiber Λ.X k).map g) ≫
        TraceCupPoint.tensor Λ.X k M' N' =
      TraceCupPoint.tensor Λ.X k M N ≫ (TraceCupPoint.fiber Λ.X k).map (f ⊗ₘ g)
  associativity (M N P : CondensedGeometricPoint.Complexes Λ.X k)
    (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M)
    (hN : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) N)
    (hP : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) P) :
    (TraceCupPoint.tensor Λ.X k M N ▷ (TraceCupPoint.fiber Λ.X k).obj P) ≫
        TraceCupPoint.tensor Λ.X k (M ⊗ N) P ≫
        (TraceCupPoint.fiber Λ.X k).map (α_ M N P).hom =
      (α_ ((TraceCupPoint.fiber Λ.X k).obj M) ((TraceCupPoint.fiber Λ.X k).obj N)
        ((TraceCupPoint.fiber Λ.X k).obj P)).hom ≫
        ((TraceCupPoint.fiber Λ.X k).obj M ◁ TraceCupPoint.tensor Λ.X k N P) ≫
        TraceCupPoint.tensor Λ.X k M (N ⊗ P)
  symmetry (M N : CondensedGeometricPoint.Complexes Λ.X k)
    (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M)
    (hN : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) N) :
    TraceCupPoint.tensor Λ.X k M N ≫
        (TraceCupPoint.fiber Λ.X k).map
          ((TraceCupPoint.siteBraiding Λ.X (Spec (.of k))).braiding M N).hom =
      ((TraceCupPoint.scalarBraiding Λ.X).braiding
        ((TraceCupPoint.fiber Λ.X k).obj M) ((TraceCupPoint.fiber Λ.X k).obj N)).hom ≫
        TraceCupPoint.tensor Λ.X k N M
  left_unit (M : CondensedGeometricPoint.Complexes Λ.X k)
    (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M) :
    (TraceCupPoint.pointFiberUnit (Λ := Λ) k ▷ (TraceCupPoint.fiber Λ.X k).obj M) ≫
        TraceCupPoint.tensor Λ.X k (𝟙_ _) M ≫
        (TraceCupPoint.fiber Λ.X k).map (λ_ M).hom =
      (λ_ ((TraceCupPoint.fiber Λ.X k).obj M)).hom
  right_unit (M : CondensedGeometricPoint.Complexes Λ.X k)
    (hM : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) M) :
    ((TraceCupPoint.fiber Λ.X k).obj M ◁ TraceCupPoint.pointFiberUnit (Λ := Λ) k) ≫
        TraceCupPoint.tensor Λ.X k M (𝟙_ _) ≫
        (TraceCupPoint.fiber Λ.X k).map (ρ_ M).hom =
      (ρ_ ((TraceCupPoint.fiber Λ.X k).obj M)).hom

variable {Λ} {Λ' : ScalarSixRing.{u}}

/-- The native section cup is invertible on Dctf, with its unique natural inverse,
coefficient evaluation unit, associativity, Koszul symmetry and unitor constraints.
The normalized scalar square holds for every listed finite reduction, integral
reduction, rationalization, finite-field inclusion and finite-subextension inclusion
into the actual finite-subextension-valued closure coefficient ring.

Source: latest blueprint sec-six-functors/sk-thm-sf-kunneth-relative/_section.md,
compact-support specialization and finite-reduction/scalar-extension clauses
(blueprint: lem-sf-point-fibre-derived-tensor).

Proof: (1) lem-sf-condensed-geometric-point-perfect and the specified scalar realization
of def-weil-finite-coefficient-point identify each bounded constructible finite-Tor
object with the realization of its fibre, taking the coefficient unit to its scalars.
(2) Apply lem-sf-condensed-point-ambient-tensor-comparison to M and the scalar fibre
of N. Its balanced comparison and the realization counit identify its inverse with
the normalized section cup. Naturality, associativity, the Koszul interchange and
unit constraints descend from the same flat-term K-flat total-tensor formulas.
(3) lem-sf-condensed-point-derived-scalar-comparison supplies the finite quotient
squares, including equal levels, without flatness of a quotient map.
(4) lem-sf-point-fibre-integral-scalar-coherence supplies integral reductions with
the specified sectionwise quotient and their representative tensor and unit squares.
(5) lem-sf-point-fibre-rational-scalar-coherence supplies localization and finite
extension squares. lem-sf-point-fibre-qbar-scalar-coherence supplies all finite
subextension maps into the closure; its filtered compatibility retains the actual
finite-subextension coefficient sheaf. Their representative normalizations identify
these comparisons with those above, giving the simultaneous coefficient-change claim.
-/
theorem point_fibre_derived_tensor (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p) :
    (∀ (Λ : ScalarSixRing.{u}), IsCoefficient ell Λ → TensorCoherence Λ D.k) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E),
      Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E) →
      ∀ n : ℕ, ∃ a : latticeIntegralRing ell E ⟶ PointTensorReduction.finiteCoefficient ell E π n,
        IsIntegralReduction ell E π n a) ∧
    (∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ'),
      IsScalarMap ell a → Nonempty (ScalarCompatibility D.k a)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.NativePointTensor
