/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q121
-/
module

public import Sheaf.Paper.GlobalGeometricFrobenius
public import Sheaf.Paper.GeometricHypotheses
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.CoefficientCohomologyModules
public import Sheaf.Paper.ConstantWeilStructure
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.TensorProduct.Finite
import Sheaf.Paper.SfCommonStageDirectImage
import Sheaf.Paper.FieldCohomologyScalarExtension
import Sheaf.SixFunctors.FrobeniusCohomologyTransport
import Sheaf.SixFunctors.FrobeniusPointTransport
import Sheaf.Paper.FrobeniusGeometricExchange
import Sheaf.Paper.PointFdQbarCategory
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.WeilSheaf.Finiteness
import WeilConjectures.ZetaFunction.CohomologicalFamily
import Sheaf.Paper.FiniteCoefficientPoint

/-! # Scalar extension of ordinary cohomology to Qlbar

Source: blueprint main-20261015, sec-zeta-weil/sk-thm-rh/prop-arithmetic-roots,
ordinary-cohomology-after-scalar-extension clause, and sk-input-weights/prop-weight-purity,
scalar-extension display (blueprint: lem-weil-cohomology-scalar-extension-qlbar).

All spaces and operators below use the constant Weil object at its canonical least
coefficient stage. Its ordinary direct image and point fibre are computed at that
stage. The target and its action are the live global geometric Frobenius package at
compact=false. The comparison is the balanced tensor map followed by the inverse
exact coefficient/homology comparison and the recorded Qbar-functor object clause.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v w
open scoped TensorProduct ChangeOfRings
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- Canonical tensor/ULift identification, sending a tensor m to up(a) tensor up(m).
Source: blueprint scalar-extension Step 2, size transport of its tensor map
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
def ordinaryCoefficientLiftIso {F : Type u} [Field F] {Ω : Type v} [Field Ω]
    (φ : F →+* Ω) (M : ModuleCat.{u} F) :
    (ModuleCat.extendScalars φ).obj M ≅ (frobeniusCoefficientModules φ).obj M := by
  letI := φ.toAlgebra
  exact (ULift.moduleEquiv.{v, max u v, 0}.symm.trans
    (TensorProduct.AlgebraTensorModule.uliftEquiv F Ω Ω M)).toModuleIso

/-- The normalized exact-functor comparison, computed on a complex representative.
Source: Stacks Tags 00H9, 010N, 010V and blueprint scalar-extension Step 2
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
def ordinaryCoefficientHomologyIso {F : Type u} [Field F] {Ω : Type v} [Field Ω]
    (φ : F →+* Ω) (i : ℤ)
    (C : @DerivedCategory (ModuleCat.{u} F) _ _
      (HasDerivedCategory.ofIsGrothendieckAbelian _)) :
    (@DerivedCategory.homologyFunctor (ModuleCat.{max u v} Ω) _ _
      (HasDerivedCategory.standard _) i).obj
        ((frobeniusCohomologyCoefficientExtension φ).obj C) ≅
      (frobeniusCoefficientModules φ).obj
        ((@DerivedCategory.homologyFunctor (ModuleCat.{u} F) _ _
          (HasDerivedCategory.ofIsGrothendieckAbelian _) i).obj C) := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} F) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{(max u v) + 1} (ModuleCat.{max u v} Ω) :=
    HasDerivedCategory.standard _
  let G := frobeniusCoefficientModules φ
  letI : G.Additive := by
    dsimp [G, frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  letI : PreservesFiniteLimits G := by
    dsimp [G, frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  letI : PreservesFiniteColimits G := by
    dsimp [G, frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  let P := (DerivedCategory.Q (C := ModuleCat.{u} F)).objPreimage C
  let e : (DerivedCategory.Q (C := ModuleCat.{u} F)).obj P ≅ C :=
    (DerivedCategory.Q (C := ModuleCat.{u} F)).objObjPreimageIso C
  exact (DerivedCategory.homologyFunctor (ModuleCat.{max u v} Ω) i).mapIso
      ((G.mapDerivedCategory.mapIso e).symm ≪≫ G.mapDerivedCategoryFactors.app P) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} Ω) i).app _ ≪≫
    (Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor _ _ i)
      (ShortComplex.homologyFunctorIso G)).app P ≪≫
    G.mapIso (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} F) i).app P).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} F) i).mapIso e)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom] (c₀ : Compactification Y₀.hom)

/-- The canonical small model of the least coefficient field, Q_l.
Source: blueprint scalar-extension proof, Steps 1 and 5
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
abbrev rationalFamilyCoefficient :=
  AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω (Padic.finiteCoefficientBase l Ω)

/-- Canonical embedding of the small base-stage model into the specified closure.
Source: blueprint constant stage and scalar-extension Step 2
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
def rationalFamilyEmbedding : rationalFamilyCoefficient.{u} l Ω →ₐ[ℚ_[l]] Ω :=
  { toRingHom := frobeniusCohomologyStageEmbedding.{u, v} l Ω
      (Padic.finiteCoefficientBase l Ω)
    commutes' := fun r ↦ by
      change (Padic.finiteCoefficientBase l Ω).val.subtype
        ((Shrink.algEquiv ℚ_[l] (Padic.finiteCoefficientBase l Ω).val)
          (algebraMap ℚ_[l] (rationalFamilyCoefficient.{u} l Ω) r)) = _
      rw [(Shrink.algEquiv ℚ_[l] (Padic.finiteCoefficientBase l Ω).val).commutes r]
      rfl }

/-- Ordinary cohomology of the rational constant Weil object at the base stage.
Source: blueprint scalar-extension proof, Steps 1 and 5
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
def rationalFamilyStageSpace (i : ℤ) :=
  (DerivedCategory.coefficientFdCohomology (rationalFamilyCoefficient.{u} l Ω) i).obj
    ((frobeniusCohomologyRationalFunctor D l hl
      (rationalFamilyCoefficient.{u} l Ω) Y₀ c₀ false).obj
      (constantWeilRationalComplex l (rationalFamilyCoefficient.{u} l Ω) D hl Y₀).carrier)

/-- Cohomology of point transport followed by the functor applied to theta.
Source: blueprint scalar-extension proof, Steps 1 and 5
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
def rationalFamilyStageMap (i : ℤ) :
    End (rationalFamilyStageSpace D l hl Ω Y₀ c₀ i) :=
  (DerivedCategory.coefficientFdCohomology (rationalFamilyCoefficient.{u} l Ω) i).map
    ((frobeniusCohomologyTransportRational D l hl
      (rationalFamilyCoefficient.{u} l Ω) Y₀ c₀
      (constantWeilRationalComplex l (rationalFamilyCoefficient.{u} l Ω) D hl Y₀).carrier).1 ≫
      (frobeniusCohomologyRationalFunctor D l hl
        (rationalFamilyCoefficient.{u} l Ω) Y₀ c₀ false).map
        (constantWeilRationalComplex l (rationalFamilyCoefficient.{u} l Ω) D hl Y₀).str.hom)

/-- Rational ordinary cohomology, restricting the small Q_l model to Q_l.
Source: blueprint scalar-extension proof, Steps 1 and 5
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
def rationalFamilySpace (i : ℤ) :=
  (ModuleCat.restrictScalars (algebraMap ℚ_[l] (rationalFamilyCoefficient.{u} l Ω))).obj
    (rationalFamilyStageSpace D l hl Ω Y₀ c₀ i)

/-- Rational Frobenius, with the same restriction of the scalar action.
Source: blueprint scalar-extension proof, Steps 1 and 5
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
def rationalFamilyMap (i : ℤ) : End (rationalFamilySpace D l hl Ω Y₀ c₀ i) :=
  (ModuleCat.restrictScalars (algebraMap ℚ_[l] (rationalFamilyCoefficient.{u} l Ω))).map
    (rationalFamilyStageMap D l hl Ω Y₀ c₀ i)

/-- Finite dimensionality inherited from the coefficient category and its finite base field.
Source: blueprint scalar-extension proof, Steps 1 and 5
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
instance rationalFamilySpaceFinite (i : ℤ) :
    FiniteDimensional ℚ_[l] (rationalFamilySpace D l hl Ω Y₀ c₀ i) := by
  let hfinite := DerivedCategory.coefficientFdCohomology_finite
    (rationalFamilyCoefficient.{u} l Ω) i
    ((frobeniusCohomologyRationalFunctor D l hl
      (rationalFamilyCoefficient.{u} l Ω) Y₀ c₀ false).obj
      (constantWeilRationalComplex l (rationalFamilyCoefficient.{u} l Ω) D hl Y₀).carrier)
  change Module.Finite ℚ_[l]
    ((ModuleCat.restrictScalars (algebraMap ℚ_[l]
      (rationalFamilyCoefficient.{u} l Ω))).obj
      (rationalFamilyStageSpace D l hl Ω Y₀ c₀ i))
  let : Module.Finite (rationalFamilyCoefficient.{u} l Ω)
      ((ModuleCat.restrictScalars (algebraMap ℚ_[l]
        (rationalFamilyCoefficient.{u} l Ω))).obj
        (rationalFamilyStageSpace D l hl Ω Y₀ c₀ i)) := hfinite
  let : IsScalarTower ℚ_[l] (rationalFamilyCoefficient.{u} l Ω)
      ((ModuleCat.restrictScalars (algebraMap ℚ_[l]
        (rationalFamilyCoefficient.{u} l Ω))).obj
        (rationalFamilyStageSpace D l hl Ω Y₀ c₀ i)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  exact Module.Finite.trans (rationalFamilyCoefficient.{u} l Ω) _

/-- The rational-family determinant det(1-TF) before extension to the closure.
Source: blueprint scalar-extension proof, Steps 1 and 5
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
def rationalFamilyPolynomial (i : ℤ) : Polynomial ℚ_[l] :=
  letI := rationalFamilySpaceFinite D l hl Ω Y₀ c₀ i
  (rationalFamilyMap D l hl Ω Y₀ c₀ i).hom.charpolyRev

/-- The canonical tensor comparison across R → E → Ω, with independent sizes.
It sends a tensor m to a tensor m, using the specified algebra embedding.
Source: blueprint scalar-extension map and tensor balancing
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
def baseStageScalarComparison {R : Type w} [Field R] {E : Type u} [Field E]
    [Algebra R E] {Ω : Type v} [Field Ω] [Algebra R Ω]
    (φ : E →ₐ[R] Ω) (M : ModuleCat.{u} E) :
    ModuleCat.of Ω (Ω ⊗[R] ((ModuleCat.restrictScalars (algebraMap R E)).obj M)) ⟶
      (ModuleCat.extendScalars φ.toRingHom).obj M := by
  letI : Algebra E Ω := φ.toRingHom.toAlgebra
  letI : Module R ((ModuleCat.extendScalars φ.toRingHom).obj M) :=
    Module.compHom _ (algebraMap R Ω)
  letI : IsScalarTower R Ω ((ModuleCat.extendScalars φ.toRingHom).obj M) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  refine ModuleCat.ofHom <| TensorProduct.AlgebraTensorModule.lift
    (R := R) (A := Ω) (M := Ω)
    (N := (ModuleCat.restrictScalars (algebraMap R E)).obj M)
    (P := (ModuleCat.extendScalars φ.toRingHom).obj M)
    { toFun := fun a ↦
        { toFun := fun m ↦ a ⊗ₜ[E, φ.toRingHom] m
          map_add' := fun _ _ ↦ TensorProduct.tmul_add _ _ _
          map_smul' := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
  · intro r m
    change a ⊗ₜ[E] ((algebraMap R E) r • m) =
      ((algebraMap R Ω) r) • (a ⊗ₜ[E] m)
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    change (φ ((algebraMap R E) r) * a) ⊗ₜ[E] m = _
    rw [φ.commutes]
    rfl
  · intro a b
    ext m
    exact TensorProduct.add_tmul _ _ _
  · intro a b
    ext m
    rfl

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom] (c₀ : Compactification X₀.hom)


/-- Actual ordinary H^i(X,Qbar), from the recorded global geometric Frobenius package.
Its constant Weil object is the literal least-stage pair, but the target uses the
live Qbar functor and homology.
Source: blueprint scalar-extension display
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
def ordinaryConstantQbarSpace (i : ℤ) : ModuleCat.{max u v} Ω :=
  (globalGeometricFrobeniusQbarCohomology D l hl X₀ Ω c₀
    (constantWeilAlgebraicallyClosedComplex l D hl X₀ Ω) false i).a

/-- The recorded geometric Frobenius on actual ordinary Qbar cohomology.
Source: blueprint scalar-extension Step 3 and global geometric Frobenius
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
def ordinaryConstantQbarMap (i : ℤ) :
    End (ordinaryConstantQbarSpace D l hl Ω X₀ c₀ i) :=
  globalGeometricFrobeniusQbarOnCohomology D l hl X₀ Ω c₀
    (constantWeilAlgebraicallyClosedComplex l D hl X₀ Ω) false i


/-- The Qbar-functor object clause, followed by exact coefficient/homology comparison
and inverse ULift tensor transport. Its inverse is the canonical map from the
finite-stage tensor cohomology to the actual Qbar cohomology.
Source: blueprint scalar-extension Steps 1 and 2
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
def ordinaryConstantQbarComparison (i : ℤ) :
    ordinaryConstantQbarSpace D l hl Ω X₀ c₀ i ≅
      (ModuleCat.extendScalars (rationalFamilyEmbedding.{u} l Ω).toRingHom).obj
        (rationalFamilyStageSpace D l hl Ω X₀ c₀ i) := by
  letI : HasDerivedCategory.{(max u v) + 1} (ModuleCat.{max u v} Ω) :=
    HasDerivedCategory.standard _
  exact (DerivedCategory.homologyFunctor (ModuleCat.{max u v} Ω) i).mapIso
      (eqToIso (frobeniusCohomologyQbarSourceEq D l hl X₀ Ω c₀ false
        (constantWeilAlgebraicallyClosedComplex l D hl X₀ Ω).carrier)) ≪≫
    ordinaryCoefficientHomologyIso (rationalFamilyEmbedding.{u} l Ω).toRingHom i
      ((frobeniusCohomologyRationalFunctor D l hl
        (rationalFamilyCoefficient.{u} l Ω) X₀ c₀ false).obj
          (constantWeilRationalComplex l
            (rationalFamilyCoefficient.{u} l Ω) D hl X₀).carrier).obj ≪≫
    (ordinaryCoefficientLiftIso (rationalFamilyEmbedding.{u} l Ω).toRingHom
      (rationalFamilyStageSpace D l hl Ω X₀ c₀ i)).symm


/-- H^i(X,Q_l) tensor Qbar, with the factors in Mathlib's scalar-first order.
Source: blueprint canonical-map source
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
def ordinaryConstantTensorSpace (i : ℤ) :=
  ModuleCat.of Ω (Ω ⊗[ℚ_[l]] (rationalFamilySpace D l hl Ω X₀ c₀ i))

/-- F_l tensor one on the scalar extension of rational ordinary cohomology.
Source: blueprint canonical-map equivariance clause
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
def ordinaryConstantTensorMap (i : ℤ) :
    End (ordinaryConstantTensorSpace D l hl Ω X₀ c₀ i) :=
  ModuleCat.ofHom (LinearMap.baseChange Ω (rationalFamilyMap D l hl Ω X₀ c₀ i).hom)

/-- The canonical map into actual Qbar cohomology. First send a tensor h to a tensor h
at the base stage; then invert the normalized exact coefficient/homology comparison
and the recorded Qbar-functor object clause. No arbitrary map or inverse is chosen.
Source: blueprint canonical scalar-extension map
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
def ordinaryConstantScalarExtension (i : ℤ) :
    ordinaryConstantTensorSpace D l hl Ω X₀ c₀ i ⟶
      ordinaryConstantQbarSpace D l hl Ω X₀ c₀ i :=
  baseStageScalarComparison (rationalFamilyEmbedding.{u} l Ω)
    (rationalFamilyStageSpace D l hl Ω X₀ c₀ i) ≫
      (ordinaryConstantQbarComparison D l hl Ω X₀ c₀ i).inv

/-- Finite-dimensionality of the point value, inherited from its finite stage.
Source: blueprint stagewise point-cohomology convention
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
instance ordinaryConstantQbarFinite (i : ℤ) :
    FiniteDimensional Ω (ordinaryConstantQbarSpace D l hl Ω X₀ c₀ i) := by
  let : Module.Finite (rationalFamilyCoefficient.{u} l Ω)
      (rationalFamilyStageSpace D l hl Ω X₀ c₀ i) :=
    DerivedCategory.coefficientFdCohomology_finite _ i _
  let := (rationalFamilyEmbedding.{u} l Ω).toRingHom.toAlgebra
  let : Module.Finite Ω
      ((ModuleCat.extendScalars (rationalFamilyEmbedding.{u} l Ω).toRingHom).obj
        (rationalFamilyStageSpace D l hl Ω X₀ c₀ i)) := Module.Finite.base_change _ _ _
  exact Module.Finite.equiv
    (ordinaryConstantQbarComparison D l hl Ω X₀ c₀ i).symm.toLinearEquiv

/-- Finite-dimensionality of the tensor extension of rational cohomology.
Source: blueprint scalar-extension convention
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
instance ordinaryConstantTensorFinite (i : ℤ) :
    FiniteDimensional Ω (ordinaryConstantTensorSpace D l hl Ω X₀ c₀ i) := by
  let : Module.Finite ℚ_[l] (rationalFamilySpace D l hl Ω X₀ c₀ i) :=
    rationalFamilySpaceFinite D l hl Ω X₀ c₀ i
  exact Module.Finite.base_change ℚ_[l] Ω (rationalFamilySpace D l hl Ω X₀ c₀ i)

/-- Characteristic polynomial of the algebraically closed ordinary Frobenius.
Source: blueprint algebraic-multiplicity clause
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
def ordinaryConstantQbarCharpoly (i : ℤ) : Polynomial Ω :=
  letI := ordinaryConstantQbarFinite D l hl Ω X₀ c₀ i
  (ordinaryConstantQbarMap D l hl Ω X₀ c₀ i).hom.charpoly

/-- Characteristic polynomial of F_l tensor one.
Source: blueprint algebraic-multiplicity clause
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
def ordinaryConstantTensorCharpoly (i : ℤ) : Polynomial Ω :=
  letI := ordinaryConstantTensorFinite D l hl Ω X₀ c₀ i
  (ordinaryConstantTensorMap D l hl Ω X₀ c₀ i).hom.charpoly

/-- det(1-T F_Qbar) on ordinary cohomology.
Source: blueprint final determinant display
(blueprint: lem-weil-cohomology-scalar-extension-qlbar). -/
def ordinaryConstantQbarPolynomial (i : ℤ) : Polynomial Ω :=
  letI := ordinaryConstantQbarFinite D l hl Ω X₀ c₀ i
  (ordinaryConstantQbarMap D l hl Ω X₀ c₀ i).hom.charpolyRev

/-- The canonical ordinary-cohomology comparison is an isomorphism in every integer
degree and intertwines geometric Frobenius. In the smooth-proper family range it
conjugates the operators, preserving eigenvalues, their algebraic multiplicities,
and the determinant polynomial after coefficient inclusion.
Source: blueprint main-20261015, prop-arithmetic-roots, ordinary scalar-extension
clause, and prop-weight-purity, scalar-extension display
(blueprint: lem-weil-cohomology-scalar-extension-qlbar).

Proof, following the six DAG steps:
1. The constant algebraically closed Weil object is the base-stage rational constant
   pair by def-weil-constant-weil-structure. Ordinary direct image and point evaluation
   are stagewise (def-weil-derived-direct-image, def-weil-finite-coefficient-point),
   so RΓ is represented by (Q_l,RΓ of the rational constant object).
2. def-weil-coefficient-cohomology-modules identifies its H^i with scalar-extended
   finite-stage H^i. The displayed comparison is the tensor map with adjoint h ↦ 1 tensor h.
   lem-weil-cohomology-commutes-scalar-extension and the tensor tower identification
   make it independent of the complex representative and any larger coefficient stage.
3. Both ordinary Frobenius arrows, point transport and the image of theta, are
   represented at Q_l (def-weil-frobenius-point-transport and
   def-weil-frobenius-square-exchange). Their composite is the stage image of F_l.
4. Naturality of scalar extension on cohomology gives the displayed intertwining
   equation. It holds for chain maps, inverses of quasi-isomorphisms and composites,
   hence for all derived morphisms by localization (def-weil-abstract-derived-category).
5. In the family range V_i,l is this rational H^i and F_i,l is the induced action.
   Finiteness is prop-cohomological-finiteness. Extend a rational basis by tensoring,
   then transport it through the comparison. Both Qbar operators have the same matrix.
6. Their characteristic polynomials and eigenvalues therefore agree, and so do the
   root multiplicities. The finite determinant formula commutes with coefficient
   inclusion, giving equality of det(1-TF). For dimension zero the determinant is the
   empty product 1; no eigenvalue is introduced.
-/
theorem ordinaryCohomology_scalarExtension_qlbar
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X₀ : Over (Spec (.of D.k₀))) (c₀ : Compactification X₀.hom)
    [IsProper X₀.hom] [GeometricallyConnected X₀.hom]
    (d : ℕ) (hsmooth : D.IsSmoothOfPureDimension X₀ d) :
    (∀ i : ℤ,
      Function.Bijective (ordinaryConstantScalarExtension D l hl Ω X₀ c₀ i) ∧
        ordinaryConstantTensorMap D l hl Ω X₀ c₀ i ≫
            ordinaryConstantScalarExtension D l hl Ω X₀ c₀ i =
          ordinaryConstantScalarExtension D l hl Ω X₀ c₀ i ≫
            ordinaryConstantQbarMap D l hl Ω X₀ c₀ i) ∧
    ∀ (i : ℤ), 0 ≤ i → i ≤ 2 * (d : ℤ) →
      (∃ e : ordinaryConstantTensorSpace D l hl Ω X₀ c₀ i ≅
          ordinaryConstantQbarSpace D l hl Ω X₀ c₀ i,
        e.hom = ordinaryConstantScalarExtension D l hl Ω X₀ c₀ i ∧
          e.inv ≫ ordinaryConstantTensorMap D l hl Ω X₀ c₀ i ≫ e.hom =
            ordinaryConstantQbarMap D l hl Ω X₀ c₀ i) ∧
      (∀ α : Ω,
        (Module.End.HasEigenvalue (ordinaryConstantTensorMap D l hl Ω X₀ c₀ i).hom α ↔
          Module.End.HasEigenvalue (ordinaryConstantQbarMap D l hl Ω X₀ c₀ i).hom α) ∧
        (ordinaryConstantTensorCharpoly D l hl Ω X₀ c₀ i).rootMultiplicity α =
          (ordinaryConstantQbarCharpoly D l hl Ω X₀ c₀ i).rootMultiplicity α) ∧
      (rationalFamilyPolynomial D l hl Ω X₀ c₀ i).map (algebraMap ℚ_[l] Ω) =
        ordinaryConstantQbarPolynomial D l hl Ω X₀ c₀ i := by
  sorry

end WeilConjectures
