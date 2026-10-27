/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.Paper.AdicPunctualWeights
public import Sheaf.Paper.CommonStageLisse
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix

import Sheaf.Paper.ImmersionWeilPullbackLocalBehavior
import Sheaf.Paper.AdicLocalFrobeniusModelConjugacy
import WeilConjectures.Mathlib.Algebra.Polynomial.Reverse

/-!
# Local characteristic factors on the common-stage Weil heart

Source: Deligne, Weil II (1.2.13), and blueprint main-20261015,
def-wf-iota-real (blueprint: def-wf-iota-real).

The determinant is computed on an actual finite-stage stalk and included into the
specified coefficient closure. Its descent property determines a unique polynomial,
so no arbitrary stalk operator or unstructured choice of data is introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

private theorem mapped_charpolyRev
    {E : Type u} [Field E] {Ω : Type v} [Field Ω]
    (φ : E →+* Ω) (M : ModuleCat.{w} E) [FiniteDimensional E M] (f : M ⟶ M) :
    let := φ.toAlgebra
    letI : FiniteDimensional Ω ((ModuleCat.extendScalars φ).obj M) := by
      change Module.Finite Ω (TensorProduct E Ω M)
      infer_instance
    ((ModuleCat.extendScalars φ).map f).hom.charpolyRev = f.hom.charpolyRev.map φ := by
  let := φ.toAlgebra
  change (f.hom.baseChange Ω).charpoly.reverse = f.hom.charpoly.reverse.map φ
  rw [LinearMap.charpoly_baseChange]
  exact Polynomial.reverse_map φ.injective _

private theorem charpolyRev_iso
    {Ω : Type u} [Field Ω] {M N : ModuleCat.{v} Ω}
    [FiniteDimensional Ω M] [FiniteDimensional Ω N]
    (e : M ≅ N) (f : M ⟶ M) (g : N ⟶ N) (h : e.hom ≫ g = f ≫ e.hom) :
    f.hom.charpolyRev = g.hom.charpolyRev := by
  have hg : e.toLinearEquiv.conj f.hom = g.hom := by
    ext x
    have hx := congrArg (fun z : M ⟶ N ↦ z (e.inv x)) h
    simpa using hx.symm
  unfold LinearMap.charpolyRev
  rw [← hg, LinearEquiv.charpoly_conj]

/-- The finite-stage determinant det(1-T F_y), included into the coefficient closure.
The finite-dimensionality proof is the defining property of the point complex.
Source: blueprint local characteristic factor (blueprint: def-wf-iota-real). -/
def sfFiniteStageLocalCharacteristicFactor (L : Padic.FiniteCoefficientFields l Ω)
    (K : sfWeilComplex D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    Polynomial Ω :=
  letI : FiniteDimensional (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      ((DerivedCategory.coefficientFdCohomology
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) 0).obj
        (localPointComplex l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
          D hl Y₀ K (localClosedPoint D Y₀ y ι hι))) :=
    DerivedCategory.coefficientFdCohomology_finite _ 0 _
  (localClosedFrobeniusCohomology l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) D hl Y₀ K y ι hι 0).hom.charpolyRev.map
      (L.val.subtype.comp (Shrink.algEquiv ℚ_[l] L.val).toRingHom)

/-- The descended determinant is uniquely determined by every finite Weil presentation
and every compatible choice of geometric point. This is the well-definedness assertion
for the local factor, including coefficient and geometric-point independence.
Source: blueprint local characteristic factor (blueprint: def-wf-iota-real).
Proof: descend the object, Weil isomorphism, inverse and inverse equations to a common
finite extension, using the common-stage Hom description. A closed residue field embeds
in the algebraic closure over k_0. Compute det(1-T F_y) at this presentation. For another
presentation, descend the isomorphism of Weil pairs to a further common finite extension.
Naturality of the iterated Weil structure and point transport intertwines the local
operators. Changing the residue embedding conjugates the local operator along its finite
Frobenius orbit. Determinants are invariant under conjugacy and commute with scalar
extension, so all displayed polynomials agree after inclusion into Ω. Any such
presentation evaluates the universal characterization and proves uniqueness. -/
theorem sfLocalCharacteristicFactor_existsUnique
    (F : sfCommonStageWeilSheaf D l hl Y₀ Ω)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) :
    ∃! P : Polynomial Ω,
      ∀ (L : Padic.FiniteCoefficientFields l Ω)
        (K : sfWeilComplex D l hl Y₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)),
        Nonempty (F.obj ≅ sfWeilStageObject D l hl Y₀ Ω L K) →
        ∀ (ι : Y₀.left.residueField y.val →+* D.k)
          (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k),
          P = sfFiniteStageLocalCharacteristicFactor D l hl Ω Y₀ L K y ι hι := by
  obtain ⟨C⟩ := immersionWeil_pullback_local_behavior D l hl Y₀ Y₀ (𝟙 Y₀) Ω
  obtain ⟨L, K, ⟨e⟩⟩ := C.complex_descent F.obj
  let := (Y₀.hom.residueFieldAlgebraMap y.val).toAlgebra
  have : Module.Finite D.k₀ (Y₀.left.residueField y.val) :=
    ((closedPoint_iff_residueField_trdeg_zero_and_finite Y₀.hom y.val).2.1).mp y.property
  let ι : Y₀.left.residueField y.val →ₐ[D.k₀] D.k := IsAlgClosed.lift
  let hι := ι.comp_algebraMap
  let P := sfFiniteStageLocalCharacteristicFactor D l hl Ω Y₀ L K y ι.toRingHom hι
  have hP : ∀ (L' : Padic.FiniteCoefficientFields l Ω)
      (K' : sfWeilComplex D l hl Y₀
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L')),
      Nonempty (F.obj ≅ sfWeilStageObject D l hl Y₀ Ω L' K') →
      ∀ (ι' : Y₀.left.residueField y.val →+* D.k)
        (hι' : ι'.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k),
        P = sfFiniteStageLocalCharacteristicFactor D l hl Ω Y₀ L' K' y ι' hι' := by
    intro L' K' hK' ι' hι'
    obtain ⟨e'⟩ := hK'
    obtain ⟨a, ha⟩ := sfLocalFrobenius_model_conjugacy D l hl Ω Y₀ L L' K K'
      ⟨e.symm ≪≫ e'⟩ y ι.toRingHom ι' hι hι' 0
    let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L
    let E' := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L'
    let M := (DerivedCategory.coefficientFdCohomology E 0).obj
      (localPointComplex l E D hl Y₀ K (localClosedPoint D Y₀ y ι.toRingHom hι))
    let M' := (DerivedCategory.coefficientFdCohomology E' 0).obj
      (localPointComplex l E' D hl Y₀ K' (localClosedPoint D Y₀ y ι' hι'))
    have : FiniteDimensional E M := DerivedCategory.coefficientFdCohomology_finite _ 0 _
    have : FiniteDimensional E' M' := DerivedCategory.coefficientFdCohomology_finite _ 0 _
    let := (sfAdicCoefficientEmbedding.{u} l Ω L).toAlgebra
    let := (sfAdicCoefficientEmbedding.{u} l Ω L').toAlgebra
    have : FiniteDimensional Ω
        ((ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω L)).obj M) := by
      change Module.Finite Ω (TensorProduct E Ω M)
      infer_instance
    have : FiniteDimensional Ω
        ((ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω L')).obj M') := by
      change Module.Finite Ω (TensorProduct E' Ω M')
      infer_instance
    have hchar := charpolyRev_iso a _ _ ha
    rw [mapped_charpolyRev, mapped_charpolyRev] at hchar
    exact hchar
  refine ⟨P, hP, ?_⟩
  intro Q hQ
  exact (hQ L K ⟨e⟩ ι.toRingHom hι).trans (hP L K ⟨e⟩ ι.toRingHom hι).symm

/-- P_y(T)=det(1-T F_y) of a constructible Weil sheaf, with multiplicities.
It is the unique polynomial prescribed on all finite-stage presentations; only the
proof of descent is postponed, not the choice of an undetermined object.
Source: blueprint local characteristic factor (blueprint: def-wf-iota-real). -/
def sfLocalCharacteristicFactor (F : sfCommonStageWeilSheaf D l hl Y₀ Ω)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) : Polynomial Ω :=
  (sfLocalCharacteristicFactor_existsUnique D l hl Ω Y₀ F y).exists.choose

/-- Reality means that every embedded local characteristic factor has real coefficients.
Source: blueprint reality clause (blueprint: def-wf-iota-real). -/
def SfIsReal (iota : Ω →+* ℂ) (F : sfCommonStageWeilSheaf D l hl Y₀ Ω) : Prop :=
  ∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) (n : ℕ),
    star (iota ((sfLocalCharacteristicFactor D l hl Ω Y₀ F y).coeff n)) =
      iota ((sfLocalCharacteristicFactor D l hl Ω Y₀ F y).coeff n)

/-- Realizability is being a retract, in Weil sheaves, of a real lisse Weil sheaf.
The lisse condition uses the existing completed integral lattice construction.
Source: Deligne, Weil II (1.2.13) (blueprint: def-wf-iota-real). -/
def SfIsRealizable (iota : Ω →+* ℂ) (F : sfCommonStageWeilSheaf D l hl Y₀ Ω) : Prop :=
  ∃ (G : sfCommonStageWeilSheaf D l hl Y₀ Ω) (i : F ⟶ G) (r : G ⟶ F),
    HasCommonStageLisseLattice l Ω (D.geometricFiber Y₀).left G.obj.carrier ∧
      SfIsReal D l hl Ω Y₀ iota G ∧ i ≫ r = 𝟙 F

end WeilConjectures
