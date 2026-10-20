/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.Paper.AdicPunctualWeights
public import Sheaf.Paper.CommonStageLisse
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix

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
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

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
  sorry

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
