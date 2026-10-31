/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionMonoidalData
import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTensorDescent
import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionGeometricSquare
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModelSupplement
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement

/-! # Derived monoidal reduction of integral coefficient towers

Source: blueprint/latest, integral direct-image proof, paragraph (3); Stacks 03EL,
07A4, 0G7E and 0D6D (blueprint: lem-sp-reduction-derived-monoidal-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

private theorem total_kflat (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (W : SpReductionMonoidalData l E T D r) :
    SpReductionTotalKflat l E T D r W := by
  intro P Q hP hQ fP fQ
  have h := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    (spIntegralSectionRing l E T) P Q hP hQ fP fQ
  exact ⟨h.1, h.2.1⟩

private theorem level_kflat (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (W : SpReductionMonoidalData l E T D r) :
    SpReductionLevelKflat l E T D r W := by
  intro P hP _fP n
  let A := (D.scalar (spIntegralReductionScalar l E T r.coefficient n)).model
  exact SheafOfModules.changeOfRings_isKFlat_independentCoefficients
    (spIntegralReductionScalar l E T r.coefficient n) P A.E A.obj_eq A.map_eq hP


private theorem monoidal_exists (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) : Nonempty (SpReductionMonoidalTower l E T D r) := by
  obtain ⟨source, sourceModel, sourceSymmetry, ⟨sourceCoherence⟩⟩ :=
    ringedDerived_closed_symmetric_monoidal.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology T) (spIntegralSectionRing l E T)
  obtain ⟨target, targetModel, targetSymmetry, ⟨targetCoherence⟩⟩ :=
    ringedDerived_closed_symmetric_monoidal.{u + 1, u, u + 1, u + 2}
      (coefficientSequenceTopology (Scheme.ProEt.topology T)) (spMonoidalSystemRing l E T)
  obtain ⟨C⟩ := sp_reduction_strict_tensor_balancing l E T D r
  obtain ⟨μ, monoidal, hTensor, hSystem, hDerived⟩ :=
    sp_reduction_tensor_comparison_descent l E T D r C
      source sourceModel sourceSymmetry sourceCoherence
      target targetModel targetSymmetry targetCoherence
  let W : SpReductionMonoidalData l E T D r := {
    source := source
    sourceModel := sourceModel
    target := target
    targetModel := targetModel
    sourceSymmetry := sourceSymmetry
    sourceCoherence := sourceCoherence
    targetSymmetry := targetSymmetry
    targetCoherence := targetCoherence
    μ := μ
    monoidal := monoidal
    ordinary := C.ordinary
    chain := C.chain }
  exact ⟨{
    toSpReductionMonoidalData := W
    monoidal_tensor := hTensor
    forward := C.forward
    inverse := C.inverse
    summand := C.summand
    total_kflat := total_kflat l E T D r W
    system_kflat := hSystem
    level_kflat := level_kflat l E T D r W
    derived := hDerived }⟩

/-- Derived reduction has the canonical coherent tensor and geometric comparisons
on all ordinary unbounded complexes, without completeness or coefficient flatness.
The family of witnesses fixes the tensor operation once for each scheme and reduction;
the geometric comparison is compatible with those same choices at both ends.

Source: blueprint, integral direct-image proof, paragraph (3); Stacks 03EL, 07A4,
0G7E and 0D6D (blueprint: lem-sp-reduction-derived-monoidal-tower).

Proof: realize towers as modules on the vertical sequence site. Its constant/limit
projection has scalar map given by the actual completion projections, so its derived
pullback is the recorded reduction by the normalized left-derived universal property.
Choose flat-term K-flat resolutions. Their signed direct-sum tensor is K-flat with
flat terms, and arbitrary scalar extension preserves this class. On each summand,
balanced sheaf tensor sends (q tensor a) tensor (q' tensor b) to
(q tensor q') tensor ab. Its inverse inserts 1 in the first quotient factor. These
are inverse chain maps: the differential has the same Koszul sign on either side,
and every quotient map preserves products and 1. Their morphisms on the sequence
site therefore commute strictly with all consecutive transitions. K-flat localization
in both inputs descends this natural isomorphism and fixes the whole-system derived
square, independently of resolutions. For a scheme map, inverse image commutes with
the constant sequence and the actual completion projections. The ringed pullback
composition comparison gives nu; on Kan-extension generators it is the identity on
the tensor q tensor a. Exact evaluation gives the usual level pullback/scalar map.
Finally both association paths multiply three coefficients to abc, the unit is 1,
and pulling back the quotient augmentation carries q to q tensor 1. The canonical
ringed derived monoidal and composition comparisons descend these equations to the
displayed associator, unit, augmentation and tensor compatibilities. No flatness of
the quotient map, boundedness, constructibility or derived completeness is used. -/
theorem sp_reduction_derived_monoidal_tower :
    ∃ M : ∀ (T : Scheme.{u}) (_hl : ∀ x : T, IsUnit (l : T.residueField x))
      (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D),
      SpReductionMonoidalTower l E T D r,
    ∀ (T T' : Scheme.{u}) (hl : ∀ x : T, IsUnit (l : T.residueField x))
      (hl' : ∀ x : T', IsUnit (l : T'.residueField x)) (g : T' ⟶ T)
      (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
      (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D'),
    ∃ p : SpReductionPullbackTower l E T D r g D' r',
      Nonempty (SpReductionPullbackCoherence l E T D r (M T hl D r) g D' r'
        (M T' hl' D' r') p) := by
  classical
  let M := fun (T : Scheme.{u}) (_hl : ∀ x : T, IsUnit (l : T.residueField x))
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D) ↦
      Classical.choice (monoidal_exists l E T D r)
  refine ⟨M, ?_⟩
  intro T T' hl hl' g D r D' r'
  exact sp_reduction_geometric_tensor_square l E T hl D r (M T hl D r)
    hl' g D' r' (M T' hl' D' r')


end AlgebraicGeometry.ProEtale
