/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionLineChartScalars
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientFlatModel
import WeilConjectures.AlgebraicGeometry.Finite.FiniteLocallyFreeLineModels
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleSingleSupport
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

/-! # Finite-Tor constructibility of the shifted root-line input

Source: blueprint finite reduction, Step 2: compatibility with the invertible twist.
(blueprint: lem-pur-finite-reduction-line-input-constructible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

private instance lineInput_small (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _

/-- The shifted root line, after the specified exact comparison and realization,
is finite-Tor constructible at every positive coefficient level.
Source: blueprint finite reduction Step 2, invertibility of the coefficient twist;
Stacks 03PK and 08G2
(blueprint: lem-pur-finite-reduction-line-input-constructible).
Proof: choose a primitive ell^n-th root in the algebraically closed base field;
ell is different from its characteristic. Its section-normalized root chart
identifies the ordinary root line with the constant rank-one coefficient sheaf.
The latter is constructible and flat, with degree-zero Tor interval [0,0].
Exact etale-to-pro-etale comparison and intrinsic realization preserve its
constructibility and Tor interval. The canonical shift comparisons identify the
displayed object with the coefficient unit shifted by two. Shift closure gives
Tor interval [-2,-2] and bounded constructible cohomology. Isomorphism invariance
transfers both properties to the displayed input. The empty scheme and level one
satisfy exactly the same construction; no ramification divisibility is needed. -/
theorem finiteReductionLineInput_constructible (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T
      ((Scheme.sfIntrinsicDerivedEquivalence T P.Ring).functor.obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
          ((Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧))) := by
  have hl : (P.coefficients.l : P.field.k) ≠ 0 := by
    let : Fintype P.field.k₀ := Fintype.ofFinite _
    have : Fact P.field.p.Prime := ⟨P.field.prime⟩
    have : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow (by
      rw [← Nat.card_eq_fintype_card, P.field.card_base, P.field.cardinality_eq])
    have : CharP P.field.k P.field.p :=
      charP_of_injective_algebraMap' P.field.k₀ P.field.p
    exact CharP.cast_ne_zero_of_ne_of_prime _
      (Fact.out : P.coefficients.l.Prime) P.coefficients.different.symm
  have : NeZero (P.diagonalExponent : P.field.k) := ⟨by
    change ((P.coefficients.l ^ P.level : ℕ) : P.field.k) ≠ 0
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hl⟩
  have : IsAlgClosed P.field.k := IsAlgClosure.isAlgClosed P.field.k₀
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot P.field.k P.diagonalExponent
  let A := P.Ring
  let R := Scheme.proEtaleConstantRing T A
  let C := Scheme.proEtaleRingModules T R
  let U := Scheme.proEtaleConstantModule T A
  let K := (_root_.DerivedCategory.singleFunctor C 0).obj U
  have hU : U.IsFiniteLocallyFreeOfRank 1 :=
    (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one.{u + 1, u, u + 1}
      U).mp inferInstance
  have hc := (Scheme.finiteLocallyFreeLine_models T A U hU).2.1
  obtain ⟨hs, hc', _, _⟩ := Scheme.constructible_single_support T A U hc K (Iso.refl _)
  have hK : Scheme.intrinsicFiniteTorsionConstructible
      P.coefficients.l P.extension P.level P.level_pos T K := ⟨hs, hc'⟩
  have : ∀ x : T, Invertible (P.coefficients.l : T.residueField x) := fun x ↦
    IsUnit.invertible (by
      simpa only [map_natCast] using
        (P.coefficientPrime_isUnit_stalk T (T ↘ Spec (.of P.field.k)) x).map
          (T.residue x).hom)
  have ht : Scheme.HasProEtaleTorAmplitude T A K 0 0 := by
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
    let : MonoidalPreadditive C := SheafOfModules.monoidalPreadditive_kfi R
    let M := (CochainComplex.singleFunctor C 0).obj U
    apply (Scheme.finiteCoefficient_torAmplitude_iff_flatModel P.field P.coefficients.l
      P.coefficients.different P.extension P.level P.level_pos T K hK 0 0 le_rfl).2
    refine ⟨M, ?_, ?_, ?_⟩
    · intro i
      have hflat : ObjectProperty.flat (M.X i) := by
        by_cases hi : i = 0
        · exact ObjectProperty.prop_of_iso _
            (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 U i hi).symm
            (ObjectProperty.prop_unit _)
        · exact ObjectProperty.flat_of_isZero
            (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
      exact (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} R _).symm hflat.2
    · intro i hi
      exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
    · exact ⟨(_root_.DerivedCategory.singleFunctorIsoCompQ C 0).app U⟩
  let Q := finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T
  have : Q.IsClosedUnderIsomorphisms :=
    (Scheme.finite_ctf_isTriangulated P.coefficients.l P.extension P.level P.level_pos T).1
  have : Q.IsTriangulated :=
    (Scheme.finite_ctf_isTriangulated P.coefficients.l P.extension P.level P.level_pos T).2.1
  have hu : Q (P.coefficientUnit T) :=
    Q.prop_of_iso (finiteReductionUnitModel A T).symm ⟨hK, 0, 0, ht⟩
  exact Q.prop_of_iso (P.finiteReductionLineChart T ζ hζ).symm
    ((Q.prop_shift_iff_of_isStableUnderShift (P.coefficientUnit T) (2 : ℤ)).mpr hu)

end WeilConjectures.PurityFiniteSetting
