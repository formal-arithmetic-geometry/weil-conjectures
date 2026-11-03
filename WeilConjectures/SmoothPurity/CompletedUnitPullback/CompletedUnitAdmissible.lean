/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitPullbackData
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientFlatModel
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

/-! # Regular completed units and their strict reductions

Source: Bhatt--Scholze, Sections 3.5 and 6.5, Lemmas 6.5.9 and 6.8.2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  Scheme.coefficientProEtaleDirectRingMap WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.PrimitiveCounit.ringMap
namespace WeilConjectures.CompletedUnitPullback
attribute [local irreducible] calculus systemUnit systemObject systemMap systemMultiplication
  finiteMultiplication rationalObject integralObject rationalSource modelScalar modelUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem tor_iso (W : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : Scheme.proEtaleDerivedCategory W A} (e : K ≅ L) {a b : ℤ}
    (h : Scheme.HasProEtaleTorAmplitude W A K a b) :
    Scheme.HasProEtaleTorAmplitude W A L a b := by
  refine ⟨h.1, ?_⟩
  rintro M P ⟨r⟩ f hf hP N i hi
  exact h.2 M P ⟨r ≪≫ e.symm⟩ f hf hP N i hi

/-- The completed regular module is constructible with uniform Tor interval [0,0].
Source: Bhatt--Scholze, Definition 6.5.1 and Lemma 6.8.2(1); Stacks 08G1.
(blueprint: lem-pur-completed-unit-admissible).
Proof: existing constant coefficient constructibility gives constructibility,
completeness, and the actual reduction isomorphisms. The finite regular module
has its degree-zero complex as a bounded flat model: its only nonzero term is
the tensor unit, whose tensor functor is the identity and hence exact. The
bounded flat-model criterion gives Tor interval [0,0]. Transport this interval
along each specified reduction isomorphism. The same interval works at every
level. Local constancy is that of the finite regular coefficient sheaf. -/
theorem completedUnitAdmissible (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    Admissible l E W := by
  classical
  have hc := integralConstantCoefficient_constructible l E W D hl
  have ht (n : ℕ) : Scheme.HasProEtaleTorAmplitude W
      (Padic.coefficientExtensionRing l E (n + 1))
      (finiteConstantCoefficientObject l E W n) 0 0 := by
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let R := Scheme.proEtaleConstantRing W A
    let C := Scheme.proEtaleRingModules W R
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory R
    let P := (CochainComplex.singleFunctor C 0).obj
      (SheafOfModules.unit (integralCoefficientSheaf l E W n))
    apply (Scheme.finiteCoefficient_torAmplitude_iff_flatModel D l hl E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) W _
      (finiteConstantCoefficient_constructible l E W n).1 0 0 le_rfl).2
    refine ⟨P, ?_, ?_, ?_⟩
    · intro i
      have hflat : ObjectProperty.flat (P.X i) := by
        by_cases hi : i = 0
        · exact ObjectProperty.prop_of_iso _
            (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0
              (SheafOfModules.unit (integralCoefficientSheaf l E W n)) i hi).symm
            (ObjectProperty.prop_unit _)
        · exact ObjectProperty.prop_of_isZero _
            (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
      exact (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso R _).symm hflat.2
    · intro i hi
      exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
    · exact ⟨(DerivedCategory.singleFunctorIsoCompQ C 0).app _⟩
  have hr (n : ℕ) : Scheme.HasProEtaleTorAmplitude W
      (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension l E W n).obj
        (integralConstantCoefficientObject l E W)) 0 0 := by
    let := (hc.2.2.2 n).1
    exact tor_iso W _ (asIso (constantCoefficientReductionMap l E W n)).symm (ht n)
  refine ⟨⟨hc.2.1, 0, 0, le_rfl, hr⟩, ?_⟩
  intro n
  exact ⟨(hc.2.2.2 n).1, (hc.2.2.2 n).2, hr n,
    (finiteConstantCoefficient_constructible l E W n).2.1⟩

end WeilConjectures.CompletedUnitPullback
