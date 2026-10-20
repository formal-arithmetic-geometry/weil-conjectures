/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.UniformCompleteTriangulated
public import Sheaf.Paper.ProjectionCompactification
public import Sheaf.Paper.ProperBaseChangeFourCorners
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.AlgebraicGeometry.DimensionAffineOpenCover
import WeilConjectures.AlgebraicGeometry.Dimension
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.CompletedTowerDirectImage
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.Topology.Stratification
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Sheaf.AlgebraicGeometry.FiniteTypeGeometryFibreBound
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.ExtensionZeroStratifiedPerfect
import Sheaf.Paper.PbcUniformCompleteTriangulated
import Sheaf.Paper.PreservationConstructible
import Sheaf.Paper.SbcCompletedOperations
import Sheaf.SecSmoothPurity.LocalizedExtensionZeroLinearDerived

/-!
# Integral compact support preserves the compatible uniform constructible category

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-cbc/thm-cbc-finite-extension,
proof, sole paragraph; Stacks Tags 0GL0 and 095U; Bhatt--Scholze, Lemmas 6.7.2 and 6.7.7
(blueprint: lem-cbc-integral-compact-support-uniform-restriction).

The three functor properties below are tested on the full compatible uniform subcategory.
Fullness gives the restricted functor, and its triangles and shifts are inherited.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme

/-- Canonical completed-coefficient inverse image, reusing the published finite-quotient
comparison and the constant-section-normalized presentation of the completed ring.
Source: blueprint finite-extension compact-support base change; Stacks 098T
(blueprint: lem-cbc-integral-compact-support-uniform-restriction). -/
noncomputable def cbcCompletedCoefficientIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (pbcAdicCompletion Y d) ≅
      pbcAdicCompletion X d :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso
      (pbcCompletedComparison Y d).symm ≪≫
    fourCornerCoefficientIso f
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite } ≪≫
    pbcCompletedComparison X d


/-- The chosen-compactification candidate with its actual completed coefficient maps.
Source: blueprint finite-extension compact-support base change, integral functors
(blueprint: lem-cbc-integral-compact-support-uniform-restriction). -/
def cbcIntegralCompactSupport (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (cp : Compactification f) :=
  letI : QuasiCompact cp.i := cp.quasiCompact_openImmersion inferInstance
  proEtaleRingCompactSupportImage cp
    (pbcAdicCompletion Y (pbcPadicCoefficientDatum l E))
    (pbcAdicCompletion cp.Z (pbcPadicCoefficientDatum l E))
    (pbcAdicCompletion X (pbcPadicCoefficientDatum l E))
    (cbcCompletedCoefficientIso cp.g (pbcPadicCoefficientDatum l E))
    (cbcCompletedCoefficientIso cp.i (pbcPadicCoefficientDatum l E))

/-- The shift comparison is the composite of degreewise extension by zero and the
K-injective direct-image shift comparison. It induces the comparison on the restriction.
Source: blueprint finite-extension compact-support base change, integral functors
(blueprint: lem-cbc-integral-compact-support-uniform-restriction). -/
instance cbcIntegralCompactSupport_commShift (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (cp : Compactification f) :
    (cbcIntegralCompactSupport l E cp).CommShift ℤ := by
  unfold cbcIntegralCompactSupport proEtaleRingCompactSupportImage
  infer_instance

/-- The chosen Rp_* j_! restricts to an exact A-linear functor between the precise
compatible uniform categories. Fullness makes object preservation sufficient to restrict
all maps; addition and scalar multiplication below concern exactly those maps. The last
clause is exactness for the inherited ambient triangles and the specified shift comparison.
Source: blueprint thm-cbc-finite-extension, proof, sole paragraph; Stacks Tags 0GL0 and
095U; Bhatt--Scholze Lemmas 6.7.2 and 6.7.7
(blueprint: lem-cbc-integral-compact-support-uniform-restriction).

Proof:
1. Properness makes cp.Z finite type over Y, hence Noetherian. Finite affine covers and
finite generating sets bound its dimension and all geometric fibre dimensions uniformly;
quotient prime chains and the polynomial dimension formula give the bounds. Empty schemes
and fibres cause no exception. The inverse of l on Y pulls back to cp.Z.
2. The coefficient valuation ring is a DVR with finite residue field, and its positive
quotients are finite. By integral-stratified-perfect-characterization, extend the input's
finite strata and perfect local models through the open immersion, adding the closed
complement with zero model. Exact ringed open-closed identities identify these restrictions.
The characterization gives membership of j_! K in the full compatible uniform category,
including its etale origins, not merely levelwise constructibility.
3. Boundedness of j_! K and the length-one free resolution of A/(varpi^n) give a single
cohomological interval [a-1,b] for all its canonical reductions, by the cone sequence.
4. Apply preservation-constructible to the identity base-change square for cp.g, with
N=l and the uniform geometric-fibre bound. This gives precisely compatible uniform
membership of Rp_* j_! K, including its retained compatible etale-origin witnesses.
5. Exact extension by zero descends degreewise; K-injective module direct image is
triangulated. Both operations respect scalar multiplication on representatives: extension
by zero does so on every direct-sum section and hence after sheafification, and direct image
does so sectionwise. These equations descend through localization. Thus their composite
preserves addition, scalar multiplication, and distinguished triangles. Restrict these
properties through the full inclusions and the inherited triangulations. -/
theorem cbcIntegralCompactSupport_uniformRestriction (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (_hXdim : ∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (_hYdim : ∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))
    (_hXl : IsUnit (l : Γ(X, ⊤))) (_hYl : IsUnit (l : Γ(Y, ⊤)))
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (cp : Compactification f) :
    (∀ K, IsPbcBoundedConstructibleComplete X l E K →
      IsPbcBoundedConstructibleComplete Y l E ((cbcIntegralCompactSupport l E cp).obj K)) ∧
    (∀ K L, IsPbcBoundedConstructibleComplete X l E K →
      IsPbcBoundedConstructibleComplete X l E L → ∀ a b : K ⟶ L,
        (cbcIntegralCompactSupport l E cp).map (a + b) =
          (cbcIntegralCompactSupport l E cp).map a + (cbcIntegralCompactSupport l E cp).map b) ∧
    (∀ K L, IsPbcBoundedConstructibleComplete X l E K →
      IsPbcBoundedConstructibleComplete X l E L →
      ∀ (a : Padic.coefficientExtensionIntegers l E) (b : K ⟶ L),
        (cbcIntegralCompactSupport l E cp).map (a • b) =
          a • (cbcIntegralCompactSupport l E cp).map b) ∧
    (∀ T : Triangle (DerivedCategory (pbcModules X
        (pbcAdicCompletion X (pbcPadicCoefficientDatum l E)))),
      T ∈ distTriang _ → IsPbcBoundedConstructibleComplete X l E T.obj₁ →
      IsPbcBoundedConstructibleComplete X l E T.obj₂ →
      IsPbcBoundedConstructibleComplete X l E T.obj₃ →
      (cbcIntegralCompactSupport l E cp).mapTriangle.obj T ∈ distTriang _) := by
  sorry

end AlgebraicGeometry.Scheme
