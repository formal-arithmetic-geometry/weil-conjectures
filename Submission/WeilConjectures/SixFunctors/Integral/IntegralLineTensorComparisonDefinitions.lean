/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Submission.WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import Submission.WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.BifunctorShift
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
/-!
# Ordinary and completed tensor with an integral coefficient line

Source: Bhatt--Scholze, Definition 3.4.10, Lemma 3.4.12(4), Proposition 3.5.1 and
Definition 3.5.2 (blueprint: def-sf-integral-line-tensor-comparison-constructors).
The comparison is the recorded completion unit, whose representative is the map
(c,0) into Cone(1-s)[-1]. Finite comparisons are normalized on sheafified pure
tensors; the projection equation uses the actual cone projections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace WeilConjectures
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t})

/-- The line is placed in degree zero, using the existing single-complex functor.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: def-sf-integral-line-tensor-comparison-constructors). -/
def integralLineSingle : Mod l E X none ⥤ Cx l E X none :=
  HomologicalComplex.single _ (ComplexShape.up ℤ) 0

/-- The ordinary total complex P tensor T[0], with the signed direct-sum differential.
Source: Stacks 06YN (blueprint: def-sf-integral-line-tensor-comparison-constructors). -/
def integralLineComplex (P : Cx l E X none) (T : Mod l E X none) : Cx l E X none :=
  (coefficientTotalTensor.{u, t + 1, t} (topology X none) (ring l E X none)).obj
    (P, (integralLineSingle l E X).obj T)

/-- The finite scalar-extension complex, before restoring the completed-ring action.
Source: Stacks 06YY (blueprint: def-sf-integral-line-tensor-comparison-constructors). -/
def integralLineFiniteComplex (n : ℕ) :=
  (reduction l E X none n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Total tensor of the two ordinary finite reductions, over the finite ring.
Source: Stacks 06YY (blueprint: def-sf-integral-line-tensor-comparison-constructors). -/
def integralLineFiniteTensor (P : Cx l E X none) (T : Mod l E X none) (n : ℕ) :=
  (coefficientTotalTensor.{u, t + 1, t} (topology X none) (finite l E X none n)).obj
    ((integralLineFiniteComplex l E X n).obj P,
      (integralLineFiniteComplex l E X n).obj ((integralLineSingle l E X).obj T))

end WeilConjectures
