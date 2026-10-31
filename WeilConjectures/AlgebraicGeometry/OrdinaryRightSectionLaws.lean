/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSystemImageData
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.OrdinaryRightSectionZeroAdd
import WeilConjectures.AlgebraicGeometry.OrdinaryRightSectionScalarTransition
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch

/-!
# Operations and transitions of the normalized ordinary right image

Source: Zheng, Construction 4.1 and the paragraph preceding Lemma 4.10, printed pp. 21--23;
Stacks Project, Tags 00YV and 03D3
(blueprint: lem-pur-ordinary-right-section-laws).

The comparison below is the prescribed composite, natural in the strict system.
Scalar restriction is represented by `coefficientRestrictionUnderlying`, whose section
functions are identities. No transition of the system is required to be invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace SheafOfModules

/-- The specified underlying comparison, as a natural isomorphism in the strict system.
Its component is exactly the composite of `rightEvaluation` and `rightUnderlying`.
Source: Zheng, Construction 4.1 and the paragraph preceding Lemma 4.10, printed pp. 21--23
(blueprint: lem-pur-ordinary-right-section-laws). -/
def ordinaryRightSectionComparison
    {T U : Scheme.{u}} (g : T ⟶ U) (O : Type (u + 1)) [CommRing O] (t : O)
    (B : CoefficientSystemOrdinaryImage.{u + 1, u, u + 1, u, u + 1}
      (J := Scheme.ProEt.topology U) (K := Scheme.ProEt.topology T) O t
      (Scheme.proEtaleSheafInverseImage g (Type (u + 1)))
      (Scheme.proEtaleSheafDirectImage g (Type (u + 1)))
      (Scheme.proEtaleSheafAdjunction g (Type (u + 1)))) (n : ℕ) :
    B.rightSystem ⋙ coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology U) (O := O) (ell := t) n ⋙
        coefficientUnderlying (J := Scheme.ProEt.topology U) O t n ≅
      coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology T) (O := O) (ell := t) n ⋙
        coefficientUnderlying (J := Scheme.ProEt.topology T) O t n ⋙
          Scheme.proEtaleSheafDirectImage g (Type (u + 1)) :=
  Functor.isoWhiskerRight (B.rightEvaluation n)
      (coefficientUnderlying (J := Scheme.ProEt.topology U) O t n) ≪≫
    Functor.isoWhiskerLeft (coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology T) (O := O) (ell := t) n)
      (B.rightUnderlying n)

/-- Zero, addition, the canonical coefficient action, and adjacent transitions are preserved
by the prescribed ordinary right-image comparison, naturally in the strict system.
Source: Zheng, Construction 4.1 and the paragraph preceding Lemma 4.10, printed pp. 21--23;
Stacks Tags 00YV and 03D3 (blueprint: lem-pur-ordinary-right-section-laws).

Proof plan:
1. Put H = B.rightSystem(M) and take the system counit epsilon. At level n compose its
component with the inverse inverse-evaluation isomorphism to obtain a linear map h_n.
The systemTranspose equation at epsilon and the triangle identity identify rightEvaluation
with its level adjunct; levelTranspose identifies the displayed comparison with the
geometric transpose of f_n = |h_n| composed with moduleUnderlying inverse.
2. Transpose ringUnderlying. The constants equation fixes its composite with each constant
coefficient generator. Naturality of the geometric unit and terminality identify these
with the canonical direct-image constant sections. The sheafification universal property,
including preservation of sheafification by forgetting to sets, identifies this transpose
with proEtaleConstantDirectImageMap on arbitrary local coefficient sections.
3. Apply moduleZero and moduleAdd to the terminal test sheaf and to the universal pair on
the product. Linearity of h_n and the group-object adjunction lemma (00YV) show that f_n,
and hence its geometric adjunct, preserve zero and addition.
4. Apply moduleSMul to the universal scalar/module pair. Naturality of the geometric unit
on both product projections converts its transported action equation to the action equation
for the adjunct. Step 2 identifies the coefficient factor with the specified structural map.
5. The system-morphism square for epsilon, together with inverseTransition, gives
v_n h_(n+1) = Res(h_n) r_n I_(n+1)(u_n), where u and v are the two system transitions
and r_n is restrictInverse. Restriction of scalars retains the underlying section functions.
6. Substitute restrictInverseUnderlying and naturality of moduleUnderlying to obtain
v_n f_(n+1) = f_n L(u_n). Transpose with the geometric adjunction. This gives exactly the
last equality below, with the identity underlying scalar-restriction comparisons explicit.
7. Both factors defining ordinaryRightSectionComparison are natural isomorphisms in M.
Thus the formulas are natural in M; the section identities for every object are equalities
of sheaf maps and commute with restrictions. The argument uses no extra property of O, t,
the schemes, or the transitions.
-/
theorem ordinaryRightSectionLaws
    {T U : Scheme.{u}} (g : T ⟶ U) (O : Type (u + 1)) [CommRing O] (t : O)
    (B : CoefficientSystemOrdinaryImage.{u + 1, u, u + 1, u, u + 1}
      (J := Scheme.ProEt.topology U) (K := Scheme.ProEt.topology T) O t
      (Scheme.proEtaleSheafInverseImage g (Type (u + 1)))
      (Scheme.proEtaleSheafDirectImage g (Type (u + 1)))
      (Scheme.proEtaleSheafAdjunction g (Type (u + 1))))
    (M : CoefficientSystem (J := Scheme.ProEt.topology T) O t) (n : ℕ) :
    (∀ V : U.ProEtᵒᵖ,
      ((ordinaryRightSectionComparison g O t B n).hom.app M).hom.app V
          (0 : ((B.rightSystem.obj M).level n).val.obj V) =
        (0 : (M.level n).val.obj ((Scheme.proEtaleBaseChange g).op.obj V))) ∧
    (∀ (V : U.ProEtᵒᵖ) (x y : ((B.rightSystem.obj M).level n).val.obj V),
      ((ordinaryRightSectionComparison g O t B n).hom.app M).hom.app V (x + y) =
        @id ((M.level n).val.obj ((Scheme.proEtaleBaseChange g).op.obj V))
          (((ordinaryRightSectionComparison g O t B n).hom.app M).hom.app V x) +
        @id ((M.level n).val.obj ((Scheme.proEtaleBaseChange g).op.obj V))
          (((ordinaryRightSectionComparison g O t B n).hom.app M).hom.app V y)) ∧
    (∀ (V : U.ProEtᵒᵖ)
      (a : (coefficientQuotientSheaf (J := Scheme.ProEt.topology U) O t n).obj.obj V)
      (x : ((B.rightSystem.obj M).level n).val.obj V),
      ((ordinaryRightSectionComparison g O t B n).hom.app M).hom.app V (a • x) =
        (Scheme.proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
          (CommRingCat.of (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1)))).hom.app V a •
        @id ((M.level n).val.obj ((Scheme.proEtaleBaseChange g).op.obj V))
          (((ordinaryRightSectionComparison g O t B n).hom.app M).hom.app V x)) ∧
    ((coefficientUnderlying (J := Scheme.ProEt.topology U) O t (n + 1)).map
        ((B.rightSystem.obj M).transition n) ≫
      (coefficientRestrictionUnderlying (J := Scheme.ProEt.topology U)
        O t (Nat.le_succ n)).hom.app ((B.rightSystem.obj M).level n) ≫
      (ordinaryRightSectionComparison g O t B n).hom.app M =
    (ordinaryRightSectionComparison g O t B (n + 1)).hom.app M ≫
      (Scheme.proEtaleSheafDirectImage g (Type (u + 1))).map
        ((coefficientUnderlying (J := Scheme.ProEt.topology T) O t (n + 1)).map
            (M.transition n) ≫
          (coefficientRestrictionUnderlying (J := Scheme.ProEt.topology T)
            O t (Nat.le_succ n)).hom.app (M.level n))) := by
  have h₀ := ordinaryRightSectionZeroAdd g O t B M n
  have h₁ := ordinaryRightSectionScalarTransition g O t B M n
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [ordinaryRightSectionComparison, ordinaryRightSectionZeroAddComparison] using h₀.1
  · simpa [ordinaryRightSectionComparison, ordinaryRightSectionZeroAddComparison] using h₀.2
  · simpa [ordinaryRightSectionComparison,
      ordinaryRightSectionScalarTransitionComparison] using h₁.1
  · simpa [ordinaryRightSectionComparison,
      ordinaryRightSectionScalarTransitionComparison] using h₁.2

end SheafOfModules
