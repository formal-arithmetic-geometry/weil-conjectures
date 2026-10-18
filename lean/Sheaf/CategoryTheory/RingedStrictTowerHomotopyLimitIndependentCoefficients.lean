/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF maintenance NZ
-/
module

public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-!
# Total derived inverse limits with independent site and coefficient universes

Source: Stacks Project, Cohomology on Sites, Tags 0940 and 0941; More on Algebra,
Tag 0H9L (blueprint: lem-weil-pbc-ringed-strict-tower-homotopy-limit).

This companion retains the original interface through its public import. Its generalized
statement applies to the small pro-etale site and the actual completed coefficient sheaf.
-/

@[expose] public section

set_option autoImplicit false

universe w uC vC r

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace CategoryTheory

/-- Total derived inverse limit with independent site object, site morphism and
coefficient universes, computed on K-injective towers with the natural Roos triangle.

The site is essentially small in the coefficient universe `r`. The sheafification
and locally bijective instances provide Mathlib's abelian structure; they are canonical
on such a small site. In particular, for a pro-etale site use `uC = t + 1`, `vC = t`
and `r = max u (t + 1)` for coefficient-field universe `u`. These sizes stay independent.
This is the same statement as `ringedStrictTowerHomotopyLimit`, with all its conclusions.

Source: Stacks Project, Cohomology on Sites, Tags 0940 and 0941; More on Algebra,
Tag 0H9L (blueprint: lem-weil-pbc-ringed-strict-tower-homotopy-limit).

The coefficient sheaf is represented in `RingCat` with sectionwise commutativity `_hcomm`,
which is precisely a sheaf of commutative rings after forgetting to rings.
The index `n : ℕ` corresponds to the paper's positive index `n + 1`. The auxiliary
functor `E` evaluates a derived strict tower, with `ε` identifying its restriction to
complexes with termwise evaluation followed by localization. Thus it preserves all the
transition maps, not just the objects. The maps `p` and `δ` give Roos triangles natural
on the derived tower category. No exactness of countable products is a hypothesis.

Proof plan:
1. Replace C by its small model in `r`, using the
   equivalence of sites and module sheaves. This preserves strict towers, limits,
   quasi-isomorphisms and the derived localization. Identify strict module towers
   with modules over the constant ring sheaf on the small tower site C × ℕ. Apply
   prop-pur-kinjective-resolutions-exist to resolve every tower complex. By
   lem-weil-tower-category-levelwise-abelian, evaluation and exactness are
   levelwise. Inverse limit is right adjoint to the exact constant tower functor; it is
   additive, preserves homotopies, shifts and cones. Apply
   lem-weil-pbc-kinjective-total-derived and lem-pc-right-derived-functor-triangulated.
   The unit η is invertible on every K-injective representative by
   lem-weil-pbc-kinjective-hom-derived, giving the asserted computation.
2. Evaluation preserves K-injectives by lem-weil-tower-evaluation-kinjective. Products of
   these representatives represent derived products by lem-pc-ringed-space-product-kinjective.
   Every transition of an injective tower splits: extend the map from the finite prefix
   tower T_n(J_n) to J across its monic inclusion in T_(n+1)(J_n), using
   def-sp-injective-resolutions. With sections σ_n, solve y_n - q_n y_(n+1) = x_n by
   y_0 = 0 and y_(n+1) = σ_n(y_n - x_n). Its kernel is the inverse limit, giving the
   short exact sequence 0 → lim I → product I → product I → 0.
   Apply lem-weil-pbc-complex-ses-triangle to obtain the Roos triangle.
3. Functorial tower resolutions give commuting maps between these short exact sequences.
   Their triangles are natural, including the connecting morphism. Homotopy invariance
   and lem-weil-pbc-kinjective-hom-derived extend naturality to the derived category.
4. For a pro-zero evaluated tower and its shift s, choose r_n with pr_n s^r_n = 0.
   The finite coordinate sums pr_n t = sum_(k < r_n) pr_n s^k define a two-sided inverse
   to 1-s, by telescoping. An identity transition can be zero only at a zero object,
   when r_n = 1 suffices. The Roos triangle, its backward rotation and
   lem-weil-pbc-hom-into-triangle-exact imply id_(Rlim X) = 0, hence Rlim X is zero.
5. A strict chain map has its mapping cone in the tower category, with cones evaluated
   levelwise. Exactness sends its cone triangle to a distinguished triangle. A pro-zero
   cone tower has zero derived limit by step 4, so its first arrow is invertible by
   lem-weil-pbc-hom-into-triangle-exact and rotation (def-weil-triangulated-category). -/
theorem ringedStrictTowerHomotopyLimitIndependentCoefficients
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (R : Sheaf J RingCat.{r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{r, r, vC, uC} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R)] :
    ∃ (RF : DerivedCategory.{w}
        (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) ⥤
      DerivedCategory.{w} (ringedSiteModules.{r, r, vC, uC} R))
      (η : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) ⥤
        ringedSiteModules.{r, r, vC, uC} R).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF),
      RF.IsRightDerivedFunctor η
        (HomologicalComplex.quasiIso
          (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) (ComplexShape.up ℤ)) ∧
      (∀ I, CochainComplex.IsKInjective I → IsIso (η.app I)) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) ℤ),
        ∃ (I : CochainComplex
          (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) ℤ) (j : X ⟶ I),
          I.IsKInjective ∧ QuasiIso j) ∧
      ∃ (_hshift : RF.CommShift ℤ)
        (_hproducts : HasCountableProducts
          (DerivedCategory.{w} (ringedSiteModules.{r, r, vC, uC} R)))
        (E : DerivedCategory.{w}
          (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) ⥤
            (ℕᵒᵖ ⥤ DerivedCategory.{w}
              (ringedSiteModules.{r, r, vC, uC} R)))
        (_ε : DerivedCategory.Q.{w} ⋙ E ≅
          HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
            (Functor.whiskeringRight ℕᵒᵖ
              (CochainComplex (ringedSiteModules.{r, r, vC, uC} R) ℤ)
              (DerivedCategory.{w}
                (ringedSiteModules.{r, r, vC, uC} R))).obj
                  DerivedCategory.Q.{w})
        (p : ∀ Z,
          RF.obj Z ⟶ ∏ᶜ (fun n : ℕ ↦ (E.obj Z).obj (op n)))
        (δ : ∀ Z,
          (∏ᶜ (fun n : ℕ ↦ (E.obj Z).obj (op n))) ⟶ (RF.obj Z)⟦(1 : ℤ)⟧),
        RF.IsTriangulated ∧
        (∀ Z,
          IsDerivedLimitTriangle
            (fun n : ℕ ↦ (E.obj Z).map (homOfLE (Nat.le_succ n)).op)
            (RF.obj Z) (p Z) (δ Z)) ∧
        (∀ {Z W} (v : Z ⟶ W),
          RF.map v ≫ p W = p Z ≫ Limits.Pi.map (fun n : ℕ ↦ (E.map v).app (op n))) ∧
        (∀ {Z W} (v : Z ⟶ W),
          Limits.Pi.map (fun n : ℕ ↦ (E.map v).app (op n)) ≫ δ W =
            δ Z ≫ (RF.map v)⟦(1 : ℤ)⟧') ∧
        (∀ Z,
          (∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), (E.obj Z).map (homOfLE h).op = 0) →
            IsZero (RF.obj Z)) ∧
        (∀ (X Y : CochainComplex
          (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) ℤ) (v : X ⟶ Y),
          (∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
            (E.obj (DerivedCategory.Q.{w}.obj (CochainComplex.mappingCone v))).map
              (homOfLE h).op = 0) → IsIso (RF.map (DerivedCategory.Q.{w}.map v))) := by
  sorry


end CategoryTheory
