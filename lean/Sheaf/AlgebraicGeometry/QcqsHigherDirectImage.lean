/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.AlgebraicGeometry.DerivedCategories
import Sheaf.AlgebraicGeometry.KInjectiveResolutions
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Higher direct images for quasi-compact quasi-separated morphisms

Source: blueprint `sec-proper-base-change/sk-thm-iff`,
(blueprint: lem-weil-pbc-qcqs-higher-direct-image); Stacks Project, Tags 03Q8, 08BJ and 00WJ.

The cohomology of a complex of presheaves is sectionwise. Thus the presheaf in the second
clause below evaluates at `W` to `H^q(I(W ×_V U))`, with the induced restriction maps.
For a K-injective representative `I` of `K`, this is `H^q(W ×_V U, K|)`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Higher direct images of abelian sheaves are sheafified cohomology presheaves, and the
same description computes every degree of derived direct image using any K-injective
representative. The first presheaf is the cohomology presheaf of the landed
`AlgebraicGeometry.higherDirectImageSheafifiedPresheaf` (right derived evaluation with its
derived restriction maps), precomposed with étale base change: its value at `W` is
`H^q(W ×_V U, F|)`.
The second is the sectionwise cohomology of a K-injective representative, precomposed
with the same base-change functor. No termwise injectivity or strict boundedness of this
representative is required.

Source: blueprint `sec-proper-base-change/sk-thm-iff`,
(blueprint: lem-weil-pbc-qcqs-higher-direct-image); Stacks Project, Lemma 59.51.6 (03Q8).

Proof:
1. Choose a K-injective resolution of `F[0]` or of `K`
   (prop-weil-pbc-kinjective-resolutions-exist). Derived direct image is represented by
   its direct image, independently of the resolution (def-weil-pbc-direct-image,
   def-weil-pbc-derived-categories, def-weil-pbc-kinjective-resolutions).
2. For `W` étale over `V`, the projection `W ×_V U → U` is étale
   (lem-weil-pbc-etale-base-change-finite-limits). Restriction is exact
   (lem-weil-pbc-etale-inverse-image-restriction, lem-weil-pbc-sheafification-exact).
   Its exact left adjoint is extension by zero (def-weil-pbc-etale-sum-extension,
   lem-weil-pbc-etale-restriction-injectives), so restriction preserves K-injectives
   (lem-weil-pbc-right-adjoint-preserves-kinjective; Stacks 08BJ).
3. Therefore the section complex on `W ×_V U` computes its cohomology with the restricted
   coefficients (def-weil-pbc-etale-cohomology,
   prop-weil-pbc-cohomology-resolution-independent). The direct-image formula identifies
   these sections and restriction maps with those of the direct-image complex.
4. Exact sheafification commutes with cohomology
   (lem-weil-pbc-sheafification-exact, lem-weil-pbc-exact-functor-complex-cohomology,
   def-weil-pbc-sheafification; Stacks 00WJ). Hence its sectionwise cohomology presheaf
   sheafifies to the cohomology sheaf of the direct-image complex.
5. Combine the resolution formula and this sheafification comparison, first for `F[0]`
   in nonnegative degrees, then for `K` in every integer degree. -/
theorem qcqs_higherDirectImage {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f] :
    (∀ (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ),
      Nonempty
        ((presheafToSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            ((MorphismProperty.Over.pullback @Etale ⊤ f).op ⋙
              { obj := fun Z ↦
                  ((sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
                    (evaluation U.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj Z).rightDerived q).obj F
                map := fun g ↦
                  (NatTrans.rightDerived
                    (Functor.whiskerLeft
                      (sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
                      ((evaluation U.Etaleᵒᵖ AddCommGrpCat.{u + 1}).map g)) q).app F
                map_id := fun Z ↦ by
                  simp only [CategoryTheory.Functor.map_id, Functor.whiskerLeft_id',
                    NatTrans.rightDerived_id, NatTrans.id_app]
                map_comp := fun g h ↦ by
                  simp only [CategoryTheory.Functor.map_comp, Functor.whiskerLeft_comp,
                    NatTrans.rightDerived_comp, NatTrans.comp_app] }) ≅
          (DerivedCategory.Plus.homologyFunctor
            (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
              ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
                ((DerivedCategory.Plus.singleFunctor
                  (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)))) ∧
    ∀ (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (I : CochainComplex (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      I.IsKInjective → Nonempty (DerivedCategory.Q.obj I ≅ K.obj) →
      ∀ q : ℤ, Nonempty
        ((presheafToSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            ((MorphismProperty.Over.pullback @Etale ⊤ f).op ⋙
              (((sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I).homology q) ≅
          (DerivedCategory.Plus.homologyFunctor
            (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
              ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj K)) := by
  sorry

end AlgebraicGeometry.Etale
