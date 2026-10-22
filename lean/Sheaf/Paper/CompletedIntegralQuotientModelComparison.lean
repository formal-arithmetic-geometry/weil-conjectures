/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.PrincipalKoszulStrictReplacement
public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

/-! # Balanced realization of the principal quotient completion model

Source: Stacks Project, Tags 093M, 03EK, 06YT and 08TC;
Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1.
(blueprint: lem-weil-completed-integral-quotient-model-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace WeilConjectures

/-- Completing ordinary extension is the actual coefficient-reduction Roos functor,
with the specified scalar augmentation, on every input.

Source: Stacks Project, Tags 093M, 03EK, 06YT and 08TC;
Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1.
(blueprint: lem-weil-completed-integral-quotient-model-comparison).

Proof: on a flat K-flat representative P, ordinary scalar extension is again flat
and K-flat. The normalized completed quotient presentation identifies the target
principal cokernel with its actual constant residue module. Tensor associativity
then identifies (P tensor S) tensor B_n with P tensor B_n: on local pure tensors it
sends (s tensor x) tensor z to residue(s) z tensor x. The inverse sends z tensor x
to (1 tensor x) tensor z. Balancing makes these maps inverse; equality on presheaf
tensors followed by sheafification proves the identities for arbitrary sheaf sections.
The same formulas commute with the quotient transitions and the chain differentials,
so they give an isomorphism of strict towers. Apply the termwise products and the
signed mapping cocone. Both cone blocks use that same tower isomorphism; the quotient
augmentation maps to the displayed scalar augmentation, with zero shifted component.
The counit of C computes on the extended K-flat complex. Its universal property and
that of the ordinary change-of-rings model descend this comparison. On the resolving
subcategory the other side is exactly integralScalarOnGood; its normalized localization
comparison therefore supplies the displayed natural isomorphism on the full derived
category. The two-coordinate uniqueness of the strict cone lift identifies its unit
with any beta satisfying the stated equations. This proof uses no completeness of P,
no finite basis and no boundedness. It also covers the identity inclusion, P=0 and
the empty site. -/
theorem completedIntegralQuotientModelComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})
    (φ : completedIntegralCommRingSheafUnrestricted l E Y ⟶
      completedIntegralCommRingSheafUnrestricted l L Y)
    (hφ : ∀ n : ℕ, φ ≫ completedIntegralCommRingProjectionUnrestricted l L Y n =
      completedIntegralCommRingProjectionUnrestricted l E Y n ≫
        integralScalarQuotientSheafMap l E L ι Y n)
    (F : @SheafOfModules.DerivedChangeOfRingsCochainModel.{t + 1, t, max u (t + 1),
      max u (t + 1) + 1, max u (t + 1) + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{u} _)
      (AlgebraicGeometry.Scheme.ProEt.topology Y) inferInstance
      (integralCoefficientAbLocallyBijective.{t, u} Y)
      (integralCoefficientAbSheafify.{t, u} Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (completedIntegralCommRingSheafUnrestricted l L Y) φ
      (integralTowerHasDerivedCategory l E Y) (integralTowerHasDerivedCategory l L Y))
    (C : @PrincipalQuotientCompletion.Model.{t + 1, t, max u (t + 1), max u (t + 1) + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{u} _)
      (AlgebraicGeometry.Scheme.ProEt.topology Y) inferInstance
      (integralCoefficientAbSheafify.{t, u} Y)
      (integralCoefficientAbLocallyBijective.{t, u} Y)
      (completedIntegralCommRingSheafUnrestricted l L Y)
      (integralTowerHasDerivedCategory l L Y)
      (PrincipalKoszulStrictReplacement.uniformizer l L Y))
    (β : F.E.mapHomologicalComplex (.up ℤ) ⟶ integralScalarComplexFunctor l E L ι Y)
    (hβ :
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (n : ℕ)
        (U : Y.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
        (x : (P.X i).val.obj U),
        (((β.app P).f i ≫
          (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism
              (K := fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))
              (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι Y).obj P)))).f i ≫
          (Pi.π
            (fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n)) n).f i).val.app U)
          ((eqToHom (F.obj_eq (P.X i)).symm).val.app U
            ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
              (SheafOfModules.changeOfRingsPresheaf φ (P.X i)).presheaf).app U
                (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
                  (φ.hom.app U).hom] x))) =
            integralScalarTensorSection l E L ι Y n (P.X i) U
              ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U s) x) ∧
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ),
        (β.app P).f i ≫
          (CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism
              (K := fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))
              (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι Y).obj P)))).v
                i (i - 1) (by omega) = 0)) :
    ∃ c : F.T ⋙ C.completion ≅ integralScalarExtensionOfUniverses l E L ι Y,
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        C.unit.app (F.T.obj (DerivedCategory.Q.obj P.obj)) ≫
            c.hom.app (DerivedCategory.Q.obj P.obj) ≫
            (integralScalarExtensionComparisonOfUniverses l E L ι Y).hom.app P =
          F.ε.app P.obj ≫ DerivedCategory.Q.map (β.app P.obj) := by
  sorry

end WeilConjectures
