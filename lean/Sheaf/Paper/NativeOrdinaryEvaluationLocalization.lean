/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module

public import Sheaf.Paper.FiniteFreeDualChainModels
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom

/-! # Localization of a specified ordinary perfect evaluation

Source: Stacks Project, Tags 08JH and 08JJ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
namespace AlgebraicGeometry.ProEtale.FiniteFreeDualComparison
variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

/-- Localization of a natural ordinary evaluation isomorphism for arbitrary complexes.
Source: Stacks 08JH and 08JJ
(blueprint: lem-sfb-native-ordinary-evaluation-localization).

Proof: the Hom invariance hypothesis identifies ordinary Hom with K-injective
Hom for every target, including the coefficient unit. Localize kappa and use
the unit comparison to identify D with the derived dual of T on the section
side. For a flat-term K-flat target resolution, ringedOrdinaryEvaluation_localization
identifies the specified ordinary map with the derived evaluation transpose:
its uniqueness clause applies to hevaluation. For an arbitrary target, use
hnatural and Hom invariance on its resolution; two-out-of-three makes the
corresponding tensor map a quasi-isomorphism. K-flatness of D and tensor descent
then identify the original localization tensor comparison as an isomorphism.
The supplied evaluation-normalized module-object/ringed-site derived comparison transports
the dual identification and the equality of transposes to the actual native
adjunction. The localized ordinary isomorphism and the two comparison maps give the stated
equality. This result involves no scalar model, basis, or boundedness assumption; those belong
to the ordinary calculation. -/
theorem nativeOrdinaryEvaluationLocalization
    (T D : CochainComplex (Internal Λ X) ℤ)
    (κ : (complexForward Λ X).obj D ≅
        homComplex.{u + 1, u, u + 1, u + 1} (R := ring Λ X) ((complexForward Λ X).obj T)
          (ringedTensorUnitComplex.{u + 1, u, u} (Scheme.ProEt.topology X) (ring Λ X)))
    (ε : ∀ F : CochainComplex (Internal Λ X) ℤ,
        (complexForward Λ X).obj
            (internalTotalTensor Λ X F D) ≅
          homComplex.{u + 1, u, u + 1, u + 1} (R := ring Λ X) ((complexForward Λ X).obj T)
            ((complexForward Λ X).obj F))
    (hevaluation : ∀ F : CochainComplex (Internal Λ X) ℤ,
      ∃ aEF : (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X) (ring Λ X)).obj
          ((complexForward Λ X).obj F,
            homComplex.{u + 1, u, u + 1, u + 1} (R := ring Λ X) ((complexForward Λ X).obj T)
              (ringedTensorUnitComplex.{u + 1, u, u} (Scheme.ProEt.topology X) (ring Λ X))) ⟶
            homComplex.{u + 1, u, u + 1, u + 1} (R := ring Λ X) ((complexForward Λ X).obj T)
              ((complexForward Λ X).obj F),
        RingedOrdinaryEvaluationFormula.{u + 1, u, u} (Scheme.ProEt.topology X) (ring Λ X)
          ((complexForward Λ X).obj T) ((complexForward Λ X).obj F) aEF ∧
        (ε F).hom = (totalComparison Λ X F D).hom ≫
          (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X) (ring Λ X)).map
            (𝟙 ((complexForward Λ X).obj F), κ.hom) ≫ aEF)
    (hnatural : ∀ {F G : CochainComplex (Internal Λ X) ℤ} (f : F ⟶ G),
      (complexForward Λ X).map ((@tensorRight _ _ (internalComplexMonoidal Λ X) D).map f) ≫
        (ε G).hom =
        (ε F).hom ≫ ((homComplexFunctor.{u + 1, u, u + 1, u + 1} (R := ring Λ X)).obj
          (op ((complexForward Λ X).obj T))).map
            ((complexForward Λ X).map f))
    (hkflat : ∀ Z : CochainComplex (Internal Λ X) ℤ, Z.Acyclic →
      (internalTotalTensor Λ X Z D).Acyclic)
    (hhom : ∀ (F G : CochainComplex (Modules Λ X) ℤ) (f : F ⟶ G),
      QuasiIso f → QuasiIso (((homComplexFunctor (R := ring Λ X)).obj
        (op ((complexForward Λ X).obj T))).map f))
    (S : CoefficientClosedStructure (hom Λ X))
      (M : CoefficientTensorModels.{u, u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) S)
      (t : TensorComparison Λ X S M)
      (θ : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙ forward Λ X ≅
        ((forward Λ X).op.prod (forward Λ X)) ⋙ hom Λ X)
    (hcounit : ∀ K N : DerivedCategory.{u + 1} (Internal Λ X),
        (forward Λ X).map
          ((@BraidedCategory.braiding _ _ _ (internalBraiding Λ X)
              (((CondensedRing.derivedHom Λ X).obj (op K)).obj N) K).hom ≫
            (CondensedRing.derivedTensorHomAdjunction Λ K).counit.app N) =
          (t.iso.hom.app (((CondensedRing.derivedHom Λ X).obj (op K)).obj N, K)) ≫
            S.tensor.map
              (X := ((forward Λ X).obj (((CondensedRing.derivedHom Λ X).obj (op K)).obj N),
                (forward Λ X).obj K))
              (Y := ((hom Λ X).obj (op ((forward Λ X).obj K), (forward Λ X).obj N),
                (forward Λ X).obj K))
              (θ.hom.app (op K, N), 𝟙 ((forward Λ X).obj K)) ≫
            S.evaluation ((forward Λ X).obj K) ((forward Λ X).obj N)) :
    ∃ δ : DerivedCategory.Q.{u + 1}.obj D ≅
        ((CondensedRing.derivedHom Λ X).obj
          (op (DerivedCategory.Q.{u + 1}.obj T))).obj
            (nativeUnit Λ X),
    ∀ F : CochainComplex (Internal Λ X) ℤ,
      IsIso (localizationTensorMap Λ X F D) ∧
      (forward Λ X).map
          ((((CondensedRing.derivedTensor Λ X).obj (DerivedCategory.Q.{u + 1}.obj F)).map
            δ.hom) ≫
            evaluationTranspose Λ X (DerivedCategory.Q.{u + 1}.obj T)
              (DerivedCategory.Q.{u + 1}.obj F)) ≫
          sectionDerivedHomMap Λ X θ T F =
        (forward Λ X).map
            (localizationTensorMap Λ X F D) ≫
          (localizationIso Λ X).hom.app
            (internalTotalTensor Λ X F D) ≫
          DerivedCategory.Q.{u + 1}.map (ε F).hom ≫
          ringedOrdinaryHomComparison.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X) (ring Λ X)
            ((complexForward Λ X).obj T) ((complexForward Λ X).obj F) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteFreeDualComparison
