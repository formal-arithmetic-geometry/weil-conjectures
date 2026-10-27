/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q101
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence
public import Sheaf.Paper.EtaleSumTensorTotalization
public import Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat
public import Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafProjectionMap
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.Paper.PullbackTensorCanonicalShiftUnit
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.RingedTensorComplexConstraints
import Sheaf.CategoryTheory.ExactDerivedAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # Evaluation of the etale sum projection at the coefficient unit

Source: Stacks Project, Tag 0GKF, and blueprint latest,
sec-six-functors-basics/sk-prop-cohsm/lem-pur-co-smooth-etale-locality.proof.md,
Step 1 (blueprint: lem-pur-etale-sum-unit-evaluation).

The projection is characterized by its square with the published total-tensor
comparison and the localization tensor maps. The counit is the actual termwise
sum/restriction counit. All derived categories are ordinary and unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A]
variable {U X : Scheme.{u}} (e : U ⟶ X) [Etale e]

/-- Source bifunctor `(M,K) ↦ SM tensor K` for the canonical sum projection.
Source: Stacks Tag 0GKF (blueprint: lem-pur-etale-sum-unit-evaluation). -/
def sumUnitProjectionSource :
    DerivedCategoryModule A U × DerivedCategoryModule A X ⥤ DerivedCategoryModule A X :=
  Functor.prod (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory
    (𝟭 _) ⋙ Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) X)

/-- Target bifunctor `(M,K) ↦ S(M tensor TK)` for the canonical sum projection.
Source: Stacks Tag 0GKF (blueprint: lem-pur-etale-sum-unit-evaluation). -/
def sumUnitProjectionTarget :
    DerivedCategoryModule A U × DerivedCategoryModule A X ⥤ DerivedCategoryModule A X :=
  Functor.prod (𝟭 _) (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory ⋙
    Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) U) ⋙
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory

/-- The action `a_K`: tensor the specified coefficient comparison with the identity,
then apply the derived left unitor.
Source: blueprint Step 1 (blueprint: lem-pur-etale-sum-unit-evaluation). -/
def sumUnitDerivedAction (K : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat.{u + 1} A) U).obj
      ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj
        (constantComplex A X))).obj
      ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ⟶
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K :=
  ((derivedTensor (ModuleCat.{u + 1} A) U).map (etaleSumPullbackUnitIso A e).hom).app _ ≫
    (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) U _).hom

/-- The same coefficient action before deriving: pullback of the tensor unit is
identified with the tensor unit by the inverse of its monoidal unit comparison.
Source: Stacks Tag 0GKF (blueprint: lem-pur-etale-sum-unit-evaluation). -/
def sumUnitSheafAction (H : EtaleModuleSheaf X A) :
    (upperStar (ModuleCat.{u + 1} A) e).obj (𝟙_ (EtaleModuleSheaf X A)) ⊗
      (upperStar (ModuleCat.{u + 1} A) e).obj H ⟶
        (upperStar (ModuleCat.{u + 1} A) e).obj H :=
  (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} A) e)).inv ▷ _ ≫ (λ_ _).hom

/-- The derived evaluation composite, as a component in K.
Source: blueprint Step 1 (blueprint: lem-pur-etale-sum-unit-evaluation). -/
def sumUnitDerivedEvaluation
    (p : sumUnitProjectionSource A e ≅ sumUnitProjectionTarget A e)
    (K : DerivedCategoryModule A X) :=
  p.hom.app ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj
      (constantComplex A X), K) ≫
    (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
      (sumUnitDerivedAction A e K) ≫
    (derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).counit.app K

/-- The coefficient evaluation followed by the derived action unitor.
Source: blueprint Step 1 (blueprint: lem-pur-etale-sum-unit-evaluation). -/
def sumUnitDerivedScalarEvaluation (K : DerivedCategoryModule A X) :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).map
      ((derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) e inferInstance).counit.app (constantComplex A X))).app K ≫
    (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X K).hom

/-- The localization square specifying the derived sum projection on total tensors.
It uses the actual localization tensorator, the exact-functor factor isomorphisms,
and the published total comparison; no representative map is freely chosen.
Source: Stacks Tag 0GKF, unbounded descent in blueprint Step 1
(blueprint: lem-pur-etale-sum-unit-evaluation). -/
def SumUnitProjectionModel [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (Ψ : EtaleSumTensorComparison A e inferInstance)
    (p : sumUnitProjectionSource A e ≅ sumUnitProjectionTarget A e) : Prop :=
  ∀ (P : EtaleModuleComplex U A) (H : EtaleModuleComplex X A),
    p.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj H) ≫
        (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
          (((derivedTensor (ModuleCat.{u + 1} A) U).obj (DerivedCategory.Q.obj P)).map
              ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategoryFactors.hom.app H) ≫
            Functor.LaxMonoidal.μ DerivedCategory.Q P
              (((upperStar (ModuleCat.{u + 1} A) e).mapHomologicalComplex (.up ℤ)).obj H)) =
      ((derivedTensor (ModuleCat.{u + 1} A) X).map
          ((etaleLowerShriek (ModuleCat.{u + 1} A) e
            inferInstance).mapDerivedCategoryFactors.hom.app P)).app
          (DerivedCategory.Q.obj H) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          (((etaleLowerShriek (ModuleCat.{u + 1} A) e
            inferInstance).mapHomologicalComplex (.up ℤ)).obj P) H ≫
        DerivedCategory.Q.map (Ψ P H).hom ≫
        (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryFactors.inv.app
          (P ⊗ ((upperStar (ModuleCat.{u + 1} A) e).mapHomologicalComplex (.up ℤ)).obj H)

/-- Evaluation at the coefficient unit for the canonical sheafified sum projection,
and its specified unbounded derived projection. Source: Stacks Tag 0GKF and blueprint
latest, lem-pur-co-smooth-etale-locality.proof.md, Step 1
(blueprint: lem-pur-etale-sum-unit-evaluation).

Proof:
1. Identify inverse image with restriction by
lem-weil-pbc-etale-inverse-image-restriction. The constant coefficient comparison
sends a to a (prop-weil-pbc-inverse-image-modules-exact). Its localization equals the
specified u by def-pur-etale-exact-pullback-unit-composition-comparisons and
lem-weil-pbc-pullback-tensor-canonical-shift-unit.
2. The sum/restriction counit folds the lift summands. On a local generator
(s,a) tensor h the projection, action and evaluation give ah. Evaluating first
and then applying the action unitor also gives ah. Linearity and the uniqueness
of module sheafification give the sheaf equality, natural in H. This uses
lem-pur-etale-sheaf-projection-map and lem-sf-ringed-tensor-complex-constraints.
3. The coefficient complex is flat and K-flat since tensoring with it is the
identity. Sum extension preserves these properties by lem-pur-etale-sum-flat-kflat.
Use lem-pc-kflat-resolution to represent arbitrary K by a flat-term K-flat complex.
4. Apply step 2 in every degree. The total comparison of
lem-pur-etale-sum-tensor-totalization preserves each summand, and the coefficient
factor is in degree zero, so no sign is introduced. The action unitors localize
to the derived unitors (lem-sf-ringed-derived-closed-symmetric-monoidal).
The exact-derived adjunction localizes the termwise counit, giving the counit
square below, rather than a fresh choice of evaluation. Localize the chain equality.
5. Naturality transports the result from the K-flat representative to every K.
The model square is the canonical descent of the generator-normalized total
comparison; uniqueness follows from flat K-flat models and
lem-weil-pbc-site-derived-tensor-descent. It gives agreement with the sheaf
calculation on flat-term K-flat complexes. All constructions are unbounded;
no finiteness, constructibility or Noetherian assumption is used. -/
theorem etale_sum_unit_evaluation [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] :
    ∃ (Ψ : EtaleSumTensorComparison A e inferInstance)
      (p : sumUnitProjectionSource A e ≅ sumUnitProjectionTarget A e),
      EtaleSumTensorClauses A e inferInstance Ψ ∧ SumUnitProjectionModel A e Ψ p ∧
      (∀ K : DerivedCategoryModule A X,
        sumUnitDerivedEvaluation A e p K = sumUnitDerivedScalarEvaluation A e K) ∧
      (∀ H : EtaleModuleSheaf X A,
        (etaleLowerShriekTensorIso (ModuleCat.{u + 1} A) (inferInstance : Etale e)
            ((upperStar (ModuleCat.{u + 1} A) e).obj (𝟙_ (EtaleModuleSheaf X A))) H).inv ≫
          (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).map
            (sumUnitSheafAction A e H) ≫
          (etaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).counit.app H =
        ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
          inferInstance).counit.app (𝟙_ (EtaleModuleSheaf X A))) ▷ H ≫ (λ_ H).hom) ∧
      (∀ H : EtaleModuleComplex X A,
        (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
            ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategoryFactors.hom.app H) ≫
          (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryFactors.hom.app
            (((upperStar (ModuleCat.{u + 1} A) e).mapHomologicalComplex (.up ℤ)).obj H) ≫
          DerivedCategory.Q.map (((etaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).mapHomologicalComplex (.up ℤ)).counit.app H) =
        (derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e inferInstance).counit.app (DerivedCategory.Q.obj H)) := by
  sorry

end AlgebraicGeometry.Etale
