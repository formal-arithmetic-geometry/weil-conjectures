/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence

/-! # Finite germ comparisons assembled into the strict quotient tower

Source: Stacks Project, Tags 0993 and 05V1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Point sections and geometric stalks agree on the entire quotient tower,
with the finite comparison fixed on pullback-unit generators.
Source: Stacks Project, Tags 0993 and 05V1
(blueprint: lem-trf-quotient-germ-tower).

Proof: the identity pointed neighbourhood of the algebraically closed point is
initial. Its germ map from sections is inverse to the map [U,u,x] ↦ u*x; the
colimit relations prove the two inverse equations and naturality. Combine this
with the normalized finite pullback-stalk comparison degree by degree. Its germ
rule is the second displayed equation. Naturality with respect to differentials
makes these maps chain isomorphisms without any bound on complex terms. A quotient
transition changes x to its reduced section, leaving its pointed neighbourhood
and lift fixed. Applying comparison before or after reduction consequently gives
the same germ, including n=0. The maps thus assemble into a strict tower
isomorphism natural in P. Constant scalar actions commute with these maps because
both are induced by the same coefficient constants. This gives the last equation
in the integral scalar restriction as well as the first two finite germ equations. -/
theorem quotientGermTower (D : FiniteFieldDatum.{u}) {T : Scheme.{u}}
    (v : Spec (.of D.k) ⟶ T) :
  ∃ (γ : ∀ n : ℕ, pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ≅
      finiteCoefficientModuleStalkFunctor (𝟙 (Spec (.of D.k)))
        (Padic.coefficientExtensionRing l E (n + 1)))
    (δ : ∀ n : ℕ, integralOperationsLevelPullback l E v n ⋙
      pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ≅
        finiteCoefficientModuleStalkFunctor v (Padic.coefficientExtensionRing l E (n + 1)))
    (e : (integralOperationsPullbackTowerFunctor l E v ⋙
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj
        ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ))) ≅ ((Functor.ofOpSequence
      (X := fun n ↦ unrestrictedIntegralComplexFunctor l E T n)
      (unrestrictedIntegralTransition l E T)).flip ⋙
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj
        ((integralCoefficientModuleStalkFunctor l E v).mapHomologicalComplex (.up ℤ)))),
(∀ (n : ℕ) (F : integralOperationsFiniteModules l E (Spec (.of D.k)) n)
      (x : F.val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
    (γ n).hom.app F x =
      proEtaleCoefficientModuleGerm (𝟙 (Spec (.of D.k)))
        (Padic.coefficientExtensionRing l E (n + 1)) F
          (proEtaleConstantGermNeighbourhood (𝟙 (Spec (.of D.k)))) x) ∧
  (∀ (n : ℕ) (F : integralOperationsFiniteModules l E T n)
      (N : ProEtaleGeometricNeighbourhood v)
      (θ : ProEt.mk (𝟙 (Spec (.of D.k))) ⟶ (proEtaleBaseChange v).obj N.right)
      (x : F.val.obj (op N.right)),
    θ.left ≫ pullback.fst N.right.hom v = N.hom.left →
      (δ n).hom.app F
        (((integralOperationsLevelPullback l E v n).obj F).val.map θ.op
          (integralOperationsPullbackGenerator l E v n F N.right x)) =
        proEtaleCoefficientModuleGerm v (Padic.coefficientExtensionRing l E (n + 1)) F N x) ∧
  (∀ (P : CochainComplex (integralTowerModules l E T) ℤ) (n : ℕ) (i : ℤ)
      (x : ((((integralOperationsPullbackTowerFunctor l E v ⋙
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj
        ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)))).obj P).obj (op n)).X i),
    (((e.hom.app P).app (op n)).f i) x =
      (δ n).hom.app (((unrestrictedIntegralFiniteComplex l E T n).obj P).X i) x) := by sorry

end WeilConjectures
