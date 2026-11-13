/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulCoefficientConeRealization
import WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorConeComparisonAux
public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorAugmentationComponent

/-! # Tensor comparison for normalized completed Koszul augmentation cones

Source: Stacks Project, Tags 099M and 06YP.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] completedKoszulCochainMonoidal
  completedKoszulCochainMonoidalStruct
attribute [local instance] Functor.preservesZeroMorphisms_of_additive

attribute [local instance] augmentationComponentPreadditive

attribute [local irreducible] completedAdicRing

/-- The actual cone tower at P is tensor of its coefficient cone tower. This is
an isomorphism of strict towers of complexes, before any localization. It imposes
no K-flatness and asserts neither eventual vanishing nor a derived-limit result. -/
theorem completedKoszulTensorConeComparison
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A)
    (β : completedKoszulTensorTower T d r a ⟶
      (completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ))
    (hu : ∀ (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ),
      completedAdicKoszulTensorUnit T d r a P n ≫
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (β.app P)).app (op n) =
          completedQuotientTensorUnit T d P n)
    (hz : ∀ (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ) (p q : ℤ) (_hq : q ≠ 0),
      completedKoszulTensorSummand T d r a P n p q ≫
          ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            (β.app P)).app (op n)).f (p + q) = 0)
    (P : CochainComplex (CompletedAdicModules T d) ℤ) :
    Nonempty
      ((CochainComplex.mappingCone
        (β.app (𝟙_ (CochainComplex (CompletedAdicModules T d) ℤ)))).asFunctor ⋙
          tensorLeft P ≅ (CochainComplex.mappingCone (β.app P)).asFunctor) := by
  let U := 𝟙_ (CochainComplex (CompletedAdicModules T d) ℤ)
  let f := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (β.app U)
  let g := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (β.app P)
  let s := koszulTensorTowerUnitor T d (completedAdicKoszul T d r a)
    (completedAdicKoszulStep T d r a) P
  let q := quotientTensorTowerIso T d (completedAdicFiniteModule T d)
    (completedAdicFiniteModuleStep T d) P
  have h : Functor.whiskerRight f (tensorLeft P) ≫ q.hom = s.hom ≫ g := by
    apply NatTrans.ext
    funext n
    change P ◁ f.app n ≫ (quotientTensorIso T d
        (completedAdicFiniteModule T d n.unop) P).hom =
      (koszulTensorUnitor T d (completedAdicKoszul T d r a n.unop) P).hom ≫ g.app n
    unfold quotientTensorIso quotientUnitIso koszulTensorUnitor
    dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    change P ◁ f.app n ≫ (tensorLeft P).map
        ((CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _)
          (completedAdicFiniteModule T d n.unop) U).inv ≫
          (λ_ ((HomologicalComplex.single _ (.up ℤ) 0).obj
            (completedAdicFiniteModule T d n.unop))).hom) ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _)
          (completedAdicFiniteModule T d n.unop) P).hom =
      P ◁ (λ_ (completedAdicKoszul T d r a n.unop)).hom ≫ g.app n
    exact completedKoszulTensorAugmentationComponent T d r a n.unop P
        (g.app n) (f.app n) (hu P n.unop) (hz P n.unop) (hu U n.unop)
  exact ⟨Functor.isoWhiskerRight (levelConeTowerIso f) (tensorLeft P) ≪≫
    levelConeTower_mapBifunctorIso (curriedTensor (CompletedAdicModules T d)) P f ≪≫
    coneTowerIso (Functor.whiskerRight f (tensorLeft P)) g s q h ≪≫
    (levelConeTowerIso g).symm⟩

end AlgebraicGeometry.Scheme
