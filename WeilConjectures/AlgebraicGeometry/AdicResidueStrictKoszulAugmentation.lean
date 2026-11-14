/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueAdjointTower
import WeilConjectures.AlgebraicGeometry.AdicResidueKoszulTensorConeProZero
import WeilConjectures.AlgebraicGeometry.AdicResidueQuotientTensorModel

/-! # The strict Koszul augmentation on a coefficient slice

## References

* Stacks Project, Tags 099M and 0A0E
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

private theorem limit_map_projection {C : Type*} [Category C]
    {F G : ℕᵒᵖ ⥤ C} [HasLimit F] [HasLimit G] (c : Cone F) (α : F ⟶ G)
    (n : ℕᵒᵖ) :
    limit.lift F c ≫ limMap α ≫ limit.π G n = c.π.app n ≫ α.app n := by
  rw [limMap_π, ← Category.assoc, limit.lift_π]

private theorem tensor_augmentation_projection
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (r : ℕ)
    (b : Fin r → (((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U).obj ⋙
      CategoryTheory.forget CommRingCat).sections)
    (P : Cx ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U))
    (ε : ringedKoszulDualTower _ r b ⟶ adicResidueQuotientCoefficientTower X J U)
    (hε : ∀ n : ℕ, ringedKoszulDualUnit _ r b n ≫ ε.app (op n) =
      adicResidueQuotientCoefficientUnit X J U n) (n : ℕ) :
    ringedKoszulLimitUnit _ r b P ≫
        (ordinaryLimit _).map (adicResidueKoszulTensorAugmentation X J U r b P ε) ≫
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
          (adicResidueQuotientTensorComplex X J U P) =
      adicResidueQuotientTensorUnit X J U P n := by
  have hu : ringedKoszulTensorUnitComponent _ r b P (op n) ≫
      ((ringedKoszulTensor _).obj P).map (ε.app (op n)) =
        adicResidueQuotientTensorUnit X J U P n := by
    dsimp only [ringedKoszulTensorUnitComponent, adicResidueQuotientTensorUnit]
    rw [Category.assoc, ← Functor.map_comp, hε n]
  apply HomologicalComplex.hom_ext
  intro q
  change limit.lift _ (ringedKoszulTensorUnitCone _ r b P q) ≫
      limMap ((adicResidueKoszulTensorAugmentation X J U r b P ε).f q) ≫
        limit.π _ (op n) = _
  refine (limit_map_projection (ringedKoszulTensorUnitCone _ r b P q)
    ((adicResidueKoszulTensorAugmentation X J U r b P ε).f q) (op n)).trans ?_
  simpa only [id, ringedKoszulTensorUnitCone, adicResidueKoszulTensorAugmentation,
    adicResidueKoszulTensorTranspose,
    HomologicalComplex.comp_f, NatTrans.comp_app,
    HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, HomologicalComplex.functorEquivalence,
    HomologicalComplex.functorEquivalence.inverse, Functor.whiskerRight_app,
    HomologicalComplex.eval_map] using congrArg (fun f ↦ f.f q) hu

/-- The Koszul augmentation has a strict quotient target, a pro-zero cone, and the
specified finite scalar units. This is a calculation of complexes and transitions;
there is no total derived inverse limit or residue-projection assertion in its conclusion
(Stacks, Tags 099M and 0A0E). -/
theorem adicResidue_strict_koszul_augmentation
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = J)
    (M : AdicResidueLocalDerived.{u, v} X J U)
    (P : Cx ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U))
    (hP : P.IsKFlatTensor) (hflat : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q))
    (eP : (Q _).obj P ≅ M) :
    let R := (completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U
    let b := fun i ↦ ringedKoszulSliceSection
      (completed (coefficientProEtaleModelTopology.{u, v} X) A J)
      (algebraSection (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J)
        (a i)) U
    ∃ (T : CochainComplex (ℕᵒᵖ ⥤ Mod R) ℤ)
      (α : ringedKoszulTensorTowerComplex R r b P ⟶ T)
      (e : T.asFunctor ⋙ Q R ≅ adicResidueAdjointTower.{u, v} X J U M),
      (∀ n : ℕ,
        (Q R).map (ringedKoszulLimitUnit R r b P ≫ (ordinaryLimit R).map α ≫
          (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app T) ≫
          e.hom.app (op n) = eP.hom ≫
            (adicResidueScalarAdjunction.{u, v} X J U n).unit.app M) ∧
      (∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
        (Q R).map ((CochainComplex.mappingCone α).asFunctor.map (homOfLE h).op) = 0) := by
  let R := (completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U
  let b := fun i ↦ ringedKoszulSliceSection
    (completed (coefficientProEtaleModelTopology.{u, v} X) A J)
    (algebraSection (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J)
      (a i)) U
  obtain ⟨ε, hε⟩ := adicResidue_koszul_coefficient_augmentation X J U r a ha.le
  obtain ⟨e, he⟩ := adicResidue_quotient_tensor_model X J U M P hP eP
  refine ⟨adicResidueQuotientTensorComplex X J U P,
    adicResidueKoszulTensorAugmentation X J U r b P ε, e, ?_,
    adicResidue_koszul_tensor_cone_proZero X J U r a ha P hP hflat ε hε⟩
  intro n
  rw [tensor_augmentation_projection X J U r b P ε hε n]
  exact he n

end AlgebraicGeometry.Scheme
