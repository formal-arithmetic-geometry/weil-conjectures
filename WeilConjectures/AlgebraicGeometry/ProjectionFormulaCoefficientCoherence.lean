/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.FinitePullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import all WeilConjectures.AlgebraicGeometry.FiniteProjectionActionLaws
import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidalUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Braided
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Reduction
import WeilConjectures.AlgebraicGeometry.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor
import all WeilConjectures.AlgebraicGeometry.FiniteCompactSupportConstructibility
/-!
# Unit and coefficient associativity for a fixed compactification
Source: Stacks Project, sites-cohomology.tex, Tags 0B56 and 0GL1;
current blueprint sk-prop-cohsm, equation (G13)
(blueprint: lem-pur-projection-formula-coefficient-coherence).
The fixed-ring coordinates below use the canonical intrinsic realization solely to
express the recorded constructibility predicates. All arrows are the ordinary
constant-coefficient derived arrows at the specified compactification.

## Main definitions

* `inverseCompactificationProjection`: the symmetry-conjugate canonical inverse.
* `CompactificationProjectionUnit`, `CompactificationProjectionAssoc`: the two equations.
* `CompactificationProjectionDomains`: all their constructible tensor inputs.

## Main statements

* `compactificationProjection_coefficient_coherence`: both laws and their domains.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w v₁ w₁
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
-- Use the canonical sheaf braiding also in the derived comparison proofs.
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
section ActionUnit
variable {C D : Type*} [Category C] [Category D]
  [MonoidalCategory C] [MonoidalCategory D]
  (P : C ⥤ D) (S : D ⥤ C) [S.OplaxMonoidal]
  (p : ∀ (M : C) (B : D), P.obj M ⊗ B ⟶ P.obj (M ⊗ S.obj B))

private theorem coherenceAction_unit
    (hn : ∀ {M M' : C} (g : M ⟶ M') (B : D),
      P.map g ▷ B ≫ p M' B = p M B ≫ P.map (g ▷ S.obj B))
    (hb : ∀ (M : C) {B B' : D} (g : B ⟶ B'),
      P.obj M ◁ g ≫ p M B' = p M B ≫ P.map (M ◁ S.map g))
    (ha : ∀ M B B',
      (α_ (P.obj M) B B').hom ≫ p M (B ⊗ B') ≫
        P.map (M ◁ Functor.OplaxMonoidal.δ S B B' ≫
          (α_ M (S.obj B) (S.obj B')).inv) =
      p M B ▷ B' ≫ p (M ⊗ S.obj B) B')
    (M : C) [IsIso (p M (𝟙_ D))] :
    p M (𝟙_ D) ≫ P.map (M ◁ Functor.OplaxMonoidal.η S ≫ (ρ_ M).hom) =
      (ρ_ (P.obj M)).hom := by
  let u (K : C) := K ◁ Functor.OplaxMonoidal.η S ≫ (ρ_ K).hom
  have hu (K : C) :
      K ◁ Functor.OplaxMonoidal.δ S (𝟙_ D) (𝟙_ D) ≫
        (α_ K (S.obj (𝟙_ D)) (S.obj (𝟙_ D))).inv ≫ u K ▷ S.obj (𝟙_ D) =
      K ◁ S.map (λ_ (𝟙_ D)).hom := by
    dsimp [u]
    have triangle' : (α_ K (𝟙_ C) (S.obj (𝟙_ D))).inv ≫
        (ρ_ K).hom ▷ S.obj (𝟙_ D) = K ◁ (λ_ (S.obj (𝟙_ D))).hom := by
      monoidal
    rw [comp_whiskerRight, ← associator_inv_naturality_middle_assoc, triangle',
      ← whiskerLeft_comp_assoc, ← whiskerLeft_comp, Category.assoc,
      Functor.OplaxMonoidal.left_unitality_hom]
  have h := congrArg (fun k ↦ k ≫ P.map (u M ▷ S.obj (𝟙_ D)))
    (ha M (𝟙_ D) (𝟙_ D))
  simp only [Category.assoc, ← P.map_comp, hu] at h
  rw [← hb M (λ_ (𝟙_ D)).hom, ← hn] at h
  have ht : (α_ (P.obj M) (𝟙_ D) (𝟙_ D)).hom ≫
      P.obj M ◁ (λ_ (𝟙_ D)).hom = (ρ_ (P.obj M)).hom ▷ (𝟙_ D) := by
    monoidal
  rw [← Category.assoc, ht, ← comp_whiskerRight_assoc] at h
  have h' := (cancel_mono (p M (𝟙_ D))).1 h
  exact ((whiskerRight_iff _ _).1 h').symm
end ActionUnit

section FunctorUnit
variable {C D : Type*} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
  [Limits.PreservesFiniteColimits F] [F.Monoidal]
open _root_.DerivedCategory

@[irreducible] private def coherenceFunctorUnitIso : F.leftDerivedFunctor.obj (𝟙_ _) ≅ 𝟙_ _ :=
  F.leftDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
    F.mapDerivedCategoryFactors.app _ ≪≫
    Q.mapIso (((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app _) ≪≫
      (HomologicalComplex.single _ (.up ℤ) 0).mapIso (Functor.Monoidal.εIso F).symm)

omit [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D]
  [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D] in
private lemma coherenceQhMap {K L : CochainComplex D ℤ} (g : K ⟶ L) :
    Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map g) = Q.map g := by
  have h := quotientCompQhIso_hom_naturality g
  have hi : ∀ K, (quotientCompQhIso D).hom.app K = 𝟙 _ := fun _ ↦ rfl
  rw [hi, hi] at h
  exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))

omit [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
  [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D]
  [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D] [F.Monoidal] in
private lemma coherenceFactors (K : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [F.mapDerivedCategoryFactorsh_hom_app]
  have h₁ : ∀ K, (quotientCompQhIso C).hom.app K = 𝟙 _ := fun _ ↦ rfl
  have h₂ : ∀ K, (quotientCompQhIso D).inv.app K = 𝟙 _ := fun _ ↦ rfl
  have h₃ : ∀ K, (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := fun _ ↦ rfl
  erw [h₁, h₂, h₃, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.id_comp, Category.comp_id]

private lemma coherenceFunctor_oplax_tensor [F.PreservesFlat] [F.IsLeftAdjoint]
    (B B' : DerivedCategory C) :
    let := CategoryTheory.Functor.generic_oplax F
    Functor.OplaxMonoidal.δ F.leftDerivedFunctor B B' =
      (F.leftDerivedTensorComparison.app B).app B' := by
  rfl

omit [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F] in
private lemma coherenceHomotopyEta [F.IsLeftAdjoint] :
    Functor.OplaxMonoidal.η (F.mapHomotopyCategory (.up ℤ)) =
      Functor.OplaxMonoidal.mapHomotopyCategoryη (.up ℤ) F := by
  rfl

private lemma coherenceFunctor_oplax_unit [F.PreservesFlat] [F.IsLeftAdjoint] :
    let := CategoryTheory.Functor.generic_oplax F
    Functor.OplaxMonoidal.η F.leftDerivedFunctor = (coherenceFunctorUnitIso F).hom := by
  let := CategoryTheory.Functor.generic_oplax F
  have h₁ : Functor.LaxMonoidal.ε (Qh (C := D)) = 𝟙 _ := rfl
  have h₂ : Functor.LaxMonoidal.ε (Qh (C := C)) = 𝟙 _ := rfl
  change _ ≫ _ ≫ _ ≫ inv (Functor.LaxMonoidal.ε (Qh (C := D))) = _
  have hη := coherenceHomotopyEta F
  rw [hη]
  have hi : inv (Functor.LaxMonoidal.ε (Qh (C := D))) = 𝟙 _ := by
    apply (cancel_epi (Functor.LaxMonoidal.ε (Qh (C := D)))).1
    rw [IsIso.hom_inv_id, Category.comp_id]
    exact h₁.symm
  rw [hi, h₂, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  symm
  rw [← F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  unfold coherenceFunctorUnitIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.whiskerLeft_app, NatTrans.comp_app]
  erw [coherenceFactors F]
  simp only [Functor.OplaxMonoidal.mapHomotopyCategoryη,
    Functor.OplaxMonoidal.mapHomologicalComplexη, Functor.Monoidal.εIso_inv,
    Category.assoc]
  rw [coherenceQhMap]
  rfl

end FunctorUnit

section Conjugate
variable {C : Type v} [Category.{w} C] [MonoidalCategory C] [SymmetricCategory C]
  {T : Type v₁} [Category.{w₁} T] [MonoidalCategory T] [SymmetricCategory T]
  (P : C ⥤ T) (S : T ⥤ C)
  (p : ∀ (M : C) (B : T), P.obj M ⊗ B ⟶ P.obj (M ⊗ S.obj B))

private theorem conjugate_unit (e : S.obj (𝟙_ T) ⟶ 𝟙_ C) (M : C)
    [IsIso (p M (𝟙_ T))]
    (hu : p M (𝟙_ T) ≫ P.map (M ◁ e ≫ (ρ_ M).hom) = (ρ_ (P.obj M)).hom) :
    P.map (β_ (S.obj (𝟙_ T)) M).hom ≫ inv (p M (𝟙_ T)) ≫
        (β_ (P.obj M) (𝟙_ T)).hom ≫ (λ_ (P.obj M)).hom =
      P.map (e ▷ M ≫ (λ_ M).hom) := by
  rw [braiding_leftUnitor]
  rw [← hu, IsIso.inv_hom_id_assoc, ← P.map_comp]
  congr 1
  rw [← BraidedCategory.braiding_naturality_left_assoc, braiding_rightUnitor]

private theorem conjugate_assoc
    (δ : ∀ B B' : T, S.obj (B ⊗ B') ⟶ S.obj B ⊗ S.obj B')
    (hn : ∀ {M M' : C} (g : M ⟶ M') (B : T),
      P.map g ▷ B ≫ p M' B = p M B ≫ P.map (g ▷ S.obj B))
    (hb : ∀ (M : C) {B B' : T} (g : B ⟶ B'),
      P.obj M ◁ g ≫ p M B' = p M B ≫ P.map (M ◁ S.map g))
    (ha : ∀ M B B',
      (α_ (P.obj M) B B').hom ≫ p M (B ⊗ B') ≫
        P.map (M ◁ δ B B' ≫ (α_ M (S.obj B) (S.obj B')).inv) =
      p M B ▷ B' ≫ p (M ⊗ S.obj B) B')
    (hd : ∀ B B', S.map (β_ B B').hom ≫ δ B' B =
      δ B B' ≫ (β_ (S.obj B) (S.obj B')).hom)
    (M : C) (B B' : T) :
    ((β_ (B ⊗ B') (P.obj M)).hom ≫ p M (B ⊗ B') ≫
      P.map (β_ M (S.obj (B ⊗ B'))).hom) ≫
      P.map (δ B B' ▷ M ≫ (α_ (S.obj B) (S.obj B') M).hom) =
    (α_ B B' (P.obj M)).hom ≫
      B ◁ ((β_ B' (P.obj M)).hom ≫ p M B' ≫ P.map (β_ M (S.obj B')).hom) ≫
      ((β_ B (P.obj (S.obj B' ⊗ M))).hom ≫ p (S.obj B' ⊗ M) B ≫
        P.map (β_ (S.obj B' ⊗ M) (S.obj B)).hom) := by
  have perm (X Y Z : C) :
      X ◁ (β_ Y Z).hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫
          (β_ (Z ⊗ X) Y).hom =
        (β_ X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom := by
    rw [BraidedCategory.braiding_naturality_left,
      BraidedCategory.braiding_tensor_left_hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← whiskerLeft_comp_assoc, SymmetricCategory.symmetry,
      whiskerLeft_id, Category.id_comp, BraidedCategory.braiding_tensor_right_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  symm
  simp only [whiskerLeft_comp, Category.assoc]
  rw [BraidedCategory.braiding_naturality_right_assoc,
    reassoc_of% hn]
  simp only [CategoryTheory.Functor.map_comp]
  rw [BraidedCategory.braiding_naturality_right_assoc]
  rw [BraidedCategory.braiding_tensor_right_hom B (P.obj M) B']
  simp only [Category.assoc]
  rw [← BraidedCategory.braiding_tensor_left_hom_assoc]
  rw [← reassoc_of% ha]
  simp only [Iso.inv_hom_id_assoc]
  rw [reassoc_of% hb]
  simp only [← P.map_comp]
  congr 2
  apply congrArg P.map
  simp only [Category.assoc]
  rw [← whiskerLeft_comp_assoc, hd, whiskerLeft_comp, Category.assoc, perm]
  rw [BraidedCategory.braiding_naturality_right_assoc]

private theorem conjugate_inverse_hom_id (M : C) (B : T) [IsIso (p M B)] :
    ((β_ B (P.obj M)).hom ≫ p M B ≫ P.map (β_ M (S.obj B)).hom) ≫
      (P.map (β_ (S.obj B) M).hom ≫ inv (p M B) ≫ (β_ (P.obj M) B).hom) = 𝟙 _ := by
  simp only [Category.assoc]
  rw [← P.map_comp_assoc, SymmetricCategory.symmetry, P.map_id, Category.id_comp,
    IsIso.hom_inv_id_assoc, SymmetricCategory.symmetry]

private theorem conjugate_isIso (M : C) (B : T) [IsIso (p M B)] :
    IsIso ((β_ B (P.obj M)).hom ≫ p M B ≫ P.map (β_ M (S.obj B)).hom) := by
  infer_instance

omit [SymmetricCategory C] [SymmetricCategory T] in
private theorem inverse_left_action
    (B B' : T) (M : C) (a : S.obj (B ⊗ B') ⊗ M ⟶ S.obj B ⊗ (S.obj B' ⊗ M))
    (q₀ : (B ⊗ B') ⊗ P.obj M ⟶ P.obj (S.obj (B ⊗ B') ⊗ M))
    (q₁ : B ⊗ P.obj (S.obj B' ⊗ M) ⟶ P.obj (S.obj B ⊗ (S.obj B' ⊗ M)))
    (q₂ : B' ⊗ P.obj M ⟶ P.obj (S.obj B' ⊗ M))
    (r₀ : P.obj (S.obj (B ⊗ B') ⊗ M) ⟶ (B ⊗ B') ⊗ P.obj M)
    (r₁ : P.obj (S.obj B ⊗ (S.obj B' ⊗ M)) ⟶ B ⊗ P.obj (S.obj B' ⊗ M))
    (r₂ : P.obj (S.obj B' ⊗ M) ⟶ B' ⊗ P.obj M)
    [IsIso q₀] (h₀ : q₀ ≫ r₀ = 𝟙 _)
    (h₁ : q₁ ≫ r₁ = 𝟙 _) (h₂ : q₂ ≫ r₂ = 𝟙 _)
    (ha : q₀ ≫ P.map a = (α_ B B' (P.obj M)).hom ≫ B ◁ q₂ ≫ q₁) :
    r₀ ≫ (α_ B B' (P.obj M)).hom = P.map a ≫ r₁ ≫ B ◁ r₂ := by
  apply (cancel_epi q₀).1
  rw [← Category.assoc, h₀, Category.id_comp, ← Category.assoc q₀,
    ha]
  simp only [Category.assoc]
  rw [reassoc_of% h₁,
    ← whiskerLeft_comp, h₂, whiskerLeft_id, Category.comp_id]

private theorem conjugate_inverse_assoc
    (δ : ∀ B B' : T, S.obj (B ⊗ B') ⟶ S.obj B ⊗ S.obj B')
    (M : C) (B B' : T) [IsIso (p M (B ⊗ B'))]
    [IsIso (p (S.obj B' ⊗ M) B)] [IsIso (p M B')]
    (ha : ((β_ (B ⊗ B') (P.obj M)).hom ≫ p M (B ⊗ B') ≫
        P.map (β_ M (S.obj (B ⊗ B'))).hom) ≫
        P.map (δ B B' ▷ M ≫ (α_ (S.obj B) (S.obj B') M).hom) =
      (α_ B B' (P.obj M)).hom ≫
        B ◁ ((β_ B' (P.obj M)).hom ≫ p M B' ≫ P.map (β_ M (S.obj B')).hom) ≫
        ((β_ B (P.obj (S.obj B' ⊗ M))).hom ≫ p (S.obj B' ⊗ M) B ≫
          P.map (β_ (S.obj B' ⊗ M) (S.obj B)).hom)) :
    (P.map (β_ (S.obj (B ⊗ B')) M).hom ≫ inv (p M (B ⊗ B')) ≫
      (β_ (P.obj M) (B ⊗ B')).hom) ≫ (α_ B B' (P.obj M)).hom =
    P.map (δ B B' ▷ M ≫ (α_ (S.obj B) (S.obj B') M).hom) ≫
      (P.map (β_ (S.obj B) (S.obj B' ⊗ M)).hom ≫ inv (p (S.obj B' ⊗ M) B) ≫
        (β_ (P.obj (S.obj B' ⊗ M)) B).hom) ≫
      B ◁ (P.map (β_ (S.obj B') M).hom ≫ inv (p M B') ≫ (β_ (P.obj M) B').hom) := by
  have := conjugate_isIso P S p M (B ⊗ B')
  exact inverse_left_action P S B B' M
    (δ B B' ▷ M ≫ (α_ (S.obj B) (S.obj B') M).hom)
    _ _ _ _ _ _ (conjugate_inverse_hom_id P S p M (B ⊗ B'))
    (conjugate_inverse_hom_id P S p (S.obj B' ⊗ M) B)
    (conjugate_inverse_hom_id P S p M B') ha

end Conjugate

private theorem coherenceAction_congr
    {C T : Type*} [Category C] [Category T]
    [MonoidalCategory C] [MonoidalCategory T] (P : C ⥤ T) (S : T ⥤ C)
    (p p' : ∀ M B, P.obj M ⊗ B ⟶ P.obj (M ⊗ S.obj B))
    (δ δ' : ∀ B B', S.obj (B ⊗ B') ⟶ S.obj B ⊗ S.obj B')
    (hp : ∀ M B, p M B = p' M B) (hδ : ∀ B B', δ B B' = δ' B B')
    (M : C) (B B' : T)
    (h : (α_ (P.obj M) B B').hom ≫ p' M (B ⊗ B') ≫
      P.map (M ◁ δ' B B' ≫ (α_ M (S.obj B) (S.obj B')).inv) =
        p' M B ▷ B' ≫ p' (M ⊗ S.obj B) B') :
    (α_ (P.obj M) B B').hom ≫ p M (B ⊗ B') ≫
      P.map (M ◁ δ B B' ≫ (α_ M (S.obj B) (S.obj B')).inv) =
        p M B ▷ B' ≫ p (M ⊗ S.obj B) B' := by
  rw [hp, hp, hp, hδ]
  exact h

section FiniteDomains
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (T : Scheme.{u})

private theorem coherenceBC_tensor
    {K M : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T K)
    (hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) T M) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T (K ⊗ M) := by
  obtain ⟨K', hK', ⟨eK⟩⟩ := hK
  obtain ⟨⟨M', hM', ⟨eM⟩⟩, a, b, htM⟩ := hM
  let F := (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory
  have htM' : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) T a b M' :=
    (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b M').1
      ((DerivedCategory.torAmplitudeIn _ T a b).prop_of_iso eM.symm htM)
  have h := Etale.boundedConstructible_tensor Λ T hK' hM' ⟨a, b, htM'⟩
  apply (DerivedCategory.boundedConstructible _ T).prop_of_iso
    ((((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} Λ) K').app M')) ≪≫ tensorIso eK eM)
  exact DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj h

private theorem coherenceCtf_unit :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) T (𝟙_ _) :=
  (DerivedCategory.constructibleFiniteTor _ T).prop_of_iso
    (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso Λ T)
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory Λ
      (Etale.constructibleFiniteTor_tensorUnit Λ T))

private theorem coherenceCtf_tensor
    {K M : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) T K)
    (hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) T M) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) T (K ⊗ M) := by
  obtain ⟨hcK, a, b, htK⟩ := hK
  obtain ⟨hcM, c, d, htM⟩ := hM
  exact ⟨coherenceBC_tensor Λ T hcK ⟨hcM, c, d, htM⟩, a + c, b + d,
    _root_.DerivedCategory.torAmplitudeIn_tensor htK htM⟩

end FiniteDomains

/-- The canonical Koszul symmetry of the existing derived tensor, descended through
K-flat localization. No arbitrary choice of a braiding is made.
Source: Stacks 0FPT, signed total tensor symmetry
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
def projectionCoherenceSymmetry
    (C : Type v) [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (K L : DerivedCategory C) : K ⊗ L ≅ L ⊗ K :=
  DerivedMonoidal.braiding' DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) K L
private theorem coherenceSymmetry_eq
    (C : Type v) [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C] (K L : DerivedCategory C) :
    let := _root_.DerivedCategory.symmetricCategory C
    projectionCoherenceSymmetry C K L = β_ K L := by
  rfl

/-- The existing finite-ring Noetherian instance exposed at the positive quotient.
This makes the fixed-ring flat-pullback interface available without a long general search.
Source: finite coefficient convention; a finite ring is Noetherian
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
instance projectionCoherenceCoefficientNoetherian
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    IsNoetherianRing (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  isNoetherian_of_finite _ _

/-- Canonical derived realization from fixed-ring sheaves to intrinsic constant-ring
modules. The positive quotient's finiteness is supplied by its recorded theorem.
Source: Stacks 00YV, constant-coefficient realization
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
def projectionCoherenceRealization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  (Scheme.sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E n)).functor
/-- The recorded bounded constructibility predicate in canonical fixed-ring coordinates.
Source: blueprint finite-torsion convention and Stacks 00YV
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
abbrev projectionCoherenceConstructible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u})
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))))) : Prop :=
  Scheme.intrinsicFiniteTorsionConstructible l E n hn X
    ((projectionCoherenceRealization l E n hn X).obj M)
/-- The recorded finite-Tor constructibility predicate in the same coordinates.
Source: blueprint def-weil-finite-tor-amplitude and Stacks 00YV
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
abbrev projectionCoherenceFiniteTor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u})
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))))) : Prop :=
  WeilConjectures.finiteTorConstructible l E n hn X
    ((projectionCoherenceRealization l E n hn X).obj M)
/-- The unit equation, written in diagrammatic composition order. Parameters name the
specified maps, so specialization below supplies only the canonical compactification maps.
Source: blueprint def-sfb-projection-formula, unit equation; Stacks 0B56/0GL1
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
def CompactificationProjectionUnit
    {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {T : Type v₁} [Category.{w₁} T] [MonoidalCategory T]
    (P : C ⥤ T) (S : T ⥤ C) (e : S.obj (𝟙_ T) ⟶ 𝟙_ C) (M : C)
    (pi : P.obj (S.obj (𝟙_ T) ⊗ M) ⟶ (𝟙_ T) ⊗ P.obj M) : Prop :=
  pi ≫ (λ_ (P.obj M)).hom = P.map (e ▷ M ≫ (λ_ M).hom)
/-- The coefficient-associativity equation for its three specified components.
Source: blueprint def-sfb-projection-formula, associativity equation; Stacks 0B56/0GL1
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
def CompactificationProjectionAssoc
    {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {T : Type v₁} [Category.{w₁} T] [MonoidalCategory T]
    (P : C ⥤ T) (S : T ⥤ C) (B B' : T) (M : C)
    (delta : S.obj (B ⊗ B') ⟶ S.obj B ⊗ S.obj B')
    (piprod : P.obj (S.obj (B ⊗ B') ⊗ M) ⟶ (B ⊗ B') ⊗ P.obj M)
    (pileft : P.obj (S.obj B ⊗ (S.obj B' ⊗ M)) ⟶ B ⊗ P.obj (S.obj B' ⊗ M))
    (piright : P.obj (S.obj B' ⊗ M) ⟶ B' ⊗ P.obj M) : Prop :=
  piprod ≫ (α_ B B' (P.obj M)).hom =
    P.map (delta ▷ M ≫ (α_ (S.obj B) (S.obj B') M).hom) ≫ pileft ≫ B ◁ piright
private theorem coherenceCtf_iff
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))))) :
    letI := Padic.finite_coefficientExtensionRing l E n hn
    projectionCoherenceFiniteTor l E n hn T M ↔
      DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) T M := by
  let := Padic.finite_coefficientExtensionRing l E n hn
  let A := Padic.coefficientExtensionRing l E n
  constructor
  · rintro ⟨hc, a, b, ht⟩
    exact ⟨(Scheme.intrinsic_bc_realization_iff l E n hn T M).1 hc, a, b,
      (intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn A T a b ht.1 M).1 ht⟩
  · rintro ⟨hc, a, b, ht⟩
    refine ⟨(Scheme.intrinsic_bc_realization_iff l E n hn T M).2 hc,
      min a b, b, ?_⟩
    exact (intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn A T (min a b) b
      (min_le_right _ _) M).2 (ht.mono (min_le_left _ _) le_rfl)

section Arrows
variable (V : Type v) [Category.{u + 1} V] [Abelian V]
  [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalPreadditive V]
  [SymmetricCategory V] [MonoidalClosed V] [Abelian.HasFunctorialFlatResolution V]
  [UpperStarPreservesFlat V] {X Y : Scheme.{u}} {f : X ⟶ Y}
  (c : Compactification f)
/-- The symmetry-conjugate inverse of precisely the counit/open compactification map.
Only its supplied component is inverted; no isomorphism is chosen independently.
Source: Stacks 0B56/0GL1 and the displayed definition of pi in the node
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
@[irreducible] def inverseCompactificationProjection
    (B : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      V))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      V))
    (h : IsIso (((projectionMapOfCompactification
      V c).app M).app B)) :
    (rightDerivedLowerShriekOfCompactification
      V c).obj
        ((L((f)^*[V])).obj B ⊗ M) ⟶
      B ⊗ (rightDerivedLowerShriekOfCompactification
        V c).obj M :=
  letI := h
  (rightDerivedLowerShriekOfCompactification
    V c).map (projectionCoherenceSymmetry _ _ _).hom ≫
      inv (((projectionMapOfCompactification
        V c).app M).app B) ≫
        (projectionCoherenceSymmetry _ _ _).hom
section PullbackUnit
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
open _root_.DerivedCategory
variable [UpperStarPreservesFlat A]
private lemma coherenceUpperStar_oplax_unit :
    let := CategoryTheory.Functor.generic_oplax (g)^*[A]
    Functor.OplaxMonoidal.η L((g)^*[A]) = (leftDerivedUpperStarUnitIso A g).hom :=
  by
    have h := coherenceFunctor_oplax_unit (g)^*[A]
    simpa only [coherenceFunctorUnitIso, leftDerivedUpperStarUnitIso,
      leftDerivedUpperStarIsoMapDerivedCategory] using h

end PullbackUnit

section NativeAction
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A] {X Y : Scheme.{u}}
  (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

omit [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] in
private theorem coherenceNative_component
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (B : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((projectionMapOfCompactification A c).app M).app B =
      composite_projection_components
        R((c.g)_*[A]) D((c.i)_!open[A]) L((c.g)^*[A])
        (F' := L((c.i)^*[A])) (F'' := L((f)^*[A]))
        (fun K N ↦ ((rightDerivedLowerStarProjectionMap A c.g).app K).app N)
        (fun K N ↦ ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app N)
        (fun N ↦ (leftDerivedUpperStarCompactificationIso A c).hom.app N) M B := by
  rw [projectionMapOfCompactification_app_app]
  rfl

omit [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] in
private theorem coherenceNative_assoc
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (B B' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (α_ ((rightDerivedLowerShriekOfCompactification A c).obj M) B B').hom ≫
      ((projectionMapOfCompactification A c).app M).app (B ⊗ B') ≫
      (rightDerivedLowerShriekOfCompactification A c).map
        (M ◁ (leftDerivedUpperStarTensorIso A f B B').hom ≫
          (α_ M (L((f)^*[A]).obj B) (L((f)^*[A]).obj B')).inv) =
    (((projectionMapOfCompactification A c).app M).app B) ▷ B' ≫
      ((projectionMapOfCompactification A c).app (M ⊗ L((f)^*[A]).obj B)).app B' :=
  by
    have h := composite_projection_components_action
      R((c.g)_*[A]) D((c.i)_!open[A]) L((c.g)^*[A])
      (F' := L((c.i)^*[A])) (F'' := L((f)^*[A]))
      (fun K N ↦ ((rightDerivedLowerStarProjectionMap A c.g).app K).app N)
      (fun K N ↦ ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app N)
      (fun N ↦ (leftDerivedUpperStarCompactificationIso A c).hom.app N)
      (fun N N' ↦ ((leftDerivedUpperStarTensorComparison A c.g).app N).app N')
      (fun N N' ↦ ((leftDerivedUpperStarTensorComparison A c.i).app N).app N')
      (fun N N' ↦ ((leftDerivedUpperStarTensorComparison A f).app N).app N')
      (fun x N ↦ congr_app ((rightDerivedLowerStarProjectionMap A c.g).naturality x) N)
      (by
        intro K N N'
        have h :=
          (derivedUpperStarLowerStarAdjunction A c.g).rightAdjointProjectionMap_associativity
          (leftDerivedUpperStarTensorComparison A c.g) (actionTensor_assoc A c.g) K N N'
        exact action_of_assoc R((c.g)_*[A]) L((c.g)^*[A])
          (fun N N' ↦ ((leftDerivedUpperStarTensorComparison A c.g).app N).app N')
          (fun K N ↦ ((rightDerivedLowerStarProjectionMap A c.g).app K).app N)
          K N N' h)
      (fun x N ↦ congr_app
        ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.naturality x) N)
      (fun K _ _ x ↦ ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).naturality x)
      (actionTensor_open_inverse_assoc A c.i)
      (raw_comparison_tensor A c) M B B'
    exact coherenceAction_congr (rightDerivedLowerShriekOfCompactification A c)
      L((f)^*[A]) (fun K N ↦ ((projectionMapOfCompactification A c).app K).app N)
      (fun K N ↦ composite_projection_components
        R((c.g)_*[A]) D((c.i)_!open[A]) L((c.g)^*[A])
        (F' := L((c.i)^*[A])) (F'' := L((f)^*[A]))
        (fun K N ↦ ((rightDerivedLowerStarProjectionMap A c.g).app K).app N)
        (fun K N ↦ ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app N)
        (fun N ↦ (leftDerivedUpperStarCompactificationIso A c).hom.app N) K N)
      (fun N N' ↦ (leftDerivedUpperStarTensorIso A f N N').hom)
      (fun N N' ↦ ((leftDerivedUpperStarTensorComparison A f).app N).app N')
      (coherenceNative_component A f c) (by intro N N'; rfl)
      M B B' h

omit [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] in
private theorem coherenceNative_unit
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    [IsIso (((projectionMapOfCompactification A c).app M).app (𝟙_ _))] :
    ((projectionMapOfCompactification A c).app M).app (𝟙_ _) ≫
      (rightDerivedLowerShriekOfCompactification A c).map
        (M ◁ (leftDerivedUpperStarUnitIso A f).hom ≫ (ρ_ M).hom) =
      (ρ_ ((rightDerivedLowerShriekOfCompactification A c).obj M)).hom := by
  let := CategoryTheory.Functor.generic_oplax (f)^*[A]
  have h := coherenceAction_unit (rightDerivedLowerShriekOfCompactification A c)
    L((f)^*[A]) (fun M B ↦ ((projectionMapOfCompactification A c).app M).app B)
    (fun {_ _} g B ↦ congr_app ((projectionMapOfCompactification A c).naturality g) B)
    (fun M {_ _} g ↦ ((projectionMapOfCompactification A c).app M).naturality g)
    (by
      intro M B B'
      simpa only [coherenceFunctor_oplax_tensor, leftDerivedUpperStarTensorIso_hom,
        actionTensor_comparison_eq] using
        coherenceNative_assoc A f c M B B') M
  rw [coherenceUpperStar_oplax_unit] at h
  exact h

omit [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] in
private theorem coherenceNative_braiding
    (B B' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    let := _root_.DerivedCategory.symmetricCategory (Sheaf (Scheme.ProEt.topology X) A)
    let := _root_.DerivedCategory.symmetricCategory (Sheaf (Scheme.ProEt.topology Y) A)
    L((f)^*[A]).map (β_ B B').hom ≫ (leftDerivedUpperStarTensorIso A f B' B).hom =
      (leftDerivedUpperStarTensorIso A f B B').hom ≫
        (β_ (L((f)^*[A]).obj B) (L((f)^*[A]).obj B')).hom := by
  let := _root_.DerivedCategory.symmetricCategory (Sheaf (Scheme.ProEt.topology X) A)
  let := _root_.DerivedCategory.symmetricCategory (Sheaf (Scheme.ProEt.topology Y) A)
  have h := (f)^*[A].leftDerivedFunctor_map_braiding_hom_δ
    (fun K L ↦ by
      let : (f)_*[A].LaxBraided := by unfold lowerStar; infer_instance
      exact ((upperStarLowerStarAdjunction A f).leftAdjointOplaxMonoidal_δ_braiding K L).symm)
    B B'
  simp only [Functor.leftDerivedFunctorMonoidal_δ] at h
  simpa only [leftDerivedUpperStarTensorIso_hom, actionTensor_comparison_eq] using h

end NativeAction

/-- The exact list of constructible and finite-Tor tensor inputs in the two equations.
The predicates are supplied below by the recorded intrinsic predicates through the
canonical realization, so they introduce neither a replacement category nor assumptions.
Source: the node's last domain clause, blueprint (G13), Stacks 0GL0
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
def CompactificationProjectionDomains
    (cx tx : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      V)))
    (cy ty : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      V)))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      V))
    (B B' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      V)) : Prop :=
  (∀ K ∈ [𝟙_ _, B ⊗ B'], ty K) ∧
    (∀ K ∈ [(L((f)^*[V])).obj (𝟙_ _),
      (L((f)^*[V])).obj B,
      (L((f)^*[V])).obj B',
      (L((f)^*[V])).obj (B ⊗ B'),
      (L((f)^*[V])).obj B ⊗ (L((f)^*[V])).obj B'], tx K) ∧
    (∀ K ∈ [(L((f)^*[V])).obj (𝟙_ _) ⊗ M,
      (L((f)^*[V])).obj B' ⊗ M,
      (L((f)^*[V])).obj (B ⊗ B') ⊗ M,
      ((L((f)^*[V])).obj B ⊗
        (L((f)^*[V])).obj B') ⊗ M,
      (L((f)^*[V])).obj B ⊗
        ((L((f)^*[V])).obj B' ⊗ M),
      M ⊗ (L((f)^*[V])).obj (𝟙_ _),
      M ⊗ (L((f)^*[V])).obj (B ⊗ B'),
      ((L((f)^*[V])).obj B' ⊗ M) ⊗ (L((f)^*[V])).obj B,
      M ⊗ (L((f)^*[V])).obj B'], cx K) ∧
    (∀ K ∈ [(rightDerivedLowerShriekOfCompactification
      V c).obj M,
      𝟙_ _ ⊗ (rightDerivedLowerShriekOfCompactification
        V c).obj M,
      B' ⊗ (rightDerivedLowerShriekOfCompactification
        V c).obj M,
      (B ⊗ B') ⊗ (rightDerivedLowerShriekOfCompactification
        V c).obj M,
      B ⊗ (B' ⊗ (rightDerivedLowerShriekOfCompactification
        V c).obj M),
      (rightDerivedLowerShriekOfCompactification
        V c).obj
          ((L((f)^*[V])).obj (𝟙_ _) ⊗ M),
      (rightDerivedLowerShriekOfCompactification
        V c).obj
          ((L((f)^*[V])).obj B' ⊗ M),
      B ⊗ (rightDerivedLowerShriekOfCompactification
        V c).obj
          ((L((f)^*[V])).obj B' ⊗ M),
      (rightDerivedLowerShriekOfCompactification
        V c).obj
          ((L((f)^*[V])).obj (B ⊗ B') ⊗ M),
      (rightDerivedLowerShriekOfCompactification
        V c).obj
          ((L((f)^*[V])).obj B ⊗
            ((L((f)^*[V])).obj B' ⊗ M)),
      (rightDerivedLowerShriekOfCompactification V c).obj M ⊗ 𝟙_ _,
      (rightDerivedLowerShriekOfCompactification V c).obj M ⊗ (B ⊗ B'),
      (rightDerivedLowerShriekOfCompactification V c).obj
        ((L((f)^*[V])).obj B' ⊗ M) ⊗ B,
      (rightDerivedLowerShriekOfCompactification V c).obj M ⊗ B',
      (rightDerivedLowerShriekOfCompactification V c).obj
        (M ⊗ (L((f)^*[V])).obj (𝟙_ _)),
      (rightDerivedLowerShriekOfCompactification V c).obj
        (M ⊗ (L((f)^*[V])).obj (B ⊗ B')),
      (rightDerivedLowerShriekOfCompactification V c).obj
        (((L((f)^*[V])).obj B' ⊗ M) ⊗ (L((f)^*[V])).obj B),
      (rightDerivedLowerShriekOfCompactification V c).obj
        (M ⊗ (L((f)^*[V])).obj B'),
      (rightDerivedLowerShriekOfCompactification V c).obj
        (((L((f)^*[V])).obj B ⊗ (L((f)^*[V])).obj B') ⊗ M)], cy K)
/-- The complete coefficient-coherence assertion for the actual canonical maps.
The single field retains all the original quantifiers and conclusions. A structure keeps
instance certificates in its field type, avoiding their abstraction into nested proof
constants when checking a large Prop-valued definition. It adds no hypothesis or choice.
Source: Stacks 0B56/0GL1, blueprint (G13)
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
structure CompactificationProjectionCoefficientCoherence
    (cx tx : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) V)))
    (cy ty : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) V))) : Prop where
  /-- The unit and coefficient-associativity laws, together with every input domain. -/
  laws : ∀ (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) V))
    (B B' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) V)),
    cx M → ty B → ty B' →
    ∀ (hunit : IsIso (((projectionMapOfCompactification V c).app M).app (𝟙_ _)))
      (hprod : IsIso (((projectionMapOfCompactification V c).app M).app (B ⊗ B')))
      (hleft : IsIso (((projectionMapOfCompactification V c).app
        ((L((f)^*[V])).obj B' ⊗ M)).app B))
      (hright : IsIso (((projectionMapOfCompactification V c).app M).app B')),
      CompactificationProjectionUnit (rightDerivedLowerShriekOfCompactification V c)
        (L((f)^*[V])) (leftDerivedUpperStarUnitIso V f).hom M
        (inverseCompactificationProjection V c (𝟙_ _) M hunit) ∧
      CompactificationProjectionAssoc (rightDerivedLowerShriekOfCompactification V c)
        (L((f)^*[V])) B B' M (leftDerivedUpperStarTensorIso V f B B').hom
        (inverseCompactificationProjection V c (B ⊗ B') M hprod)
        (inverseCompactificationProjection V c B ((L((f)^*[V])).obj B' ⊗ M) hleft)
        (inverseCompactificationProjection V c B' M hright) ∧
      CompactificationProjectionDomains V c cx tx cy ty M B B'

private theorem coherenceUnit [QuasiCompact f]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) V))
    (hU : IsIso (((projectionMapOfCompactification V c).app M).app (𝟙_ _))) :
    CompactificationProjectionUnit (rightDerivedLowerShriekOfCompactification V c)
      L((f)^*[V]) (leftDerivedUpperStarUnitIso V f).hom M
      (inverseCompactificationProjection V c (𝟙_ _) M hU) := by
  let := c.isSeparated
  let := c.locallyOfFiniteType
  let := c.hasCompactification
  let := hU
  let := _root_.DerivedCategory.symmetricCategory (Sheaf (Scheme.ProEt.topology X) V)
  let := _root_.DerivedCategory.symmetricCategory (Sheaf (Scheme.ProEt.topology Y) V)
  simpa only [CompactificationProjectionUnit, inverseCompactificationProjection,
    coherenceSymmetry_eq, Category.assoc] using
    conjugate_unit (rightDerivedLowerShriekOfCompactification V c) L((f)^*[V])
    (fun M B ↦ ((projectionMapOfCompactification V c).app M).app B)
    (leftDerivedUpperStarUnitIso V f).hom M (coherenceNative_unit V f c M)

private theorem coherenceAssoc [QuasiCompact f]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) V))
    (B B' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) V))
    (hprod : IsIso (((projectionMapOfCompactification V c).app M).app (B ⊗ B')))
    (hleft : IsIso (((projectionMapOfCompactification V c).app
      (L((f)^*[V]).obj B' ⊗ M)).app B))
    (hright : IsIso (((projectionMapOfCompactification V c).app M).app B')) :
    CompactificationProjectionAssoc (rightDerivedLowerShriekOfCompactification V c)
      L((f)^*[V]) B B' M (leftDerivedUpperStarTensorIso V f B B').hom
      (inverseCompactificationProjection V c (B ⊗ B') M hprod)
      (inverseCompactificationProjection V c B (L((f)^*[V]).obj B' ⊗ M) hleft)
      (inverseCompactificationProjection V c B' M hright) := by
  let := c.isSeparated
  let := c.locallyOfFiniteType
  let := c.hasCompactification
  let := hprod
  let := hleft
  let := hright
  let := _root_.DerivedCategory.symmetricCategory (Sheaf (Scheme.ProEt.topology X) V)
  let := _root_.DerivedCategory.symmetricCategory (Sheaf (Scheme.ProEt.topology Y) V)
  let P := rightDerivedLowerShriekOfCompactification V c
  let S := L((f)^*[V])
  let p := fun M B ↦ ((projectionMapOfCompactification V c).app M).app B
  have ha := conjugate_assoc P S p
    (fun B B' ↦ (leftDerivedUpperStarTensorIso V f B B').hom)
    (fun {_ _} g B ↦ congr_app ((projectionMapOfCompactification V c).naturality g) B)
    (fun M {_ _} g ↦ ((projectionMapOfCompactification V c).app M).naturality g)
    (coherenceNative_assoc V f c) (coherenceNative_braiding V f) M B B'
  simpa only [CompactificationProjectionAssoc, inverseCompactificationProjection,
    coherenceSymmetry_eq, P, S] using
    conjugate_inverse_assoc P S p
      (fun B B' ↦ (leftDerivedUpperStarTensorIso V f B B').hom) M B B' ha

omit [UpperStarPreservesFlat V] in
private theorem coherenceDomains
    (cx tx : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) V)))
    (cy ty : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) V)))
    (hu : ty (𝟙_ _))
    (htt : ∀ K L, ty K → ty L → ty (K ⊗ L))
    (hxx : ∀ K L, tx K → tx L → tx (K ⊗ L))
    (hxc : ∀ K L, tx K → cx L → cx (K ⊗ L))
    (hcx : ∀ K L, cx K → tx L → cx (K ⊗ L))
    (hyc : ∀ K L, ty K → cy L → cy (K ⊗ L))
    (hcy : ∀ K L, cy K → ty L → cy (K ⊗ L))
    (hs : ∀ K, ty K → tx ((L((f)^*[V])).obj K))
    (hp : ∀ K, cx K → cy ((rightDerivedLowerShriekOfCompactification V c).obj K))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) V))
    (B B' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) V))
    (hM : cx M) (hB : ty B) (hB' : ty B') :
    CompactificationProjectionDomains V c cx tx cy ty M B B' := by
  have hBB := htt B B' hB hB'
  have hS0 := hs _ hu
  have hSB := hs _ hB
  have hSB' := hs _ hB'
  have hSBB := hs _ hBB
  have hSS := hxx _ _ hSB hSB'
  have hSM := hxc _ _ hSB' hM
  have hP := hp _ hM
  have hPSM := hp _ hSM
  simp only [CompactificationProjectionDomains, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, forall_false, forall_true_iff, and_true]
  exact ⟨⟨hu, hBB⟩, ⟨hS0, hSB, hSB', hSBB, hSS⟩,
    ⟨hxc _ _ hS0 hM, hSM, hxc _ _ hSBB hM, hxc _ _ hSS hM,
      hxc _ _ hSB hSM, hcx _ _ hM hS0, hcx _ _ hM hSBB,
      hcx _ _ hSM hSB, hcx _ _ hM hSB'⟩,
    ⟨hP, hyc _ _ hu hP, hyc _ _ hB' hP, hyc _ _ hBB hP,
      hyc _ _ hB (hyc _ _ hB' hP), hp _ (hxc _ _ hS0 hM), hPSM,
      hyc _ _ hB hPSM, hp _ (hxc _ _ hSBB hM), hp _ (hxc _ _ hSB hSM),
      hcy _ _ hP hu, hcy _ _ hP hBB, hcy _ _ hPSM hB, hcy _ _ hP hB',
      hp _ (hcx _ _ hM hS0), hp _ (hcx _ _ hM hSBB),
      hp _ (hcx _ _ hSM hSB), hp _ (hcx _ _ hM hSB'), hp _ (hxc _ _ hSS hM)⟩⟩

private theorem coherenceFromDomains [QuasiCompact f]
    (cx tx : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) V)))
    (cy ty : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) V)))
    (hu : ty (𝟙_ _))
    (htt : ∀ K L, ty K → ty L → ty (K ⊗ L))
    (hxx : ∀ K L, tx K → tx L → tx (K ⊗ L))
    (hxc : ∀ K L, tx K → cx L → cx (K ⊗ L))
    (hcx : ∀ K L, cx K → tx L → cx (K ⊗ L))
    (hyc : ∀ K L, ty K → cy L → cy (K ⊗ L))
    (hcy : ∀ K L, cy K → ty L → cy (K ⊗ L))
    (hs : ∀ K, ty K → tx ((L((f)^*[V])).obj K))
    (hp : ∀ K, cx K → cy ((rightDerivedLowerShriekOfCompactification V c).obj K)) :
    CompactificationProjectionCoefficientCoherence V c cx tx cy ty := by
  constructor
  intro M B B' hM hB hB' hU hprod hleft hright
  exact ⟨coherenceUnit V c M hU, coherenceAssoc V c M B B' hprod hleft hright,
    coherenceDomains V c cx tx cy ty hu htt hxx hxc hcx hyc hcy hs hp M B B' hM hB hB'⟩

end Arrows
/-- The fixed-compactification inverse projection maps satisfy the unit and
coefficient-associativity equations, with all displayed inputs in their stated domains.
Source: Stacks 0B56 and 0GL1; current blueprint sk-prop-cohsm, (G13)
(blueprint: lem-pur-projection-formula-coefficient-coherence).
Proof:
1. Reuse the canonical proper and open right projection-action components, their
associativity laws, and tensor-compatible pasting. Naturality and associativity,
together with invertibility of the unit component, imply the right unit law.
The oplax unit agrees with the specified degree-zero single-complex comparison,
by the derived-functor counit factorization and the homotopy quotient comparison.
2. Conjugate the right action by the canonical tensor symmetry. Naturality,
the hexagon identities and symmetry squared equal to identity give the left
unit and associativity equations. Cancel precisely the four invertible
components assumed in the assertion, yielding its specified inverse maps.
3. Identify intrinsic constructibility and finite Tor amplitude with the fixed-ring
predicates by the canonical realization. Tensor and pullback preserve the required
predicates, and compact support preserves bounded constructibility. The unit is
constructible and flat in degree zero. These facts give every displayed domain,
without imposing finite Tor amplitude on M. -/
theorem compactificationProjection_coefficient_coherence
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ)
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of D.k))]
    [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    CompactificationProjectionCoefficientCoherence
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c
      (projectionCoherenceConstructible l E (n + 1) (Nat.succ_pos n) X)
      (projectionCoherenceFiniteTor l E (n + 1) (Nat.succ_pos n) X)
      (projectionCoherenceConstructible l E (n + 1) (Nat.succ_pos n) Y)
      (projectionCoherenceFiniteTor l E (n + 1) (Nat.succ_pos n) Y) := by
  classical
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let Λ := ULift.{u + 1} A
  let V := ModuleCat.{u + 1} Λ
  let cx := projectionCoherenceConstructible l E (n + 1) (Nat.succ_pos n) X
  let tx := projectionCoherenceFiniteTor l E (n + 1) (Nat.succ_pos n) X
  let cy := projectionCoherenceConstructible l E (n + 1) (Nat.succ_pos n) Y
  let ty := projectionCoherenceFiniteTor l E (n + 1) (Nat.succ_pos n) Y
  have bc (T : Scheme.{u}) (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) V)) :
      projectionCoherenceConstructible l E (n + 1) (Nat.succ_pos n) T K ↔
        DerivedCategory.boundedConstructible V T K :=
    Scheme.intrinsic_bc_realization_iff l E (n + 1) (Nat.succ_pos n) T K
  have ct (T : Scheme.{u}) (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) V)) :
      projectionCoherenceFiniteTor l E (n + 1) (Nat.succ_pos n) T K ↔
        DerivedCategory.constructibleFiniteTor V T K :=
    coherenceCtf_iff l E (n + 1) (Nat.succ_pos n) T K
  have tensorR (T : Scheme.{u})
      (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology T) V))
      (hc : projectionCoherenceConstructible l E (n + 1) (Nat.succ_pos n) T K)
      (ht : projectionCoherenceFiniteTor l E (n + 1) (Nat.succ_pos n) T M) :
      projectionCoherenceConstructible l E (n + 1) (Nat.succ_pos n) T (K ⊗ M) :=
    (bc T _).2 (coherenceBC_tensor Λ T ((bc T K).1 hc) ((ct T M).1 ht))
  have tensorL (T : Scheme.{u})
      (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology T) V))
      (ht : projectionCoherenceFiniteTor l E (n + 1) (Nat.succ_pos n) T K)
      (hc : projectionCoherenceConstructible l E (n + 1) (Nat.succ_pos n) T M) :
      projectionCoherenceConstructible l E (n + 1) (Nat.succ_pos n) T (K ⊗ M) := by
    let := _root_.DerivedCategory.symmetricCategory (Sheaf (Scheme.ProEt.topology T) V)
    exact (bc T _).2 ((DerivedCategory.boundedConstructible V T).prop_of_iso
      (β_ M K) ((bc T _).1 (tensorR T M K hc ht)))
  have tensorT (T : Scheme.{u})
      (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology T) V))
      (hK : projectionCoherenceFiniteTor l E (n + 1) (Nat.succ_pos n) T K)
      (hM : projectionCoherenceFiniteTor l E (n + 1) (Nat.succ_pos n) T M) :
      projectionCoherenceFiniteTor l E (n + 1) (Nat.succ_pos n) T (K ⊗ M) :=
    (ct T _).2 (coherenceCtf_tensor Λ T ((ct T K).1 hK) ((ct T M).1 hM))
  have hs : ∀ K, ty K → tx ((L((f)^*[V])).obj K) := by
    intro K hK
    exact (ct X _).2 (constructibleFiniteTor_leftDerivedFunctor_upperStar_obj f
      ((ct Y K).1 hK))
  have hunit : ty (𝟙_ _) := (ct Y _).2 (coherenceCtf_unit Λ Y)
  have hchar : IsUnit (l : D.k) := by
    let := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
    let : CharP D.k D.p :=
      charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
    exact (CharP.isUnit_natCast_iff (R := D.k) D.prime).2
      (fun h ↦ _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 h).symm)
  have hp : ∀ K, cx K → cy ((rightDerivedLowerShriekOfCompactification V c).obj K) := by
    intro K hK
    let := c.hasCompactification
    let := Scheme.coefficient_has_invertible_exponent l E D.k hchar
      (n + 1) (Nat.succ_pos n)
    have h := boundedConstructible_rightDerivedLowerShriek Λ f
      (X ↘ Spec (.of D.k)) (Y ↘ Spec (.of D.k)) (by simp) K ((bc X K).1 hK)
    exact (bc Y _).2 ((DerivedCategory.boundedConstructible V Y).prop_of_iso
      (Scheme.fixed_compact_support_comparison A c K ((bc X K).1 hK)).symm h)
  exact coherenceFromDomains V c cx tx cy ty hunit
    (tensorT Y) (tensorT X) (tensorL X) (tensorR X) (tensorL Y) (tensorR Y) hs hp

end AlgebraicGeometry.ProEtale
