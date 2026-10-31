/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.Pasting
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.CategoryTheory.Monoidal.DerivedSymmetric
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperFactor.KunnethMapAgrees
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange

/-!
# Finite-cover tensor comparisons and their counit compatibility

Source: blueprint, sec-six-functors, sk-lem-sf-kunneth-star.proof.md,
Field coefficients and sheaves; Stacks Tags 0959, 03QP, 0F0G and 0D6E
(blueprint: lem-sf-finite-cover-tensor-counit-comparison).

The comparison arrows below are concrete counit mates. No arbitrary map or choice
of an isomorphism enters their definitions. Finite direct images are written as R(-);
the exactness clause identifies them with the termwise direct images.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.BraidedCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.FiniteCoverCounit

variable (Λ : Type (u + 1)) [CommRing Λ]
variable {B X Y T T' : Scheme.{u}}

/-- The map id × π on the chosen products.
Source: blueprint, finite-map displayed identifications
(blueprint: lem-sf-finite-cover-tensor-counit-comparison). -/
noncomputable def productMap (b : Y ⟶ B) (c : T ⟶ B) (π : T' ⟶ T) :
    pullback b (π ≫ c) ⟶ pullback b c :=
  pullback.map _ _ _ _ (𝟙 Y) π (𝟙 B) (by simp) (by simp)

/-- External tensor with the direct image of E, as a functor in the first factor.
Source: blueprint, first finite-image identification
(blueprint: lem-sf-finite-cover-tensor-counit-comparison). -/
noncomputable def source (b : Y ⟶ B) (c : T ⟶ B) (π : T' ⟶ T)
    (E : DerivedCategoryModule Λ T') :
    DerivedCategoryModule Λ Y ⥤ DerivedCategoryModule Λ (pullback b c) :=
  L((pullback.fst b c)^*[ModuleCat.{u + 1} Λ]) ⋙
    derivedTensorRight (ModuleCat.{u + 1} Λ) _
      (L((pullback.snd b c)^*[ModuleCat.{u + 1} Λ]).obj
        (R((π)_*[ModuleCat.{u + 1} Λ]).obj E))

/-- The target v_*(p'^*N tensor r'^*E) of the finite tensor comparison.
Source: blueprint, first finite-image identification
(blueprint: lem-sf-finite-cover-tensor-counit-comparison). -/
noncomputable def target (b : Y ⟶ B) (c : T ⟶ B) (π : T' ⟶ T)
    (E : DerivedCategoryModule Λ T') :
    DerivedCategoryModule Λ Y ⥤ DerivedCategoryModule Λ (pullback b c) :=
  L((pullback.fst b (π ≫ c))^*[ModuleCat.{u + 1} Λ]) ⋙
    derivedTensorRight (ModuleCat.{u + 1} Λ) _
      (L((pullback.snd b (π ≫ c))^*[ModuleCat.{u + 1} Λ]).obj E) ⋙
    R((productMap b c π)_*[ModuleCat.{u + 1} Λ])

/-- Finite exchange followed by projection, defined by its actual counit transpose.
The existing tensorBaseChangeMap is the mate of monoidality, the inverse-image
square and the pulled-back π-counit. The final compositor replaces v^*p^* by p'^*.
Source: blueprint, finite-map displayed identifications; Stacks 0959 and 0F0G
(blueprint: lem-sf-finite-cover-tensor-counit-comparison). -/
noncomputable def comparison (b : Y ⟶ B) (c : T ⟶ B) (π : T' ⟶ T)
    (N : DerivedCategoryModule Λ Y) (E : DerivedCategoryModule Λ T') :
    (source Λ b c π E).obj N ⟶ (target Λ b c π E).obj N :=
  tensorBaseChangeMap (ModuleCat.{u + 1} Λ) (productMap b c π)
      (pullback.snd b (π ≫ c)) (pullback.snd b c) π
      (by simp [productMap, pullback.map])
      (L((pullback.fst b c)^*[ModuleCat.{u + 1} Λ]).obj N) E ≫
    R((productMap b c π)_*[ModuleCat.{u + 1} Λ]).map
      (((derivedTensor (ModuleCat.{u + 1} Λ) _).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (productMap b c π)
          (pullback.fst b c) (pullback.fst b (π ≫ c))
          (by simp [productMap, pullback.map])).inv.app N)).app _)

/-- The unit-normalized target v_*p'^*N.
Source: blueprint, first displayed finite-image identification
(blueprint: lem-sf-finite-cover-tensor-counit-comparison). -/
noncomputable def unitTarget (b : Y ⟶ B) (c : T ⟶ B) (π : T' ⟶ T) :
    DerivedCategoryModule Λ Y ⥤ DerivedCategoryModule Λ (pullback b c) :=
  L((pullback.fst b (π ≫ c))^*[ModuleCat.{u + 1} Λ]) ⋙
    R((productMap b c π)_*[ModuleCat.{u + 1} Λ])

/-- Remove the pulled-back constant unit from the target tensor product.
Source: blueprint, L_{T'} and the tensor unit in the first identification
(blueprint: lem-sf-finite-cover-tensor-counit-comparison). -/
noncomputable def unitComparison (b : Y ⟶ B) (c : T ⟶ B) (π : T' ⟶ T)
    (N : DerivedCategoryModule Λ Y) :
    (source Λ b c π (constantComplex Λ T')).obj N ⟶
      (unitTarget Λ b c π).obj N :=
  comparison Λ b c π N (constantComplex Λ T') ≫
    R((productMap b c π)_*[ModuleCat.{u + 1} Λ]).map
      (((derivedTensor (ModuleCat.{u + 1} Λ) _).obj _).map
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ)
          (pullback.snd b (π ≫ c))).hom ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) _ _).hom)

/-- The composition comparison Rh_*Rw_* ≅ Rv_*Rh'_*, using conjugate compositors.
Source: blueprint, equality hw = vh'; Stacks 0D6E, composite adjunction counit
(blueprint: lem-sf-finite-cover-tensor-counit-comparison). -/
noncomputable def composition (b : Y ⟶ B) (c : T ⟶ B) (f : X ⟶ Y) (π : T' ⟶ T) :
    R((productMap (f ≫ b) c π)_*[ModuleCat.{u + 1} Λ]) ⋙
        R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} Λ]) ≅
      R((pullback.mapOverBaseRight f b (π ≫ c))_*[ModuleCat.{u + 1} Λ]) ⋙
        R((productMap b c π)_*[ModuleCat.{u + 1} Λ]) :=
  rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} Λ)
      (productMap (f ≫ b) c π) (pullback.mapOverBaseRight f b c) _ rfl ≪≫
    (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} Λ)
      (pullback.mapOverBaseRight f b (π ≫ c)) (productMap b c π)
      (productMap (f ≫ b) c π ≫ pullback.mapOverBaseRight f b c)
      (by apply pullback.hom_ext <;> simp [productMap, pullback.map])).symm

/-- The second displayed comparison, before removing a constant coefficient factor.
Source: blueprint, second finite-image identification and hw = vh'
(blueprint: lem-sf-finite-cover-tensor-counit-comparison). -/
noncomputable def outputComparison (b : Y ⟶ B) (c : T ⟶ B) (f : X ⟶ Y) (π : T' ⟶ T)
    (M : DerivedCategoryModule Λ X) (E : DerivedCategoryModule Λ T') :
    R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} Λ]).obj
        ((source Λ (f ≫ b) c π E).obj M) ⟶
      R((productMap b c π)_*[ModuleCat.{u + 1} Λ]).obj
        (R((pullback.mapOverBaseRight f b (π ≫ c))_*[ModuleCat.{u + 1} Λ]).obj
          (externalProduct (ModuleCat.{u + 1} Λ) (f ≫ b) (π ≫ c) M E)) :=
  R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} Λ]).map
      (comparison Λ (f ≫ b) c π M E) ≫
    (composition Λ b c f π).hom.app _

/-- The unit-normalized second displayed comparison.
Source: blueprint, second displayed finite-image identification
(blueprint: lem-sf-finite-cover-tensor-counit-comparison). -/
noncomputable def unitOutputComparison
    (b : Y ⟶ B) (c : T ⟶ B) (f : X ⟶ Y) (π : T' ⟶ T)
    (M : DerivedCategoryModule Λ X) :
    R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} Λ]).obj
        ((source Λ (f ≫ b) c π (constantComplex Λ T')).obj M) ⟶
      R((productMap b c π)_*[ModuleCat.{u + 1} Λ]).obj
        (R((pullback.mapOverBaseRight f b (π ≫ c))_*[ModuleCat.{u + 1} Λ]).obj
          (L((pullback.fst (f ≫ b) (π ≫ c))^*[ModuleCat.{u + 1} Λ]).obj M)) :=
  R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} Λ]).map
      (unitComparison Λ (f ≫ b) c π M) ≫
    (composition Λ b c f π).hom.app _

/-- The base-change map adjoint to p'^* of the f-counit, with no invertibility assumed.
Source: blueprint, counit calculation following the finite-image identifications
(blueprint: lem-sf-finite-cover-tensor-counit-comparison). -/
noncomputable def exchange (b : Y ⟶ B) (c : T ⟶ B) (f : X ⟶ Y) :
    R((f)_*[ModuleCat.{u + 1} Λ]) ⋙ L((pullback.fst b c)^*[ModuleCat.{u + 1} Λ]) ⟶
      L((pullback.fst (f ≫ b) c)^*[ModuleCat.{u + 1} Λ]) ⋙
        R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} Λ]) :=
  derivedBaseChangeMap (ModuleCat.{u + 1} Λ) ⟨by simp⟩

set_option maxHeartbeats 800000 in
-- Naturality crosses compositions of derived pullback and tensor functors.
private theorem comparison_naturality (b : Y ⟶ B) (c : T ⟶ B) (π : T' ⟶ T)
    {N N' : DerivedCategoryModule Λ Y} (φ : N ⟶ N') (E : DerivedCategoryModule Λ T') :
    (source Λ b c π E).map φ ≫ comparison Λ b c π N' E =
      comparison Λ b c π N E ≫ (target Λ b c π E).map φ := by
  let v := productMap b c π
  let p := pullback.fst b c
  let p' := pullback.fst b (π ≫ c)
  let e := leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) v p p'
    (by simp [v, p, p', productMap, pullback.map])
  have ht := tensorBaseChangeMap_naturality (ModuleCat.{u + 1} Λ) v
    (pullback.snd b (π ≫ c)) (pullback.snd b c) π
    (by simp [v, productMap, pullback.map])
    (L((p)^*[ModuleCat.{u + 1} Λ]).map φ) (𝟙 E)
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at ht
  have he := e.inv.naturality φ
  have he' := congrArg
    (fun ψ ↦ ((derivedTensor (ModuleCat.{u + 1} Λ) _).map ψ).app
      (L((pullback.snd b (π ≫ c))^*[ModuleCat.{u + 1} Λ]).obj E)) he
  simp only [Functor.comp_map, Functor.map_comp, NatTrans.comp_app] at he'
  dsimp only [source, target, comparison, Functor.comp_map, derivedTensorRight,
    Functor.flip_obj_map]
  rw [← Category.assoc, ht]
  simpa only [Functor.map_comp, Category.assoc] using congrArg
    (fun ψ ↦ tensorBaseChangeMap (ModuleCat.{u + 1} Λ) v
      (pullback.snd b (π ≫ c)) (pullback.snd b c) π
      (by simp [v, productMap, pullback.map]) (L((p)^*[ModuleCat.{u + 1} Λ]).obj N) E ≫
        R((v)_*[ModuleCat.{u + 1} Λ]).map ψ) he'

private theorem comparison_isIso [Finite Λ] (b : Y ⟶ B) (c : T ⟶ B) (π : T' ⟶ T)
    [IsFinite π] (N : DerivedCategoryModule Λ Y) (E : DerivedCategoryModule Λ T') :
    IsIso (comparison Λ b c π N E) := by
  have hp : IsPullback (productMap b c π) (pullback.snd b (π ≫ c))
      (pullback.snd b c) π := by
    refine .of_right (h₁₂ := pullback.fst b c) (h₂₂ := c) (v₁₃ := b) ?_ ?_
      (IsPullback.of_hasPullback b c)
    · simpa [productMap, pullback.map] using (IsPullback.of_hasPullback b (π ≫ c))
    · simp [productMap, pullback.map]
  have : IsFinite (productMap b c π) :=
    MorphismProperty.of_isPullback (P := @IsFinite) hp.flip inferInstance
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ
    isAddTorsion_of_finite hp.flip
  have := isIso_rightDerivedLowerStarProjectionMap_of_isProper Λ
    isAddTorsion_of_finite (productMap b c π)
  dsimp only [comparison]
  rw [tensorBaseChangeMap_eq_projectionMap]
  infer_instance

/-- The finite comparison data for a finite-dimensional constant coefficient: natural
isomorphisms a and d whose components are exactly comparison and outputComparison.
Source: blueprint, sk-lem-sf-kunneth-star.proof.md, Field coefficients and sheaves,
the two finite-image identifications; Stacks Tags 0959, 03QP, 0F0G and 0D6E
(blueprint: lem-sf-finite-cover-tensor-counit-comparison-data).

Proof: v = productMap b c π and w = productMap (f ≫ b) c π are base changes
of finite π, hence finite and proper. The finite coefficient ring is additive torsion.
Proper torsion base change identifies the pulled-back Rπ_*E with Rv_* of its
pullback, and the proper projection formula (Stacks 0F0G) makes tensorBaseChangeMap
an isomorphism. Composing with the inverse-image compositor gives comparison.
Naturality of tensorBaseChangeMap and the compositor assembles these components
into a natural isomorphism. Whiskering with R((f × id)_*) and composing with the
prescribed direct-image compositor gives outputComparison. Whiskering with the
bounded-below inclusion gives a and d; their component equations hold by construction. -/
theorem finiteCoverTensorCounitComparison_constantModule_data
    (k : Type u) [Field k] (L : Type (u + 1)) [Field L] [Finite L]
    (hL : IsUnit (ringChar L : k))
    {X Y T T' : Scheme.{u}} (b : Y ⟶ Spec (.of k)) (c : T ⟶ Spec (.of k))
    (f : X ⟶ Y) (π : T' ⟶ T) [IsFinite π]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsSeparated (f ≫ b)] [LocallyOfFiniteType (f ≫ b)] [QuasiCompact (f ≫ b)]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    [IsSeparated (π ≫ c)] [LocallyOfFiniteType (π ≫ c)] [QuasiCompact (π ≫ c)]
    (V : ModuleCat.{u + 1} L) [Module.Finite L V] :
    ∀ E : DerivedCategoryModule L T',
      E = (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf T'.smallEtaleTopology (ModuleCat.{u + 1} L)).obj V) →
    ∃ (a : _root_.DerivedCategory.Plus.ι ⋙ R((f)_*[ModuleCat.{u + 1} L]) ⋙
          source L b c π E ≅
        _root_.DerivedCategory.Plus.ι ⋙ R((f)_*[ModuleCat.{u + 1} L]) ⋙ target L b c π E)
      (d : _root_.DerivedCategory.Plus.ι ⋙ source L (f ≫ b) c π E ⋙
          R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} L]) ≅
        _root_.DerivedCategory.Plus.ι ⋙
          L((pullback.fst (f ≫ b) (π ≫ c))^*[ModuleCat.{u + 1} L]) ⋙
          derivedTensorRight (ModuleCat.{u + 1} L) _
            (L((pullback.snd (f ≫ b) (π ≫ c))^*[ModuleCat.{u + 1} L]).obj E) ⋙
          R((pullback.mapOverBaseRight f b (π ≫ c))_*[ModuleCat.{u + 1} L]) ⋙
          R((productMap b c π)_*[ModuleCat.{u + 1} L])),
      ∀ M : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} L)),
        a.hom.app M = comparison L b c π (R((f)_*[ModuleCat.{u + 1} L]).obj M.obj) E ∧
        d.hom.app M = outputComparison L b c f π M.obj E := by
  classical
  have _ := hL
  intro E _
  let a₀ : source L b c π E ≅ target L b c π E :=
    NatIso.ofComponents (fun N ↦ by
      have := comparison_isIso L b c π N E
      exact asIso (comparison L b c π N E))
      (fun φ ↦ comparison_naturality L b c π φ E)
  let d₀ : source L (f ≫ b) c π E ≅ target L (f ≫ b) c π E :=
    NatIso.ofComponents (fun N ↦ by
      have := comparison_isIso L (f ≫ b) c π N E
      exact asIso (comparison L (f ≫ b) c π N E))
      (fun φ ↦ comparison_naturality L (f ≫ b) c π φ E)
  let a := Functor.isoWhiskerLeft (_root_.DerivedCategory.Plus.ι ⋙
    R((f)_*[ModuleCat.{u + 1} L])) a₀
  let H := R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} L])
  let d := Functor.isoWhiskerLeft _root_.DerivedCategory.Plus.ι
    (Functor.isoWhiskerRight d₀ H ≪≫ Functor.isoWhiskerLeft
      (L((pullback.fst (f ≫ b) (π ≫ c))^*[ModuleCat.{u + 1} L]) ⋙
        derivedTensorRight (ModuleCat.{u + 1} L) _
          (L((pullback.snd (f ≫ b) (π ≫ c))^*[ModuleCat.{u + 1} L]).obj E))
      (composition L b c f π))
  exact ⟨a, d, fun _ ↦ ⟨rfl, rfl⟩⟩

section

attribute [local instance] _root_.DerivedCategory.braidedCategory'

private theorem mate_square
    {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
    {L₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} {L₁' : C₁ ⥤ C₃} {R₁' : C₃ ⥤ C₁}
    {L₂ : C₀ ⥤ C₂} {R₂ : C₂ ⥤ C₀} {L₂' : C₂ ⥤ C₃} {R₂' : C₃ ⥤ C₂}
    (a₁ : L₁ ⊣ R₁) (a₁' : L₁' ⊣ R₁') (a₂ : L₂ ⊣ R₂) (a₂' : L₂' ⊣ R₂')
    (q : L₂ ⋙ L₂' ⟶ L₁ ⋙ L₁')
    {K₀ : C₀} {K₁ : C₁} {K₂ : C₂} {K₃ : C₃}
    (x : K₀ ⟶ R₁.obj K₁) (y : K₁ ⟶ R₁'.obj K₃)
    (z : K₀ ⟶ R₂.obj K₂) (w : K₂ ⟶ R₂'.obj K₃)
    (h : q.app K₀ ≫ L₁'.map ((a₁.homEquiv _ _).symm x) ≫
        (a₁'.homEquiv _ _).symm y =
      L₂'.map ((a₂.homEquiv _ _).symm z) ≫ (a₂'.homEquiv _ _).symm w) :
    x ≫ R₁.map y ≫ (conjugateEquiv (a₁.comp a₁') (a₂.comp a₂') q).app K₃ =
      z ≫ R₂.map w := by
  apply ((a₂.comp a₂').homEquiv _ _).symm.injective
  have hc (φ : K₀ ⟶ (R₁' ⋙ R₁).obj K₃) :
      ((a₂.comp a₂').homEquiv _ _).symm
        (φ ≫ (conjugateEquiv (a₁.comp a₁') (a₂.comp a₂') q).app K₃) =
      q.app K₀ ≫ ((a₁.comp a₁').homEquiv _ _).symm φ := by
    rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
      conjugateEquiv_counit, q.naturality_assoc, Adjunction.homEquiv_counit]
  rw [← Category.assoc, hc]
  simp only [Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
  erw [Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_left_symm]
  exact h


private theorem tensor_square
    {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
    [MonoidalCategory C₀] [MonoidalCategory C₁] [MonoidalCategory C₂] [MonoidalCategory C₃]
    (L₁ : C₀ ⥤ C₁) (L₁' : C₁ ⥤ C₃) (L₂ : C₀ ⥤ C₂) (L₂' : C₂ ⥤ C₃)
    (q : L₂ ⋙ L₂' ⟶ L₁ ⋙ L₁')
    (δ₁ : ∀ A B, L₁.obj (A ⊗ B) ⟶ L₁.obj A ⊗ L₁.obj B)
    (δ₁' : ∀ A B, L₁'.obj (A ⊗ B) ⟶ L₁'.obj A ⊗ L₁'.obj B)
    (δ₂ : ∀ A B, L₂.obj (A ⊗ B) ⟶ L₂.obj A ⊗ L₂.obj B)
    (δ₂' : ∀ A B, L₂'.obj (A ⊗ B) ⟶ L₂'.obj A ⊗ L₂'.obj B)
    (hn₁ : ∀ {A A' B B'} (a : A ⟶ A') (b : B ⟶ B'),
      L₁'.map (a ⊗ₘ b) ≫ δ₁' A' B' = δ₁' A B ≫ (L₁'.map a ⊗ₘ L₁'.map b))
    (hn₂ : ∀ {A A' B B'} (a : A ⟶ A') (b : B ⟶ B'),
      L₂'.map (a ⊗ₘ b) ≫ δ₂' A' B' = δ₂' A B ≫ (L₂'.map a ⊗ₘ L₂'.map b))
    (hq : ∀ A B, L₂'.map (δ₂ A B) ≫ δ₂' _ _ ≫ (q.app A ⊗ₘ q.app B) =
      q.app (A ⊗ B) ≫ L₁'.map (δ₁ A B) ≫ δ₁' _ _)
    {A₀ B₀ : C₀} {A₁ B₁ : C₁} {A₂ B₂ : C₂} {A₃ B₃ : C₃}
    (a : L₁.obj A₀ ⟶ A₁) (b : L₁.obj B₀ ⟶ B₁)
    (c : L₁'.obj A₁ ⟶ A₃) (d : L₁'.obj B₁ ⟶ B₃)
    (e : L₂.obj A₀ ⟶ A₂) (f : L₂.obj B₀ ⟶ B₂)
    (g : L₂'.obj A₂ ⟶ A₃) (i : L₂'.obj B₂ ⟶ B₃)
    (hA : q.app A₀ ≫ L₁'.map a ≫ c = L₂'.map e ≫ g)
    (hB : q.app B₀ ≫ L₁'.map b ≫ d = L₂'.map f ≫ i) :
    q.app (A₀ ⊗ B₀) ≫ L₁'.map (δ₁ _ _ ≫ (a ⊗ₘ b)) ≫ δ₁' _ _ ≫ (c ⊗ₘ d) =
      L₂'.map (δ₂ _ _ ≫ (e ⊗ₘ f)) ≫ δ₂' _ _ ≫ (g ⊗ₘ i) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (hn₁ a b), reassoc_of% (hn₂ e f)]
  rw [← reassoc_of% (hq A₀ B₀)]
  simp only [tensorHom_comp_tensorHom, hA, hB]


private theorem tensor_mate_square
    {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
    [MonoidalCategory C₀] [MonoidalCategory C₁] [MonoidalCategory C₂] [MonoidalCategory C₃]
    {L₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} {L₁' : C₁ ⥤ C₃} {R₁' : C₃ ⥤ C₁}
    {L₂ : C₀ ⥤ C₂} {R₂ : C₂ ⥤ C₀} {L₂' : C₂ ⥤ C₃} {R₂' : C₃ ⥤ C₂}
    (a₁ : L₁ ⊣ R₁) (a₁' : L₁' ⊣ R₁') (a₂ : L₂ ⊣ R₂) (a₂' : L₂' ⊣ R₂')
    (q : L₂ ⋙ L₂' ⟶ L₁ ⋙ L₁')
    (d₀ : R₁' ⋙ R₁ ⟶ R₂' ⋙ R₂)
    (hd₀ : d₀ = conjugateEquiv (a₁.comp a₁') (a₂.comp a₂') q)
    (δ₁ : ∀ A B, L₁.obj (A ⊗ B) ⟶ L₁.obj A ⊗ L₁.obj B)
    (δ₁' : ∀ A B, L₁'.obj (A ⊗ B) ⟶ L₁'.obj A ⊗ L₁'.obj B)
    (δ₂ : ∀ A B, L₂.obj (A ⊗ B) ⟶ L₂.obj A ⊗ L₂.obj B)
    (δ₂' : ∀ A B, L₂'.obj (A ⊗ B) ⟶ L₂'.obj A ⊗ L₂'.obj B)
    (hn₁ : ∀ {A A' B B'} (a : A ⟶ A') (b : B ⟶ B'),
      L₁'.map (a ⊗ₘ b) ≫ δ₁' A' B' = δ₁' A B ≫ (L₁'.map a ⊗ₘ L₁'.map b))
    (hn₂ : ∀ {A A' B B'} (a : A ⟶ A') (b : B ⟶ B'),
      L₂'.map (a ⊗ₘ b) ≫ δ₂' A' B' = δ₂' A B ≫ (L₂'.map a ⊗ₘ L₂'.map b))
    (hq : ∀ A B, L₂'.map (δ₂ A B) ≫ δ₂' _ _ ≫ (q.app A ⊗ₘ q.app B) =
      q.app (A ⊗ B) ≫ L₁'.map (δ₁ A B) ≫ δ₁' _ _)
    {A₀ B₀ : C₀} {A₁ B₁ : C₁} {A₂ B₂ : C₂} {A₃ B₃ : C₃}
    (a : L₁.obj A₀ ⟶ A₁) (b : L₁.obj B₀ ⟶ B₁)
    (c : L₁'.obj A₁ ⟶ A₃) (d : L₁'.obj B₁ ⟶ B₃)
    (e : L₂.obj A₀ ⟶ A₂) (f : L₂.obj B₀ ⟶ B₂)
    (g : L₂'.obj A₂ ⟶ A₃) (i : L₂'.obj B₂ ⟶ B₃)
    (hA : q.app A₀ ≫ L₁'.map a ≫ c = L₂'.map e ≫ g)
    (hB : q.app B₀ ≫ L₁'.map b ≫ d = L₂'.map f ≫ i)
    (x : A₀ ⊗ B₀ ⟶ R₁.obj (A₁ ⊗ B₁))
    (y : A₁ ⊗ B₁ ⟶ R₁'.obj (A₃ ⊗ B₃))
    (z : A₀ ⊗ B₀ ⟶ R₂.obj (A₂ ⊗ B₂))
    (w : A₂ ⊗ B₂ ⟶ R₂'.obj (A₃ ⊗ B₃))
    (hx : (a₁.homEquiv _ _).symm x = δ₁ _ _ ≫ (a ⊗ₘ b))
    (hy : (a₁'.homEquiv _ _).symm y = δ₁' _ _ ≫ (c ⊗ₘ d))
    (hz : (a₂.homEquiv _ _).symm z = δ₂ _ _ ≫ (e ⊗ₘ f))
    (hw : (a₂'.homEquiv _ _).symm w = δ₂' _ _ ≫ (g ⊗ₘ i)) :
    x ≫ R₁.map y ≫ d₀.app _ = z ≫ R₂.map w := by
  rw [hd₀]
  apply mate_square a₁ a₁' a₂ a₂' q x y z w
  rw [hx, hy, hz, hw]
  exact tensor_square L₁ L₁' L₂ L₂' q δ₁ δ₁' δ₂ δ₂' hn₁ hn₂ hq
    a b c d e f g i hA hB


private theorem derived_tensor_mate_square
    {S₀ S₁ S₂ S₃ : Scheme.{u}}
    {L₁ : (DerivedCategoryModule Λ S₀) ⥤ (DerivedCategoryModule Λ S₁)} {R₁ : (DerivedCategoryModule
      Λ S₁) ⥤ (DerivedCategoryModule Λ S₀)} {L₁' : (DerivedCategoryModule Λ S₁) ⥤
      (DerivedCategoryModule Λ S₃)} {R₁' : (DerivedCategoryModule Λ S₃) ⥤ (DerivedCategoryModule Λ
      S₁)}
    {L₂ : (DerivedCategoryModule Λ S₀) ⥤ (DerivedCategoryModule Λ S₂)} {R₂ : (DerivedCategoryModule
      Λ S₂) ⥤ (DerivedCategoryModule Λ S₀)} {L₂' : (DerivedCategoryModule Λ S₂) ⥤
      (DerivedCategoryModule Λ S₃)} {R₂' : (DerivedCategoryModule Λ S₃) ⥤ (DerivedCategoryModule Λ
      S₂)}
    (a₁ : L₁ ⊣ R₁) (a₁' : L₁' ⊣ R₁') (a₂ : L₂ ⊣ R₂) (a₂' : L₂' ⊣ R₂')
    (q : L₂ ⋙ L₂' ⟶ L₁ ⋙ L₁')
    (d₀ : R₁' ⋙ R₁ ⟶ R₂' ⋙ R₂)
    (hd₀ : d₀ = conjugateEquiv (a₁.comp a₁') (a₂.comp a₂') q)
    (δ₁ : ∀ A B, L₁.obj (A ⊗ B) ⟶ L₁.obj A ⊗ L₁.obj B)
    (δ₁' : ∀ A B, L₁'.obj (A ⊗ B) ⟶ L₁'.obj A ⊗ L₁'.obj B)
    (δ₂ : ∀ A B, L₂.obj (A ⊗ B) ⟶ L₂.obj A ⊗ L₂.obj B)
    (δ₂' : ∀ A B, L₂'.obj (A ⊗ B) ⟶ L₂'.obj A ⊗ L₂'.obj B)
    (hn₁ : ∀ {A A' B B'} (a : A ⟶ A') (b : B ⟶ B'),
      L₁'.map (a ⊗ₘ b) ≫ δ₁' A' B' = δ₁' A B ≫ (L₁'.map a ⊗ₘ L₁'.map b))
    (hn₂ : ∀ {A A' B B'} (a : A ⟶ A') (b : B ⟶ B'),
      L₂'.map (a ⊗ₘ b) ≫ δ₂' A' B' = δ₂' A B ≫ (L₂'.map a ⊗ₘ L₂'.map b))
    (hq : ∀ A B, L₂'.map (δ₂ A B) ≫ δ₂' _ _ ≫ (q.app A ⊗ₘ q.app B) =
      q.app (A ⊗ B) ≫ L₁'.map (δ₁ A B) ≫ δ₁' _ _)
    {A₀ B₀ : (DerivedCategoryModule Λ S₀)} {A₁ B₁ : (DerivedCategoryModule Λ S₁)} {A₂ B₂ :
      (DerivedCategoryModule Λ S₂)} {A₃ B₃ : (DerivedCategoryModule Λ S₃)}
    (a : L₁.obj A₀ ⟶ A₁) (b : L₁.obj B₀ ⟶ B₁)
    (c : L₁'.obj A₁ ⟶ A₃) (d : L₁'.obj B₁ ⟶ B₃)
    (e : L₂.obj A₀ ⟶ A₂) (f : L₂.obj B₀ ⟶ B₂)
    (g : L₂'.obj A₂ ⟶ A₃) (i : L₂'.obj B₂ ⟶ B₃)
    (hA : q.app A₀ ≫ L₁'.map a ≫ c = L₂'.map e ≫ g)
    (hB : q.app B₀ ≫ L₁'.map b ≫ d = L₂'.map f ≫ i)
    (x : A₀ ⊗ B₀ ⟶ R₁.obj (A₁ ⊗ B₁))
    (y : A₁ ⊗ B₁ ⟶ R₁'.obj (A₃ ⊗ B₃))
    (z : A₀ ⊗ B₀ ⟶ R₂.obj (A₂ ⊗ B₂))
    (w : A₂ ⊗ B₂ ⟶ R₂'.obj (A₃ ⊗ B₃))
    (hx : (a₁.homEquiv _ _).symm x = δ₁ _ _ ≫ (a ⊗ₘ b))
    (hy : (a₁'.homEquiv _ _).symm y = δ₁' _ _ ≫ (c ⊗ₘ d))
    (hz : (a₂.homEquiv _ _).symm z = δ₂ _ _ ≫ (e ⊗ₘ f))
    (hw : (a₂'.homEquiv _ _).symm w = δ₂' _ _ ≫ (g ⊗ₘ i)) :
    x ≫ R₁.map y ≫ d₀.app _ = z ≫ R₂.map w := by
  exact tensor_mate_square a₁ a₁' a₂ a₂' q d₀ hd₀
    δ₁ δ₁' δ₂ δ₂' hn₁ hn₂ hq a b c d e f g i hA hB x y z w hx hy hz hw


private theorem factor_coherence {W A B V X Y : Scheme.{u}}
    (s : W ⟶ A) (h : A ⟶ B) (t : W ⟶ V) (v : V ⟶ B)
    (p : A ⟶ X) (q : B ⟶ Y) (p' : W ⟶ X) (q' : V ⟶ Y) (f : X ⟶ Y)
    (sq : CommSq s t h v) (sq₀ : CommSq p h f q) (sq₁ : CommSq p' t f q')
    (hp : p' = s ≫ p) (hq : q' = v ≫ q)
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app
        (L((q)^*[ModuleCat.{u + 1} Λ]).obj N) ≫
      L((s)^*[ModuleCat.{u + 1} Λ]).map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq₀).hom.app N) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s p p' hp).inv.app
        (L((f)^*[ModuleCat.{u + 1} Λ]).obj N) =
    L((t)^*[ModuleCat.{u + 1} Λ]).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) v q q' hq).inv.app N) ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq₁).hom.app N := by
  have hu : p' ≫ f = (s ≫ h) ≫ q := by rw [hp, Category.assoc, sq₀.w, Category.assoc]
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [map_leftDerivedUpperStarComp_hom_app_leftDerivedUpperStarComp_inv_app
    (ModuleCat.{u + 1} Λ) s p f p' (p ≫ f) (p' ≫ f) hp rfl rfl]
  rw [leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app_assoc
    (ModuleCat.{u + 1} Λ) s h q (s ≫ h) (p ≫ f) (p' ≫ f) rfl sq₀.w hu]
  rw [Iso.hom_inv_id_app_assoc]
  rw [← map_leftDerivedUpperStarComp_inv_app_leftDerivedUpperStarComp_inv_app_assoc
    (ModuleCat.{u + 1} Λ) t v q (s ≫ h) q' (p' ≫ f) sq.w hq hu]

private theorem factor_counit_coherence {W A B V X Y : Scheme.{u}}
    (s : W ⟶ A) (h : A ⟶ B) (t : W ⟶ V) (v : V ⟶ B)
    (p : A ⟶ X) (q : B ⟶ Y) (p' : W ⟶ X) (q' : V ⟶ Y) (f : X ⟶ Y)
    (sq : CommSq s t h v) (sq₀ : CommSq p h f q) (sq₁ : CommSq p' t f q')
    (hp : p' = s ≫ p) (hq : q' = v ≫ q)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app
        (L((q)^*[ModuleCat.{u + 1} Λ]).obj (R((f)_*[ModuleCat.{u + 1} Λ]).obj M)) ≫
      L((s)^*[ModuleCat.{u + 1} Λ]).map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq₀).hom.app
            (R((f)_*[ModuleCat.{u + 1} Λ]).obj M) ≫
          L((p)^*[ModuleCat.{u + 1} Λ]).map
            ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app M)) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s p p' hp).inv.app M =
    L((t)^*[ModuleCat.{u + 1} Λ]).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) v q q' hq).inv.app
          (R((f)_*[ModuleCat.{u + 1} Λ]).obj M)) ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq₁).hom.app
        (R((f)_*[ModuleCat.{u + 1} Λ]).obj M) ≫
      L((p')^*[ModuleCat.{u + 1} Λ]).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app M) := by
  have hc := factor_coherence Λ s h t v p q p' q' f sq sq₀ sq₁ hp hq
    (R((f)_*[ModuleCat.{u + 1} Λ]).obj M)
  have he := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s p p' hp).inv.naturality
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at he
  simp only [Functor.map_comp, Category.assoc]
  rw [he, reassoc_of% hc]

private theorem square_flip {W A B V : Scheme.{u}}
    {s : W ⟶ A} {h : A ⟶ B} {t : W ⟶ V} {v : V ⟶ B}
    (sq : CommSq s t h v)
    (N : DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq.flip).hom.app N =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).inv.app N := by
  dsimp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Iso.trans_inv, Iso.symm_inv]
  exact leftDerivedUpperStarComp_inv_app_comp_hom_app_congr (ModuleCat.{u + 1} Λ)
    s h t v (t ≫ v) (s ≫ h) sq.w.symm rfl rfl sq.w N


private theorem factor_counit_coherence_op {W A B V X Y : Scheme.{u}}
    (s : W ⟶ A) (h : A ⟶ B) (t : W ⟶ V) (v : V ⟶ B)
    (p : V ⟶ X) (q : B ⟶ Y) (p' : W ⟶ X) (q' : A ⟶ Y) (f : X ⟶ Y)
    (sq : CommSq s t h v) (sq₀ : CommSq p v f q) (sq₁ : CommSq p' s f q')
    (hp : p' = t ≫ p) (hq : q' = h ≫ q)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app
        (L((q)^*[ModuleCat.{u + 1} Λ]).obj (R((f)_*[ModuleCat.{u + 1} Λ]).obj M)) ≫
      L((s)^*[ModuleCat.{u + 1} Λ]).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) h q q' hq).inv.app
          (R((f)_*[ModuleCat.{u + 1} Λ]).obj M)) ≫
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq₁).hom.app
        (R((f)_*[ModuleCat.{u + 1} Λ]).obj M) ≫
      L((p')^*[ModuleCat.{u + 1} Λ]).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app M) =
    L((t)^*[ModuleCat.{u + 1} Λ]).map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq₀).hom.app
            (R((f)_*[ModuleCat.{u + 1} Λ]).obj M) ≫
          L((p)^*[ModuleCat.{u + 1} Λ]).map
            ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app M)) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) t p p' hp).inv.app M := by
  have H := factor_counit_coherence Λ t v s h p q p' q' f
    sq.flip sq₀ sq₁ hp hq M
  rw [square_flip Λ sq] at H
  have HH := congrArg
    (fun ψ ↦ (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app
      (L((q)^*[ModuleCat.{u + 1} Λ]).obj (R((f)_*[ModuleCat.{u + 1} Λ]).obj M)) ≫ ψ) H
  simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using HH.symm

set_option maxHeartbeats 800000 in
-- Unfold the fixed compositors through their two composite adjunctions.
private theorem composition_conjugate (b : Y ⟶ B) (c : T ⟶ B) (f : X ⟶ Y) (π : T' ⟶ T) :
    (composition Λ b c f π).hom =
      conjugateEquiv
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (pullback.mapOverBaseRight f b c)).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (productMap (f ≫ b) c π)))
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (productMap b c π)).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (pullback.mapOverBaseRight f b (π ≫ c))))
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ)
          (CommSq.mk (show productMap (f ≫ b) c π ≫ pullback.mapOverBaseRight f b c =
              pullback.mapOverBaseRight f b (π ≫ c) ≫ productMap b c π by
            apply pullback.hom_ext <;> simp [productMap, pullback.map]))).hom := by
  dsimp only [composition, Iso.trans_hom, Iso.symm_hom,
    rightDerivedLowerStarCompIsoOfComp]
  rw [conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_apply_inv, conjugateEquiv_comp]
  rfl

private theorem comparison_transpose_general {W A S S' : Scheme.{u}}
    (v : W ⟶ A) (r' : W ⟶ S') (r : A ⟶ S) (π : S' ⟶ S)
    (sq : CommSq r' v π r) (P : DerivedCategoryModule Λ A)
    (P' : DerivedCategoryModule Λ W) (E : DerivedCategoryModule Λ S')
    (ψ : L((v)^*[ModuleCat.{u + 1} Λ]).obj P ⟶ P') :
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).homEquiv _ _).symm
      (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) v r' r π sq.w.symm P E ≫
        R((v)_*[ModuleCat.{u + 1} Λ]).map
          (((derivedTensor (ModuleCat.{u + 1} Λ) W).map ψ).app
            (L((r')^*[ModuleCat.{u + 1} Λ]).obj E))) =
    ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) v).app P).app _ ≫
      (ψ ⊗ₘ ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app
          (R((π)_*[ModuleCat.{u + 1} Λ]).obj E) ≫
        L((r')^*[ModuleCat.{u + 1} Λ]).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).counit.app E))) := by
  rw [Adjunction.homEquiv_naturality_right_symm, tensorBaseChangeMap]
  erw [Equiv.symm_apply_apply]
  simp only [derivedTensor, curriedTensor_map_app, curriedTensor_obj_map,
    derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    MonoidalCategory.tensorHom_def, whisker_exchange, Category.assoc]
  rw [leftDerivedUpperStarComp_inv_app_comp_hom_app_congr_assoc
    (ModuleCat.{u + 1} Λ) v r r' π (v ≫ r) (r' ≫ π) rfl sq.w.symm sq.w rfl]

private theorem external_transpose_general {W A X Y S : Scheme.{u}}
    (h : W ⟶ A) (p : A ⟶ Y) (p' : W ⟶ X) (f : X ⟶ Y)
    (r : A ⟶ S) (r' : W ⟶ S) (sq : CommSq p' h f p) (hr : r' = h ≫ r)
    (M : DerivedCategoryModule Λ X) (Q : DerivedCategoryModule Λ S) :
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).homEquiv _ _).symm
      (((derivedTensorBraiding (ModuleCat.{u + 1} Λ) A).hom.app
          (L((p)^*[ModuleCat.{u + 1} Λ]).obj (R((f)_*[ModuleCat.{u + 1} Λ]).obj M))).app
            (L((r)^*[ModuleCat.{u + 1} Λ]).obj Q) ≫
        tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h p' p f sq.w.symm
          (L((r)^*[ModuleCat.{u + 1} Λ]).obj Q) M ≫
        R((h)_*[ModuleCat.{u + 1} Λ]).map
          (((derivedTensor (ModuleCat.{u + 1} Λ) W).map
            ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) h r r' hr).inv.app Q)).app
              (L((p')^*[ModuleCat.{u + 1} Λ]).obj M) ≫
            ((derivedTensorBraiding (ModuleCat.{u + 1} Λ) W).hom.app
              (L((r')^*[ModuleCat.{u + 1} Λ]).obj Q)).app
                (L((p')^*[ModuleCat.{u + 1} Λ]).obj M))) =
    ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) h).app _).app _ ≫
      (((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app
          (R((f)_*[ModuleCat.{u + 1} Λ]).obj M) ≫
        L((p')^*[ModuleCat.{u + 1} Λ]).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app M)) ⊗ₘ
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) h r r' hr).inv.app Q) := by
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm, tensorBaseChangeMap]
  erw [Equiv.symm_apply_apply]
  simp only [derivedTensorBraiding, curriedBraidingNatIso_hom_app_app, Category.assoc]
  rw [leftDerivedUpperStar_map_braiding_hom_comp_tensorComparison_assoc]
  simp only [derivedTensor, curriedTensor_map_app, curriedTensor_obj_map,
    derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  rw [← tensorHom_def'_assoc, ← braiding_naturality_assoc]
  rw [_root_.DerivedCategory.braiding_hom_braiding_hom
    (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (fun _ _ ↦ SymmetricCategory.symmetry _ _)]
  simp only [Category.comp_id]
  rw [leftDerivedUpperStarComp_inv_app_comp_hom_app_congr_assoc
    (ModuleCat.{u + 1} Λ) h p p' f (h ≫ p) (p' ≫ f) rfl sq.w.symm sq.w rfl]

private theorem rectangle_counit
    {S₀ S₁ S₂ S₃ : Scheme.{u}}
    (h : S₁ ⟶ S₀) (w : S₃ ⟶ S₁) (v : S₂ ⟶ S₀) (h' : S₃ ⟶ S₂)
    (f : X ⟶ Y) (π : T' ⟶ T)
    (pX : S₁ ⟶ X) (pY : S₀ ⟶ Y) (pX' : S₃ ⟶ X) (pY' : S₂ ⟶ Y)
    (rX : S₁ ⟶ T) (rY : S₀ ⟶ T) (rX' : S₃ ⟶ T') (rY' : S₂ ⟶ T')
    (sq : CommSq w h' h v) (sqf : CommSq pX h f pY) (sqf' : CommSq pX' h' f pY')
    (sqπ : CommSq rY' v π rY) (sqπ' : CommSq rX' w π rX)
    (hpX : pX' = w ≫ pX) (hpY : pY' = v ≫ pY)
    (hrX : rX' = h' ≫ rY') (hrY : rX = h ≫ rY)
    (M : DerivedCategoryModule Λ X) (E : DerivedCategoryModule Λ T')
    (d₀ : R((w)_*[ModuleCat.{u + 1} Λ]) ⋙ R((h)_*[ModuleCat.{u + 1} Λ]) ⟶
      R((h')_*[ModuleCat.{u + 1} Λ]) ⋙ R((v)_*[ModuleCat.{u + 1} Λ]))
    (hd₀ : d₀ = conjugateEquiv
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) w))
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h'))
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom)
    (x : L((pY)^*[ModuleCat.{u + 1} Λ]).obj
          (R((f)_*[ModuleCat.{u + 1} Λ]).obj M) ⊗
        L((rY)^*[ModuleCat.{u + 1} Λ]).obj (R((π)_*[ModuleCat.{u + 1} Λ]).obj E) ⟶
      R((h)_*[ModuleCat.{u + 1} Λ]).obj
        (L((pX)^*[ModuleCat.{u + 1} Λ]).obj M ⊗
          L((rX)^*[ModuleCat.{u + 1} Λ]).obj (R((π)_*[ModuleCat.{u + 1} Λ]).obj E)))
    (y : L((pX)^*[ModuleCat.{u + 1} Λ]).obj M ⊗
        L((rX)^*[ModuleCat.{u + 1} Λ]).obj (R((π)_*[ModuleCat.{u + 1} Λ]).obj E) ⟶
      R((w)_*[ModuleCat.{u + 1} Λ]).obj
        (L((pX')^*[ModuleCat.{u + 1} Λ]).obj M ⊗
          L((rX')^*[ModuleCat.{u + 1} Λ]).obj E))
    (z : L((pY)^*[ModuleCat.{u + 1} Λ]).obj
          (R((f)_*[ModuleCat.{u + 1} Λ]).obj M) ⊗
        L((rY)^*[ModuleCat.{u + 1} Λ]).obj (R((π)_*[ModuleCat.{u + 1} Λ]).obj E) ⟶
      R((v)_*[ModuleCat.{u + 1} Λ]).obj
        (L((pY')^*[ModuleCat.{u + 1} Λ]).obj
            (R((f)_*[ModuleCat.{u + 1} Λ]).obj M) ⊗
          L((rY')^*[ModuleCat.{u + 1} Λ]).obj E))
    (t : L((pY')^*[ModuleCat.{u + 1} Λ]).obj
          (R((f)_*[ModuleCat.{u + 1} Λ]).obj M) ⊗
        L((rY')^*[ModuleCat.{u + 1} Λ]).obj E ⟶
      R((h')_*[ModuleCat.{u + 1} Λ]).obj
        (L((pX')^*[ModuleCat.{u + 1} Λ]).obj M ⊗
          L((rX')^*[ModuleCat.{u + 1} Λ]).obj E))
    (hx : ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).homEquiv
      _ _).symm x =
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) h).app _).app _ ≫
        (((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sqf).hom.app
            (R((f)_*[ModuleCat.{u + 1} Λ]).obj M) ≫
          L((pX)^*[ModuleCat.{u + 1} Λ]).map
            ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app M)) ⊗ₘ
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) h rY rX hrY).inv.app
            (R((π)_*[ModuleCat.{u + 1} Λ]).obj E)))
    (hy : ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) w).homEquiv
      _ _).symm y =
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) w).app _).app _ ≫
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) w pX pX' hpX).inv.app M ⊗ₘ
          ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sqπ').hom.app
              (R((π)_*[ModuleCat.{u + 1} Λ]).obj E) ≫
            L((rX')^*[ModuleCat.{u + 1} Λ]).map
              ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).counit.app E))))
    (hz : ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).homEquiv
      _ _).symm z =
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) v).app _).app _ ≫
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) v pY pY' hpY).inv.app
            (R((f)_*[ModuleCat.{u + 1} Λ]).obj M) ⊗ₘ
          ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sqπ).hom.app
              (R((π)_*[ModuleCat.{u + 1} Λ]).obj E) ≫
            L((rY')^*[ModuleCat.{u + 1} Λ]).map
              ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).counit.app E))))
    (ht : ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h').homEquiv
      _ _).symm t =
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) h').app _).app _ ≫
        (((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sqf').hom.app
            (R((f)_*[ModuleCat.{u + 1} Λ]).obj M) ≫
          L((pX')^*[ModuleCat.{u + 1} Λ]).map
            ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app M)) ⊗ₘ
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) h' rY' rX' hrX).inv.app E)) :
    x ≫ R((h)_*[ModuleCat.{u + 1} Λ]).map y ≫ d₀.app _ =
      z ≫ R((v)_*[ModuleCat.{u + 1} Λ]).map t := by
  let q := derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq
  have hA := factor_counit_coherence Λ w h h' v pX pY pX' pY' f
    sq sqf sqf' hpX hpY M
  have hB := factor_counit_coherence_op Λ w h h' v rY' rY rX' rX π
    sq sqπ sqπ' hrX hrY E
  exact derived_tensor_mate_square Λ
    (S₀ := S₀)
    (S₁ := S₁)
    (S₂ := S₂)
    (S₃ := S₃)
    (A₀ := L((pY)^*[ModuleCat.{u + 1} Λ]).obj
      (R((f)_*[ModuleCat.{u + 1} Λ]).obj M))
    (B₀ := L((rY)^*[ModuleCat.{u + 1} Λ]).obj
      (R((π)_*[ModuleCat.{u + 1} Λ]).obj E))
    (A₁ := L((pX)^*[ModuleCat.{u + 1} Λ]).obj M)
    (B₁ := L((rX)^*[ModuleCat.{u + 1} Λ]).obj
      (R((π)_*[ModuleCat.{u + 1} Λ]).obj E))
    (A₂ := L((pY')^*[ModuleCat.{u + 1} Λ]).obj
      (R((f)_*[ModuleCat.{u + 1} Λ]).obj M))
    (B₂ := L((rY')^*[ModuleCat.{u + 1} Λ]).obj E)
    (A₃ := L((pX')^*[ModuleCat.{u + 1} Λ]).obj M)
    (B₃ := L((rX')^*[ModuleCat.{u + 1} Λ]).obj E)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) w)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h') q.hom
    d₀ hd₀
    (fun A B ↦ ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) h).app A).app B)
    (fun A B ↦ ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) w).app A).app B)
    (fun A B ↦ ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) v).app A).app B)
    (fun A B ↦ ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) h').app A).app B)
    (fun a b ↦ (leftDerivedUpperStarTensorComparison_naturality
      (ModuleCat.{u + 1} Λ) w a b).symm)
    (fun a b ↦ (leftDerivedUpperStarTensorComparison_naturality
      (ModuleCat.{u + 1} Λ) h' a b).symm)
    (derivedSquareUpperStarIso_hom_tensor (ModuleCat.{u + 1} Λ) sq)
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sqf).hom.app
        (R((f)_*[ModuleCat.{u + 1} Λ]).obj M) ≫
      L((pX)^*[ModuleCat.{u + 1} Λ]).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app M))
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) h rY rX hrY).inv.app
      (R((π)_*[ModuleCat.{u + 1} Λ]).obj E))
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) w pX pX' hpX).inv.app M)
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sqπ').hom.app
        (R((π)_*[ModuleCat.{u + 1} Λ]).obj E) ≫
      L((rX')^*[ModuleCat.{u + 1} Λ]).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).counit.app E))
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) v pY pY' hpY).inv.app
      (R((f)_*[ModuleCat.{u + 1} Λ]).obj M))
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sqπ).hom.app
        (R((π)_*[ModuleCat.{u + 1} Λ]).obj E) ≫
      L((rY')^*[ModuleCat.{u + 1} Λ]).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).counit.app E))
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sqf').hom.app
        (R((f)_*[ModuleCat.{u + 1} Λ]).obj M) ≫
      L((pX')^*[ModuleCat.{u + 1} Λ]).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app M))
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) h' rY' rX' hrX).inv.app E)
    hA hB
    x y z t hx hy hz ht
private noncomputable def comparisonArrow {W A S S' : Scheme.{u}}
    (v : W ⟶ A) (r' : W ⟶ S') (r : A ⟶ S) (π : S' ⟶ S)
    (sq : CommSq r' v π r) (P : DerivedCategoryModule Λ A)
    (P' : DerivedCategoryModule Λ W) (E : DerivedCategoryModule Λ S')
    (ψ : L((v)^*[ModuleCat.{u + 1} Λ]).obj P ⟶ P') :=
  (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) v r' r π sq.w.symm P E ≫
        R((v)_*[ModuleCat.{u + 1} Λ]).map
          (((derivedTensor (ModuleCat.{u + 1} Λ) W).map ψ).app
            (L((r')^*[ModuleCat.{u + 1} Λ]).obj E)))

private noncomputable def externalArrow {W A X Y S : Scheme.{u}}
    (h : W ⟶ A) (p : A ⟶ Y) (p' : W ⟶ X) (f : X ⟶ Y)
    (r : A ⟶ S) (r' : W ⟶ S) (sq : CommSq p' h f p) (hr : r' = h ≫ r)
    (M : DerivedCategoryModule Λ X) (Q : DerivedCategoryModule Λ S) :=
  (((derivedTensorBraiding (ModuleCat.{u + 1} Λ) A).hom.app
          (L((p)^*[ModuleCat.{u + 1} Λ]).obj (R((f)_*[ModuleCat.{u + 1} Λ]).obj M))).app
            (L((r)^*[ModuleCat.{u + 1} Λ]).obj Q) ≫
        tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h p' p f sq.w.symm
          (L((r)^*[ModuleCat.{u + 1} Λ]).obj Q) M ≫
        R((h)_*[ModuleCat.{u + 1} Λ]).map
          (((derivedTensor (ModuleCat.{u + 1} Λ) W).map
            ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) h r r' hr).inv.app Q)).app
              (L((p')^*[ModuleCat.{u + 1} Λ]).obj M) ≫
            ((derivedTensorBraiding (ModuleCat.{u + 1} Λ) W).hom.app
              (L((r')^*[ModuleCat.{u + 1} Λ]).obj Q)).app
                (L((p')^*[ModuleCat.{u + 1} Λ]).obj M)))

private theorem canonical_rectangle
    {S₀ S₁ S₂ S₃ : Scheme.{u}}
    (h : S₁ ⟶ S₀) (w : S₃ ⟶ S₁) (v : S₂ ⟶ S₀) (h' : S₃ ⟶ S₂)
    (f : X ⟶ Y) (π : T' ⟶ T)
    (pX : S₁ ⟶ X) (pY : S₀ ⟶ Y) (pX' : S₃ ⟶ X) (pY' : S₂ ⟶ Y)
    (rX : S₁ ⟶ T) (rY : S₀ ⟶ T) (rX' : S₃ ⟶ T') (rY' : S₂ ⟶ T')
    (sq : CommSq w h' h v) (sqf : CommSq pX h f pY) (sqf' : CommSq pX' h' f pY')
    (sqπ : CommSq rY' v π rY) (sqπ' : CommSq rX' w π rX)
    (hpX : pX' = w ≫ pX) (hpY : pY' = v ≫ pY)
    (hrX : rX' = h' ≫ rY') (hrY : rX = h ≫ rY)
    (M : DerivedCategoryModule Λ X) (E : DerivedCategoryModule Λ T')
    (d₀ : R((w)_*[ModuleCat.{u + 1} Λ]) ⋙ R((h)_*[ModuleCat.{u + 1} Λ]) ⟶
      R((h')_*[ModuleCat.{u + 1} Λ]) ⋙ R((v)_*[ModuleCat.{u + 1} Λ]))
    (hd₀ : d₀ = conjugateEquiv
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) w))
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h'))
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom)
 :
    externalArrow Λ h pY pX f rY rX sqf hrY M (R((π)_*[ModuleCat.{u + 1} Λ]).obj E) ≫
      R((h)_*[ModuleCat.{u + 1} Λ]).map (comparisonArrow Λ w rX' rX π sqπ'
        (L((pX)^*[ModuleCat.{u + 1} Λ]).obj M)
        (L((pX')^*[ModuleCat.{u + 1} Λ]).obj M) E
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) w pX pX' hpX).inv.app M)) ≫ d₀.app _ =
    comparisonArrow Λ v rY' rY π sqπ
        (L((pY)^*[ModuleCat.{u + 1} Λ]).obj
          (R((f)_*[ModuleCat.{u + 1} Λ]).obj M))
        (L((pY')^*[ModuleCat.{u + 1} Λ]).obj
          (R((f)_*[ModuleCat.{u + 1} Λ]).obj M)) E
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) v pY pY' hpY).inv.app
          (R((f)_*[ModuleCat.{u + 1} Λ]).obj M)) ≫
      R((v)_*[ModuleCat.{u + 1} Λ]).map (externalArrow Λ h' pY' pX' f rY' rX' sqf' hrX M E) := by
  exact rectangle_counit Λ h w v h' f π pX pY pX' pY' rX rY rX' rY'
    sq sqf sqf' sqπ sqπ' hpX hpY hrX hrY M E d₀ hd₀
    (externalArrow Λ h pY pX f rY rX sqf hrY M (R((π)_*[ModuleCat.{u + 1} Λ]).obj E))
    (comparisonArrow Λ w rX' rX π sqπ'
        (L((pX)^*[ModuleCat.{u + 1} Λ]).obj M)
        (L((pX')^*[ModuleCat.{u + 1} Λ]).obj M) E
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) w pX pX' hpX).inv.app M))
    (comparisonArrow Λ v rY' rY π sqπ
        (L((pY)^*[ModuleCat.{u + 1} Λ]).obj
          (R((f)_*[ModuleCat.{u + 1} Λ]).obj M))
        (L((pY')^*[ModuleCat.{u + 1} Λ]).obj
          (R((f)_*[ModuleCat.{u + 1} Λ]).obj M)) E
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) v pY pY' hpY).inv.app
          (R((f)_*[ModuleCat.{u + 1} Λ]).obj M)))
    (externalArrow Λ h' pY' pX' f rY' rX' sqf' hrX M E)
    (external_transpose_general Λ h pY pX f rY rX sqf hrY M
      (R((π)_*[ModuleCat.{u + 1} Λ]).obj E))
    (comparison_transpose_general Λ w rX' rX π sqπ'
      (L((pX)^*[ModuleCat.{u + 1} Λ]).obj M)
      (L((pX')^*[ModuleCat.{u + 1} Λ]).obj M) E
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) w pX pX' hpX).inv.app M))
    (comparison_transpose_general Λ v rY' rY π sqπ
      (L((pY)^*[ModuleCat.{u + 1} Λ]).obj
        (R((f)_*[ModuleCat.{u + 1} Λ]).obj M))
      (L((pY')^*[ModuleCat.{u + 1} Λ]).obj
        (R((f)_*[ModuleCat.{u + 1} Λ]).obj M)) E
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) v pY pY' hpY).inv.app
        (R((f)_*[ModuleCat.{u + 1} Λ]).obj M)))
    (external_transpose_general Λ h' pY' pX' f rY' rX' sqf' hrX M E)
private theorem counit_all (b : Y ⟶ B) (c : T ⟶ B) (f : X ⟶ Y) (π : T' ⟶ T)
    (M : DerivedCategoryModule Λ X) (E : DerivedCategoryModule Λ T') :
    externalProductRightDerivedLowerStarMap (ModuleCat.{u + 1} Λ) b c f M
        (R((π)_*[ModuleCat.{u + 1} Λ]).obj E) ≫
      outputComparison Λ b c f π M E =
    comparison Λ b c π (R((f)_*[ModuleCat.{u + 1} Λ]).obj M) E ≫
      R((productMap b c π)_*[ModuleCat.{u + 1} Λ]).map
        (externalProductRightDerivedLowerStarMap (ModuleCat.{u + 1} Λ) b (π ≫ c) f M E) := by
  let h := pullback.mapOverBaseRight f b c
  let w := productMap (f ≫ b) c π
  let v := productMap b c π
  let h' := pullback.mapOverBaseRight f b (π ≫ c)
  let sq : CommSq w h' h v := ⟨by
    apply pullback.hom_ext <;> simp [w, h', h, v, productMap, pullback.map]⟩
  let pX := pullback.fst (f ≫ b) c
  let pY := pullback.fst b c
  let pX' := pullback.fst (f ≫ b) (π ≫ c)
  let pY' := pullback.fst b (π ≫ c)
  let rX := pullback.snd (f ≫ b) c
  let rY := pullback.snd b c
  let rX' := pullback.snd (f ≫ b) (π ≫ c)
  let rY' := pullback.snd b (π ≫ c)
  let sqf : CommSq pX h f pY := (isPullback_mapOverBaseRight_fst b c f).toCommSq.flip
  let sqf' : CommSq pX' h' f pY' :=
    (isPullback_mapOverBaseRight_fst b (π ≫ c) f).toCommSq.flip
  let sqπ : CommSq rY' v π rY := ⟨by simp [rY', v, rY, productMap, pullback.map]⟩
  let sqπ' : CommSq rX' w π rX := ⟨by simp [rX', w, rX, productMap, pullback.map]⟩
  have hpX : pX' = w ≫ pX := by simp [pX', w, pX, productMap, pullback.map]
  have hpY : pY' = v ≫ pY := by simp [pY', v, pY, productMap, pullback.map]
  have hrX : rX' = h' ≫ rY' := by simp [rX', h', rY']
  have hrY : rX = h ≫ rY := by simp [rX, h, rY]
  exact canonical_rectangle Λ h w v h' f π pX pY pX' pY' rX rY rX' rY'
    sq sqf sqf' sqπ sqπ' hpX hpY hrX hrY M E
    (composition Λ b c f π).hom (composition_conjugate Λ b c f π)


end

/-- For a finite-dimensional constant coefficient, comparison and outputComparison
satisfy the counit square with the two external-product direct-image maps.
Source: blueprint, sk-lem-sf-kunneth-star.proof.md, Field coefficients and sheaves,
the counit calculation; Stacks Tags 0959, 0F0G and 0D6E
(blueprint: lem-sf-finite-cover-tensor-counit-comparison-counit).

Proof: the transpose of finite exchange is the pulled-back π-counit, and the projection
map is adjoint to the tensor of that counit with the identity; so the transposes of
comparison along v and w are 1 ⊗ e_v and 1 ⊗ e_w (inverse-image monoidality). Transpose
both sides of the equation along the composite adjunctions of h ∘ w = v ∘ h', normalized
by the composition comparison. The left side becomes w^*(p_X^*ε_f ⊗ 1) followed by
1 ⊗ e_w, the right side 1 ⊗ h'^*e_v followed by p_X'^*ε_f. Since r_Y v h' = π r'_X =
r_X w, both equal p_X'^*ε_f ⊗ r_X'^*ε_π by bifunctoriality of the tensor product, and
transposition is bijective. No invertibility is used. -/
theorem finiteCoverTensorCounitComparison_constantModule_counit
    (k : Type u) [Field k] (L : Type (u + 1)) [Field L] [Finite L]
    (hL : IsUnit (ringChar L : k))
    {X Y T T' : Scheme.{u}} (b : Y ⟶ Spec (.of k)) (c : T ⟶ Spec (.of k))
    (f : X ⟶ Y) (π : T' ⟶ T) [IsFinite π]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsSeparated (f ≫ b)] [LocallyOfFiniteType (f ≫ b)] [QuasiCompact (f ≫ b)]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    [IsSeparated (π ≫ c)] [LocallyOfFiniteType (π ≫ c)] [QuasiCompact (π ≫ c)]
    (V : ModuleCat.{u + 1} L) [Module.Finite L V] :
    ∀ E : DerivedCategoryModule L T',
      E = (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf T'.smallEtaleTopology (ModuleCat.{u + 1} L)).obj V) →
    ∀ M : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} L)),
      externalProductRightDerivedLowerStarMap (ModuleCat.{u + 1} L) b c f M.obj
          (R((π)_*[ModuleCat.{u + 1} L]).obj E) ≫
        outputComparison L b c f π M.obj E =
      comparison L b c π (R((f)_*[ModuleCat.{u + 1} L]).obj M.obj) E ≫
        R((productMap b c π)_*[ModuleCat.{u + 1} L]).map
          (externalProductRightDerivedLowerStarMap (ModuleCat.{u + 1} L)
            b (π ≫ c) f M.obj E) := by
  have _ := hL
  intro E _ M
  exact counit_all L b c f π M.obj E

/-- The same canonical finite comparisons for a finite-dimensional constant module.
Naturality in M is encoded by the two natural isomorphisms, and the hom equations
pin them to comparison and outputComparison. The equality is the double-adjunction
counit calculation with V in place of L.
Source: blueprint, final sentence of Field coefficients and sheaves
(blueprint: lem-sf-finite-cover-tensor-counit-comparison).

Proof: the canonical comparison data (finiteCoverTensorCounitComparison_constantModule_data,
finite exchange, the proper projection formula and the composition comparison) gives a
and d with the prescribed components; rewriting by these component equations, the counit
equation is finiteCoverTensorCounitComparison_constantModule_counit. The
unit-coefficient result finiteCoverTensorCounitComparison below is derived from this
one, so it must not be used here. -/
theorem finiteCoverTensorCounitComparison_constantModule
    (k : Type u) [Field k] (L : Type (u + 1)) [Field L] [Finite L]
    (hL : IsUnit (ringChar L : k))
    {X Y T T' : Scheme.{u}} (b : Y ⟶ Spec (.of k)) (c : T ⟶ Spec (.of k))
    (f : X ⟶ Y) (π : T' ⟶ T) [IsFinite π]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsSeparated (f ≫ b)] [LocallyOfFiniteType (f ≫ b)] [QuasiCompact (f ≫ b)]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    [IsSeparated (π ≫ c)] [LocallyOfFiniteType (π ≫ c)] [QuasiCompact (π ≫ c)]
    (V : ModuleCat.{u + 1} L) [Module.Finite L V] :
    ∀ E : DerivedCategoryModule L T',
      E = (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf T'.smallEtaleTopology (ModuleCat.{u + 1} L)).obj V) →
    ∃ (a : _root_.DerivedCategory.Plus.ι ⋙ R((f)_*[ModuleCat.{u + 1} L]) ⋙
          source L b c π E ≅
        _root_.DerivedCategory.Plus.ι ⋙ R((f)_*[ModuleCat.{u + 1} L]) ⋙ target L b c π E)
      (d : _root_.DerivedCategory.Plus.ι ⋙ source L (f ≫ b) c π E ⋙
          R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} L]) ≅
        _root_.DerivedCategory.Plus.ι ⋙
          L((pullback.fst (f ≫ b) (π ≫ c))^*[ModuleCat.{u + 1} L]) ⋙
          derivedTensorRight (ModuleCat.{u + 1} L) _
            (L((pullback.snd (f ≫ b) (π ≫ c))^*[ModuleCat.{u + 1} L]).obj E) ⋙
          R((pullback.mapOverBaseRight f b (π ≫ c))_*[ModuleCat.{u + 1} L]) ⋙
          R((productMap b c π)_*[ModuleCat.{u + 1} L])),
      ∀ M : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} L)),
        a.hom.app M = comparison L b c π (R((f)_*[ModuleCat.{u + 1} L]).obj M.obj) E ∧
        d.hom.app M = outputComparison L b c f π M.obj E ∧
        externalProductRightDerivedLowerStarMap (ModuleCat.{u + 1} L) b c f M.obj
            (R((π)_*[ModuleCat.{u + 1} L]).obj E) ≫ d.hom.app M =
          a.hom.app M ≫ R((productMap b c π)_*[ModuleCat.{u + 1} L]).map
            (externalProductRightDerivedLowerStarMap (ModuleCat.{u + 1} L)
              b (π ≫ c) f M.obj E) := by
  intro E hE
  obtain ⟨a, d, had⟩ := finiteCoverTensorCounitComparison_constantModule_data
    k L hL b c f π V E hE
  have hc := finiteCoverTensorCounitComparison_constantModule_counit
    k L hL b c f π V E hE
  refine ⟨a, d, ?_⟩
  intro M
  refine ⟨(had M).1, (had M).2, ?_⟩
  rw [(had M).1, (had M).2]
  exact hc M

section UnitNormalization

universe v
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]

attribute [local instance] _root_.DerivedCategory.braidedCategory'

private noncomputable def externalUnitIso (b : Y ⟶ B) (c : T ⟶ B) :
    L((pullback.fst b c)^*[A]) ⋙
        derivedTensorRight A _
          (L((pullback.snd b c)^*[A]).obj (𝟙_ _)) ≅
      L((pullback.fst b c)^*[A]) :=
  NatIso.ofComponents (fun N ↦
    ((derivedTensor A _).obj _).mapIso
      (leftDerivedUpperStarUnitIso A (pullback.snd b c)) ≪≫
        derivedTensorRightUnitor A _ _) (fun {N N'} φ ↦ by
    dsimp only [Iso.trans_hom, Functor.mapIso_hom, derivedTensorRight,
      Functor.flip_obj_map, Functor.comp_map]
    rw [Category.assoc, ← NatTrans.naturality_assoc]
    simp only [derivedTensor, curriedTensor_map_app, curriedTensor_obj_map,
      derivedTensorRightUnitor]
    rw [rightUnitor_naturality])
omit [UpperStarPreservesFlat A] in
private theorem externalUnitIso_hom_app (b : Y ⟶ B) (c : T ⟶ B)
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (externalUnitIso A b c).hom.app N =
      ((derivedTensor A _).obj _).map
          (leftDerivedUpperStarUnitIso A (pullback.snd b c)).hom ≫
        (derivedTensorRightUnitor A _ _).hom := rfl

-- Use the component lemma instead of expanding the natural-isomorphism construction.
attribute [local irreducible] externalUnitIso

private theorem tensor_unit_calculus
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    (H : D ⥤ C) (K : C) (K' : D) {E : C} {Q J E' : D}
    (e : E ⟶ 𝟙_ C) (e' : E' ⟶ 𝟙_ D) (s : Q ⟶ E') (u : Q ⟶ J) (η : J ⟶ 𝟙_ D)
    (t : E ⊗ K ⟶ H.obj (Q ⊗ K')) (t₁ : (𝟙_ C) ⊗ K ⟶ H.obj (J ⊗ K'))
    (ψ : K ⟶ H.obj K') (hs : s ≫ e' = u ≫ η)
    (hn : e ▷ K ≫ t₁ = t ≫ H.map (u ▷ K'))
    (ht : t₁ ≫ H.map (η ▷ K' ≫ (λ_ K').hom) = (λ_ K).hom ≫ ψ) :
    (β_ K E).hom ≫ t ≫ H.map (s ▷ K' ≫ (β_ E' K').hom) ≫
        H.map (K' ◁ e' ≫ (ρ_ K').hom) =
      K ◁ e ≫ (ρ_ K).hom ≫ ψ := by
  simp only [← Functor.map_comp, Category.assoc]
  rw [← braiding_naturality_left_assoc, braiding_rightUnitor,
    ← comp_whiskerRight_assoc, hs, comp_whiskerRight]
  simp only [Functor.map_comp, Category.assoc] at ht ⊢
  rw [← reassoc_of% hn, ht, ← braiding_naturality_right_assoc, braiding_leftUnitor_assoc]

omit [UpperStarPreservesFlat A] in
private theorem derived_tensor_unit_calculus {S S' : Scheme.{u}}
    (H : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf S.smallEtaleTopology A))
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A))
    (K' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A))
    {E : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)}
    {Q J E' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A)}
    (e : E ⟶ (𝟙_ _)) (e' : E' ⟶ (𝟙_ _))
    (s : Q ⟶ E') (v : Q ⟶ J) (η : J ⟶ (𝟙_ _))
    (t : ((derivedTensor A S).obj E).obj K ⟶
      H.obj (((derivedTensor A S').obj Q).obj K'))
    (t₁ : ((derivedTensor A S).obj (𝟙_ _)).obj K ⟶
      H.obj (((derivedTensor A S').obj J).obj K'))
    (ψ : K ⟶ H.obj K') (hs : s ≫ e' = v ≫ η)
    (hn : ((derivedTensor A S).map e).app K ≫ t₁ =
      t ≫ H.map (((derivedTensor A S').map v).app K'))
    (ht : t₁ ≫ H.map (((derivedTensor A S').map η).app K' ≫
        (derivedTensorLeftUnitor A S' K').hom) =
      (derivedTensorLeftUnitor A S K).hom ≫ ψ) :
    ((derivedTensorBraiding A S).hom.app K).app E ≫ t ≫
        H.map (((derivedTensor A S').map s).app K' ≫
          ((derivedTensorBraiding A S').hom.app E').app K') ≫
        H.map (((derivedTensor A S').obj K').map e' ≫
          (derivedTensorRightUnitor A S' K').hom) =
      ((derivedTensor A S).obj K).map e ≫
        (derivedTensorRightUnitor A S K).hom ≫ ψ := by
  simp only [derivedTensor, curriedTensor_map_app, curriedTensor_obj_map,
    derivedTensorLeftUnitor, derivedTensorRightUnitor, derivedTensorBraiding,
    curriedBraidingNatIso_hom_app_app] at hn ht ⊢
  exact tensor_unit_calculus H K K' e e' s v η t t₁ ψ hs hn ht

private noncomputable def unitExchange (b : Y ⟶ B) (c : T ⟶ B) (f : X ⟶ Y) :
    R((f)_*[A]) ⋙ L((pullback.fst b c)^*[A]) ⟶
      L((pullback.fst (f ≫ b) c)^*[A]) ⋙ R((pullback.mapOverBaseRight f b c)_*[A]) :=
  derivedBaseChangeMap A ⟨by simp⟩

set_option maxHeartbeats 1600000 in
-- Checking the derived tensor coherence expands the pullback comparison terms.
private theorem external_unit (b : Y ⟶ B) (c : T ⟶ B) (f : X ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hcomp :
      (leftDerivedUpperStarComp A (pullback.mapOverBaseRight f b c)
          (pullback.snd b c) (pullback.snd (f ≫ b) c) (by simp)).inv.app (𝟙_ _) ≫
          (leftDerivedUpperStarUnitIso A (pullback.snd (f ≫ b) c)).hom =
        L((pullback.mapOverBaseRight f b c)^*[A]).map
            (leftDerivedUpperStarUnitIso A (pullback.snd b c)).hom ≫
          (leftDerivedUpperStarUnitIso A (pullback.mapOverBaseRight f b c)).hom) :
    externalProductRightDerivedLowerStarMap A b c f M
          (𝟙_ _) ≫
        R((pullback.mapOverBaseRight f b c)_*[A]).map
          ((externalUnitIso A (f ≫ b) c).hom.app M) =
      (externalUnitIso A b c).hom.app (R((f)_*[A]).obj M) ≫
        (unitExchange A b c f).app M := by
  let h := pullback.mapOverBaseRight f b c
  let p := pullback.fst b c
  let p' := pullback.fst (f ≫ b) c
  let q := pullback.snd b c
  let q' := pullback.snd (f ≫ b) c
  let H := R((h)_*[A])
  let U := L((h)^*[A])
  let e := leftDerivedUpperStarUnitIso A q
  let e' := leftDerivedUpperStarUnitIso A q'
  let s := leftDerivedUpperStarComp A h q q' (by simp [h, q, q'])
  let K := L((p)^*[A]).obj (R((f)_*[A]).obj M)
  let K' := L((p')^*[A]).obj M
  have hs : s.inv.app (𝟙_ _) ≫ e'.hom = U.map e.hom ≫
      (leftDerivedUpperStarUnitIso A h).hom := hcomp
  have hn := tensorBaseChangeMap_naturality A h p' p f
    (isPullback_mapOverBaseRight_fst b c f).w e.hom (𝟙 M)
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at hn
  have ht := tensorBaseChangeMap_tensorUnit A h p' p f
    (isPullback_mapOverBaseRight_fst b c f).w M
  simp only [externalUnitIso_hom_app]
  simp only [externalProductRightDerivedLowerStarMap, Category.assoc]
  exact derived_tensor_unit_calculus A H K K' e.hom e'.hom (s.inv.app (𝟙_ _))
    (U.map e.hom) (leftDerivedUpperStarUnitIso A h).hom
    (tensorBaseChangeMap A h p' p f (isPullback_mapOverBaseRight_fst b c f).w _ M)
    (tensorBaseChangeMap A h p' p f (isPullback_mapOverBaseRight_fst b c f).w (𝟙_ _) M)
    ((unitExchange A b c f).app M) hs hn (by simpa only [Functor.comp_obj, unitExchange,
      derivedTensor, curriedTensor_map_app, derivedTensorLeftUnitor] using ht)


end UnitNormalization

attribute [local irreducible] externalUnitIso

private theorem comp_unit (h : X ⟶ Y) (q : Y ⟶ T) (q' : X ⟶ T)
    (w : q' = h ≫ q) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) h q q' w).inv.app (𝟙_ _) ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) q').hom =
      L((h)^*[ModuleCat.{u + 1} Λ]).map
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) q).hom ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) h).hom := by
  rw [leftDerivedUpperStarUnitIso_hom_eq_η,
    leftDerivedUpperStarUnitIso_hom_eq_η, leftDerivedUpperStarUnitIso_hom_eq_η,
    ← leftDerivedUpperStarComp_hom_app_unit (ModuleCat.{u + 1} Λ) h q q' w,
    Iso.inv_hom_id_app_assoc]

set_option maxHeartbeats 2000000 in
-- The natural isomorphisms contain derived tensor and pullback coherence terms.
/-- Finite direct image commutes with the external counit comparison, naturally in
bounded-below M. The two natural isomorphisms have their actual exchange/projection/
composition arrows as homs, and the last equation identifies the Künneth counit mate
with v_* of base change; it asserts no invertibility of that base-change map.

Source: blueprint, sk-lem-sf-kunneth-star.proof.md, Field coefficients and sheaves;
Stacks Tags 0959, 03QP, 0F0G and 0D6E
(blueprint: lem-sf-finite-cover-tensor-counit-comparison).

Proof:
1. The data theorem constructs the prescribed comparison isomorphisms using proper
   torsion base change and the proper projection formula for the finite product maps.
2. The counit theorem transposes the square along the composite adjunctions. The
   pullback square comparison is monoidal, and the prescribed direct-image
   compositor is its adjunction conjugate. The two tensor factors agree by
   pullback-compositor coherence and naturality of the f- and π-counits.
3. Specialize the finite-dimensional statement to the coefficient unit. Normalize
   its external tensors by the canonical pullback-unit isomorphisms. The unit
   compatibility of the pullback compositor identifies the exchange maps.
4. Finite sums follow by distributivity of inverse image, tensor and direct image
   over finite biproducts; the equations are checked on biproduct projections.
   The zero module and empty sum are included. -/
theorem finiteCoverTensorCounitComparison
    (k : Type u) [Field k] (L : Type (u + 1)) [Field L] [Finite L]
    (hL : IsUnit (ringChar L : k))
    {X Y T T' : Scheme.{u}} (b : Y ⟶ Spec (.of k)) (c : T ⟶ Spec (.of k))
    (f : X ⟶ Y) (π : T' ⟶ T) [IsFinite π]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsSeparated (f ≫ b)] [LocallyOfFiniteType (f ≫ b)] [QuasiCompact (f ≫ b)]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    [IsSeparated (π ≫ c)] [LocallyOfFiniteType (π ≫ c)] [QuasiCompact (π ≫ c)] :
    PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} L) π) ∧
    PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} L) (productMap b c π)) ∧
    PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} L) (productMap (f ≫ b) c π)) ∧
    ∃ (a : _root_.DerivedCategory.Plus.ι ⋙ R((f)_*[ModuleCat.{u + 1} L]) ⋙
          source L b c π (constantComplex L T') ≅
        _root_.DerivedCategory.Plus.ι ⋙ R((f)_*[ModuleCat.{u + 1} L]) ⋙
          unitTarget L b c π)
      (d : _root_.DerivedCategory.Plus.ι ⋙ source L (f ≫ b) c π (constantComplex L T') ⋙
          R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} L]) ≅
        _root_.DerivedCategory.Plus.ι ⋙
          L((pullback.fst (f ≫ b) (π ≫ c))^*[ModuleCat.{u + 1} L]) ⋙
          R((pullback.mapOverBaseRight f b (π ≫ c))_*[ModuleCat.{u + 1} L]) ⋙
          R((productMap b c π)_*[ModuleCat.{u + 1} L])),
      ∀ M : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} L)),
        a.hom.app M = unitComparison L b c π (R((f)_*[ModuleCat.{u + 1} L]).obj M.obj) ∧
        d.hom.app M = unitOutputComparison L b c f π M.obj ∧
        externalProductRightDerivedLowerStarMap (ModuleCat.{u + 1} L) b c f M.obj
            (R((π)_*[ModuleCat.{u + 1} L]).obj (constantComplex L T')) ≫ d.hom.app M =
          a.hom.app M ≫ R((productMap b c π)_*[ModuleCat.{u + 1} L]).map
            ((exchange L b (π ≫ c) f).app M.obj) := by
  classical
  have hp (Z : Scheme.{u}) (z : Z ⟶ Spec (.of k)) :
      IsPullback (productMap z c π) (pullback.snd z (π ≫ c)) (pullback.snd z c) π := by
    refine .of_right (h₁₂ := pullback.fst z c) (h₂₂ := c) (v₁₃ := z) ?_ ?_
      (IsPullback.of_hasPullback z c)
    · simpa [productMap, pullback.map] using (IsPullback.of_hasPullback z (π ≫ c))
    · simp [productMap, pullback.map]
  have : IsFinite (productMap b c π) :=
    MorphismProperty.of_isPullback (P := @IsFinite) (hp Y b).flip inferInstance
  have : IsFinite (productMap (f ≫ b) c π) :=
    MorphismProperty.of_isPullback (P := @IsFinite) (hp X (f ≫ b)).flip inferInstance
  -- Specialize the finite-dimensional statement to the coefficient unit.
  obtain ⟨a, d, had⟩ := finiteCoverTensorCounitComparison_constantModule k L hL b c f π
    (ModuleCat.of L L) (constantComplex L T') (by rfl)
  let H := R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} L])
  let H' := R((pullback.mapOverBaseRight f b (π ≫ c))_*[ModuleCat.{u + 1} L])
  let V := R((productMap b c π)_*[ModuleCat.{u + 1} L])
  -- Normalize both external products using pullback of the tensor unit.
  let eY := externalUnitIso (ModuleCat.{u + 1} L) b (π ≫ c)
  let eX := externalUnitIso (ModuleCat.{u + 1} L) (f ≫ b) (π ≫ c)
  let a' := a ≪≫ Functor.isoWhiskerLeft (_root_.DerivedCategory.Plus.ι ⋙
    R((f)_*[ModuleCat.{u + 1} L])) (Functor.isoWhiskerRight eY V)
  let d' := d ≪≫ Functor.isoWhiskerLeft _root_.DerivedCategory.Plus.ι
    (Functor.isoWhiskerRight eX (H' ⋙ V))
  refine ⟨inferInstance, inferInstance, inferInstance, a', d', ?_⟩
  intro M
  have ha : a'.hom.app M =
      unitComparison L b c π (R((f)_*[ModuleCat.{u + 1} L]).obj M.obj) := by
    change a.hom.app M ≫ V.map (eY.hom.app _) = _
    rw [(had M).1]
    dsimp only [eY]
    rw [externalUnitIso_hom_app]
    rfl
  have hd : d'.hom.app M = unitOutputComparison L b c f π M.obj := by
    change d.hom.app M ≫ V.map (H'.map (eX.hom.app M.obj)) = _
    rw [(had M).2.1]
    have hn := (composition L b c f π).hom.naturality (eX.hom.app M.obj)
    simpa only [outputComparison, unitOutputComparison, unitComparison, eX,
      externalUnitIso_hom_app, H, H', V, constantComplex, Functor.comp_obj,
      Functor.comp_map, Functor.map_comp, Category.assoc] using
      congrArg (fun φ ↦ H.map
        (comparison L (f ≫ b) c π M.obj (constantComplex L T')) ≫ φ) hn.symm
  refine ⟨ha, hd, ?_⟩
  change _ ≫ (d.hom.app M ≫ V.map (H'.map (eX.hom.app M.obj))) =
    (a.hom.app M ≫ V.map (eY.hom.app _)) ≫ V.map _
  rw [← Category.assoc, (had M).2.2, Category.assoc, ← V.map_comp]
  dsimp only [constantComplex, eX, eY, H']
  rw [external_unit (ModuleCat.{u + 1} L) b (π ≫ c) f M.obj
      (comp_unit L _ _ _ (by simp)), V.map_comp]
  simp only [Category.assoc]
  rfl

/-- External tensor with a finite sum of finite direct images.
Source: blueprint, final sentence of Field coefficients and sheaves
(blueprint: lem-sf-finite-cover-tensor-counit-comparison). -/
noncomputable def sumSource (b : Y ⟶ B) (c : T ⟶ B) (n : ℕ)
    {T' : Fin n → Scheme.{u}} (π : ∀ i, T' i ⟶ T)
    (E : ∀ i, DerivedCategoryModule Λ (T' i)) :
    DerivedCategoryModule Λ Y ⥤ DerivedCategoryModule Λ (pullback b c) :=
  L((pullback.fst b c)^*[ModuleCat.{u + 1} Λ]) ⋙
    derivedTensorRight (ModuleCat.{u + 1} Λ) _
      (L((pullback.snd b c)^*[ModuleCat.{u + 1} Λ]).obj
        (⨁ fun i ↦ R((π i)_*[ModuleCat.{u + 1} Λ]).obj (E i)))

/-- The direct sum of finite comparisons, preceded by canonical tensor distributivity.
Source: blueprint, finite sums in Field coefficients and sheaves
(blueprint: lem-sf-finite-cover-tensor-counit-comparison). -/
noncomputable def sumComparison (b : Y ⟶ B) (c : T ⟶ B) (n : ℕ)
    {T' : Fin n → Scheme.{u}} (π : ∀ i, T' i ⟶ T)
    (E : ∀ i, DerivedCategoryModule Λ (T' i)) (N : DerivedCategoryModule Λ Y) :
    (sumSource Λ b c n π E).obj N ⟶ ⨁ fun i ↦ (target Λ b c (π i) (E i)).obj N :=
  ((L((pullback.snd b c)^*[ModuleCat.{u + 1} Λ]) ⋙
      (derivedTensor (ModuleCat.{u + 1} Λ) _).obj
        (L((pullback.fst b c)^*[ModuleCat.{u + 1} Λ]).obj N)).mapBiproduct
          (fun i ↦ R((π i)_*[ModuleCat.{u + 1} Λ]).obj (E i))).hom ≫
    biproduct.map (fun i ↦ comparison Λ b c (π i) N (E i))

/-- The second comparison for a finite sum, including pushforward distributivity.
Source: blueprint, finite sums and composition hw = vh'
(blueprint: lem-sf-finite-cover-tensor-counit-comparison). -/
noncomputable def sumOutputComparison
    (b : Y ⟶ B) (c : T ⟶ B) (f : X ⟶ Y) (n : ℕ)
    {T' : Fin n → Scheme.{u}} (π : ∀ i, T' i ⟶ T)
    (E : ∀ i, DerivedCategoryModule Λ (T' i)) (M : DerivedCategoryModule Λ X) :
    R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} Λ]).obj
        ((sumSource Λ (f ≫ b) c n π E).obj M) ⟶
      ⨁ fun i ↦ R((productMap b c (π i))_*[ModuleCat.{u + 1} Λ]).obj
        (R((pullback.mapOverBaseRight f b (π i ≫ c))_*[ModuleCat.{u + 1} Λ]).obj
          (externalProduct (ModuleCat.{u + 1} Λ) (f ≫ b) (π i ≫ c) M (E i))) :=
  R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} Λ]).map
      (sumComparison Λ (f ≫ b) c n π E M) ≫
    (R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} Λ]).mapBiproduct
      (fun i ↦ (target Λ (f ≫ b) c (π i) (E i)).obj M)).hom ≫
    biproduct.map (fun i ↦ (composition Λ b c f (π i)).hom.app _)

set_option maxHeartbeats 2000000 in
-- Derived pullback and tensor expressions in the biproduct proof exceed the default budget.
/-- Finite sums of finite-dimensional constant modules give the same identifications
and the same counit compatibility. The two canonical comparison arrows are invertible;
both naturality equations are explicit, so these give natural isomorphisms,
including the second pushforward/composition comparison.
Source: blueprint, final sentence of Field coefficients and sheaves
(blueprint: lem-sf-finite-cover-tensor-counit-comparison).

Proof: apply steps 1--5 of the node to each finite direct image and step 6 to
its constant finite-dimensional coefficient. Additivity distributes inverse image,
tensor and direct image over finite biproducts. Take the biproduct of the inverses
and of the commuting counit squares. Naturality follows from that of these same
functors and maps; no choice of basis enters the resulting arrows. At n = 0 all
biproducts and arrows are zero, so the assertion includes the empty sum. -/
theorem finiteCoverTensorCounitComparison_finiteSum
    (k : Type u) [Field k] (L : Type (u + 1)) [Field L] [Finite L]
    (hL : IsUnit (ringChar L : k))
    {X Y T : Scheme.{u}} (b : Y ⟶ Spec (.of k)) (c : T ⟶ Spec (.of k)) (f : X ⟶ Y)
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsSeparated (f ≫ b)] [LocallyOfFiniteType (f ≫ b)] [QuasiCompact (f ≫ b)]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    (n : ℕ) (T' : Fin n → Scheme.{u}) (π : ∀ i, T' i ⟶ T) [∀ i, IsFinite (π i)]
    [∀ i, IsSeparated (π i ≫ c)] [∀ i, LocallyOfFiniteType (π i ≫ c)]
    [∀ i, QuasiCompact (π i ≫ c)]
    (V : Fin n → ModuleCat.{u + 1} L) [∀ i, Module.Finite L (V i)] :
    ∀ E : ∀ i, DerivedCategoryModule L (T' i),
      (∀ i, E i = (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (T' i).smallEtaleTopology (ModuleCat.{u + 1} L)).obj (V i))) →
    (∀ M : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} L)),
      IsIso (sumComparison L b c n π E (R((f)_*[ModuleCat.{u + 1} L]).obj M.obj)) ∧
      IsIso (sumOutputComparison L b c f n π E M.obj) ∧
      externalProductRightDerivedLowerStarMap (ModuleCat.{u + 1} L) b c f M.obj
          (⨁ fun i ↦ R((π i)_*[ModuleCat.{u + 1} L]).obj (E i)) ≫
          sumOutputComparison L b c f n π E M.obj =
        sumComparison L b c n π E (R((f)_*[ModuleCat.{u + 1} L]).obj M.obj) ≫
          biproduct.map (fun i ↦ R((productMap b c (π i))_*[ModuleCat.{u + 1} L]).map
            (externalProductRightDerivedLowerStarMap (ModuleCat.{u + 1} L)
              b (π i ≫ c) f M.obj (E i)))) ∧
    (∀ (M N : _root_.DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} L))) (φ : M ⟶ N),
      (sumSource L b c n π E).map (R((f)_*[ModuleCat.{u + 1} L]).map φ.hom) ≫
          sumComparison L b c n π E (R((f)_*[ModuleCat.{u + 1} L]).obj N.obj) =
        sumComparison L b c n π E (R((f)_*[ModuleCat.{u + 1} L]).obj M.obj) ≫
          biproduct.map (fun i ↦ (target L b c (π i) (E i)).map
            (R((f)_*[ModuleCat.{u + 1} L]).map φ.hom))) ∧
    (∀ (M N : _root_.DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} L))) (φ : M ⟶ N),
      R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} L]).map
          ((sumSource L (f ≫ b) c n π E).map φ.hom) ≫
          sumOutputComparison L b c f n π E N.obj =
        sumOutputComparison L b c f n π E M.obj ≫
          biproduct.map (fun i ↦ R((productMap b c (π i))_*[ModuleCat.{u + 1} L]).map
            (R((pullback.mapOverBaseRight f b (π i ≫ c))_*[ModuleCat.{u + 1} L]).map
              (externalProductMap (ModuleCat.{u + 1} L) (f ≫ b) (π i ≫ c)
                φ.hom (𝟙 (E i)))))) := by
  classical
  intro E hE
  choose a d hd using fun i ↦
    finiteCoverTensorCounitComparison_constantModule k L hL b c f (π i) (V i) (E i) (hE i)
  let P := fun i ↦ R((π i)_*[ModuleCat.{u + 1} L]).obj (E i)
  let H := R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} L])
  let S (Z : Scheme.{u}) (z : Z ⟶ Spec (.of k)) (K : DerivedCategoryModule L Z) :=
    L((pullback.snd z c)^*[ModuleCat.{u + 1} L]) ⋙
      (derivedTensor (ModuleCat.{u + 1} L) _).obj
        (L((pullback.fst z c)^*[ModuleCat.{u + 1} L]).obj K)
  have hsum (Z : Scheme.{u}) (z : Z ⟶ Spec (.of k))
      (K : DerivedCategoryModule L Z) (i : Fin n) :
      sumComparison L z c n π E K ≫
          biproduct.π (fun j ↦ (target L z c (π j) (E j)).obj K) i =
        (S Z z K).map (biproduct.π P i) ≫ comparison L z c (π i) K (E i) := by
    simp [sumComparison, S, P]
  have hout (K : DerivedCategoryModule L X) :
      sumOutputComparison L b c f n π E K =
        ((S X (f ≫ b) K ⋙ H).mapBiproduct P).hom ≫
          biproduct.map (fun i ↦ outputComparison L b c f (π i) K (E i)) := by
    apply biproduct.hom_ext
    intro i
    simp only [sumOutputComparison, Category.assoc, biproduct.map_π,
      Functor.mapBiproduct_hom, Functor.comp_map]
    erw [biproduct.lift_π_assoc, biproduct.lift_π_assoc]
    rw [← H.map_comp_assoc, hsum]
    simp only [outputComparison, Functor.map_comp, Category.assoc]
    rfl
  have houtπ (K : DerivedCategoryModule L X) (i : Fin n) :
      sumOutputComparison L b c f n π E K ≫
          biproduct.π (fun j ↦ R((productMap b c (π j))_*[ModuleCat.{u + 1} L]).obj
            (R((pullback.mapOverBaseRight f b (π j ≫ c))_*[ModuleCat.{u + 1} L]).obj
              (externalProduct (ModuleCat.{u + 1} L) (f ≫ b) (π j ≫ c) K (E j)))) i =
        H.map ((S X (f ≫ b) K).map (biproduct.π P i)) ≫
          outputComparison L b c f (π i) K (E i) := by
    rw [hout]
    simp
  have hnat (Z : Scheme.{u}) (z : Z ⟶ Spec (.of k))
      {K K' : DerivedCategoryModule L Z} (φ : K ⟶ K') (i : Fin n) :
      (sumSource L z c n π E).map φ ≫ (S Z z K').map (biproduct.π P i) =
        (S Z z K).map (biproduct.π P i) ≫ (source L z c (π i) (E i)).map φ := by
    simpa only [sumSource, source, S, P, Functor.comp_map, derivedTensorRight,
      Functor.flip_obj_map] using
      (((derivedTensor (ModuleCat.{u + 1} L) _).map
        (L((pullback.fst z c)^*[ModuleCat.{u + 1} L]).map φ)).naturality
          (L((pullback.snd z c)^*[ModuleCat.{u + 1} L]).map
            (biproduct.π P i))).symm
  have hκ (K : DerivedCategoryModule L X) {Q Q' : DerivedCategoryModule L T}
      (ψ : Q ⟶ Q') :
      (S Y b (R((f)_*[ModuleCat.{u + 1} L]).obj K)).map ψ ≫
          externalProductRightDerivedLowerStarMap (ModuleCat.{u + 1} L) b c f K Q' =
        externalProductRightDerivedLowerStarMap (ModuleCat.{u + 1} L) b c f K Q ≫
          H.map ((S X (f ≫ b) K).map ψ) := by
    let h := pullback.mapOverBaseRight f b c
    let q := pullback.snd b c
    let q' := pullback.snd (f ≫ b) c
    let p' := pullback.fst (f ≫ b) c
    let U := L((h)^*[ModuleCat.{u + 1} L])
    let r := L((q)^*[ModuleCat.{u + 1} L])
    let r' := L((q')^*[ModuleCat.{u + 1} L])
    let TK := (derivedTensor (ModuleCat.{u + 1} L) _).flip.obj
      (L((p')^*[ModuleCat.{u + 1} L]).obj K)
    let e := (leftDerivedUpperStarComp (ModuleCat.{u + 1} L) h q q' (by simp [h, q, q']))
    have he : U.map (r.map ψ) ≫ e.inv.app Q' = e.inv.app Q ≫ r'.map ψ :=
      e.inv.naturality ψ
    have het := congrArg TK.map he
    simp only [Functor.map_comp] at het
    have hb := ((derivedTensorBraiding (ModuleCat.{u + 1} L) (pullback b c)).hom.app
      (L((pullback.fst b c)^*[ModuleCat.{u + 1} L]).obj
        (R((f)_*[ModuleCat.{u + 1} L]).obj K))).naturality (r.map ψ)
    have ht := tensorBaseChangeMap_naturality (ModuleCat.{u + 1} L) h p'
      (pullback.fst b c) f (isPullback_mapOverBaseRight_fst b c f).w (r.map ψ) (𝟙 K)
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at ht
    have hx := NatTrans.naturality_app
      (derivedTensorBraiding (ModuleCat.{u + 1} L) (pullback (f ≫ b) c)).hom
      (L((p')^*[ModuleCat.{u + 1} L]).obj K) (r'.map ψ)
    have hδ : TK.map (U.map (r.map ψ)) ≫
          TK.map (e.inv.app Q') ≫
            ((derivedTensorBraiding (ModuleCat.{u + 1} L) _).hom.app _).app _ =
        TK.map (e.inv.app Q) ≫
          ((derivedTensorBraiding (ModuleCat.{u + 1} L) _).hom.app _).app _ ≫
            ((derivedTensor (ModuleCat.{u + 1} L) _).obj
              (L((p')^*[ModuleCat.{u + 1} L]).obj K)).map (r'.map ψ) := by
      rw [← Category.assoc, het, Category.assoc]
      exact congrArg (TK.map (e.inv.app Q) ≫ ·) hx
    dsimp only [S, Functor.comp_map]
    simp only [externalProductRightDerivedLowerStarMap, Category.assoc]
    erw [reassoc_of% hb, reassoc_of% ht]
    simp only [H, ← Functor.map_comp, Category.assoc]
    congr 2
    simpa only [H, h, TK, U, r, r', e, q, q', p', Functor.flip_obj_map,
      externalProduct, Functor.map_comp, Category.assoc] using congrArg H.map hδ
  -- Assemble the component identities using biproduct projections.
  refine ⟨?_, ?_, ?_⟩
  · intro M
    have ha (i : Fin n) :
        IsIso (comparison L b c (π i) (R((f)_*[ModuleCat.{u + 1} L]).obj M.obj) (E i)) := by
      rw [← (hd i M).1]
      infer_instance
    have ho (i : Fin n) : IsIso (outputComparison L b c f (π i) M.obj (E i)) := by
      rw [← (hd i M).2.1]
      infer_instance
    refine ⟨?_, ?_, ?_⟩
    · have hdiag : IsIso (biproduct.map (fun i ↦ comparison L b c (π i)
          (R((f)_*[ModuleCat.{u + 1} L]).obj M.obj) (E i))) :=
        inferInstanceAs (IsIso (biproduct.mapIso (fun i ↦ asIso
          (comparison L b c (π i) (R((f)_*[ModuleCat.{u + 1} L]).obj M.obj)
            (E i)))).hom)
      dsimp only [sumComparison]
      exact IsIso.comp_isIso' (Functor.mapBiproduct _ _).isIso_hom hdiag
    · have hdiag : IsIso (biproduct.map (fun i ↦ outputComparison L b c f (π i) M.obj
          (E i))) := inferInstanceAs (IsIso (biproduct.mapIso (fun i ↦ asIso
            (outputComparison L b c f (π i) M.obj (E i)))).hom)
      rw [hout]
      exact IsIso.comp_isIso' (Functor.mapBiproduct _ _).isIso_hom hdiag
    · apply biproduct.hom_ext
      intro i
      simp only [Category.assoc, biproduct.map_π]
      rw [houtπ, ← Category.assoc, ← hκ, Category.assoc, ← (hd i M).2.1,
        (hd i M).2.2]
      rw [reassoc_of% (hsum Y b (R((f)_*[ModuleCat.{u + 1} L]).obj M.obj) i)]
      simp only [(hd i M).1]
  · intro M N φ
    apply biproduct.hom_ext
    intro i
    simp only [Category.assoc, biproduct.map_π]
    rw [hsum, ← Category.assoc, hnat, Category.assoc]
    rw [reassoc_of% (hsum Y b (R((f)_*[ModuleCat.{u + 1} L]).obj M.obj) i)]
    have hn := (a i).hom.naturality φ
    simpa only [Functor.comp_map, ObjectProperty.ι_map, (hd i M).1, (hd i N).1] using
      congrArg ((S Y b (R((f)_*[ModuleCat.{u + 1} L]).obj M.obj)).map
        (biproduct.π P i) ≫ ·) hn
  · intro M N φ
    apply biproduct.hom_ext
    intro i
    simp only [Category.assoc, biproduct.map_π]
    rw [houtπ, ← H.map_comp_assoc, hnat, H.map_comp, Category.assoc]
    rw [reassoc_of% (houtπ M.obj i)]
    have hn := (d i).hom.naturality φ
    have hn' := congrArg (H.map ((S X (f ≫ b) M.obj).map (biproduct.π P i)) ≫ ·) hn
    dsimp only [externalProductMap]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]
    simpa only [H, Functor.comp_map, ObjectProperty.ι_map, (hd i M).2.1, (hd i N).2.1,
      target, derivedTensorRight, Functor.flip_obj_map, Category.assoc] using hn'


end AlgebraicGeometry.Etale.FiniteCoverCounit
