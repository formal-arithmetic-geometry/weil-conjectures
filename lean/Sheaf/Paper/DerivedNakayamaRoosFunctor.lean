/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.Topology.ProfiniteCondensedRing
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# Functoriality of the specified augmented Roos complex

Source: blueprint main-20261015, first-reduction lemma, Cones paragraph
(blueprint: det-pe-derived-nakayama-roos-functor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

-- Keep instance inference from unfolding the inverse-image monoidal construction.
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.monoidal_upperStarFromPoint

namespace AlgebraicGeometry.ProEtale.AdicCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Apply a chain map to every reduction in the strict product.
Source: blueprint, Cones paragraph (blueprint: det-pe-derived-nakayama-roos-functor). -/
def productMap {P P' : CochainComplex (Modules l E X) ℤ} (f : P ⟶ P') :
    product l E X P ⟶ product l E X P' :=
  Limits.Pi.map (fun n ↦ (level l E X n).map f)

private theorem productMap_step {P P' : CochainComplex (Modules l E X) ℤ} (f : P ⟶ P') :
    oneSubShift l E X P ≫ productMap l E X f =
      productMap l E X f ≫ oneSubShift l E X P' := by
  exact (towerTransitionEndomorphism_natural_backward _ _
    (fun n ↦ (level l E X n).map f) (fun n ↦
      ((NatTrans.mapHomologicalComplex
        ((tensoringRight (Modules l E X)).map
          ((DerivedNakayama.pullback l E X).map (quotientStep l E n)))
          (.up ℤ)).naturality f))).symm

/-- The diagonal map commutes with the Roos differential.
Source: blueprint, Cones paragraph (blueprint: det-pe-derived-nakayama-roos-functor). -/
theorem roosMap_comm {P P' : CochainComplex (Modules l E X) ℤ}
    (f : P ⟶ P') (i : ℤ) :
    biprod.map ((productMap l E X f).f i) ((productMap l E X f).f (i - 1)) ≫
        (roos l E X P').d i (i + 1) =
      (roos l E X P).d i (i + 1) ≫
        biprod.map ((productMap l E X f).f (i + 1))
          ((productMap l E X f).f ((i + 1) - 1)) := by
  simp only [roos, CochainComplex.of_d, roosD]
  dsimp only [roosX]
  have hs := congrArg (fun a ↦ a.f i) (productMap_step l E X f)
  simp only [HomologicalComplex.comp_f] at hs
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst,
      biprod.map_fst_assoc, biprod.lift_fst_assoc]
    rw [(productMap l E X f).comm]
  · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd,
      biprod.map_fst_assoc, biprod.map_snd_assoc, biprod.lift_snd_assoc,
      Preadditive.comp_sub, Preadditive.sub_comp]
    have heq : ∀ {j k : ℤ} (h : j = k),
        (productMap l E X f).f j ≫ eqToHom (congrArg (product l E X P').X h) =
          eqToHom (congrArg (product l E X P).X h) ≫ (productMap l E X f).f k := by
      intro j k h
      subst k
      simp
    rw [← reassoc_of% hs, heq (Int.add_sub_cancel i 1).symm]
    rw [(productMap l E X f).comm]

/-- The chain map on Roos complexes is diagonal in the two product coordinates.
Source: blueprint, Cones paragraph (blueprint: det-pe-derived-nakayama-roos-functor). -/
def roosMap {P P' : CochainComplex (Modules l E X) ℤ} (f : P ⟶ P') :
    roos l E X P ⟶ roos l E X P' :=
  CochainComplex.ofHom
    (fun i ↦ biprod.map ((productMap l E X f).f i) ((productMap l E X f).f (i - 1)))
    (roosMap_comm l E X f)

/-- The strict augmented Roos construction is a functor, before localization.
Source: blueprint, Cones paragraph (blueprint: det-pe-derived-nakayama-roos-functor). -/
def roosFunctor : CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ where
  obj := roos l E X
  map := roosMap l E X
  map_id P := by
    have hid : productMap l E X (𝟙 P) = 𝟙 _ := by simp [productMap]
    apply HomologicalComplex.Hom.ext
    funext i
    change biprod.map ((productMap l E X (𝟙 P)).f i)
      ((productMap l E X (𝟙 P)).f (i - 1)) =
        𝟙 ((product l E X P).X i ⊞ (product l E X P).X (i - 1))
    rw [hid]
    simp only [HomologicalComplex.id_f]
    apply biprod.hom_ext <;> simp
  map_comp {P P' P''} f g := by
    have hcomp : productMap l E X (f ≫ g) =
        productMap l E X f ≫ productMap l E X g := by
      apply Pi.hom_ext
      intro n
      simp [productMap]
    apply HomologicalComplex.Hom.ext
    funext i
    change biprod.map ((productMap l E X (f ≫ g)).f i)
      ((productMap l E X (f ≫ g)).f (i - 1)) =
        biprod.map ((productMap l E X f).f i) ((productMap l E X f).f (i - 1)) ≫
          biprod.map ((productMap l E X g).f i) ((productMap l E X g).f (i - 1))
    rw [hcomp]
    simp only [HomologicalComplex.comp_f]
    apply biprod.hom_ext <;> simp

set_option backward.isDefEq.respectTransparency false

/-- The actual augmentations, with zero second coordinate, are natural in complexes.
Source: blueprint, Cones paragraph (blueprint: det-pe-derived-nakayama-roos-functor). -/
def roosAugmentation : 𝟭 _ ⟶ roosFunctor l E X where
  app := augmentation l E X
  naturality {P P'} f := by
    have h : f ≫ unitProduct l E X P' = unitProduct l E X P ≫ productMap l E X f := by
      apply Pi.hom_ext
      intro n
      dsimp only [unitProduct, productMap]
      simp only [Category.assoc, Pi.lift_π, Pi.map_π, Pi.lift_π_assoc]
      apply HomologicalComplex.Hom.ext
      funext i
      exact ((rightUnitorNatIso (Modules l E X)).inv ≫
        (tensoringRight (Modules l E X)).map (finiteUnit l E X n)).naturality (f.f i)
    apply HomologicalComplex.Hom.ext
    funext i
    dsimp [augmentation, roosFunctor, roosMap]
    apply biprod.hom_ext
    · simpa using congrArg (fun a ↦ a.f i) h
    · simp

private def productXIso (P : CochainComplex (Modules l E X) ℤ) (i : ℤ) :
    (product l E X P).X i ≅ ∏ᶜ (fun n : ℕ ↦ P.X i ⊗ finiteModule l E X n) :=
  asIso (piComparison (HomologicalComplex.eval (Modules l E X) (.up ℤ) i)
    (fun n : ℕ ↦ (level l E X n).obj P))

private def productXMap {P P' : CochainComplex (Modules l E X) ℤ} {i j : ℤ}
    (f : P.X i ⟶ P'.X j) : (product l E X P).X i ⟶ (product l E X P').X j :=
  (productXIso l E X P i).hom ≫ Limits.Pi.map (fun n ↦ f ▷ finiteModule l E X n) ≫
    (productXIso l E X P' j).inv

private theorem productXMap_comp {P P' P'' : CochainComplex (Modules l E X) ℤ}
    {i j k : ℤ} (f : P.X i ⟶ P'.X j) (g : P'.X j ⟶ P''.X k) :
    productXMap l E X (P := P) (P' := P'') (f ≫ g) =
      productXMap l E X (P := P) (P' := P') f ≫
        productXMap l E X (P := P') (P' := P'') g := by
  simp only [productXMap, Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  rw [← Category.assoc]
  congr 1
  apply Pi.hom_ext
  intro n
  simp

private theorem productXMap_id (P : CochainComplex (Modules l E X) ℤ) (i : ℤ) :
    productXMap l E X (P := P) (P' := P) (𝟙 (P.X i)) = 𝟙 _ := by
  simp only [productXMap, id_whiskerRight]
  have h : Limits.Pi.map (fun n : ℕ ↦ 𝟙 (P.X i ⊗ finiteModule l E X n)) = 𝟙 _ := by
    apply Pi.hom_ext
    intro n
    simp
  rw [h]
  simp

private theorem productXMap_add {P P' : CochainComplex (Modules l E X) ℤ}
    {i j : ℤ} (f g : P.X i ⟶ P'.X j) :
    productXMap l E X (P := P) (P' := P') (f + g) =
      productXMap l E X (P := P) (P' := P') f +
        productXMap l E X (P := P) (P' := P') g := by
  dsimp only [productXMap]
  rw [← Preadditive.comp_add, ← Preadditive.add_comp]
  congr 2
  apply Pi.hom_ext
  intro n
  simp [MonoidalPreadditive.add_whiskerRight]

private theorem productMap_f {P P' : CochainComplex (Modules l E X) ℤ}
    (f : P ⟶ P') (i : ℤ) :
    (productMap l E X f).f i = productXMap l E X (P := P) (P' := P') (f.f i) := by
  rw [productXMap]
  apply (cancel_mono (productXIso l E X P' i).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, productXIso, asIso_hom, Pi.map_π]
  erw [piComparison_comp_π, piComparison_comp_π_assoc]
  change ((productMap l E X f) ≫ Pi.π _ n).f i = _
  simp only [productMap, Pi.map_π]
  rfl

/-- The strict Roos functor is additive.
Source: the coordinatewise construction in the Cones paragraph
(blueprint: det-pe-derived-nakayama-roos-functor). -/
instance roosFunctor_additive : (roosFunctor l E X).Additive where
  map_add {P P'} f g := by
    have h : productMap l E X (f + g) = productMap l E X f + productMap l E X g := by
      apply Pi.hom_ext
      intro n
      simp [productMap, Preadditive.add_comp]
    apply HomologicalComplex.Hom.ext
    funext i
    change biprod.map ((productMap l E X (f + g)).f i)
      ((productMap l E X (f + g)).f (i - 1)) =
        biprod.map ((productMap l E X f).f i) ((productMap l E X f).f (i - 1)) +
        biprod.map ((productMap l E X g).f i) ((productMap l E X g).f (i - 1))
    rw [h]
    change biprod.map (_ + _) (_ + _) = _
    apply biprod.hom_ext <;> simp [Preadditive.add_comp, Preadditive.comp_add]

/-- A degreewise split sequence remains degreewise split after the strict Roos functor.
Source: blueprint first-reduction proof, product and four-summand construction
(blueprint: det-pe-derived-nakayama-roos-functor). -/
private def roosFunctor_degreewiseSplit
    (S : ShortComplex (CochainComplex (Modules l E X) ℤ))
    (σ : ∀ i, (ShortComplex.mk (S.f.f i) (S.g.f i)
      (by exact congrArg (fun a ↦ a.f i) S.zero)).Splitting) (i : ℤ) :
    ((S.map (roosFunctor l E X)).map (HomologicalComplex.eval _ _ i)).Splitting where
  r := biprod.map
    (productXMap l E X (P := S.X₂) (P' := S.X₁) (σ i).r)
    (productXMap l E X (P := S.X₂) (P' := S.X₁) (σ (i - 1)).r)
  s := biprod.map
    (productXMap l E X (P := S.X₃) (P' := S.X₂) (σ i).s)
    (productXMap l E X (P := S.X₃) (P' := S.X₂) (σ (i - 1)).s)
  f_r := by
    change biprod.map ((productMap l E X S.f).f i)
      ((productMap l E X S.f).f (i - 1)) ≫ _ = 𝟙 (roosX l E X S.X₁ i)
    apply biprod.hom_ext <;>
      simp only [Category.assoc, biprod.map_fst, biprod.map_snd,
        biprod.map_fst_assoc, biprod.map_snd_assoc, productMap_f,
        ← productXMap_comp]
    · rw [show S.f.f i ≫ (σ i).r = 𝟙 (S.X₁.X i) from (σ i).f_r, productXMap_id]
      simp only [roosX, Category.comp_id, Category.id_comp]
    · rw [show S.f.f (i - 1) ≫ (σ (i - 1)).r = 𝟙 (S.X₁.X (i - 1)) from (σ (i - 1)).f_r,
        productXMap_id]
      simp only [roosX, Category.comp_id, Category.id_comp]
  s_g := by
    change _ ≫ biprod.map ((productMap l E X S.g).f i)
      ((productMap l E X S.g).f (i - 1)) = _
    apply biprod.hom_ext <;>
      simp only [Category.assoc, biprod.map_fst, biprod.map_snd,
        biprod.map_fst_assoc, biprod.map_snd_assoc, Category.id_comp, productMap_f,
        ← productXMap_comp]
    · rw [show (σ i).s ≫ S.g.f i = 𝟙 (S.X₃.X i) from (σ i).s_g, productXMap_id]
      simp only [Category.comp_id]
    · rw [show (σ (i - 1)).s ≫ S.g.f (i - 1) = 𝟙 (S.X₃.X (i - 1)) from (σ (i - 1)).s_g,
        productXMap_id]
      simp only [Category.comp_id]
  id := by
    change biprod.map _ _ ≫ biprod.map ((productMap l E X S.f).f i)
      ((productMap l E X S.f).f (i - 1)) +
      biprod.map ((productMap l E X S.g).f i)
        ((productMap l E X S.g).f (i - 1)) ≫ biprod.map _ _ = 𝟙 _
    apply biprod.hom_ext <;>
      simp only [Preadditive.add_comp, Category.assoc, biprod.map_fst, biprod.map_snd,
        biprod.map_fst_assoc, biprod.map_snd_assoc, Category.id_comp, productMap_f,
        ← productXMap_comp, ← Preadditive.comp_add, ← productXMap_add]
    · have h : (σ i).r ≫ S.f.f i + S.g.f i ≫ (σ i).s = 𝟙 (S.X₂.X i) := (σ i).id
      rw [h, productXMap_id]
      simp only [Category.comp_id]
    · have h : (σ (i - 1)).r ≫ S.f.f (i - 1) + S.g.f (i - 1) ≫
        (σ (i - 1)).s = 𝟙 (S.X₂.X (i - 1)) := (σ (i - 1)).id
      rw [h, productXMap_id]
      simp only [Category.comp_id]

/-- In a degreewise split sequence, invertibility of the actual augmentations at
both endpoints implies invertibility at the middle term.
Source: blueprint first-reduction proof, Cones paragraph and the triangle criterion
(blueprint: det-pe-derived-nakayama-roos-functor). -/
theorem roos_augmentation_middle
    (S : ShortComplex (CochainComplex (Modules l E X) ℤ))
    (σ : ∀ i, (S.map (HomologicalComplex.eval _ _ i)).Splitting)
    (h₁ : IsIso (DerivedCategory.Q.map (augmentation l E X S.X₁)))
    (h₃ : IsIso (DerivedCategory.Q.map (augmentation l E X S.X₃))) :
    IsIso (DerivedCategory.Q.map (augmentation l E X S.X₂)) := by
  have hS : S.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact S
    (fun i ↦ (σ i).shortExact)
  have hS' : (S.map (roosFunctor l E X)).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _
      (fun i ↦ (roosFunctor_degreewiseSplit l E X S σ i).shortExact)
  let φ : S ⟶ S.map (roosFunctor l E X) :=
    { τ₁ := augmentation l E X S.X₁
      τ₂ := augmentation l E X S.X₂
      τ₃ := augmentation l E X S.X₃
      comm₁₂ := ((roosAugmentation l E X).naturality S.f).symm
      comm₂₃ := ((roosAugmentation l E X).naturality S.g).symm }
  exact Pretriangulated.isIso₂_of_isIso₁₃ (DerivedCategory.triangleOfSES.map hS hS' φ)
    (DerivedCategory.triangleOfSES_distinguished hS)
    (DerivedCategory.triangleOfSES_distinguished hS') h₁ h₃

/-- The Roos augmentation on a mapping cone is invertible if it is invertible
on the target and on the shifted source. This uses the degreewise split sequence
of the mapping cone, without localizing the completion construction.
Source: blueprint, Cones paragraph (blueprint: det-pe-derived-nakayama-roos-functor). -/
theorem roos_augmentation_cone {P P' : CochainComplex (Modules l E X) ℤ}
    (f : P ⟶ P')
    (hB : IsIso ((DerivedCategory.Q (C := Modules l E X)).map (augmentation l E X P')))
    (hA : IsIso ((DerivedCategory.Q (C := Modules l E X)).map (augmentation l E X (P⟦(1 : ℤ)⟧)))) :
    IsIso ((DerivedCategory.Q (C := Modules l E X)).map
      (augmentation l E X (CochainComplex.mappingCone f))) := by
  let q : CochainComplex.mappingCone f ⟶ P⟦(1 : ℤ)⟧ :=
    (CochainComplex.mappingCone.triangle f).mor₃
  let S : ShortComplex (CochainComplex (Modules l E X) ℤ) :=
    { X₁ := P'
      X₂ := CochainComplex.mappingCone f
      X₃ := P⟦(1 : ℤ)⟧
      f := CochainComplex.mappingCone.inr f
      g := q
      zero := by
        apply HomologicalComplex.Hom.ext
        funext i
        simp [q] }
  apply roos_augmentation_middle l E X S _ hB hA
  intro i
  refine { r := (CochainComplex.mappingCone.snd f).v i i (add_zero i)
           s := -(CochainComplex.mappingCone.inl f).v (i + 1) i (by omega)
           f_r := ?_, s_g := ?_, id := ?_ }
  · change (CochainComplex.mappingCone.inr f).f i ≫ _ = 𝟙 (P'.X i)
    simp
  · change _ ≫ q.f i = 𝟙 (P.X (i + 1))
    simp [q, CochainComplex.shiftFunctorObjXIso]
  · change (CochainComplex.mappingCone.snd f).v i i (add_zero i) ≫
        (CochainComplex.mappingCone.inr f).f i +
      q.f i ≫
        (-(CochainComplex.mappingCone.inl f).v (i + 1) i (by omega)) = 𝟙 _
    apply CochainComplex.mappingCone.ext_from f (i + 1) i rfl <;>
      simp [q, Preadditive.comp_add, CochainComplex.shiftFunctorObjXIso]

end AlgebraicGeometry.ProEtale.AdicCompletion
