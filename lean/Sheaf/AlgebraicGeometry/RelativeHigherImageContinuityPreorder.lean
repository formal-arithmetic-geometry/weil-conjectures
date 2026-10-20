/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K6
-/
module

public import Sheaf.AlgebraicGeometry.RelativeHigherDirectImageContinuity
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Filtered.Basic

/-! # Relative continuity for directed preorders

Source: Stacks Project, Tag 0EYM. Reindex by the equivalent partially ordered
thin skeleton, apply the stated continuity theorem, and identify descent maps
by the colimit universal property.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor Limits Opposite
attribute [-instance] CategoryTheory.catToReflQuiver
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Etale

/-- The canonical exchange, with derived-functor endpoints written explicitly.
This is an abbreviation of the existing map, with identical data. -/
noncomputable abbrev relativeHigherImageExchange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} g').obj F ⟶ F') (q : ℕ) :
    (upperStar AddCommGrpCat.{u + 1} g).obj
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ⟶
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
      ((f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F')) :=
  relativeHigherDirectImageExchange sq F F' φ q

private lemma transport_functor_app {C D : Type*} [Category C] [Category D]
    {U V : C ⥤ D} (h : U = V) (X : C) :
    (eqToIso h).hom.app X = eqToHom (congrArg (fun T : C ⥤ D ↦ T.obj X) h) := by
  cases h
  rfl

private lemma desc_whisker_equivalence
    {J K C : Type*} [Category J] [Category K] [Category C]
    (ε : J ≌ K) {D : K ⥤ C} (c : Cocone D) (hc : IsColimit c) (t : Cocone D) :
    (hc.whiskerEquivalence ε).desc (t.whisker ε.functor) = hc.desc t := by
  apply (hc.whiskerEquivalence ε).hom_ext
  intro j
  exact ((hc.whiskerEquivalence ε).fac (t.whisker ε.functor) j).trans
    (hc.fac t (ε.functor.obj j)).symm

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Etale.upperStar Etale.lowerStar

private theorem continuity_partial_normalized
    {I : Type u} [PartialOrder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (DV DB : Iᵒᵖ ⥤ Scheme.{u}) (η : DV ⟶ DB)
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DV.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DB.map a)]
    [∀ i : Iᵒᵖ, QuasiCompact (η.app i)]
    [∀ i : Iᵒᵖ, QuasiSeparated (η.app i)]
    (cV : Cone DV) (hcV : IsLimit cV) (cB : Cone DB) (hcB : IsLimit cB)
    (v : cV.pt ⟶ cB.pt)
    (hu : ∀ i : Iᵒᵖ, cV.π.app i ≫ η.app i = v ≫ cB.π.app i)
    (F : ∀ i : I, Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (a : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (DV.map a.op)).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, φ (𝟙 i) =
      eqToHom (congrArg (fun a : DV.obj (op i) ⟶ DV.obj (op i) ↦
        ((a)^*[AddCommGrpCat.{u + 1}]).obj (F i)) (DV.map_id (op i))) ≫
        (upperStarId AddCommGrpCat.{u + 1} (DV.obj (op i))).hom.app (F i))
    (hφcomp : ∀ (i j k : I) (a : i ⟶ j) (b : j ⟶ k),
      φ (a ≫ b) =
        (upperStarComp AddCommGrpCat.{u + 1} (DV.map b.op) (DV.map a.op)
          (DV.map (a ≫ b).op) (DV.map_comp b.op a.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (DV.map b.op)).map (φ a) ≫ φ b)
    (A : I ⥤ Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eA : ∀ i : I, A.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op i))).obj (F i))
    (hA : ∀ (i j : I) (a : i ⟶ j), A.map a =
      (eA i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (cV.π.app (op j)) (DV.map a.op)
          (cV.π.app (op i)) (cV.w a.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op j))).map (φ a) ≫ (eA j).inv)
    (cA : Cocone A) (hcA : IsColimit cA) (q : ℕ)
    (H : I ⥤ Sheaf cB.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (cB.π.app (op i))).obj
        ((DerivedCategory.Plus.homologyFunctor
          (Sheaf (DB.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
          (((η.app (op i))_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
              (F i)))))
    (hH : ∀ (i j : I) (a : i ⟶ j), H.map a =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (cB.π.app (op j)) (DB.map a.op)
          (cB.π.app (op i)) (cB.w a.op).symm).hom.app
          ((DerivedCategory.Plus.homologyFunctor
            (Sheaf (DB.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
            (((η.app (op i))_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus).obj
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
                (F i)))) ≫
        (upperStar AddCommGrpCat.{u + 1} (cB.π.app (op j))).map
          (relativeHigherImageExchange ⟨η.naturality a.op⟩ (F i) (F j) (φ a) q) ≫
        (eH j).inv)
    (cH : Cocone H) (hcH : IsColimit cH)
    (legs : H ⟶ (Functor.const I).obj
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf cB.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((v)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj cA.pt))))
    (hlegs : ∀ i : I, legs.app i = (eH i).hom ≫
      relativeHigherImageExchange ⟨hu (op i)⟩ (F i) cA.pt
        ((eA i).inv ≫ cA.ι.app i) q) :
    IsIso (hcH.desc
      { pt := (DerivedCategory.Plus.homologyFunctor
          (Sheaf cB.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
          ((v)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj cA.pt))
        ι := legs }) := by
  exact higherDirectImage_relative_continuity DV DB η cV hcV cB hcB v hu F φ
    (by intro i; rw [transport_functor_app]; exact hφid i)
    hφcomp A eA hA cA hcA q H eH hH cH hcH legs hlegs

/-- Relative higher-image continuity also holds for directed preorders.

Source: Stacks Project, Tag 0EYM
(blueprint: lem-kun-relative-continuity-preorder).
Proof: Replace I by its thin skeleton J, a partially ordered category equivalent
to I. Filteredness, limit cones and colimit cocones are preserved by equivalence.
Reindex every scheme, coefficient map, presentation and leg along J → I.
Functoriality gives the coefficient laws, and all transition and leg equations
are the original ones evaluated at the chosen representatives. Apply relative
continuity for partial orders. Its comparison map equals the original descent
map because their composites with each reindexed cocone leg agree. Thus the
original comparison is an isomorphism. -/
theorem higherDirectImage_relative_continuity_preorder
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (DV DB : Iᵒᵖ ⥤ Scheme.{u}) (η : DV ⟶ DB)
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DV.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DB.map a)]
    [∀ i : Iᵒᵖ, QuasiCompact (η.app i)]
    [∀ i : Iᵒᵖ, QuasiSeparated (η.app i)]
    (cV : Cone DV) (hcV : IsLimit cV) (cB : Cone DB) (hcB : IsLimit cB)
    (v : cV.pt ⟶ cB.pt)
    (hu : ∀ i : Iᵒᵖ, cV.π.app i ≫ η.app i = v ≫ cB.π.app i)
    (F : ∀ i : I, Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (a : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (DV.map a.op)).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, φ (𝟙 i) =
      eqToHom (congrArg (fun a : DV.obj (op i) ⟶ DV.obj (op i) ↦
        ((a)^*[AddCommGrpCat.{u + 1}]).obj (F i)) (DV.map_id (op i))) ≫
        (upperStarId AddCommGrpCat.{u + 1} (DV.obj (op i))).hom.app (F i))
    (hφcomp : ∀ (i j k : I) (a : i ⟶ j) (b : j ⟶ k),
      φ (a ≫ b) =
        (upperStarComp AddCommGrpCat.{u + 1} (DV.map b.op) (DV.map a.op)
          (DV.map (a ≫ b).op) (DV.map_comp b.op a.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (DV.map b.op)).map (φ a) ≫ φ b)
    (A : I ⥤ Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eA : ∀ i : I, A.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op i))).obj (F i))
    (hA : ∀ (i j : I) (a : i ⟶ j), A.map a =
      (eA i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (cV.π.app (op j)) (DV.map a.op)
          (cV.π.app (op i)) (cV.w a.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (cV.π.app (op j))).map (φ a) ≫ (eA j).inv)
    (cA : Cocone A) (hcA : IsColimit cA) (q : ℕ)
    (H : I ⥤ Sheaf cB.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (cB.π.app (op i))).obj
        ((DerivedCategory.Plus.homologyFunctor
          (Sheaf (DB.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
          (((η.app (op i))_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
              (F i)))))
    (hH : ∀ (i j : I) (a : i ⟶ j), H.map a =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (cB.π.app (op j)) (DB.map a.op)
          (cB.π.app (op i)) (cB.w a.op).symm).hom.app
          ((DerivedCategory.Plus.homologyFunctor
            (Sheaf (DB.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
            (((η.app (op i))_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus).obj
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
                (F i)))) ≫
        (upperStar AddCommGrpCat.{u + 1} (cB.π.app (op j))).map
          (relativeHigherImageExchange ⟨η.naturality a.op⟩ (F i) (F j) (φ a) q) ≫
        (eH j).inv)
    (cH : Cocone H) (hcH : IsColimit cH)
    (legs : H ⟶ (Functor.const I).obj
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf cB.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((v)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj cA.pt))))
    (hlegs : ∀ i : I, legs.app i = (eH i).hom ≫
      relativeHigherImageExchange ⟨hu (op i)⟩ (F i) cA.pt
        ((eA i).inv ≫ cA.ι.app i) q) :
    IsIso (hcH.desc
      { pt := (DerivedCategory.Plus.homologyFunctor
          (Sheaf cB.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
          ((v)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj cA.pt))
        ι := legs }) := by
  classical
  let J := ThinSkeleton I
  obtain ⟨ε⟩ : Nonempty (J ≌ I) := ⟨ThinSkeleton.equivalence I⟩
  let K := ε.functor
  have : Nonempty J := ⟨ThinSkeleton.mk (Classical.choice ‹Nonempty I›)⟩
  have : IsFiltered J := IsFiltered.of_equivalence ε.symm
  have : IsDirected J (· ≤ ·) := IsFiltered.isDirectedOrder J
  let DV' := K.op ⋙ DV
  let DB' := K.op ⋙ DB
  let η' := whiskerLeft K.op η
  let F' := fun j : J ↦ F (K.obj j)
  let φ' : ∀ {i j : J} (a : i ⟶ j),
      ((DV'.map a.op)^*[AddCommGrpCat.{u + 1}]).obj (F' i) ⟶ F' j :=
    fun a ↦ φ (K.map a)
  have hid' : ∀ i : J, φ' (𝟙 i) =
      eqToHom (congrArg (fun a : DV'.obj (op i) ⟶ DV'.obj (op i) ↦
        ((a)^*[AddCommGrpCat.{u + 1}]).obj (F' i)) (DV'.map_id (op i))) ≫
      (upperStarId AddCommGrpCat.{u + 1} (DV'.obj (op i))).hom.app (F' i) := by
    intro i
    exact hφid (K.obj i)
  have hcomp' : ∀ (i j k : J) (a : i ⟶ j) (b : j ⟶ k),
      φ' (a ≫ b) =
        (upperStarComp AddCommGrpCat.{u + 1} (DV'.map b.op) (DV'.map a.op)
          (DV'.map (a ≫ b).op) (DV'.map_comp b.op a.op)).hom.app (F' i) ≫
        ((DV'.map b.op)^*[AddCommGrpCat.{u + 1}]).map (φ' a) ≫ φ' b := by
    intro i j k a b
    exact hφcomp (K.obj i) (K.obj j) (K.obj k) (K.map a) (K.map b)
  have hA' : ∀ (i j : J) (a : i ⟶ j), (K ⋙ A).map a =
      (eA (K.obj i)).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1}
          ((cV.whisker K.op).π.app (op j)) (DV'.map a.op)
          ((cV.whisker K.op).π.app (op i))
          ((cV.whisker K.op).w a.op).symm).hom.app (F' i) ≫
        (((cV.whisker K.op).π.app (op j))^*[AddCommGrpCat.{u + 1}]).map (φ' a) ≫
          (eA (K.obj j)).inv := by
    intro i j a
    exact hA (K.obj i) (K.obj j) (K.map a)
  have hH' : ∀ (i j : J) (a : i ⟶ j), (K ⋙ H).map a =
      (eH (K.obj i)).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1}
          ((cB.whisker K.op).π.app (op j)) (DB'.map a.op)
          ((cB.whisker K.op).π.app (op i))
          ((cB.whisker K.op).w a.op).symm).hom.app
          ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
            ((η'.app (op i))_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj (F' i)))) ≫
        (((cB.whisker K.op).π.app (op j))^*[AddCommGrpCat.{u + 1}]).map
          (relativeHigherImageExchange ⟨η'.naturality a.op⟩
            (F' i) (F' j) (φ' a) q) ≫ (eH (K.obj j)).inv := by
    intro i j a
    exact hH (K.obj i) (K.obj j) (K.map a)
  have hlegs' : ∀ i : J, (whiskerLeft K legs).app i = (eH (K.obj i)).hom ≫
      relativeHigherImageExchange ⟨hu (op (K.obj i))⟩ (F' i) (cA.whisker K).pt
        ((eA (K.obj i)).inv ≫ (cA.whisker K).ι.app i) q := by
    intro i
    exact hlegs (K.obj i)
  have : ∀ {i j : Jᵒᵖ} (a : i ⟶ j), IsAffineHom (DV'.map a) := by
    intro i j a
    exact inferInstanceAs (IsAffineHom (DV.map (K.op.map a)))
  have : ∀ {i j : Jᵒᵖ} (a : i ⟶ j), IsAffineHom (DB'.map a) := by
    intro i j a
    exact inferInstanceAs (IsAffineHom (DB.map (K.op.map a)))
  have : ∀ i : Jᵒᵖ, QuasiCompact (η'.app i) := fun i ↦
    inferInstanceAs (QuasiCompact (η.app (K.op.obj i)))
  have : ∀ i : Jᵒᵖ, QuasiSeparated (η'.app i) := fun i ↦
    inferInstanceAs (QuasiSeparated (η.app (K.op.obj i)))
  have hcont := continuity_partial_normalized DV' DB' η'
    (cV.whisker K.op) (hcV.whiskerEquivalence ε.op)
    (cB.whisker K.op) (hcB.whiskerEquivalence ε.op) v
    (fun i ↦ hu (K.op.obj i)) F' φ' hid' hcomp'
    (K ⋙ A) (fun i ↦ eA (K.obj i)) hA' (cA.whisker K) (hcA.whiskerEquivalence ε)
    q (K ⋙ H) (fun i ↦ eH (K.obj i)) hH' (cH.whisker K)
    (hcH.whiskerEquivalence ε) (whiskerLeft K legs) hlegs'
  change IsIso ((hcH.whiskerEquivalence ε).desc
    ((Cocone.mk _ legs).whisker ε.functor)) at hcont
  rw [desc_whisker_equivalence] at hcont
  exact hcont

end AlgebraicGeometry.Etale
