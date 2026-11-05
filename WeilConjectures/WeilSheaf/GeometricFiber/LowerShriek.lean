/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.GeometricFiber.Forget
public import WeilConjectures.PoincareDuality.ProjectionFormulaOpenImmersion
import WeilConjectures.Tactic.TransportModProofs
import WeilConjectures.Tactic.ExactModProofs
import WeilConjectures.Tactic.TransportExact
import WeilConjectures.Tactic.ExactByKernel

/-!
# The geometric direct image with compact support along the base-changed compactification

Let `X ⟶[i] Z ⟶[g] Y` be the compactification of `f : X ⟶ Y` defining the direct image with
compact support of Weil complexes, and `ī`, `ḡ`, `f̄` the base changes to the geometric fibres
(`AlgebraicGeometry.WeilComplex.geometricFiberHom`). The functor `ī_! ⋙ Rḡ_*` on bounded
constructible complexes is the direct image with compact support `Rf̄_!`
(`AlgebraicGeometry.WeilComplex.geometricFiberLowerShriekIso`), and this identification carries
the composite of the projection morphism of `ḡ^* ⊣ Rḡ_*` and of the inverse projection comparison
of `ī_! ⊣ ī^*` to the exceptional projection morphism of `f̄`
(`AlgebraicGeometry.WeilComplex.geometricFiberLowerShriekIso_hom_app_whiskerRight_comp`).

## Implementation notes

The base change `(geometricFiberHomCompactification f)` of the compactification has as middle
object an `Over` object which is not definitionally the one of `geometricFiberHom i`, and
comparing the two is prohibitively slow. We therefore use the compactification
`AlgebraicGeometry.WeilComplex.geometricFiberLowerShriekCompactification` whose fields are
literally `(geometricFiberHom i).left` and `(geometricFiberHom g).left`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.WeilComplex

open ProEtale

attribute [local instance] Compactification.over

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [QuasiCompact (nativeProjectionCompactification k₀ f).i]

omit [Finite k₀] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] in
/-- The base changes `ī` and `ḡ` of the halves of the compactification compose to `f̄`. -/
lemma geometricFiberHom_i_comp_g :
    geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).i ≫
      geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).g =
      geometricFiberHom (k₀ := k₀) f := by
  ext1
  simp only [Over.comp_left, Over.homMk_left]
  rw [← Scheme.Hom.geometricFiberMap_comp]
  exact Scheme.Hom.geometricFiberMap_congr (nativeProjectionCompactification k₀ f).comm.symm _ _

/-- The compactification `X̄ ⟶[ī] Z̄ ⟶[ḡ] Ȳ` of `f̄` obtained by base change, with fields the
underlying morphisms of `geometricFiberHom i` and `geometricFiberHom g`. -/
noncomputable def geometricFiberLowerShriekCompactification :
    Compactification (geometricFiberHom (k₀ := k₀) f).left where
  Z := (Over.mk ((nativeProjectionCompactification k₀ f).Z ↘
    Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left
  g := (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).g).left
  i := (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).i).left
  comm := (congrArg Over.Hom.left (geometricFiberHom_i_comp_g f)).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

variable (k₀ l) in
/-- The identification `ḡ^* ⋙ ī^* ≅ f̄^*` of pullbacks of bounded constructible complexes: the
inverse of the identification `Lf̄^* ≅ Lḡ^* ⋙ Lī^*` of the base-changed compactification. -/
noncomputable def geometricFiberUpperStarCompIso :
    CondensedRing.boundedConstructibleUpperStar _ l
        (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).g) ⋙
      CondensedRing.boundedConstructibleUpperStar _ l
        (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).i) ≅
      CondensedRing.boundedConstructibleUpperStar (Profinite.padicAlgClRingObj l) l
        (geometricFiberHom (k₀ := k₀) f) :=
  (eqToIso (congrArg (CondensedRing.boundedConstructibleUpperStar _ l)
      (geometricFiberHom_i_comp_g f).symm) ≪≫
    CondensedRing.boundedConstructibleUpperStarComp _ l _ _).symm

/-- The identity of `Z̄`, from the `Over` object of `geometricFiberHom g` to the middle object of
the compactification `geometricFiberLowerShriekCompactification f`. -/
noncomputable def geometricFiberLowerShriekRefinement :
    Over.mk ((nativeProjectionCompactification k₀ f).Z ↘
        Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ≅
      (geometricFiberLowerShriekCompactification f).overObj :=
  Over.isoMk (Iso.refl ((Over.mk ((nativeProjectionCompactification k₀ f).Z ↘
      Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left)) (by
    simp only [Iso.refl_hom, Category.id_comp, Compactification.overObj_hom]
    exact Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure _
      (comp_over (nativeProjectionCompactification k₀ f).g (Spec (CommRingCat.of k₀))))

instance : IsProper (geometricFiberLowerShriekRefinement (k₀ := k₀) f).hom.left := by
  dsimp only [geometricFiberLowerShriekRefinement, Over.isoMk_hom_left, Iso.refl_hom]
  infer_instance

lemma isPullback_geometricFiberLowerShriekRefinement :
    IsPullback (𝟙 _) (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).i)
      (geometricFiberLowerShriekCompactification f).overI
      (geometricFiberLowerShriekRefinement (k₀ := k₀) f).hom :=
  IsPullback.of_horiz_isIso ⟨by ext1; simp [geometricFiberLowerShriekRefinement,
    geometricFiberLowerShriekCompactification, Compactification.overI]⟩

lemma geometricFiberLowerShriekRefinement_hom_comp_overG :
    (geometricFiberLowerShriekRefinement (k₀ := k₀) f).hom ≫ (geometricFiberLowerShriekCompactification f).overG =
      geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).g := by
  ext1
  simp [geometricFiberLowerShriekRefinement, geometricFiberLowerShriekCompactification,
    Compactification.overG]

instance : IsIso (CondensedRing.boundedConstructibleOpenImmersionLowerShriekRefinementPushforward l
    (isPullback_geometricFiberLowerShriekRefinement (k₀ := k₀) f)) :=
  CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl l
    (isPullback_geometricFiberLowerShriekRefinement (k₀ := k₀) f)

omit [Finite k₀] [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] in
/-- Transport of a compatibility of morphisms `p_Q`, `p_R` with `p_P` along isomorphisms. -/
lemma whiskerRight_comp_of_refinement {C : Type*} [Category* C] [MonoidalCategory C]
    {P Q R P' Q' R' B : C} (r : P ⟶ Q) (s : Q ⟶ P) (i : P ⟶ R) (r' : P' ⟶ Q') (s' : Q' ⟶ P')
    (i' : P' ⟶ R') (hs : s ≫ r = 𝟙 Q) (hr' : r' ≫ s' = 𝟙 P')
    (pP : P ⊗ B ⟶ P') (pQ : Q ⊗ B ⟶ Q') (pR : R ⊗ B ⟶ R')
    (hρ : r ▷ B ≫ pQ = pP ≫ r') (hι : i ▷ B ≫ pR = pP ≫ i') :
    (s ≫ i) ▷ B ≫ pR = pQ ≫ s' ≫ i' := by
  have : pP = r ▷ B ≫ pQ ≫ s' := by
    rw [reassoc_of% hρ, hr', Category.comp_id]
  rw [comp_whiskerRight, Category.assoc, hι, this]
  simp only [Category.assoc, ← comp_whiskerRight_assoc, hs, id_whiskerRight, Category.id_comp]

variable (k₀ l) in
/-- The identification `ī_! ⋙ Rḡ_* ≅ Rf̄_!` of the composite of the extension by zero and the
proper direct image along the base-changed compactification with the direct image with compact
support of bounded constructible complexes on the geometric fibres. -/
noncomputable def geometricFiberLowerShriekIso :
    CondensedRing.boundedConstructibleOpenImmersionLowerShriek _ l
        (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).i) ⋙
      CondensedRing.boundedConstructibleLowerStar l
        (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).g) ≅
      CondensedRing.boundedConstructibleLowerShriek l (geometricFiberHom (k₀ := k₀) f) :=
  (CondensedRing.boundedConstructibleLowerShriekRefinementIso l
      (isPullback_geometricFiberLowerShriekRefinement (k₀ := k₀) f)
      (geometricFiberLowerShriekRefinement_hom_comp_overG (k₀ := k₀) f)).symm ≪≫
    CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl l _ _

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 400000 in
-- the monoidal structure of the derived category of condensed modules is found slowly
open scoped CategoryTheory.Obj in
/-- **The identification `ī_! ⋙ Rḡ_* ≅ Rf̄_!` intertwines the projection morphisms**: through it,
the exceptional projection morphism of `f̄` is the projection morphism of `ḡ^* ⊣ Rḡ_*` followed
by the inverse projection comparison of `ī_! ⊣ ī^*` and the identification `ī^* ḡ^* ≅ f̄^*`. -/
theorem geometricFiberLowerShriekIso_hom_app_whiskerRight_comp (K B) :
    (geometricFiberLowerShriekIso k₀ l f).hom.app K ▷ B ≫
        CondensedRing.boundedConstructibleExceptionalProjectionMorphism l
          (geometricFiberHom (k₀ := k₀) f) K B =
      ((CondensedRing.boundedConstructibleUpperStarLowerStarAdjunction l
          (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).g)).projectionMorphism
          ((CondensedRing.boundedConstructibleOpenImmersionLowerShriek _ l
            (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).i)).obj K) B ≫
        (CondensedRing.boundedConstructibleLowerStar l
          (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).g)).map
          (inv ((CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ l
              (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).i)).projectionComparison
              K ((CondensedRing.boundedConstructibleUpperStar _ l
                (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).g)).obj B)) ≫
            (CondensedRing.boundedConstructibleOpenImmersionLowerShriek _ l
              (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).i)).map
              (K ◁ (geometricFiberUpperStarCompIso k₀ l f).hom.app B))) ≫
        (geometricFiberLowerShriekIso k₀ l f).hom.app
          (K ⊗ (CondensedRing.boundedConstructibleUpperStar _ l
            (geometricFiberHom (k₀ := k₀) f)).obj B) := by
  have hρ := CondensedRing.boundedConstructibleLowerShriekRefinementIso_hom_app_whiskerRight_comp l
    (isPullback_geometricFiberLowerShriekRefinement (k₀ := k₀) f)
    (geometricFiberLowerShriekRefinement_hom_comp_overG (k₀ := k₀) f) (geometricFiberHom_i_comp_g f)
    (geometricFiberLowerShriekCompactification f).overI_overG K B
  have hc := CondensedRing.homMk_exceptionalProjectionMorphismOfCompactification_eq l
    (geometricFiberLowerShriekCompactification (k₀ := k₀) f) K B _
    (CondensedRing.ι_map_eqToIso_trans_upperStarComp_inv_app_compactification l
      (geometricFiberLowerShriekCompactification (k₀ := k₀) f) B)
  have h := CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_hom_app_whiskerRight_comp l
    (geometricFiberLowerShriekCompactification f)
    (CondensedRing.compactificationOverField (geometricFiberHom (k₀ := k₀) f)) K B
  rw [hc] at h
  simp only [geometricFiberUpperStarCompIso, Iso.symm_hom]
  simp only [geometricFiberLowerShriekIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  refine whiskerRight_comp_of_refinement _ _ _ _ _ _
    ((CondensedRing.boundedConstructibleLowerShriekRefinementIso l
      (isPullback_geometricFiberLowerShriekRefinement (k₀ := k₀) f)
      (geometricFiberLowerShriekRefinement_hom_comp_overG (k₀ := k₀) f)).inv_hom_id_app K)
    ((CondensedRing.boundedConstructibleLowerShriekRefinementIso l
      (isPullback_geometricFiberLowerShriekRefinement (k₀ := k₀) f)
      (geometricFiberLowerShriekRefinement_hom_comp_overG (k₀ := k₀) f)).hom_inv_id_app _)
    ?pP _ _ ?hρ ?hι
  case hι => exact h
  case hρ =>
    rw [Category.assoc]
    transport_exact hρ

end AlgebraicGeometry.WeilComplex
