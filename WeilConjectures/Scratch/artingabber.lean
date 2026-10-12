module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.TransitionComposition

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

open Scheme in
/-- After pullback along a smooth `e : Y' ⟶ Y`, the transition map `Rf_* K ⟶ R(π ≫ f)_* π^* K`
along the base change `π : X' ⟶ X` of `e` is a split monomorphism: by smooth base change it is
the transition map along `X' ×_Y Y' ⟶ X'` over `Y'`, which has the section `(𝟙, f')`. -/
theorem Etale.isSplitMono_upperStar_map_lowerStarPlusTransition {X Y Y' X' : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (e : Y' ⟶ Y) [Smooth e]
    (π : X' ⟶ X) (f' : X' ⟶ Y') (sq : IsPullback π f' f e)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : ∀ j, IsTorsionSheafOfInvertibleOrder Y
      ((DerivedCategory.Plus.homologyFunctor _ j).obj K)) :
    IsSplitMono (D+((e)^*[ModuleCat.{u + 1} Λ]).map
      (Etale.lowerStarPlusTransition Λ π f (π ≫ f) rfl K)) := by
  let e' := pullback.fst (π ≫ f) e
  let h' := pullback.snd (π ≫ f) e
  have sq'' : CommSq e' h' (π ≫ f) e := ⟨pullback.condition⟩
  let a : pullback (π ≫ f) e ⟶ X' := sq.lift (e' ≫ π) h' (by
    rw [Category.assoc]; exact pullback.condition)
  have wa : a ≫ π = e' ≫ π := sq.lift_fst _ _ _
  have wh : a ≫ f' = h' := sq.lift_snd _ _ _
  have key := Etale.baseChange_app_comp_targetTransitionPlus Λ sq.toCommSq π (π ≫ f) rfl sq''
    a wa wh K
  -- the section `σ = (𝟙, f')` of `a`
  let σ : X' ⟶ pullback (π ≫ f) e := pullback.lift (𝟙 X') f' (by
    rw [Category.id_comp]; exact sq.w)
  have hσe : σ ≫ e' = 𝟙 X' ≫ 𝟙 X' := by simp [σ, e']
  have hσh : σ ≫ h' = f' := by simp [σ, h']
  have hσa : σ ≫ a = 𝟙 X' := by
    apply sq.hom_ext
    · simp [a, σ, e']
      erw [Category.id_comp]
    · simp [a, σ, hσh, wh]
  have hcomp := Etale.targetTransitionPlus_comp Λ π f' π a e' h' wa wh (𝟙 X') σ (𝟙 X') f'
    hσe hσh π (𝟙 X') hσa (by simp) (by simp) (by simp) K
  have hiso := Etale.isIso_targetTransitionPlus Λ π f' π (𝟙 X') (𝟙 X') f' (by simp) (by simp) K
  have hT : IsSplitMono (Etale.targetTransitionPlus Λ π f' π a e' h' wa wh K) := by
    rw [← hcomp] at hiso
    have aux {C : Type (u + 2)} [Category.{u + 1} C] {A B D : C} (x : A ⟶ B) (y : B ⟶ D)
        (hxy : IsIso (x ≫ y)) : IsSplitMono x :=
      IsSplitMono.mk' ⟨y ≫ inv (x ≫ y), by rw [← Category.assoc, IsIso.hom_inv_id]⟩
    exact aux _ _ hiso
  have hBC := Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder Λ e sq K hK
  refine IsSplitMono.mk' (SplitMono.mk ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq'').app _ ≫
      retraction (Etale.targetTransitionPlus Λ π f' π a e' h' wa wh K) ≫
      inv ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)) ?_)
  rw [← Category.assoc, ← Category.assoc, ← key]
  simp

end AlgebraicGeometry
