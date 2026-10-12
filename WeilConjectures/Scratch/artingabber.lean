module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
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

/-- The transition maps of higher direct images compose with the transition maps over `X`. -/
lemma Etale.higherDirectImageTransition_comp_higherDirectImageOverMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {U V : Over X} (φ : U ⟶ V) :
    Etale.higherDirectImageTransition Λ V.hom f (V.hom ≫ f) rfl q G ≫
        Etale.higherDirectImageOverMap Λ f G q φ =
      Etale.higherDirectImageTransition Λ U.hom f (U.hom ≫ f) rfl q G := by
  have h1 := Etale.homologyFunctor_map_overLowerStarTransition Λ f G q φ
  have h2 := Etale.lowerStarPlusTransition_comp Λ V.hom φ.left U.hom (Over.w φ) f (V.hom ≫ f)
    (U.hom ≫ f) rfl (by rw [← Category.assoc, Over.w]) rfl
    ((DerivedCategory.Plus.singleFunctor _ 0).obj G)
  simp only [Etale.higherDirectImageTransition, Functor.map_comp, Category.assoc]
  rw [← h1, ← Functor.map_comp_assoc, Etale.overLowerStarTransition, h2]

/-- A functor preserves split monomorphisms. -/
lemma isSplitMono_functor_map {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {A B : C}
    (φ : A ⟶ B) [IsSplitMono φ] : IsSplitMono (F.map φ) :=
  IsSplitMono.mk' ⟨F.map (retraction φ), by rw [← F.map_comp, IsSplitMono.id, F.map_id]⟩

/-- A natural isomorphism transports split monomorphisms. -/
lemma isSplitMono_map_of_iso {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (e : F ≅ G) {A B : C} (φ : A ⟶ B) [IsSplitMono (F.map φ)] : IsSplitMono (G.map φ) := by
  have h : G.map φ = e.inv.app A ≫ F.map φ ≫ e.hom.app B := by simp
  rw [h]
  infer_instance

open Scheme in
/-- The transition map of higher direct images along the base change `π : X' ⟶ X` of a smooth
`e : Y' ⟶ Y` is injective on the stalks at the geometric points of `Y` which lift to `Y'`. -/
theorem Etale.injective_sheafFiber_map_higherDirectImageTransition {X Y Y' X' : Scheme.{u}}
    [HasInvertibleExponent Λ Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (e : Y' ⟶ Y) [Smooth e]
    (π : X' ⟶ X) (f' : X' ⟶ Y') (sq : IsPullback π f' f e)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y') (q : ℤ) :
    Function.Injective (((pointSmallEtale (t ≫ e)).ulift.{u + 1}).sheafFiber.map
      (Etale.higherDirectImageTransition Λ π f (π ≫ f) rfl q G)).hom := by
  obtain ⟨n, hn, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := Y)
  have hs := Etale.isSplitMono_upperStar_map_lowerStarPlusTransition Λ f e π f' sq
    ((DerivedCategory.Plus.singleFunctor _ 0).obj G) fun j ↦
      IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero Λ n hn.ne' hΛ hu _
  let τ := Etale.lowerStarPlusTransition Λ π f (π ≫ f) rfl
    ((DerivedCategory.Plus.singleFunctor _ 0).obj G)
  have h₀ : IsSplitMono ((D+((e)^*[ModuleCat.{u + 1} Λ]) ⋙
      DerivedCategory.Plus.homologyFunctor _ q).map τ) :=
    isSplitMono_functor_map (DerivedCategory.Plus.homologyFunctor _ q) _
  have h₁ : IsSplitMono (((DerivedCategory.Plus.homologyFunctor _ q) ⋙
      (e)^*[ModuleCat.{u + 1} Λ]).map τ) :=
    isSplitMono_map_of_iso
      (((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q).symm τ
  have h₂ : IsSplitMono ((DerivedCategory.Plus.homologyFunctor _ q ⋙ (e)^*[ModuleCat.{u + 1} Λ] ⋙
      ((pointSmallEtale t).ulift.{u + 1}).sheafFiber).map τ) :=
    isSplitMono_functor_map ((pointSmallEtale t).ulift.{u + 1}).sheafFiber
      (((DerivedCategory.Plus.homologyFunctor _ q) ⋙ (e)^*[ModuleCat.{u + 1} Λ]).map τ)
  have h₃ : IsSplitMono ((DerivedCategory.Plus.homologyFunctor _ q ⋙
      ((pointSmallEtale (t ≫ e)).ulift.{u + 1}).sheafFiber).map τ) :=
    isSplitMono_map_of_iso (Functor.isoWhiskerLeft (DerivedCategory.Plus.homologyFunctor _ q)
      (Etale.upperStarCompUliftSheafFiberIso (ModuleCat.{u + 1} Λ) e t)) τ
  have h₄ : Mono (((pointSmallEtale (t ≫ e)).ulift.{u + 1}).sheafFiber.map
      ((DerivedCategory.Plus.homologyFunctor _ q).map τ)) := h₃.mono
  rw [← ModuleCat.mono_iff_injective, Etale.higherDirectImageTransition, Functor.map_comp,
    Functor.map_comp]
  have h₅ : Mono (((pointSmallEtale (t ≫ e)).ulift.{u + 1}).sheafFiber.mapIso
      ((DerivedCategory.Plus.homologyFunctor _ q).mapIso (R+((π ≫ f)_*[ModuleCat.{u + 1} Λ]).mapIso
        ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app G)))).hom :=
    inferInstance
  exact @mono_comp _ _ _ _ _ _ h₄ _ h₅

end AlgebraicGeometry
