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

section Skeleton

open Scheme

/-- DIM3 (to be proved). -/
lemma DIM3 {k : Type u} [Field k] {U : Scheme.{u}} [IsAffine U] (aU : U ⟶ Spec (.of k))
    [LocallyOfFiniteType aU] (y : U) :
    ∃ (r : ℕ) (p : U ⟶ Spec (.of (MvPolynomial (Fin r) k))),
      topologicalKrullDim (closure ({y} : Set U)) = r ∧
      p ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = aU ∧ (p y).asIdeal = ⊥ := sorry

/-- D1 (to be proved). -/
lemma D1 {k : Type u} [Field k] {Z : Scheme.{u}} (aZ : Z ⟶ Spec (.of k))
    [LocallyOfFiniteType aZ] (r : ℕ) (g : Z ⟶ Spec (.of (MvPolynomial (Fin r) k)))
    (hg : g ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = aZ)
    (η : Spec (.of (MvPolynomial (Fin r) k))) (hη : η.asIdeal = ⊥) :
    topologicalKrullDim (g ⁻¹' {η}) + r ≤ topologicalKrullDim Z := sorry

/-- FIELD (to be proved). -/
lemma FIELD {R : CommRingCat.{u}} [IsDomain R] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec R) (hs : (s.base (IsLocalRing.closedPoint Ω)).asIdeal = ⊥) :
    ∃ (K : Type u) (_ : Field K) (_ : IsSepClosed K),
      Nonempty (strictLocalization s ≅ Spec (.of K)) := sorry

/-- PB (to be proved). -/
lemma PB {XU U X Y W A : Scheme.{u}} (fU : XU ⟶ U) (ιX : XU ⟶ X) (ιU : U ⟶ Y) (f : X ⟶ Y)
    (h : IsPullback fU ιX ιU f) (p : U ⟶ A) (w : W ⟶ A) :
    IsPullback (pullback.snd w (fU ≫ p) ≫ ιX)
      (pullback.map w (fU ≫ p) w p (𝟙 _) fU (𝟙 _) (by simp) (by simp)) f
      (pullback.snd w p ≫ ιU) := sorry

variable [Finite Λ] {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]

theorem Etale.isZero_sheafFiber_higherDirectImage_of_isAffineOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [LocallyOfFiniteType f]
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [IsSeparated aY]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (N : ℕ)
    (hX : topologicalKrullDim X ≤ N) (U : Y.Opens) (hU : IsAffineOpen U) (y : U) (r : ℕ)
    (hr : topologicalKrullDim (closure ({y} : Set U)) = r) (q : ℤ) (hq : (N : ℤ) < q + r) :
    IsZero ((Y.uliftPointSmallEtale y.1).sheafFiber.obj (Etale.higherDirectImage Λ f q G)) := by
  have : IsAffine U := hU
  have : HasInvertibleExponent Λ Y := HasInvertibleExponent.of_hom aY
  obtain ⟨r', p, hr', hp, hpy⟩ := DIM3 (U.ι ≫ aY) y
  have hrr : r' = r := by
    have := hr'.symm.trans hr
    exact_mod_cast this
  subst hrr
  let XU : Scheme.{u} := f ⁻¹ᵁ U
  let fU : XU ⟶ U := f ∣_ U
  let f₀ : XU ⟶ Spec (.of (MvPolynomial (Fin r') k)) := fU ≫ p
  -- the geometric point and its lift to `U`
  let yb := Y.algClosurePoint y.1
  have hyb : Set.range yb.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [algClosurePoint_base]
    exact ⟨y, rfl⟩
  let yU := IsOpenImmersion.lift U.ι yb hyb
  have hyU : yU ≫ U.ι = yb := IsOpenImmersion.lift_fac _ _ _
  let sA := yU ≫ p
  -- the system of the `XU ×_{𝔸ʳ} V` over the affine pointed étale neighbourhoods of `sA`
  have : LocallySmall.{u} (AffinePointedEtaleNeighborhood sA) := ⟨fun _ _ ↦ small_self _⟩
  let I := InitiallySmall.CofilteredInitialModel.{u} (AffinePointedEtaleNeighborhood sA)
  let ιI := InitiallySmall.fromCofilteredInitialModel.{u} (AffinePointedEtaleNeighborhood sA)
  let D : I ⥤ Over X := ιI ⋙ affineNeighborhoodDiagramOver sA ⋙ Over.pullback f₀ ⋙
    Over.map (f ⁻¹ᵁ U).ι
  let c : Cone D := ((Over.map (f ⁻¹ᵁ U).ι).mapCone
    ((Over.pullback f₀).mapCone (strictLocalizationConeOver sA))).whisker ιI
  have hc : IsLimit ((Over.forget X).mapCone c) :=
    (Functor.Initial.isLimitWhiskerEquiv ιI _).symm (isLimitStrictLocalizationConePullback sA f₀)
  have hlim : IsZero ((Y.uliftPointSmallEtale y.1).sheafFiber.obj (Etale.higherDirectImage Λ
      (c.pt.hom ≫ f) q ((c.pt.hom)^*[ModuleCat.{u + 1} Λ].obj G))) := sorry
  have : IsAffine (f ⁻¹ᵁ U) := hU.preimage f
  have hDaff (i : I) : IsAffine (D.obj i).left := by
    have : IsAffine ((affineNeighborhoodDiagramOver sA).obj (ιI.obj i)).left := (ιI.obj i).2
    dsimp [D]
    infer_instance
  have (i : I) : IsAffineHom ((D.obj i).hom ≫ f) :=
    IsAffineHom.of_comp _ aY
  have : IsAffine c.pt.left := by
    change IsAffine (pullback (strictLocalizationToBase sA) f₀)
    infer_instance
  have : IsAffineHom (c.pt.hom ≫ f) := IsAffineHom.of_comp _ aY
  have : ∀ {i j : I} (φ : i ⟶ j), IsAffineHom (D.map φ).left := fun _ ↦ inferInstance
  have lim := Etale.higherDirectImage_limit Λ f G D c hc q y.1
  rw [ModuleCat.isZero_iff_subsingleton]
  suffices H : ∀ m : ((Y.uliftPointSmallEtale y.1).sheafFiber.obj
      (Etale.higherDirectImage Λ f q G) : ModuleCat.{u + 1} Λ), m = 0 from ⟨fun a b ↦ (H a).trans (H b).symm⟩
  intro m
  obtain ⟨j₀⟩ : Nonempty I := IsCofiltered.nonempty
  obtain ⟨j, φ, hφ⟩ := lim.2 j₀ (((Y.uliftPointSmallEtale y.1).sheafFiber.map
    (Etale.higherDirectImageTransition Λ (D.obj j₀).hom f _ rfl q G)).hom m)
    ((ModuleCat.isZero_iff_subsingleton.1 hlim).elim _ _)
  have hcomp := Etale.higherDirectImageTransition_comp_higherDirectImageOverMap Λ f G q
    (D.map φ)
  have h0 : ((Y.uliftPointSmallEtale y.1).sheafFiber.map
      (Etale.higherDirectImageTransition Λ (D.obj j).hom f _ rfl q G)).hom m = 0 := by
    rw [← hcomp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    exact hφ
  let W := (affineNeighborhoodDiagramOver sA).obj (ιI.obj j)
  have : Etale W.hom := (ιI.obj j).obj.1.prop
  let e : pullback W.hom p ⟶ Y := pullback.snd W.hom p ≫ U.ι
  have : Smooth e := inferInstance
  have hsq := PB fU (f ⁻¹ᵁ U).ι U.ι f (isPullback_morphismRestrict f U) p W.hom
  let wb : Spec (.of (AlgebraicClosure (Y.residueField y.1))) ⟶ W.left := (ιI.obj j).obj.2.left
  have hw : wb ≫ W.hom = sA := Over.w (ιI.obj j).obj.2
  let t := pullback.lift wb yU hw
  have hte : t ≫ e = Y.algClosurePoint y.1 := by simp [t, e, hyU, yb]
  have hinj := Etale.injective_sheafFiber_map_higherDirectImageTransition Λ f e
    (pullback.snd W.hom f₀ ≫ (f ⁻¹ᵁ U).ι) _ hsq G t q
  rw [hte] at hinj
  exact hinj (h0.trans (map_zero _).symm)

end Skeleton

end AlgebraicGeometry
