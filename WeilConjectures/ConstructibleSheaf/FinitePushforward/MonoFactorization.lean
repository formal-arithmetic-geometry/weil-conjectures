/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Limits.AffineOverLimitProperties
public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FiniteApproximation
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.MayerVietoris
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.MonoLimit
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.MonoPointFunctions
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.Presentation

/-!
# Maps into pushforwards along a limit of finite morphisms

Let `ν : Y ⟶ X` be presented as a cofiltered limit `Y = lim Dᵢ` of schemes `pᵢ : Dᵢ ⟶ X` finite
over `X` (a `Scheme.Hom.FiniteApproximation`, which exists for integral `ν` over a
quasi-compact quasi-separated `X`). Pulling back sections along `Y ⟶ Dᵢ` gives maps
`(pᵢ)_* M ⟶ ν_* M` of pushforwards of constant sheaves. Over a quasi-compact quasi-separated
étale `X`-scheme `V`, the sections of `ν_* M` are the filtered colimit of those of `(pᵢ)_* M`:
they are locally constant functions on `V ×_X Y = lim (V ×_X Dᵢ)`.

Since a constructible sheaf `F` is finitely presented by extensions by zero along étale maps
from affine schemes (Stacks 095N), every map `F ⟶ ν_* M` factors through some `(pᵢ)_* M`
(`AlgebraicGeometry.Etale.exists_comp_constantSheafPullbackMap_eq`). This is Step 5 of the proof
of Stacks 09Z6 in the blueprint (`lem-weil-pbc-constructible-finite-pushforward-noetherian`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] (M : ModuleCat.{u + 1} Λ) {X Y : Scheme.{u}}
  {ν : Y ⟶ X} (A : ν.FiniteApproximation)

section Sections

variable (V : X.Etale) [CompactSpace V.left] [QuasiSeparatedSpace V.left]

instance (i : A.I) : CompactSpace (pullback (A.p i) V.hom : Scheme.{u}) :=
  have : CompactSpace ((𝟭 Scheme.{u}).obj V.left) := ‹CompactSpace V.left›
  QuasiCompact.compactSpace_of_compactSpace (pullback.snd (A.p i) V.hom)

instance (i : A.I) : QuasiSeparatedSpace (pullback (A.p i) V.hom : Scheme.{u}) :=
  have : QuasiSeparatedSpace ((𝟭 Scheme.{u}).obj V.left) := ‹QuasiSeparatedSpace V.left›
  quasiSeparatedSpace_of_quasiSeparated (pullback.snd (A.p i) V.hom)

omit [CompactSpace V.left] [QuasiSeparatedSpace V.left] in
lemma pullbackSymmetry_inv_comp_pullbackConeπ (i : A.I) :
    (pullbackSymmetry ν V.hom).inv ≫
        pullback.map ν V.hom (A.p i) V.hom (A.π.app i) (𝟙 _) (𝟙 _) (by simp [A.π_p])
          (by simp) =
      pullbackLiftOfOver ν (A.p i) (A.π.app i) (A.π_p i) V ≫
        (pullbackSymmetry V.hom (A.p i)).hom := by
  apply pullback.hom_ext <;> simp

/-- **Sections of `ν_* M` come from a finite stage.** -/
theorem exists_constantSheafPullbackMap_app_eq
    (s : ((ν)_*[ModuleCat.{u + 1} Λ].obj
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).obj.obj (op V)) :
    ∃ (i : A.I) (t : ((A.p i)_*[ModuleCat.{u + 1} Λ].obj
      ((constantSheaf (A.D.obj i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).obj.obj
        (op V)),
      (constantSheafPullbackMap M ν (A.p i) (A.π.app i) (A.π_p i)).hom.app (op V) t = s := by
  let E := (Y.moduleConstantSheafToPointFunctionSheaf M).hom.app
    (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ ν).obj V)) s
  have hE : IsLocallyConstant (E : ↥(pullback V.hom ν) → M) :=
    isLocallyConstant_moduleConstantSheafToPointFunctionSheaf_app M Y _ s
  let hc := isLimitPullbackCone A.D A.isLimit A.p A.map_p ν A.π_p V.hom
  obtain ⟨i, G, hG, hEG⟩ := exists_isLocallyConstant_eq_comp_of_isLimit _ hc
    ((E : ↥(pullback V.hom ν) → M) ∘ (pullbackSymmetry ν V.hom).hom)
    (hE.comp_continuous (pullbackSymmetry ν V.hom).hom.continuous)
  obtain ⟨t, ht⟩ := exists_moduleConstantSheafToPointFunctionSheaf_app_eq M (A.D.obj i)
    ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ (A.p i)).obj V)
    (G ∘ (pullbackSymmetry V.hom (A.p i)).hom)
    (hG.comp_continuous (pullbackSymmetry V.hom (A.p i)).hom.continuous)
  refine ⟨i, t, injective_moduleConstantSheafToPointFunctionSheaf_app M Y _ (funext fun z ↦ ?_)⟩
  refine (constantSheafPullbackMap_apply M ν (A.p i) (A.π.app i) (A.π_p i) V t z).trans ?_
  rw [ht]
  have h₁ := congrFun hEG ((pullbackSymmetry ν V.hom).inv z)
  simp only [Function.comp_apply] at h₁
  rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id] at h₁
  refine Eq.trans ?_ h₁.symm
  change G ((pullbackLiftOfOver ν (A.p i) (A.π.app i) (A.π_p i) V ≫
    (pullbackSymmetry V.hom (A.p i)).hom) z) = G (((pullbackSymmetry ν V.hom).inv ≫ _) z)
  rw [pullbackSymmetry_inv_comp_pullbackConeπ]

omit [QuasiSeparatedSpace V.left] in
/-- **Sections vanishing on `ν_* M` vanish at a later finite stage.** -/
theorem exists_constantSheafPullbackMap_app_eq_zero {i : A.I}
    (t : ((A.p i)_*[ModuleCat.{u + 1} Λ].obj
      ((constantSheaf (A.D.obj i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).obj.obj
        (op V))
    (ht : (constantSheafPullbackMap M ν (A.p i) (A.π.app i) (A.π_p i)).hom.app (op V) t = 0) :
    ∃ (j : A.I) (f : j ⟶ i),
      (constantSheafPullbackMap M (A.p j) (A.p i) (A.D.map f) (A.map_p f)).hom.app (op V) t =
        0 := by
  let G := (A.D.obj i).moduleConstantSheafToPointFunctionSheaf M |>.hom.app
    (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ (A.p i)).obj V)) t
  have hG : IsLocallyConstant (G : ↥(pullback V.hom (A.p i)) → M) :=
    isLocallyConstant_moduleConstantSheafToPointFunctionSheaf_app M _ _ t
  have hG0 (z : ↥(pullback V.hom ν)) :
      G (pullbackLiftOfOver ν (A.p i) (A.π.app i) (A.π_p i) V z) = 0 := by
    have := congrFun (congrArg ((Y.moduleConstantSheafToPointFunctionSheaf M).hom.app
      (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ ν).obj V))) ht) z
    rw [map_zero] at this
    exact (constantSheafPullbackMap_apply M ν (A.p i) (A.π.app i) (A.π_p i) V t z).symm.trans
      this
  let hc := isLimitPullbackCone A.D A.isLimit A.p A.map_p ν A.π_p V.hom
  obtain ⟨j, f, hf⟩ := exists_comp_eq_zero_of_isLimit _ hc
    ((G : ↥(pullback V.hom (A.p i)) → M) ∘ (pullbackSymmetry V.hom (A.p i)).inv)
    (hG.comp_continuous (pullbackSymmetry V.hom (A.p i)).inv.continuous) (by
      have key₂ : (pullbackCone A.D A.p A.map_p (c := ⟨Y, A.π⟩) ν A.π_p V.hom).π.app i =
          (pullbackSymmetry ν V.hom).hom ≫
            pullbackLiftOfOver ν (A.p i) (A.π.app i) (A.π_p i) V ≫
              (pullbackSymmetry V.hom (A.p i)).hom := by
        rw [← pullbackSymmetry_inv_comp_pullbackConeπ, Iso.hom_inv_id_assoc]
      have key₃ : (pullbackCone A.D A.p A.map_p (c := ⟨Y, A.π⟩) ν A.π_p V.hom).π.app i ≫
          (pullbackSymmetry V.hom (A.p i)).inv =
            (pullbackSymmetry ν V.hom).hom ≫
              pullbackLiftOfOver ν (A.p i) (A.π.app i) (A.π_p i) V := by
        rw [key₂]
        simp
      funext w
      exact (congrArg G (congrArg (fun k ↦ k w) key₃)).trans (hG0 _))
  refine ⟨j, f, injective_moduleConstantSheafToPointFunctionSheaf_app M _ _ ?_⟩
  rw [map_zero]
  funext z
  refine (constantSheafPullbackMap_apply M (A.p j) (A.p i) (A.D.map f) (A.map_p f) V t z).trans ?_
  have h₁ := congrFun hf ((pullbackSymmetry V.hom (A.p j)).hom z)
  refine Eq.trans ?_ h₁
  have key : pullbackLiftOfOver (A.p j) (A.p i) (A.D.map f) (A.map_p f) V =
      (pullbackSymmetry V.hom (A.p j)).hom ≫ (pullbackDiagram A.D A.p A.map_p V.hom).map f ≫
        (pullbackSymmetry V.hom (A.p i)).inv := by
    apply pullback.hom_ext <;> simp
  change G _ = G (((pullbackSymmetry V.hom (A.p j)).hom ≫ _ ≫
    (pullbackSymmetry V.hom (A.p i)).inv) z)
  rw [← key]

end Sections

/-- The map `v_! Λ ⟶ F` given by the zero section is zero. -/
lemma sectionHom_zero (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {W : Scheme.{u}} (v : W ⟶ X) (h : AlgebraicGeometry.Etale v) :
    sectionHom F v h 0 = 0 := by
  have := sectionHom_comp (0 : F ⟶ F) v h 0
  rw [comp_zero, map_zero] at this
  exact this.symm

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- **Maps from a constructible sheaf into `ν_* M` factor through a finite stage.** Let
`ν : Y ⟶ X` be a cofiltered limit of finite `X`-schemes `pᵢ : Dᵢ ⟶ X`, with `X`
quasi-compact and quasi-separated, and let `F` be a constructible sheaf of `Λ`-modules, `Λ`
noetherian. Every map `ψ : F ⟶ ν_* M` factors as `F ⟶ (pᵢ)_* M ⟶ ν_* M` for some `i`. -/
theorem exists_comp_constantSheafPullbackMap_eq [IsNoetherianRing Λ] [CompactSpace X]
    [QuasiSeparatedSpace X] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F]
    (ψ : F ⟶ (ν)_*[ModuleCat.{u + 1} Λ].obj
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :
    ∃ (i : A.I) (θ : F ⟶ (A.p i)_*[ModuleCat.{u + 1} Λ].obj
      ((constantSheaf (A.D.obj i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)),
      θ ≫ constantSheafPullbackMap M ν (A.p i) (A.π.app i) (A.π_p i) = ψ := by
  classical
  obtain ⟨m, n, V, v, hv, hV, U, w, hw, hU, φ, π, hφπ, ⟨hc⟩⟩ :=
    exists_presentation_of_isConstructibleSheaf F
  let E₀ (k : Fin n) := (etaleLowerShriek (ModuleCat.{u + 1} Λ) (w k) (hw k)).obj
    ((constantSheaf (U k).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))
  let E₁ (l : Fin m) := (etaleLowerShriek (ModuleCat.{u + 1} Λ) (v l) (hv l)).obj
    ((constantSheaf (V l).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))
  let κ (i : A.I) := constantSheafPullbackMap M ν (A.p i) (A.π.app i) (A.π_p i)
  let τ {i j : A.I} (f : j ⟶ i) :=
    constantSheafPullbackMap M (A.p j) (A.p i) (A.D.map f) (A.map_p f)
  have hτκ {i j : A.I} (f : j ⟶ i) : τ f ≫ κ j = κ i := by
    refine (constantSheafPullbackMap_comp M _ _ _ _ _ _ _).trans
      (constantSheafPullbackMap_congr M _ _ _ _ ?_ _)
    simpa using (A.π.naturality f).symm
  have hττ {i j k : A.I} (f : j ⟶ i) (g : k ⟶ j) : τ f ≫ τ g = τ (g ≫ f) := by
    refine (constantSheafPullbackMap_comp M _ _ _ _ _ _ _).trans
      (constantSheafPullbackMap_congr M _ _ _ _ ?_ _)
    simp
  have hUc (k : Fin n) : CompactSpace (Etale.self (w k) (hw k)).left :=
    have := hU k
    inferInstanceAs (CompactSpace (U k))
  have hUs (k : Fin n) : QuasiSeparatedSpace (Etale.self (w k) (hw k)).left :=
    have := hU k
    inferInstanceAs (QuasiSeparatedSpace (U k))
  have hVc (l : Fin m) : CompactSpace (Etale.self (v l) (hv l)).left :=
    have := hV l
    inferInstanceAs (CompactSpace (V l))
  -- the sections of `ν_* M` given by `π ≫ ψ`, lifted to finite stages
  choose s hs using fun k ↦ sectionHom_surjective _ (w k) (hw k) (Sigma.ι E₀ k ≫ π ≫ ψ)
  choose i t ht using fun k ↦ exists_constantSheafPullbackMap_app_eq M A _ (s k)
  obtain ⟨j₀, a⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  replace a : ∀ k, j₀ ⟶ i k := fun k ↦ (@a (i k) (by simp)).some
  let θ' := Sigma.desc fun k ↦ sectionHom _ (w k) (hw k) ((τ (a k)).hom.app _ (t k))
  have hθ' : θ' ≫ κ j₀ = π ≫ ψ := by
    refine Sigma.hom_ext _ _ fun k ↦ ?_
    rw [Sigma.ι_desc_assoc, sectionHom_comp, ← hs k]
    congr 1
    rw [← ht k]
    exact congrArg (fun φ ↦ φ.hom.app _ (t k)) (hτκ (a k))
  -- the relations vanish at a later finite stage
  choose r hr using fun l ↦ sectionHom_surjective _ (v l) (hv l) (Sigma.ι E₁ l ≫ φ ≫ θ')
  have hr₀ (l : Fin m) : (κ j₀).hom.app _ (r l) = 0 := by
    apply sectionHom_injective _ (v l) (hv l)
    rw [sectionHom_zero, ← sectionHom_comp, hr l, Category.assoc, Category.assoc, hθ',
      ← Category.assoc φ, hφπ, zero_comp, comp_zero]
  choose j f hf using fun l ↦ exists_constantSheafPullbackMap_app_eq_zero M A _ (r l) (hr₀ l)
  obtain ⟨S, T, hT⟩ := IsCofiltered.inf_exists (insert j₀ (Finset.univ.image j))
    (Finset.univ.image fun l ↦ (⟨j l, j₀, by simp, by simp, f l⟩ :
      Σ' (X Y : A.I) (_ : X ∈ insert j₀ (Finset.univ.image j))
        (_ : Y ∈ insert j₀ (Finset.univ.image j)), X ⟶ Y))
  obtain ⟨c, hc'⟩ : ∃ c : S ⟶ j₀, ∀ l, ∃ g : S ⟶ j l, g ≫ f l = c :=
    ⟨T (by simp), fun l ↦ ⟨T (by simp), hT _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ l))⟩⟩
  have hθ'' : φ ≫ θ' ≫ τ c = 0 := by
    refine Sigma.hom_ext _ _ fun l ↦ ?_
    obtain ⟨g, hg⟩ := hc' l
    have h₁ : Sigma.ι E₁ l ≫ φ ≫ θ' ≫ τ c =
        sectionHom _ (v l) (hv l) ((τ c).hom.app _ (r l)) := by
      rw [← sectionHom_comp, hr l, Category.assoc, Category.assoc]
    have h₂ : (τ c).hom.app _ (r l) = 0 := by
      have e : τ c = τ (f l) ≫ τ g := by rw [hττ, hg]
      rw [e]
      exact (congrArg ((τ g).hom.app _) (hf l)).trans (map_zero _)
    rw [h₁, h₂, sectionHom_zero, comp_zero]
  refine ⟨S, hc.desc (CokernelCofork.ofπ (θ' ≫ τ c) hθ''), ?_⟩
  have : Epi π := epi_of_isColimit_cofork hc
  rw [← cancel_epi π]
  have hfac : π ≫ hc.desc (CokernelCofork.ofπ (θ' ≫ τ c) hθ'') = θ' ≫ τ c :=
    hc.fac (CokernelCofork.ofπ (θ' ≫ τ c) hθ'') WalkingParallelPair.one
  rw [← Category.assoc, hfac, Category.assoc, hτκ, hθ']

end AlgebraicGeometry.Etale
