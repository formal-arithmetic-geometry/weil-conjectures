/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.PolynomialAffineNoether
public import WeilConjectures.AlgebraicGeometry.PolynomialAffineSmooth
public import WeilConjectures.TraceFormula.OpenCover
public import WeilConjectures.TraceFormula.Specialization.ConstantFamilySpecializationGeneric
public import WeilConjectures.TraceFormula.Specialization.DeformationModelFactor
public import WeilConjectures.TraceFormula.Specialization.FiniteSupportConservative
public import WeilConjectures.TraceFormula.Specialization.NearbyFiniteness
public import WeilConjectures.TraceFormula.Specialization.TraitModelInstances
public import WeilConjectures.TraceFormula.Specialization.ZeroSectionAffine

/-!

# The specialization map of a constant family is an isomorphism

For `Y` separated of finite type over `k` and `L` bounded constructible on `Y` with
`ℚ̄_ℓ`-coefficients, the specialization map `σ_Y(L) : Lπ_Y^* L ⟶ Ψ_{Y × S}(L)` of the constant
family `Y × S` is an isomorphism (`ProEtale.CondensedRing.isIso_constantFamilySpecialization_app`).

## Proof

We first treat affine spaces `𝔸ᴺ_k`, by induction on `N`
(`ProEtale.CondensedRing.isIso_constantFamilySpecialization_app_polyAffine`).
* `σ_{𝔸ᴺ}(L)` is an isomorphism over a dense open `U ⊆ 𝔸ᴺ_k`
  (`ProEtale.CondensedRing.exists_dense_isIso_constantFamilySpecialization`). For `N = 0` the affine
  space is a point, so `U` is everything.
* For `N + 1`, after an automorphism `ψ` of `𝔸^{N+1}_k` the projection `q : 𝔸^{N+1}_k ⟶ 𝔸ᴺ_k`
  forgetting `X₀` is finite on `T = 𝔸^{N+1}_k ∖ U`
  (`AlgebraicGeometry.exists_isFinite_polyAffineProj_of_ne_univ`). Compactify `q` by
  `v : 𝔸^{N+1}_k ⟶ ℙ¹_{𝔸ᴺ_k}` and `q̄ : ℙ¹_{𝔸ᴺ_k} ⟶ 𝔸ᴺ_k`. The proper compatibility along `q̄` and
  the induction hypothesis show that `Rq̄_{s*} σ_{ℙ¹}(v_! L)` is an isomorphism, and the smooth
  compatibility along `v` identifies the restriction of `σ_{ℙ¹}(v_! L)` to `𝔸^{N+1}` with
  `σ_{𝔸^{N+1}}(L)`. So the cone of `σ_{ℙ¹}(v_! L)` is supported on `T ∪ (ℙ¹ ∖ 𝔸^{N+1})`, which is
  finite over `𝔸ᴺ_k`, and it vanishes because direct image is conservative on finite support
  (`ProEtale.CondensedRing.isIso_of_isIso_rightDerivedLowerStar_of_isFinite`).

An affine `Y` embeds into some `𝔸ᴺ_k` by a closed immersion `i`
(`ProEtale.CondensedRing.isIso_constantFamilySpecialization_app_of_isAffine`). The proper
compatibility identifies `Ri_{s*} σ_Y(L)` with `σ_{𝔸ᴺ}(Ri_* L)`, and `Ri_{s*}` reflects
isomorphisms. For a general `Y` the question is local for a finite affine open cover, by the smooth
compatibility.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section FiniteSupport

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **Direct image reflects isomorphisms with finite support**: let `q : Y ⟶ B` be a morphism of
separated `k`-schemes of finite type and `T ⊆ Y` a closed subset finite over `B`, the image of
`t : T' ⟶ Y` with `T' ⟶ B` finite. A morphism `φ` of bounded constructible complexes on `Y` which
is an isomorphism near every point outside `T` and such that `Rq_* φ` is an isomorphism is an
isomorphism. -/
theorem isIso_of_isIso_rightDerivedLowerStar_of_isFinite {Y B : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] (q : Y ⟶ B)
    {T : Scheme.{u}} (t : T ⟶ Y.left) [IsFinite (t ≫ q.left)]
    {E F : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))}
    (hE : boundedConstructible _ E) (hF : boundedConstructible _ F) (φ : E ⟶ F)
    (hφ : ∀ y ∉ Set.range t.base, ∃ (V : Scheme.{u}) (g : V ⟶ Y.left), IsOpenImmersion g ∧
      y ∈ Set.range g.base ∧ IsIso ((L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map φ))
    (hq : IsIso ((R((q.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).map φ)) :
    IsIso φ := by
  obtain ⟨C, a, b, hT⟩ := distinguished_cocone_triangle φ
  have hC : boundedConstructible _ C :=
    (boundedConstructible _).ext_of_isTriangulatedClosed₃ _ hT hE hF
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (isZero_of_isZero_rightDerivedLowerStar_of_isFinite q t ⟨C, hC⟩ (fun y hy ↦ ?_) ?_)
  · obtain ⟨V, g, hg, hyg, h⟩ := hφ y hy
    exact ⟨V, g, hg, hyg, (Triangle.isZero₃_iff_isIso₁ _
      ((L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map_distinguished _ hT)).2 h⟩
  · exact (Triangle.isZero₃_iff_isIso₁ _
      ((R((q.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).map_distinguished _ hT)).2 hq

end FiniteSupport

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']

/-- For `f : A ⟶ B` and `g : B ⟶ C` with `f ≫ g` finite, the composite of the maps of special
fibres of the constant families is finite: it is a base change of `f ≫ g`. -/
lemma isFinite_deformationSpecialFibreMap_comp {A B C : Over (Spec (.of k))} (f : A ⟶ B)
    (g : B ⟶ C) [IsFinite (f.left ≫ g.left)] :
    IsFinite ((deformationSpecialFibreMap f (siteIdeal_bot_map_appLE_le f.left ⊥) k').left ≫
      (deformationSpecialFibreMap g (siteIdeal_bot_map_appLE_le g.left ⊥) k').left) :=
  MorphismProperty.of_isPullback
    ((isPullback_deformationSpecialFibreMap_bot k' f _).paste_horiz
      (isPullback_deformationSpecialFibreMap_bot k' g _)).flip ‹_›

variable {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] in
/-- The source `Lπ_Y^* L` of the specialization map of a bounded constructible complex is bounded
constructible. -/
lemma boundedConstructible_leftDerivedUpperStar_constantSpecialFibreProj_obj
    (Y : Over (Spec (.of k))) (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructible _ ((L((constantSpecialFibreProj k' Y)^*⟦
      Profinite.padicAlgClRingObj ℓ⟧)).obj L.obj) :=
  boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ L.property

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The target `Ψ_{Y × S}(L)` of the specialization map of a bounded constructible complex is
bounded constructible. -/
lemma boundedConstructible_nearbyCycles_deformationModel_bot_obj (Y : Over (Spec (.of k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructible _ (((deformationModel Y ⊥ k').nearbyCycles
      (Profinite.padicAlgClRingObj ℓ)).obj L.obj) :=
  (deformationModel Y ⊥ k').preservesBoundedConstructible_of_isTraitModel
    (isTraitModel_deformationModel Y ⊥ k') (deformationModel_exists_comp_ε Y ⊥ k') L.obj
    L.property

/-- **Smooth pullback of the restricted specialization map**: for `g : A ⟶ B` smooth, `K` bounded
constructible on `B` and an open `W` of the special fibre of `A`, the restriction to `W` of
`σ_A(Lg^* K)` is an isomorphism if and only if that of `Lg_s^* σ_B(K)` is. -/
theorem isIso_map_constantFamilySpecialization_app_upperStar_iff_of_smooth
    {A B : Over (Spec (.of k))}
    [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] (g : A ⟶ B)
    [Smooth g.left] (K : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (W : (deformationSpecialFibre A ⊥ k').left.Opens) :
    IsIso ((L((W.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map
        ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ) A).app
          (L((g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj))) ↔
      IsIso ((L((W.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map
        (L(((deformationSpecialFibreMap g (siteIdeal_bot_map_appLE_le g.left ⊥) k').left)^*⟦
          Profinite.padicAlgClRingObj ℓ⟧).map
          ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ) B).app K.obj))) := by
  have : Smooth (deformationModelHom g (siteIdeal_bot_map_appLE_le g.left ⊥) k').total :=
    smooth_deformationTotalMap k' g (siteIdeal_bot_map_appLE_le g.left ⊥)
      (IdealSheafData.comap_bot _).symm
  have hα := isIso_pullbackExchange_deformationModel_app_of_smooth k'
    (deformationModelHom g (siteIdeal_bot_map_appLE_le g.left ⊥) k')
    (isPullback_deformationGenericMap _ _ k') K.property
  have h := map_constantFamilySpecialization_app_comp_pullbackExchange_app k'
    (Profinite.padicAlgClRingObj ℓ) g K.obj
  have h' := (L((W.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).congr_map h
  simp only [Functor.map_comp] at h'
  revert hα h'
  normalize_precoherent
  intro hα h'
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk' _ _ (asIso _) (asIso _) h'.symm)).symm

/-- **Restricting along a smooth pullback**: for `g : A ⟶ B` smooth, `K` bounded constructible on
`B`, `L ≅ Lg^* K` and an open `W` of the special fibre of `A` over which `σ_A(L)` is invertible,
`σ_B(K)` is invertible over the open immersion `W ⟶ A_s ⟶ B_s`. -/
theorem isIso_map_constantFamilySpecialization_app_of_smooth {A B : Over (Spec (.of k))}
    [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] (g : A ⟶ B)
    [Smooth g.left] (K : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology A.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) A.left))}
    (e : L ≅ (L((g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K.obj)
    (W : (deformationSpecialFibre A ⊥ k').left.Opens)
    (hW : IsIso ((L((W.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map
        ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ) A).app L))) :
    IsIso ((L((W.ι ≫ (deformationSpecialFibreMap g (siteIdeal_bot_map_appLE_le g.left ⊥)
      k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map
        ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ) B).app K.obj)) := by
  have h₁ := (isoLocus_restrictedConstantFamilySpecialization_iff k' _ A _ _).1
    ((restrictedConstantFamilySpecialization k' _ A W).isoLocus.prop_of_iso e
      ((isoLocus_restrictedConstantFamilySpecialization_iff k' _ A _ _).2 hW))
  have h₂ := isIso_map_constantFamilySpecialization_app_upperStar_iff_of_smooth k' g K W
  have key : IsIso ((L((W.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map
      ((L(((deformationSpecialFibreMap g (siteIdeal_bot_map_appLE_le g.left ⊥) k').left)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).map
          ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ) B).app K.obj))) := by
    revert h₁ h₂
    normalize_precoherent
    intro h₁ h₂
    exact h₂.1 h₁
  exact (NatIso.isIso_map_iff (leftDerivedUpperStarComp _ W.ι _) _).2 key

/-- **Inductive step for affine spaces**: let `ψ` be an automorphism of `𝔸^{N+1}_k` and
`v : 𝔸^{N+1}_k ⟶ ℙ¹_{𝔸ᴺ_k}` the composite of `ψ` and the compactification of `X₀`.
If `σ_{𝔸ᴺ}` is invertible, `σ_{𝔸^{N+1}}(L)` is invertible over an open `U ⊆ 𝔸^{N+1}_k`, and the
complement of `U` lies in the image of some `a : V ⟶ 𝔸^{N+1}_k` with `V ⟶ 𝔸ᴺ_k` finite, then
`σ_{𝔸^{N+1}}(L)` is an isomorphism. -/
theorem isIso_constantFamilySpecialization_app_of_isFinite (N : ℕ)
    (ih : ∀ K : Dᵇc((polyAffine k N).left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      IsIso ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ)
        (polyAffine k N)).app K.obj))
    (ψ : polyAffine k (N + 1) ≅ polyAffine k (N + 1)) {V : Scheme.{u}}
    (a : V ⟶ (polyAffine k (N + 1)).left)
    (hfin : IsFinite (a ≫ ψ.hom.left ≫ (polyAffineProj k N).left))
    (L₀ : Dᵇc((polyAffine k (N + 1)).left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (U : (polyAffine k (N + 1)).left.Opens)
    (hU : IsIso ((L((((constantSpecialFibreProj k' (polyAffine k (N + 1))) ⁻¹ᵁ U).ι)^*⟦
      Profinite.padicAlgClRingObj ℓ⟧)).map ((constantFamilySpecialization k'
        (Profinite.padicAlgClRingObj ℓ) (polyAffine k (N + 1))).app L₀.obj)))
    (hY : (U : Set (polyAffine k (N + 1)).left)ᶜ ⊆ Set.range a.base) :
    IsIso ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ)
      (polyAffine k (N + 1))).app L₀.obj) := by
  let Λ := Profinite.padicAlgClRingObj ℓ
  let P := polyAffine k (N + 1)
  let P' := overProjectiveLine (polyAffine k N)
  let p := overProjectiveLineProj (polyAffine k N)
  let v := ψ.hom ≫ polyAffineChart k N
  have : IsIso ψ.hom.left := inferInstanceAs (IsIso ((Over.forget _).map ψ.hom))
  have : IsOpenImmersion v.left :=
    inferInstanceAs (IsOpenImmersion (ψ.hom.left ≫ (polyAffineChart k N).left))
  let L := (boundedConstructibleOpenImmersionLowerShriek Λ ℓ v).obj L₀
  let φ := (constantFamilySpecialization k' Λ P').app L.obj
  let vs := (deformationSpecialFibreMap v (siteIdeal_bot_map_appLE_le v.left ⊥) k').left
  -- `Lv^* L ≅ L₀`
  let e₀ : L₀.obj ≅ (L((v.left)^*⟦Λ⟧)).obj L.obj := (boundedConstructible _).ι.mapIso
    (asIso ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ v).unit.app L₀))
  -- it suffices to show that `φ = σ_{ℙ¹}(L)` is an isomorphism
  suffices hφ : IsIso φ by
    rw [NatTrans.isIso_app_iff_of_iso _ e₀,
      isIso_constantFamilySpecialization_app_upperStar_iff_of_smooth k' v L]
    infer_instance
  -- the proper compatibility along `p` and the induction hypothesis: `Rp_{s*} φ` is invertible
  have hq : IsIso ((R(((deformationSpecialFibreMap p (siteIdeal_bot_map_appLE_le p.left ⊥)
      k').left)_*⟦Λ⟧)).map φ) := by
    rw [← isIso_constantFamilySpecialization_app_lowerStar_iff_of_isProper k' p L]
    exact ih ((boundedConstructibleLowerStar ℓ p).obj L)
  -- the closed subset `T ∪ (ℙ¹ ∖ 𝔸^{N+1})` of the special fibre, finite over `𝔸ᴺ ⊗ k'`
  let aO : Over.mk (a ≫ P.hom) ⟶ P' :=
    Over.homMk (a ≫ v.left) (by rw [Category.assoc, Over.w v]; rfl)
  let inf := overProjectiveLineInfinity (polyAffine k N)
  have : IsFinite (inf.left ≫ p.left) := by
    rw [← Over.comp_left, overProjectiveLineInfinity_proj]
    exact inferInstanceAs (IsFinite (𝟙 _))
  have : IsFinite (aO.left ≫ p.left) := by
    have h : aO.left ≫ p.left = a ≫ ψ.hom.left ≫ (polyAffineProj k N).left := by
      rw [← polyAffineChart_proj]
      rfl
    rw [h]
    exact hfin
  let t₁ := (deformationSpecialFibreMap inf (siteIdeal_bot_map_appLE_le inf.left ⊥) k').left
  let t₂ := (deformationSpecialFibreMap aO (siteIdeal_bot_map_appLE_le aO.left ⊥) k').left
  let ps := (deformationSpecialFibreMap p (siteIdeal_bot_map_appLE_le p.left ⊥) k').left
  have : IsFinite (t₁ ≫ ps) := isFinite_deformationSpecialFibreMap_comp k' inf p
  have : IsFinite (t₂ ≫ ps) := isFinite_deformationSpecialFibreMap_comp k' aO p
  have : IsFinite (coprod.desc t₁ t₂ ≫ ps) := by
    rw [coprod.desc_comp]
    infer_instance
  refine isIso_of_isIso_rightDerivedLowerStar_of_isFinite
    (deformationSpecialFibreMap p (siteIdeal_bot_map_appLE_le p.left ⊥) k') (coprod.desc t₁ t₂)
    (boundedConstructible_leftDerivedUpperStar_constantSpecialFibreProj_obj k' P' L)
    (boundedConstructible_nearbyCycles_deformationModel_bot_obj k' P' L) φ ?_ hq
  -- the support condition
  intro y hy
  have hy₁ : y ∉ Set.range t₁.base := fun h ↦ hy (range_subset_range_coprod_desc_left _ _ h)
  have hy₂ : y ∉ Set.range t₂.base := fun h ↦ hy (range_subset_range_coprod_desc_right _ _ h)
  rw [Scheme.range_snd_of_isPullback (isPullback_deformationSpecialFibreMap_bot k' inf
    (siteIdeal_bot_map_appLE_le inf.left ⊥)).flip] at hy₁
  rw [Scheme.range_snd_of_isPullback (isPullback_deformationSpecialFibreMap_bot k' aO
    (siteIdeal_bot_map_appLE_le aO.left ⊥)).flip] at hy₂
  -- `y` lies over the affine chart
  have hyv : y ∈ Set.range vs.base := by
    rw [Scheme.range_snd_of_isPullback (isPullback_deformationSpecialFibreMap_bot k' v
      (siteIdeal_bot_map_appLE_le v.left ⊥)).flip]
    have h₂ : Set.range v.left.base = Set.range (polyAffineChart k N).left.base := by
      change Set.range (ψ.hom.left ≫ (polyAffineChart k N).left).base = _
      rw [← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_comp_of_isIso,
        Scheme.Hom.coe_opensRange]
    change constantSpecialFibreProj k' P' y ∈ Set.range v.left.base
    rw [h₂, range_polyAffineChart]
    exact hy₁
  obtain ⟨x, rfl⟩ := hyv
  have : IsOpenImmersion vs := isOpenImmersion_deformationSpecialFibreMap_of_isOpenImmersion _ _ k'
    (IdealSheafData.comap_bot _).symm
  by_cases hx : constantSpecialFibreProj k' P x ∈ U
  · -- over `U` the specialization map is invertible
    refine ⟨_, ((constantSpecialFibreProj k' P) ⁻¹ᵁ U).ι ≫ vs, inferInstance, ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    exact isIso_map_constantFamilySpecialization_app_of_smooth k' v L e₀ _ hU
  · -- outside `U`, the point lies over `a`
    refine absurd ?_ hy₂
    change constantSpecialFibreProj k' P' (vs x) ∈ Set.range (a ≫ v.left).base
    have hc : constantSpecialFibreProj k' P' (vs x) = v.left (constantSpecialFibreProj k' P x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        (isPullback_deformationSpecialFibreMap_bot k' v (siteIdeal_bot_map_appLE_le v.left ⊥)).w]
    obtain ⟨z, hz⟩ := hY hx
    exact ⟨z, by rw [hc, Scheme.Hom.comp_apply, hz]⟩

/-- The base case `N = 0` of
`ProEtale.CondensedRing.isIso_constantFamilySpecialization_app_polyAffine`: for `L` bounded
constructible on the point `𝔸⁰_k`, `σ_{𝔸⁰}(L)` is an isomorphism. -/
theorem isIso_constantFamilySpecialization_app_polyAffine_zero
    (L : Dᵇc((polyAffine k 0).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ)
      (polyAffine k 0)).app L.obj) := by
  obtain ⟨U, hUd, hU⟩ := exists_dense_isIso_constantFamilySpecialization k' (polyAffine k 0) L
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have : Subsingleton (polyAffine k 0).left :=
    (polyAffine k 0).hom.homeomorph.injective.subsingleton
  have hU' : U = ⊤ := by
    refine SetLike.coe_injective (Set.eq_univ_of_forall fun x ↦ ?_)
    obtain ⟨y, hy⟩ := hUd.nonempty
    exact Subsingleton.elim y x ▸ hy
  subst hU'
  let F := deformationSpecialFibre (polyAffine k 0) ⊥ k'
  have : IsLocallyNoetherian F.left := LocallyOfFiniteType.isLocallyNoetherian F.hom
  have : CompactSpace F.left := QuasiCompact.compactSpace_of_compactSpace F.hom
  have : IsNoetherian F.left := ⟨⟩
  have hP := jointlyReflectIsomorphisms_leftDerivedUpperStar_of_cover
    (Profinite.padicAlgClRingObj ℓ) (fun _ : Unit ↦ (constantSpecialFibreProj k'
      (polyAffine k 0) ⁻¹ᵁ ⊤).ι) (fun x ↦ ⟨(), by simp⟩)
  have (_ : Unit) := hU
  exact hP.isIso _

/-- **The constant family of affine space** : for `L` bounded constructible on `𝔸ᴺ_k`, the
specialization map `σ_{𝔸ᴺ}(L) : Lπ^* L ⟶ Ψ_{𝔸ᴺ × S}(L)` is an isomorphism. -/
theorem isIso_constantFamilySpecialization_app_polyAffine (N : ℕ)
    (L : Dᵇc((polyAffine k N).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ)
      (polyAffine k N)).app L.obj) := by
  induction N with
  | zero => exact isIso_constantFamilySpecialization_app_polyAffine_zero k' L
  | succ N ih =>
    obtain ⟨U, hUd, hU⟩ :=
      exists_dense_isIso_constantFamilySpecialization k' (polyAffine k (N + 1)) L
    have hne : (U : Set (polyAffine k (N + 1)).left)ᶜ ≠ Set.univ := by
      intro h
      obtain ⟨x, hx⟩ := hUd.nonempty
      exact (Set.eq_univ_iff_forall.1 h x) hx
    obtain ⟨ψ, V, a, hYa, hfin⟩ :=
      exists_isFinite_polyAffineProj_of_ne_univ N U.isOpen.isClosed_compl hne
    exact isIso_constantFamilySpecialization_app_of_isFinite k' N ih ψ a hfin L U hU hYa

variable {A : Over (Spec (.of k))} [LocallyOfFiniteType A.hom] [QuasiCompact A.hom]
  [IsSeparated A.hom]

/-- **The constant family of an affine scheme**: for `Y` affine of finite type over `k` and `L`
bounded constructible on `Y`, `σ_Y(L)` is an isomorphism. -/
theorem isIso_constantFamilySpecialization_app_of_isAffine [IsAffine A.left]
    (L : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ) A).app L.obj) := by
  obtain ⟨N, i, _⟩ := exists_isClosedImmersion_polyAffine A
  have hg := siteIdeal_bot_map_appLE_le i.left ⊥
  have h := isIso_constantFamilySpecialization_app_polyAffine k' N
    ((boundedConstructibleLowerStar ℓ i).obj L)
  rw [show ((boundedConstructibleLowerStar ℓ i).obj L).obj =
    R((i.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj L.obj from rfl,
    isIso_constantFamilySpecialization_app_lowerStar_iff_of_isProper k' i L] at h
  have : IsClosedImmersion (deformationSpecialFibreMap i hg k').left :=
    MorphismProperty.of_isPullback (isPullback_deformationSpecialFibreMap_bot k' i hg).flip
      inferInstance
  exact ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
    (deformationSpecialFibreMap i hg k').left).fullyFaithfulROfIsIsoCounit).isIso_of_isIso_map _

/-- **Nearby cycles of a constant family**: for
`Y` separated of finite type over `k` and `L` bounded constructible on `Y`, the specialization map
`σ_Y(L) : Lπ_Y^* L ⟶ Ψ_{Y × S}(L)` is an isomorphism. -/
theorem isIso_constantFamilySpecialization_app (L : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ) A).app L.obj) := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  choose U hU hxU _ using fun x : A.left ↦ exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : A.left.Opens) from trivial)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : A.left ↦ ((U x : A.left.Opens) :
    Set A.left)) (fun x ↦ (U x).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  let V (a : t) := overRestrict A (U a.1)
  let g (a : t) : V a ⟶ A := overRestrictι A (U a.1)
  have hg (a : t) := siteIdeal_bot_map_appLE_le (g a).left ⊥
  have hV (a : t) : IsAffine (V a).left := hU a.1
  have h (a : t) : IsIso (L(((deformationSpecialFibreMap (g a) (hg a) k').left)^*⟦
      Profinite.padicAlgClRingObj ℓ⟧).map
        ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ) A).app L.obj)) := by
    rw [← isIso_constantFamilySpecialization_app_upperStar_iff_of_smooth k' (g a) L]
    exact isIso_constantFamilySpecialization_app_of_isAffine k'
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (g a)).obj L)
  have (a : t) : QuasiCompact (deformationSpecialFibreMap (g a) (hg a) k').left :=
    MorphismProperty.of_isPullback (isPullback_deformationSpecialFibreMap_bot k' (g a) (hg a)).flip
      inferInstance
  have := h
  refine (jointlyReflectIsomorphisms_leftDerivedUpperStar_of_cover
    (Profinite.padicAlgClRingObj ℓ) (fun a ↦ (deformationSpecialFibreMap (g a) (hg a) k').left)
    fun p ↦ ?_).isIso _
  obtain ⟨x, hx, hpx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (constantSpecialFibreProj k' A p)))
  refine ⟨⟨x, hx⟩, ?_⟩
  rw [Scheme.range_snd_of_isPullback
    (isPullback_deformationSpecialFibreMap_bot k' (g _) (hg _)).flip]
  change constantSpecialFibreProj k' A p ∈ Set.range (U x).ι.base
  rw [(U x).range_ι]
  exact hpx

end AlgebraicGeometry.ProEtale.CondensedRing
