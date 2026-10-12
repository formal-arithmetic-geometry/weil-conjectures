/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.ShiftedHomPresheaf
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.StageCohomology

/-!
# Higher direct images and limits of schemes

Let `k : B ⟶ S` be a morphism of schemes, `G` a sheaf of `Λ`-modules on `B_ét` and
`T = lim Tᵢ` a cofiltered limit of schemes over `B` with affine transition morphisms, all
quasi-compact and quasi-separated over `S`. Then `colimᵢ R^q gᵢ_* (G|_{Tᵢ}) ≅ R^q g_* (G|_T)`,
where `gᵢ : Tᵢ ⟶ S` and `g : T ⟶ S` are the structure morphisms
(`AlgebraicGeometry.Etale.higherDirectImage_limit`, Stacks `09Z1`).

## Proof

The stalk of `R^q g_* (G|_T) = H^q(Rg_*(G|_T))` at a geometric point is the colimit, over the
étale neighbourhoods `W` of the point, of `Hom(Λ_S[W][0], (Rg_*(G|_T))⟦q⟧)`
(`AlgebraicGeometry.Etale.shiftedHomPresheafToSheaf` is locally bijective), and the affine
neighbourhoods are cofinal. For `W` affine, `Hom(Λ_S[W][0], (Rg_*(G|_T))⟦q⟧)` is the cohomology
of `T ×_S W` (`AlgebraicGeometry.Etale.stageCohomologyEquiv`), compatibly with the transition
maps, and `T ×_S W = lim Tᵢ ×_S W` is a cofiltered limit of quasi-compact quasi-separated
schemes with affine transition morphisms; so the claim follows from the continuity of étale
cohomology (`AlgebraicGeometry.Etale.overCohomologyMap_isColimit_of_isLimit`).

## References

- Stacks Project, Lemma 59.51.7, <https://stacks.math.columbia.edu/tag/09Z1>
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

section Point

/-- Every étale neighbourhood of a geometric point is refined by an affine one. -/
lemma Scheme.exists_isAffine_uliftPointSmallEtale_fiber {S : Scheme.{u}} (s : S) {V : S.Etale}
    (v : (S.uliftPointSmallEtale s).fiber.obj V) :
    ∃ (V' : S.Etale) (f : V' ⟶ V) (v' : (S.uliftPointSmallEtale s).fiber.obj V'),
      (S.uliftPointSmallEtale s).fiber.map f v' = v ∧ IsAffine V'.left := by
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp V.left.isBasis_affineOpens
    (show v.down.left (IsLocalRing.closedPoint _) ∈ (⊤ : V.left.Opens) from trivial)
  have hr : Set.range v.down.left ⊆ (U : Set V.left) := by
    rintro _ ⟨z, rfl⟩
    have : Subsingleton (Spec (.of (AlgebraicClosure (S.residueField s)))) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum _))
    rwa [show z = IsLocalRing.closedPoint _ from @Subsingleton.elim _ this z _]
  obtain ⟨v', hv'⟩ := exists_ulift_pointSmallEtale_fiber_ofOpens (S.algClosurePoint s) v U hr
  exact ⟨_, Etale.ofOpensι V U, v', hv', hU⟩

end Point

section Sections

variable {S : Scheme.{u}}
  (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (q : ℤ)

/-- The section of `H^q(L)` over `W` given by a class `Λ_S[W][0] ⟶ L⟦q⟧`. -/
noncomputable abbrev Etale.shiftedHomSection {W : S.Etale}
    (x : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ S).obj W) ⟶ L⟦q⟧) :
    ToType (((DerivedCategory.Plus.homologyFunctor _ q).obj L).obj.obj (op W)) :=
  (Etale.shiftedHomPresheafToSheaf L q).app (op W) x

lemma Etale.shiftedHomSection_map {W W' : S.Etale} (g : W' ⟶ W)
    (x : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ S).obj W) ⟶ L⟦q⟧) :
    Etale.shiftedHomSection Λ L q
        ((DerivedCategory.Plus.singleFunctor _ 0).map ((Etale.freeSheaf Λ S).map g) ≫ x) =
      ((DerivedCategory.Plus.homologyFunctor _ q).obj L).obj.map g.op
        (Etale.shiftedHomSection Λ L q x) :=
  ConcreteCategory.congr_hom ((Etale.shiftedHomPresheafToSheaf L q).naturality g.op) x

lemma Etale.shiftedHomSection_comp {L' : DerivedCategory.Plus
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (f : L ⟶ L') {W : S.Etale}
    (x : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ S).obj W) ⟶ L⟦q⟧) :
    Etale.shiftedHomSection Λ L' q (x ≫ f⟦q⟧') =
      ((DerivedCategory.Plus.homologyFunctor _ q).map f).hom.app (op W)
        (Etale.shiftedHomSection Λ L q x) :=
  Etale.shiftedHomPresheafToSheaf_app_comp f q (op W) x

variable (s : S)

/-- Every section of `H^q(L)` near a geometric point comes, on an affine étale neighbourhood,
from a class `Λ_S[W][0] ⟶ L⟦q⟧`. -/
lemma Etale.exists_shiftedHomSection {W : S.Etale}
    (σ : ToType (((DerivedCategory.Plus.homologyFunctor _ q).obj L).obj.obj (op W)))
    (w : (S.uliftPointSmallEtale s).fiber.obj W) :
    ∃ (W' : S.Etale) (g : W' ⟶ W) (w' : (S.uliftPointSmallEtale s).fiber.obj W')
      (x : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ S).obj W') ⟶ L⟦q⟧),
      (S.uliftPointSmallEtale s).fiber.map g w' = w ∧ IsAffine W'.left ∧
        Etale.shiftedHomSection Λ L q x =
          ((DerivedCategory.Plus.homologyFunctor _ q).obj L).obj.map g.op σ := by
  obtain ⟨_, _⟩ := Etale.isLocallyBijective_shiftedHomPresheafToSheaf L q
  obtain ⟨W₁, g₁, ⟨t, ht⟩, w₁, rfl⟩ := (S.uliftPointSmallEtale s).jointly_surjective _
    (Presheaf.imageSieve_mem S.smallEtaleTopology (Etale.shiftedHomPresheafToSheaf L q)
      (U := op W) σ) w
  obtain ⟨W₂, g₂, w₂, rfl, hW₂⟩ := Scheme.exists_isAffine_uliftPointSmallEtale_fiber s w₁
  refine ⟨W₂, g₂ ≫ g₁, w₂, (Etale.shiftedHomPresheaf Λ L q).map g₂.op t, by simp, hW₂, ?_⟩
  have h := ConcreteCategory.congr_hom ((Etale.shiftedHomPresheafToSheaf L q).naturality g₂.op) t
  refine h.trans ?_
  simp only [ConcreteCategory.comp_apply] at ht ⊢
  rw [ht]
  change _ = ((DerivedCategory.Plus.homologyFunctor _ q).obj L).obj.map (g₁.op ≫ g₂.op) σ
  rw [Functor.map_comp]
  rfl

/-- A class `Λ_S[W][0] ⟶ L⟦q⟧` whose section of `H^q(L)` vanishes vanishes on an affine étale
neighbourhood of any geometric point. -/
lemma Etale.exists_eq_zero_of_shiftedHomSection_eq_zero {W : S.Etale}
    (x : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ S).obj W) ⟶ L⟦q⟧)
    (hx : Etale.shiftedHomSection Λ L q x = 0) (w : (S.uliftPointSmallEtale s).fiber.obj W) :
    ∃ (W' : S.Etale) (g : W' ⟶ W) (w' : (S.uliftPointSmallEtale s).fiber.obj W'),
      (S.uliftPointSmallEtale s).fiber.map g w' = w ∧ IsAffine W'.left ∧
        (DerivedCategory.Plus.singleFunctor _ 0).map ((Etale.freeSheaf Λ S).map g) ≫ x = 0 := by
  obtain ⟨_, _⟩ := Etale.isLocallyBijective_shiftedHomPresheafToSheaf L q
  have h0 : (Etale.shiftedHomPresheafToSheaf L q).app (op W) x =
      (Etale.shiftedHomPresheafToSheaf L q).app (op W) 0 := by
    rw [map_zero]; exact hx
  obtain ⟨W₁, g₁, hg₁, w₁, rfl⟩ := (S.uliftPointSmallEtale s).jointly_surjective _
    (Presheaf.equalizerSieve_mem S.smallEtaleTopology (Etale.shiftedHomPresheafToSheaf L q)
      x 0 h0) w
  obtain ⟨W₂, g₂, w₂, rfl, hW₂⟩ := Scheme.exists_isAffine_uliftPointSmallEtale_fiber s w₁
  refine ⟨W₂, g₂ ≫ g₁, w₂, by simp, hW₂, ?_⟩
  have h₁ : (DerivedCategory.Plus.singleFunctor _ 0).map ((Etale.freeSheaf Λ S).map g₁) ≫ x = 0 :=
    hg₁.trans (map_zero _)
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, h₁, Limits.comp_zero]

end Sections

section Limit

variable {S B : Scheme.{u}} (k : B ⟶ S) (G : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over B)
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
  [∀ i, QuasiCompact ((D.obj i).hom ≫ k)] [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
  (c : Cone D) (hc : IsLimit ((Over.forget B).mapCone c))
  [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)] (q : ℤ)

/-- The derived direct image `R(U ⟶ S)_*(U^*(G[0]))`, for `U` over `B`. -/
noncomputable abbrev Etale.overLowerStar (U : Over B) :
    DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  R+((U.hom ≫ k)_*[ModuleCat.{u + 1} Λ]).obj
    (D+((U.hom)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G))

/-- The transition map `R(U ⟶ S)_*(U^*(G[0])) ⟶ R(U' ⟶ S)_*(U'^*(G[0]))` along `φ : U' ⟶ U`
over `B`. -/
noncomputable abbrev Etale.overLowerStarMap {U U' : Over B} (φ : U' ⟶ U) :
    Etale.overLowerStar Λ k G U ⟶ Etale.overLowerStar Λ k G U' :=
  Etale.overLowerStarTransition Λ k U.hom U'.hom φ.left (Over.w φ)
    ((DerivedCategory.Plus.singleFunctor _ 0).obj G)

include hc in
/-- **Continuity of the classes `Λ_S[W][0] ⟶ (Rg_*(G|_T))⟦q⟧` along `T = lim Tᵢ`**, for an
étale `S`-scheme `W` which is affine: they are the filtered colimit of the corresponding classes
for the `Tᵢ`, along the transition maps. -/
theorem Etale.overLowerStarMap_isColimit (W : S.Etale) [IsAffine W.left] :
    (∀ y : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ S).obj W) ⟶
        (Etale.overLowerStar Λ k G c.pt)⟦q⟧,
      ∃ (i : I) (x : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ S).obj W) ⟶
          (Etale.overLowerStar Λ k G (D.obj i))⟦q⟧),
        x ≫ (Etale.overLowerStarMap Λ k G (c.π.app i))⟦q⟧' = y) ∧
    ∀ (i : I) (x : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ S).obj W) ⟶
        (Etale.overLowerStar Λ k G (D.obj i))⟦q⟧),
      x ≫ (Etale.overLowerStarMap Λ k G (c.π.app i))⟦q⟧' = 0 →
        ∃ (j : I) (f : j ⟶ i), x ≫ (Etale.overLowerStarMap Λ k G (D.map f))⟦q⟧' = 0 := by
  have : ∀ i, CompactSpace ((D ⋙ Etale.stageFunctor (Etale.isPullback_stageBase k W)).obj
      i).left := fun i ↦ inferInstanceAs (CompactSpace (pullback ((D.obj i).hom ≫ k) W.hom))
  have : ∀ i, QuasiSeparatedSpace ((D ⋙ Etale.stageFunctor (Etale.isPullback_stageBase k W)).obj
      i).left := fun i ↦ by
    have : QuasiSeparated (pullback.snd ((D.obj i).hom ≫ k) W.hom) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd ((D.obj i).hom ≫ k) W.hom)
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom
      ((D ⋙ Etale.stageFunctor (Etale.isPullback_stageBase k W)).map f).left := fun f ↦
    inferInstanceAs (IsAffineHom ((Etale.stageFunctor (Etale.isPullback_stageBase k W)).map
      (D.map f)).left)
  have hCL := Etale.overCohomologyMap_isColimit_of_isLimit Λ (Etale.stageBaseSheaf Λ k W G)
    (D ⋙ Etale.stageFunctor (Etale.isPullback_stageBase k W))
    ((Etale.stageFunctor (Etale.isPullback_stageBase k W)).mapCone c)
    (Etale.isLimitStageFunctorMapCone (Etale.isPullback_stageBase k W) c hc) q
  set β := Etale.stageCohomologyEquiv Λ k W G q
  constructor
  · intro y
    obtain ⟨i, z, hz⟩ := hCL.1 (β c.pt y)
    refine ⟨i, (β (D.obj i)).symm z, (β c.pt).injective ?_⟩
    rw [Etale.overLowerStarMap, Etale.stageCohomologyEquiv_comp, Equiv.apply_symm_apply]
    exact hz
  · intro i x hx
    have h0 : Etale.overCohomologyMap Λ (Etale.stageBaseSheaf Λ k W G) q
        ((Etale.stageFunctor (Etale.isPullback_stageBase k W)).map (c.π.app i))
        (β (D.obj i) x) = 0 := by
      rw [← Etale.stageCohomologyEquiv_comp, ← Etale.overLowerStarMap, hx,
        Etale.stageCohomologyEquiv_zero]
    obtain ⟨j, f, hf⟩ := hCL.2 i _ h0
    refine ⟨j, f, (β (D.obj j)).injective ?_⟩
    rw [Etale.overLowerStarMap, Etale.stageCohomologyEquiv_comp, Etale.stageCohomologyEquiv_zero]
    exact hf


include hc in
/-- **The stalks of the derived direct images along `T = lim Tᵢ`**: at every geometric point
of `S`, the stalk of `H^q(Rg_*(G|_T))` is the filtered colimit of the stalks of the
`H^q(Rgᵢ_*(G|_{Tᵢ}))` along the transition maps. -/
theorem Etale.sheafFiber_homologyFunctor_overLowerStarMap_limit (s : S) :
    (∀ y : ToType ((S.uliftPointSmallEtale s).sheafFiber.obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj (Etale.overLowerStar Λ k G c.pt))),
      ∃ (i : I) (y' : ToType ((S.uliftPointSmallEtale s).sheafFiber.obj
          ((DerivedCategory.Plus.homologyFunctor _ q).obj (Etale.overLowerStar Λ k G (D.obj i))))),
        (S.uliftPointSmallEtale s).sheafFiber.map ((DerivedCategory.Plus.homologyFunctor _ q).map
          (Etale.overLowerStarMap Λ k G (c.π.app i))) y' = y) ∧
    ∀ (i : I) (y' : ToType ((S.uliftPointSmallEtale s).sheafFiber.obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj (Etale.overLowerStar Λ k G (D.obj i))))),
      (S.uliftPointSmallEtale s).sheafFiber.map ((DerivedCategory.Plus.homologyFunctor _ q).map
          (Etale.overLowerStarMap Λ k G (c.π.app i))) y' = 0 →
        ∃ (j : I) (f : j ⟶ i), (S.uliftPointSmallEtale s).sheafFiber.map
          ((DerivedCategory.Plus.homologyFunctor _ q).map
            (Etale.overLowerStarMap Λ k G (D.map f))) y' = 0 := by
  set Φ := S.uliftPointSmallEtale s
  constructor
  · intro y
    obtain ⟨W₀, w₀, σ, rfl⟩ := Φ.toPresheafFiber_jointly_surjective
      (P := ((DerivedCategory.Plus.homologyFunctor _ q).obj (Etale.overLowerStar Λ k G c.pt)).obj) y
    obtain ⟨W, g, w, t, rfl, hW, ht⟩ :=
      Etale.exists_shiftedHomSection Λ (Etale.overLowerStar Λ k G c.pt) q s σ w₀
    have := hW
    obtain ⟨i, x, hx⟩ := (Etale.overLowerStarMap_isColimit Λ k G D c hc q W).1 t
    refine ⟨i, Φ.toPresheafFiber W w _
      (Etale.shiftedHomSection Λ (Etale.overLowerStar Λ k G (D.obj i)) q x), ?_⟩
    change Φ.presheafFiber.map _ _ = _
    rw [Φ.toPresheafFiber_naturality_apply, ← Etale.shiftedHomSection_comp, hx, ht,
      Φ.toPresheafFiber_w_apply]
  · intro i y' hy'
    obtain ⟨W₀, w₀, σ, rfl⟩ := Φ.toPresheafFiber_jointly_surjective
      (P := ((DerivedCategory.Plus.homologyFunctor _ q).obj
        (Etale.overLowerStar Λ k G (D.obj i))).obj) y'
    obtain ⟨W, g, w, t, rfl, hW, ht⟩ :=
      Etale.exists_shiftedHomSection Λ (Etale.overLowerStar Λ k G (D.obj i)) q s σ w₀
    have h₁ : Φ.toPresheafFiber W w _ (Etale.shiftedHomSection Λ (Etale.overLowerStar Λ k G c.pt)
        q (t ≫ (Etale.overLowerStarMap Λ k G (c.π.app i))⟦q⟧')) =
        Φ.toPresheafFiber W w _ 0 := by
      rw [Etale.shiftedHomSection_comp, ← Φ.toPresheafFiber_naturality_apply, ht,
        Φ.toPresheafFiber_w_apply, map_zero]
      exact hy'
    rw [Φ.toPresheafFiber_eq_iff'] at h₁
    obtain ⟨W₁, g₁, w₁, rfl, h₁⟩ := h₁
    rw [map_zero, ← Etale.shiftedHomSection_map] at h₁
    obtain ⟨W₂, g₂, w₂, rfl, hW₂, h₂⟩ := Etale.exists_eq_zero_of_shiftedHomSection_eq_zero Λ
      (Etale.overLowerStar Λ k G c.pt) q s _ h₁ w₁
    have hx₂ : ((DerivedCategory.Plus.singleFunctor _ 0).map ((Etale.freeSheaf Λ S).map g₂) ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map ((Etale.freeSheaf Λ S).map g₁) ≫ t) ≫
          (Etale.overLowerStarMap Λ k G (c.π.app i))⟦q⟧' = 0 := by
      simpa only [Category.assoc] using h₂
    have := hW₂
    obtain ⟨j, f, hf⟩ := (Etale.overLowerStarMap_isColimit Λ k G D c hc q W₂).2 i _ hx₂
    refine ⟨j, f, ?_⟩
    rw [← Φ.toPresheafFiber_w_apply, ← ht, ← Φ.toPresheafFiber_w_apply,
      ← Etale.shiftedHomSection_map, ← Φ.toPresheafFiber_w_apply, ← Etale.shiftedHomSection_map]
    change Φ.presheafFiber.map _ _ = _
    rw [Φ.toPresheafFiber_naturality_apply, ← Etale.shiftedHomSection_comp, hf,
      Etale.shiftedHomSection, map_zero, map_zero]


/-- The identification `H^q(R(U ⟶ S)_*(U^*(G[0]))) ⟶ R^q(U ⟶ S)_*(U^* G)`, induced by
`U^*(G[0]) ≅ (U^* G)[0]`. -/
noncomputable abbrev Etale.overLowerStarHomologyMap (U : Over B) :
    (DerivedCategory.Plus.homologyFunctor _ q).obj (Etale.overLowerStar Λ k G U) ⟶
      Etale.higherDirectImage Λ (U.hom ≫ k) q (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj G) :=
  (DerivedCategory.Plus.homologyFunctor _ q).map (R+((U.hom ≫ k)_*[ModuleCat.{u + 1} Λ]).map
    ((((U.hom)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G))

end Limit

/-- Blueprint `sbc-lem-higher-direct-image-limit`: Higher direct images and limits of schemes.

Let `W ⟶ S` be a morphism of schemes, `G` a sheaf of `Λ`-modules on `W_ét`, and
`T = lim T_i` a cofiltered limit of schemes over `W` with affine transition morphisms, all
quasi-compact and quasi-separated over `S`. Then `colim_i R^q g_{i,*} (G|_{T_i}) ≅
R^q g_* (G|_T)`, where `g_i : T_i ⟶ S` and `g : T ⟶ S` are the structure morphisms. The
statement is recorded on every geometric stalk, in the form of the two defining properties of
a filtered colimit of modules: every element at the limit comes from some stage, and an element
of a stage dying at the limit already dies at a later stage. This is the case of the blueprint
statement for a system of sheaves pulled back from a fixed scheme.

The proof is that of the blueprint: the stalks are colimits over the affine étale neighbourhoods
`U` of the cohomology of `T ×_S U = lim Tᵢ ×_S U`
(`AlgebraicGeometry.Etale.sheafFiber_homologyFunctor_overLowerStarMap_limit`), to which the
continuity of étale cohomology applies. -/
@[stacks 09Z1]
theorem Etale.higherDirectImage_limit {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Over W) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)] [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)] (q : ℤ) (s : S) :
    (∀ y : ((S.uliftPointSmallEtale s).sheafFiber.obj (Etale.higherDirectImage Λ
        (c.pt.hom ≫ k) q (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G)) : ModuleCat.{u + 1} Λ),
      ∃ (i : I) (y' : ((S.uliftPointSmallEtale s).sheafFiber.obj
        (Etale.higherDirectImage Λ ((D.obj i).hom ≫ k) q
          (((D.obj i).hom)^*[ModuleCat.{u + 1} Λ].obj G)) : ModuleCat.{u + 1} Λ)),
        ((S.uliftPointSmallEtale s).sheafFiber.map
          (Etale.higherDirectImageOverMap Λ k G q (c.π.app i))).hom y' = y) ∧
    ∀ (i : I) y', ((S.uliftPointSmallEtale s).sheafFiber.map
        (Etale.higherDirectImageOverMap Λ k G q (c.π.app i))).hom y' = 0 →
      ∃ (j : I) (f : j ⟶ i), ((S.uliftPointSmallEtale s).sheafFiber.map
        (Etale.higherDirectImageOverMap Λ k G q (D.map f))).hom y' = 0 := by
  set Φ := S.uliftPointSmallEtale s
  have hcomm : ∀ {U U' : Over W} (φ : U' ⟶ U) (y : ToType (Φ.sheafFiber.obj
      ((DerivedCategory.Plus.homologyFunctor _ q).obj (Etale.overLowerStar Λ k G U)))),
      (Φ.sheafFiber.map (Etale.higherDirectImageOverMap Λ k G q φ)).hom
          ((Φ.sheafFiber.map (Etale.overLowerStarHomologyMap Λ k G q U)).hom y) =
        (Φ.sheafFiber.map (Etale.overLowerStarHomologyMap Λ k G q U')).hom
          ((Φ.sheafFiber.map ((DerivedCategory.Plus.homologyFunctor _ q).map
            (Etale.overLowerStarMap Λ k G φ))).hom y) := by
    intro U U' φ y
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, Etale.homologyFunctor_map_overLowerStarTransition]
  have hinv : ∀ (U : Over W) (y : ToType (Φ.sheafFiber.obj (Etale.higherDirectImage Λ
      (U.hom ≫ k) q (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj G)))),
      (Φ.sheafFiber.map (Etale.overLowerStarHomologyMap Λ k G q U)).hom
        ((Φ.sheafFiber.map (inv (Etale.overLowerStarHomologyMap Λ k G q U))).hom y) = y := by
    intro U y
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  have hinv' : ∀ (U : Over W) (y : ToType (Φ.sheafFiber.obj
      ((DerivedCategory.Plus.homologyFunctor _ q).obj (Etale.overLowerStar Λ k G U)))),
      (Φ.sheafFiber.map (inv (Etale.overLowerStarHomologyMap Λ k G q U))).hom
        ((Φ.sheafFiber.map (Etale.overLowerStarHomologyMap Λ k G q U)).hom y) = y := by
    intro U y
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, IsIso.hom_inv_id,
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  obtain ⟨h₁, h₂⟩ :=
    Etale.sheafFiber_homologyFunctor_overLowerStarMap_limit Λ k G D c hc q s
  constructor
  · intro y
    obtain ⟨i, y', hy'⟩ := h₁ ((Φ.sheafFiber.map
      (inv (Etale.overLowerStarHomologyMap Λ k G q c.pt))).hom y)
    refine ⟨i, (Φ.sheafFiber.map (Etale.overLowerStarHomologyMap Λ k G q (D.obj i))).hom y', ?_⟩
    rw [hcomm, hy', hinv]
  · intro i y' hy'
    rw [← hinv (D.obj i) y', hcomm] at hy'
    have h0 := congrArg (Φ.sheafFiber.map
      (inv (Etale.overLowerStarHomologyMap Λ k G q c.pt))).hom hy'
    rw [hinv', map_zero] at h0
    obtain ⟨j, f, hf⟩ := h₂ i _ h0
    refine ⟨j, f, ?_⟩
    rw [← hinv (D.obj i) y', hcomm, hf, map_zero]

end AlgebraicGeometry
