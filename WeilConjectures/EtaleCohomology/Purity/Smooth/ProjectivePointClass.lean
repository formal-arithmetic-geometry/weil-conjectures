/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.HyperplaneClass
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct

/-!
# The class of a point of projective space

Let `P = [0 : ⋯ : 0 : 1] ∈ ℙ(Option m; S)` be the point where all coordinates but `T_∗` vanish,
the complement of the total space `W = ⋃ₐ D₊(T_a)` of `𝒪(1)` on the hyperplane `ℙ(m; S)`. Its
class is the cup product with supports of the classes of the hyperplanes `V(T_a)`, `a : m`, the
localized first Chern classes of the coordinate sections of `𝒪(1)`. Forgetting supports it is the
power `h^{#m}` of the first Chern class `h` of the hyperplane class, and it is a Thom class: on the
chart `D₊(T_∗) ≅ 𝔸^m_S` it is the product of the Kummer boundaries of the coordinates
(`AlgebraicGeometry.Etale.nonempty_pointClassData`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

namespace VectorBundle

variable {V T : Scheme.{u}} {r : ℕ} {π : V ⟶ T} (E : VectorBundle r π) (s : T ⟶ V)
  (hs : s ≫ π = 𝟙 T)

/-- Over a trivialising open `U i`, the zero scheme `Z(s) = s⁻¹(0)` of a section `s` is the zero
locus of its components `f = (s₁, …, s_r)` (`AlgebraicGeometry.VectorBundle.sectionCoord`). -/
lemma exists_isPullback_sectionCoord (i : E.ι) (f : Fin r → Γ((E.U i).toScheme, ⊤))
    (hf : E.sectionCoord s hs i = f) :
    ∃ g : (E.U i).toScheme.zeroLocusSubscheme (Set.range f) ⟶ pullback E.zero s,
      IsPullback g ((E.U i).toScheme.zeroLocusSubschemeι (Set.range f))
        (pullback.snd E.zero s) (E.U i).ι := by
  subst hf
  have hgs := isPullback_zeroLocusSubschemeι (E.sectionRes s hs i)
    (Set.range (E.coord i)) (Set.range (E.sectionCoord s hs i))
    (by rw [← Set.range_comp]; rfl)
  have hout := hgs.paste_horiz (E.frame i).isPullback
  have he : E.sectionRes s hs i ≫ (E.frame i).e = (E.U i).ι ≫ s := E.sectionRes_ι s hs i
  rw [he] at hout
  refine ⟨pullback.lift _ _ (by rw [hout.w, Category.assoc]), ?_⟩
  exact IsPullback.of_right (by rwa [pullback.lift_fst]) (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback E.zero s)

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ V]
  {k : Type u} [Field k] (aT : T ⟶ Spec (.of k)) [IsSeparated aT] [LocallyOfFiniteType aT]

attribute [local instance] HasInvertibleExponent.opens

/-- *(L1), the class in a chart*, for any presentation `f` of the components of the section:
over the trivialising open `U i` the localized top Chern class restricts to
`∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_r)`, supported on `V(f) = Z(s) ∩ U i`. -/
lemma exists_restrictSupportedClass_localizedTopChern_eq (i : E.ι)
    (f : Fin r → Γ((E.U i).toScheme, ⊤)) (hf : E.sectionCoord s hs i = f) :
    haveI : HasInvertibleExponent Λ T := .of_hom E.zero
    ∃ (g : (E.U i).toScheme.zeroLocusSubscheme (Set.range f) ⟶ pullback E.zero s)
      (hg : IsPullback g ((E.U i).toScheme.zeroLocusSubschemeι (Set.range f))
        (pullback.snd E.zero s) (E.U i).ι),
      restrictSupportedClass (ModuleCat.{u + 1} Λ) (E.U i).ι (pullback.snd E.zero s) _ g hg
          (leftDerivedUpperStarConstantComplexIso Λ _).inv
          (leftDerivedUpperStarTateShiftIso Λ _ r) (E.localizedTopChern s Λ aT) =
        kummerBoundaryProduct Λ f := by
  subst hf
  obtain ⟨g, hg⟩ := E.exists_isPullback_sectionCoord s hs i _ rfl
  exact ⟨g, hg, E.restrictSupportedClass_localizedTopChern s hs Λ aT i g hg⟩

end VectorBundle

namespace ProjectiveSpace

variable (n : Type u) (S : Scheme.{u})

/-- In the chart `D₊(T_b)`, the component of the coordinate section `[x] ↦ [x : x_t]` of `𝒪(1)` is
the ratio `T_t / T_b`. -/
lemma twistBundle_sectionCoord (t b : n) (a : Fin 1) :
    (twistBundle n S).sectionCoord (twistBundleSection n S t) (twistBundleSection_comp_π n S t)
      b a = (standardOpen n S b).topIso.inv (coordRatio n S b t) := by
  have key (r : (standardOpen n S b).toScheme ⟶ (twistBundleπ n S ⁻¹ᵁ standardOpen n S b).toScheme)
      (hr : r ≫ (twistBundleπ n S ⁻¹ᵁ standardOpen n S b).ι ≫ (twistBundleOpen n S).ι =
        (standardOpen n S b).ι ≫ twistBundleSectionAux n S t) :
      r.appTop (twistBundleFiberCoord n S b) =
        (standardOpen n S b).topIso.inv (coordRatio n S b t) := by
    have e₁ : (twistBundleπ n S ⁻¹ᵁ standardOpen n S b).topIso.inv =
        (twistBundleπ n S ⁻¹ᵁ standardOpen n S b).ι.appLE
          (twistBundleπ n S ⁻¹ᵁ standardOpen n S b) ⊤ (Scheme.Opens.ι_preimage_self _).ge := by
      rw [Scheme.Opens.ι_appLE]
      rfl
    have e₂ : r.appTop = r.appLE ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    have hh : (standardOpen n S b).ι ≫ twistBundleSectionAux n S t =
        homOfSections ((standardOpen n S b).ι ≫ ℙ(n; S) ↘ S)
          (fun a ↦ (standardOpen n S b).topIso.inv ((twistBundleSectionSections n S t a).s b))
          (Scheme.CoordinateCover.span_topIso_inv _ (span_twistBundleSectionSections n S t) b) :=
      Scheme.CoordinateCover.ι_hom (𝒟 := standardCoordinateCover n S) _ _ _ _
    rw [twistBundleFiberCoord, e₁, e₂, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
      appLE_eq_of_eq ((Category.assoc _ _ _).trans hr), appLE_eq_of_eq hh]
    exact (homOfSections_appLE_coordRatio (S := S) ((standardOpen n S b).ι ≫ ℙ(n; S) ↘ S)
      (fun a ↦ (standardOpen n S b).topIso.inv ((twistBundleSectionSections n S t a).s b))
      (Scheme.CoordinateCover.span_topIso_inv _ (span_twistBundleSectionSections n S t) b)
      (twistBundleSectionSections_some_s_self n S t b) none _).trans rfl
  simp only [VectorBundle.sectionCoord, twistBundle_coord]
  refine key _ ((Category.assoc _ _ _).symm.trans
    (((twistBundle n S).sectionRes_ι _ (twistBundleSection_comp_π n S t) b =≫ _).trans ?_))
  rw [Category.assoc, twistBundleSection_ι]
  rfl

/-- A point of the standard open `D₊(T_b)` lies in the basic open of `T_t / T_b` if and only if
it lies in `D₊(T_t)`. -/
lemma mem_basicOpen_topIso_inv_coordRatio (b t : n) (y : (standardOpen n S b).toScheme) :
    y ∈ (standardOpen n S b).toScheme.basicOpen
      ((standardOpen n S b).topIso.inv (coordRatio n S b t)) ↔ y.1 ∈ standardOpen n S t := by
  rw [← (standardOpen n S b).ι.preimage_image_eq (Scheme.basicOpen _ _),
    Scheme.Opens.ι_image_basicOpen_topIso_inv]
  have h : ℙ(n; S).basicOpen (coordRatio n S b t) = standardOpen n S b ⊓ standardOpen n S t :=
    (standardCoordinateCover n S).basicOpen_ratio b t
  rw [h]
  exact ⟨fun hy ↦ hy.2, fun hy ↦ ⟨y.2, hy⟩⟩

/-- The zero scheme of the coordinate section `[x] ↦ [x : x_t]` of `𝒪(1)` is the complement of
`D₊(T_t)`. -/
lemma range_pullbackSnd_twistBundleSection (t : n) :
    Set.range (pullback.snd (twistBundle n S).zero (twistBundleSection n S t)).base =
      ((standardOpen n S t : Set ℙ(n; S)))ᶜ := by
  ext x
  obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_standardOpen n S).ge (Set.mem_univ x))
  obtain ⟨g, hg⟩ := (twistBundle n S).exists_isPullback_sectionCoord (twistBundleSection n S t)
    (twistBundleSection_comp_π n S t) b
    (fun _ ↦ (standardOpen n S b).topIso.inv (coordRatio n S b t))
    (funext (twistBundle_sectionCoord n S t b))
  have hr : Set.range (((standardOpen n S b).toScheme.zeroLocusSubschemeι
      {(standardOpen n S b).topIso.inv (coordRatio n S b t)}) ≫ (standardOpen n S b).ι).base =
        Set.range (pullback.snd (twistBundle n S).zero (twistBundleSection n S t)).base ∩
          Set.range (standardOpen n S b).ι.base := by
    have h := Scheme.range_eq_inter_of_isPullback hg rfl
    rw [hg.w, Set.range_const] at h
    exact h
  have hV := range_zeroLocusSubschemeι_singleton
    ((standardOpen n S b).topIso.inv (coordRatio n S b t))
  rw [Scheme.Opens.range_ι] at hV
  constructor
  · intro hx
    have hx' : x ∈ Set.range (((standardOpen n S b).toScheme.zeroLocusSubschemeι
        {(standardOpen n S b).topIso.inv (coordRatio n S b t)}) ≫ (standardOpen n S b).ι).base := by
      rw [hr]
      exact ⟨hx, by rw [Scheme.Opens.range_ι]; exact hb⟩
    obtain ⟨v, rfl⟩ := hx'
    have hv : (Scheme.zeroLocusSubschemeι _ _).base v ∈ Set.range
        ((standardOpen n S b).toScheme.zeroLocusSubschemeι
          {(standardOpen n S b).topIso.inv (coordRatio n S b t)}).base := ⟨v, rfl⟩
    rw [hV] at hv
    intro ht
    exact hv ((mem_basicOpen_topIso_inv_coordRatio n S b t _).2 ht)
  · intro hx
    have hy : (⟨x, hb⟩ : (standardOpen n S b).toScheme) ∈ Set.range
        ((standardOpen n S b).toScheme.zeroLocusSubschemeι
          {(standardOpen n S b).topIso.inv (coordRatio n S b t)}).base := by
      rw [hV]
      exact fun h ↦ hx ((mem_basicOpen_topIso_inv_coordRatio n S b t _).1 h)
    obtain ⟨v, hv⟩ := hy
    have hx' : x ∈ Set.range (((standardOpen n S b).toScheme.zeroLocusSubschemeι
        {(standardOpen n S b).topIso.inv (coordRatio n S b t)}) ≫ (standardOpen n S b).ι).base :=
      ⟨v, by rw [Scheme.Hom.comp_apply, hv]; rfl⟩
    rw [hr] at hx'
    exact hx'.1

end ProjectiveSpace

namespace Etale

open ProjectiveSpace

attribute [local instance] HasInvertibleExponent.opens

section Cup

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasKummerClass Λ] {U Z₁ Z₂ Z : Scheme.{u}}
  [HasInvertibleExponent Λ U]

/-- *Forgetting supports in a cup product with supports*: `α ∪ β` becomes the cup product of the
classes `α`, `β` with supports forgotten. -/
lemma cupWithSupportsTateObject_comp_counit (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base) {m m' : ℤ}
    (α : constantComplex Λ U ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₁)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ U m)⟦2 * m⟧)))
    (β : constantComplex Λ U ⟶ (R(i₂)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₂)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ U m')⟦2 * m'⟧))) :
    cupWithSupportsTateObject Λ i₁ i₂ i h α β ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app _ =
      constantComplexDiagonal Λ U ≫
        derivedTensorHom _
          (α ≫ (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i₁).counit.app _)
          (β ≫ (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i₂).counit.app _) ≫
        (shiftTateObjectAddIso Λ U m m').hom := by
  have hn := (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.naturality
    (shiftTateObjectAddIso Λ U m m').hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [cupWithSupportsTateObject, Category.assoc, hn, cupWithSupports_eq, Category.assoc,
    Category.assoc, reassoc_of% supportedProduct_comp_counit, derivedTensorHom_comp_assoc]

/-- Forgetting supports commutes with an identification of the coefficients. -/
lemma eqToHom_comp_counit (i : Z ⟶ U) [IsClosedImmersion i]
    {M M' : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : M = M') :
    eqToHom (by rw [h]) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app M' =
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app M ≫ eqToHom h := by
  subst h
  simp

end Cup

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] (m : Type u) [Fintype m] {S : Scheme.{u}}
  [HasInvertibleExponent Λ S] {k : Type u} [Field k] (aS : S ⟶ Spec (.of k)) [IsSeparated aS]
  [LocallyOfFiniteType aS]

/-- *The class of a point of projective space*, the inductive construction. For a tuple
`a₁, …, a_n` of coordinates, the cup product with supports `[V(T_{a₁})] ∪ ⋯ ∪ [V(T_{a_n})]` of the
localized first Chern classes of the coordinate sections of `𝒪(1)` is a class supported on
`V(T_{a₁}, …, T_{a_n})`, which is `hⁿ` after forgetting supports, and which restricts on the chart
`D₊(T_∗)` to the product of the Kummer boundaries of the coordinates `T_{aⱼ} / T_∗`. -/
theorem exists_pointClass_aux : ∀ (n : ℕ) (a : Fin n → m)
    (f : Fin n → Γ((standardOpen (Option m) S none).toScheme, ⊤))
    (_ : ∀ j, f j = (standardOpen (Option m) S none).topIso.inv
      (coordRatio (Option m) S none (some (a j)))),
    ∃ (Z : Scheme.{u}) (i : Z ⟶ ℙ(Option m; S)) (_ : IsClosedImmersion i)
      (γ : constantComplex Λ ℙ(Option m; S) ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ ℙ(Option m; S) n)⟦2 * (n : ℤ)⟧)))
      (g : (standardOpen (Option m) S none).toScheme.zeroLocusSubscheme (Set.range f) ⟶ Z)
      (hg : IsPullback g ((standardOpen (Option m) S none).toScheme.zeroLocusSubschemeι
        (Set.range f)) i (standardOpen (Option m) S none).ι),
      Set.range i.base = {x | ∀ j, x ∉ standardOpen (Option m) S (some (a j))} ∧
      γ ≫ (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app _ =
        chernPow (hyperplaneChernClass (hyperplaneClass Λ m aS)) n ∧
      restrictSupportedClass (ModuleCat.{u + 1} Λ) (standardOpen (Option m) S none).ι i _ g hg
        (leftDerivedUpperStarConstantComplexIso Λ _).inv
        (leftDerivedUpperStarTateShiftIso Λ _ n) γ = kummerBoundaryProduct Λ f
  | 0, a, f, hf => by
    let f₀ : Fin 0 → Γ(ℙ(Option m; S), ⊤) := Fin.elim0
    have himg : (standardOpen (Option m) S none).ι.appTop '' Set.range f₀ = Set.range f := by
      rw [Set.range_eq_empty f₀, Set.range_eq_empty f, Set.image_empty]
    have hg := isPullback_zeroLocusSubschemeι (standardOpen (Option m) S none).ι
      (Set.range f₀) (Set.range f) himg
    refine ⟨_, ℙ(Option m; S).zeroLocusSubschemeι (Set.range f₀), inferInstance,
      kummerBoundaryProduct Λ f₀, _, hg, ?_, ?_, ?_⟩
    · rw [Set.range_eq_empty f₀, range_zeroLocusSubschemeι_empty]
      ext x
      simp
    · rw [kummerBoundaryProduct]
      exact (existsUnique_comp_counit_of_range_eq_univ _ _
        (by rw [Set.range_eq_empty f₀, range_zeroLocusSubschemeι_empty]) _).exists.choose_spec
    · exact restrictSupportedClass_kummerBoundaryProduct Λ _ f₀ f (fun j ↦ j.elim0) _ hg
  | n + 1, a, f, hf => by
    obtain ⟨f₀, x, rfl⟩ : ∃ f₀ x, f = Fin.append f₀ (fun _ : Fin 1 ↦ x) :=
      ⟨Fin.init f, f (Fin.last n), by
        rw [Fin.append_right_eq_snoc]
        exact (Fin.snoc_init_self f).symm⟩
    have hf₀ (j : Fin n) : f₀ j = (standardOpen (Option m) S none).topIso.inv
        (coordRatio (Option m) S none (some (a j.castSucc))) := by
      rw [← hf j.castSucc]
      exact (Fin.append_left f₀ _ j).symm
    have hx : x = (standardOpen (Option m) S none).topIso.inv
        (coordRatio (Option m) S none (some (a (Fin.last n)))) := by
      rw [← hf (Fin.last n)]
      exact (Fin.append_right f₀ (fun _ : Fin 1 ↦ x) 0).symm
    obtain ⟨Z, i, _, γ, g, hg, hrange, hforget, hres⟩ :=
      exists_pointClass_aux n (fun j ↦ a j.castSucc) f₀ hf₀
    set b := a (Fin.last n) with hb
    set E := twistBundle (Option m) S
    set sb := twistBundleSection (Option m) S (some b)
    set ιb := pullback.snd E.zero sb
    set c := E.localizedTopChern sb Λ (ℙ(Option m; S) ↘ S ≫ aS)
    obtain ⟨g₁, hg₁, hres₁⟩ : ∃ (g₁ : (standardOpen (Option m) S none).toScheme.zeroLocusSubscheme
          (Set.range fun _ : Fin 1 ↦ x) ⟶ pullback E.zero sb)
        (hg₁ : IsPullback g₁ ((standardOpen (Option m) S none).toScheme.zeroLocusSubschemeι
          (Set.range fun _ : Fin 1 ↦ x)) ιb (standardOpen (Option m) S none).ι),
        restrictSupportedClass (ModuleCat.{u + 1} Λ) (standardOpen (Option m) S none).ι ιb _ g₁
          hg₁ (leftDerivedUpperStarConstantComplexIso Λ _).inv
          (leftDerivedUpperStarTateShiftIso Λ _ ((1 : ℕ) : ℤ)) c =
        kummerBoundaryProduct Λ fun _ : Fin 1 ↦ x :=
      E.exists_restrictSupportedClass_localizedTopChern_eq sb
        (twistBundleSection_comp_π (Option m) S (some b)) Λ (ℙ(Option m; S) ↘ S ≫ aS) none
        (fun _ ↦ x) (funext fun _ ↦ (twistBundle_sectionCoord (Option m) S (some b) none _).trans
          hx.symm)
    have hY := IsPullback.of_hasPullback ιb i
    have hr : Set.range (pullback.snd ιb i ≫ i).base = Set.range i.base ∩ Set.range ιb.base := by
      rw [Scheme.range_eq_inter_of_isPullback hY pullback.condition, Set.inter_comm]
    have hS : Ideal.span (Set.range (Fin.append f₀ fun _ : Fin 1 ↦ x)) =
        Ideal.span (Set.range fun _ : Fin 1 ↦ x) ⊔ Ideal.span (Set.range f₀) := by
      rw [Fin.range_append, Ideal.span_union, sup_comm]
    obtain ⟨G, hG⟩ : ∃ G, IsPullback G
        ((standardOpen (Option m) S none).toScheme.zeroLocusSubschemeι
        (Set.range (Fin.append f₀ fun _ : Fin 1 ↦ x))) (pullback.snd ιb i ≫ i)
        (standardOpen (Option m) S none).ι := by
      have h := (Scheme.isPullback_zeroLocusSubschemeι_union hS).of_isPullback_inter hg₁ hg hY
      rw [IdealSheafData.inclusion_subschemeι] at h
      exact ⟨_, h⟩
    have hc : c ≫ (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) ιb).counit.app _ =
        hyperplaneChernClass (hyperplaneClass Λ m aS) :=
      (E.forgetSupports_localizedTopChern Λ _ sb
        (twistBundleSection_comp_π (Option m) S (some b))).trans
        (topChernClass_twistBundle_eq_hyperplaneChernClass aS)
    refine ⟨pullback ιb i, pullback.snd ιb i ≫ i, inferInstance,
      cupWithSupportsTateObject Λ i ιb _ hr (m := n) (m' := ((1 : ℕ) : ℤ)) γ c ≫
        eqToHom (by rw [Nat.cast_add]), _, hG, ?_, ?_, ?_⟩
    · rw [hr, hrange, range_pullbackSnd_twistBundleSection]
      ext y
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_compl_iff, SetLike.mem_coe,
        Fin.forall_fin_succ' (P := fun j ↦ y ∉ standardOpen (Option m) S (some (a j)))]
      exact Iff.rfl
    · have h₁ := eqToHom_comp_counit (Λ := Λ) (pullback.snd ιb i ≫ i)
        (M := (tateObject Λ ℙ(Option m; S) ((n : ℤ) + ((1 : ℕ) : ℤ)))⟦
          2 * ((n : ℤ) + ((1 : ℕ) : ℤ))⟧)
        (M' := (tateObject Λ ℙ(Option m; S) ((n + 1 : ℕ) : ℤ))⟦2 * ((n + 1 : ℕ) : ℤ)⟧)
        (by rw [Nat.cast_add])
      rw [Category.assoc, h₁, ← Category.assoc, cupWithSupportsTateObject_comp_counit, hforget, hc]
      simp only [derivedTensorHom, Category.assoc]
      rfl
    · rw [restrictSupportedClass_comp_eqToHom Λ _ _ _ _ hG (Nat.cast_add n 1).symm,
        restrictSupportedClass_cupWithSupportsTateObject Λ _ i ιb _ _ _ _ hr
          (by rw [Fin.range_append, Scheme.range_zeroLocusSubschemeι_union]) g g₁ _ hg hg₁ hG,
        hres, hres₁, kummerBoundaryProduct_append]

/-- *The class of the point* `P = [0 : ⋯ : 0 : 1]` of `ℙ(Option m; S)`: a closed immersion
`i : Z ⟶ ℙ(Option m; S)` with image `P`, the complement of the total space
`W = ⋃ₐ D₊(T_a)` of `𝒪(1)` on the hyperplane, mapping isomorphically to `S`, and a Thom class
`γ ∈ H^{2#m}_P(ℙ(Option m; S), Λ(#m))` which is `h^{#m}` after forgetting supports, `h` the first
Chern class of the hyperplane class. -/
structure PointClassData where
  /-- The support of the class, a closed subscheme with image the point `P`. -/
  Z : Scheme.{u}
  /-- The closed immersion of the support. -/
  i : Z ⟶ ℙ(Option m; S)
  [isClosedImmersion : IsClosedImmersion i]
  isIso_comp : IsIso (i ≫ ℙ(Option m; S) ↘ S)
  range_eq : Set.range i.base = (Set.range (twistBundleOpen m S).ι.base)ᶜ
  /-- The class of the point. -/
  γ : constantComplex Λ ℙ(Option m; S) ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
    ((R(i)^![ModuleCat.{u + 1} Λ]).obj
      ((tateObject Λ ℙ(Option m; S) (Fintype.card m))⟦2 * (Fintype.card m : ℤ)⟧))
  isIso_supportedClassMap : IsIso (supportedClassMap Λ i γ)
  forget_eq : γ ≫ (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app _ =
    chernPow (hyperplaneChernClass (hyperplaneClass Λ m aS)) (Fintype.card m)

attribute [instance] PointClassData.isClosedImmersion

include aS in
/-- *The class of a point of projective space* exists. It is the cup product with supports of
the localized first Chern classes of the coordinate sections `T_a`, `a : m`, of `𝒪(1)`
(`AlgebraicGeometry.VectorBundle.localizedTopChern`): forgetting supports each is `h`
(`AlgebraicGeometry.VectorBundle.forgetSupports_localizedTopChern`,
`AlgebraicGeometry.Etale.topChernClass_twistBundle_eq_hyperplaneChernClass`), and on the chart
`D₊(T_∗) ≅ 𝔸^m_S` the class restricts to the product of the Kummer boundaries of the coordinates
`T_a / T_∗`, the Thom class of the origin
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_coord`). -/
theorem nonempty_pointClassData : Nonempty (PointClassData Λ m aS) := by
  let σ : Fin (Fintype.card m) ≃ m := (Fintype.equivFin m).symm
  set U := standardOpen (Option m) S none
  let f : Fin (Fintype.card m) → Γ(U.toScheme, ⊤) :=
    fun j ↦ U.topIso.inv (coordRatio (Option m) S none (some (σ j)))
  obtain ⟨Z, i, _, γ₀, g, hg, hrange, hforget, hres⟩ :=
    exists_pointClass_aux Λ m aS _ σ f fun _ ↦ rfl
  have hsub : Set.range i.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_standardOpen (Option m) S).ge (Set.mem_univ (i z)))
    cases b with
    | none => exact hb
    | some a =>
      have hz : i z ∈ Set.range i.base := ⟨z, rfl⟩
      rw [hrange] at hz
      exact absurd (by simpa [σ] using hb) (hz (σ.symm a))
  have hgs (z : Z) : ∃ v, g v = z := by
    obtain ⟨w, hw⟩ := hsub ⟨z, rfl⟩
    obtain ⟨v, hv, -⟩ := hg.exists_scheme_point z w hw.symm
    exact ⟨v, hv⟩
  have : IsOpenImmersion g :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hg.flip inferInstance
  have : Surjective g := ⟨hgs⟩
  have : IsIso g := (isIso_iff_isOpenImmersion_and_surjective g).2 ⟨inferInstance, inferInstance⟩
  -- the chart `D₊(T_∗) ≅ 𝔸^m_S` and the model
  let e : ULift.{u} (Fin (Fintype.card m)) ≃ {j : Option m // j ≠ none} :=
    { toFun := fun j ↦ ⟨some (σ j.down), Option.some_ne_none _⟩
      invFun := fun j ↦ ⟨σ.symm (j.1.get (Option.ne_none_iff_isSome.mp j.2))⟩
      left_inv := fun j ↦ by simp
      right_inv := fun j ↦ by
        obtain ⟨_ | a, h⟩ := j
        · exact absurd rfl h
        · simp }
  have he (j : Fin (Fintype.card m)) :
      (standardOpenIso (Option m) S none).hom.appTop (AffineSpace.coord S (e ⟨j⟩)) = f j :=
    standardOpenIso_hom_appTop_coord _ _
  have : IsIso (AffineSpace.reindex e S) := (AffineSpace.reindexIso S e).isIso_hom
  have hthom := isIso_supportedClassMap_kummerBoundaryProduct_of_etale Λ
    (standardOpenIso (Option m) S none).hom _ f he
    (isIso_supportedClassMap_kummerBoundaryProduct_of_etale Λ (AffineSpace.reindex e S)
      (fun a ↦ AffineSpace.coord S (ULift.up a)) _
      (fun a ↦ AffineSpace.reindex_appTop_coord _ _ _)
      (isIso_supportedClassMap_kummerBoundaryProduct_coord Λ (Fintype.card m) S aS))
  -- the support maps isomorphically to `S`
  have himg : (standardOpenIso (Option m) S none).hom.appTop '' Set.range (AffineSpace.coord S) =
      Set.range f := by
    rw [← Set.range_comp, ← (Equiv.ulift.symm.trans e).surjective.range_comp]
    exact congrArg Set.range (funext he)
  have hz := isPullback_zeroLocusSubschemeι (standardOpenIso (Option m) S none).hom _ _ himg
  have : IsIso (𝔸({j : Option m // j ≠ none}; S).zeroLocusSubschemeι
      (Set.range (AffineSpace.coord S)) ≫ 𝔸({j : Option m // j ≠ none}; S) ↘ S) :=
    inferInstanceAs (IsIso (AffineSpace.zeroSectionIsoZeroLocusSubscheme _ S rfl).inv)
  have hcomp : IsIso (g ≫ i ≫ ℙ(Option m; S) ↘ S) := by
    have := hz.isIso_fst_of_isIso
    rw [← Category.assoc, hg.w, Category.assoc, ← standardOpenIso_hom_over, ← Category.assoc,
      ← hz.w, Category.assoc]
    infer_instance
  refine ⟨PointClassData.mk Z i (IsIso.of_isIso_comp_left g _) ?_ γ₀ ?_ hforget⟩
  · rw [hrange, Scheme.Opens.range_ι]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, SetLike.mem_coe, twistBundleOpen,
      TopologicalSpace.Opens.mem_iSup, not_exists]
    exact σ.forall_congr_right (q := fun b ↦ x ∉ standardOpen (Option m) S (some b))
  · have hu (z : Z) : ∃ (_ : PUnit.{u + 1}) (v : U.toScheme.zeroLocusSubscheme (Set.range f)),
        g.base v = z :=
      ⟨PUnit.unit, hgs z⟩
    refine isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective Λ (fun _ ↦ g) hu _
      fun _ ↦ ?_
    refine (isIso_supportedClassMap_restrictSupportedClass_iff Λ U.ι i _ g hg _ _
      (leftDerivedUpperStarTateShiftIso Λ U.ι (Fintype.card m)) γ₀
      (isIso_supportedRestriction_of_isOpenImmersion _ _ _ _ _ _ _ _ _)).1 ?_
    rw [hres]
    exact hthom

end Etale

end AlgebraicGeometry
