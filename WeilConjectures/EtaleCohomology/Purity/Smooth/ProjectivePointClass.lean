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

open Scheme

namespace VectorBundle

variable {V T : Scheme.{u}} {r : ℕ} {π : V ⟶ T} (E : VectorBundle r π) (s : T ⟶ V)
  (hs : s ≫ π = 𝟙 T)

/-- Over a trivialising open `U i`, the zero scheme `Z(s) = s⁻¹(0)` of a section `s` is the zero
locus of its components `s₁, …, s_r` (`AlgebraicGeometry.VectorBundle.sectionCoord`). -/
lemma exists_isPullback_sectionCoord (i : E.ι) :
    ∃ g : (E.U i).toScheme.zeroLocusSubscheme (Set.range (E.sectionCoord s hs i)) ⟶
        pullback E.zero s,
      IsPullback g ((E.U i).toScheme.zeroLocusSubschemeι (Set.range (E.sectionCoord s hs i)))
        (pullback.snd E.zero s) (E.U i).ι := by
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
  obtain ⟨g, hg⟩ := E.exists_isPullback_sectionCoord s hs i
  exact ⟨g, hg, E.restrictSupportedClass_localizedTopChern s hs Λ aT i g hg⟩

end VectorBundle

namespace ProjectiveSpace

variable (n : Type u) (S : Scheme.{u})

/-- In the chart `D₊(T_b)`, the component of the coordinate section `[x] ↦ [x : x_t]` of `𝒪(1)` is
the ratio `T_t / T_b`. -/
lemma twistBundle_sectionCoord (t b : n) (a : Fin 1) :
    (twistBundle n S).sectionCoord (twistBundleSection n S t) (twistBundleSection_comp_π n S t)
      b a = (standardOpen n S b).topIso.inv (coordRatio n S b t) := by
  sorry

/-- The zero scheme of the coordinate section `[x] ↦ [x : x_t]` of `𝒪(1)` is the complement of
`D₊(T_t)`. -/
lemma range_pullbackSnd_twistBundleSection (t : n) :
    Set.range (pullback.snd (twistBundle n S).zero (twistBundleSection n S t)).base =
      ((standardOpen n S t : Set ℙ(n; S)))ᶜ := by
  sorry

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
    eqToHom (by rw [h]) ≫ (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app M' =
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
      exact (existsUnique_comp_counit_of_range_eq_univ _ _ _ _).exists.choose_spec
    · exact restrictSupportedClass_kummerBoundaryProduct Λ _ f₀ f (fun j ↦ j.elim0) _ hg
  | n + 1, a, f, hf => by
    obtain ⟨f₀, x, rfl⟩ : ∃ f₀ x, f = Fin.append f₀ (fun _ : Fin 1 ↦ x) :=
      ⟨Fin.init f, f (Fin.last n), by rw [Fin.append_right_eq_snoc, Fin.snoc_init_self]⟩
    have hf₀ (j : Fin n) : f₀ j = (standardOpen (Option m) S none).topIso.inv
        (coordRatio (Option m) S none (some (a j.castSucc))) := by
      rw [← hf j.castSucc, Fin.append_left]
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
    obtain ⟨g₁, hg₁, hres₁⟩ := E.exists_restrictSupportedClass_localizedTopChern_eq sb
      (twistBundleSection_comp_π (Option m) S (some b)) Λ (ℙ(Option m; S) ↘ S ≫ aS) none
      (fun _ ↦ x) (funext fun _ ↦ (twistBundle_sectionCoord (Option m) S (some b) none _).trans
        hx.symm)
    have hY := IsPullback.of_hasPullback ιb i
    have hr : Set.range (pullback.snd ιb i ≫ i).base = Set.range i.base ∩ Set.range ιb.base := by
      rw [Scheme.range_eq_inter_of_isPullback hY pullback.condition, Set.inter_comm]
    have hS : Ideal.span (Set.range (Fin.append f₀ fun _ : Fin 1 ↦ x)) =
        Ideal.span (Set.range fun _ : Fin 1 ↦ x) ⊔ Ideal.span (Set.range f₀) := by
      rw [Fin.range_append, Ideal.span_union, sup_comm]
    have hG := (Scheme.isPullback_zeroLocusSubschemeι_union hS).of_isPullback_inter hg₁ hg hY
    rw [IdealSheafData.inclusion_subschemeι] at hG
    have hc : c ≫ (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) ιb).counit.app _ =
        hyperplaneChernClass (hyperplaneClass Λ m aS) :=
      (E.forgetSupports_localizedTopChern Λ _ sb
        (twistBundleSection_comp_π (Option m) S (some b))).trans
        (topChernClass_twistBundle_eq_hyperplaneChernClass aS)
    refine ⟨pullback ιb i, pullback.snd ιb i ≫ i, inferInstance,
      cupWithSupportsTateObject Λ i ιb _ hr (m := n) (m' := ((1 : ℕ) : ℤ)) γ c ≫
        eqToHom (by push_cast; rfl), _, hG, ?_, ?_, ?_⟩
    · rw [hr, hrange, range_pullbackSnd_twistBundleSection]
      ext y
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, SetLike.mem_coe,
        Fin.forall_fin_succ' (P := fun j ↦ y ∉ standardOpen (Option m) S (some (a j)))]
    · rw [Category.assoc, eqToHom_comp_counit, ← Category.assoc,
        cupWithSupportsTateObject_comp_counit, hforget, hc]
      simp [chernPow, derivedTensorHom]
    · rw [restrictSupportedClass_comp_eqToHom Λ _ _ _ _ hG (by push_cast; rfl),
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
  sorry

end Etale

end AlgebraicGeometry
