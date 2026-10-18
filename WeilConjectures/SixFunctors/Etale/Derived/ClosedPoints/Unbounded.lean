/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Hypercohomology
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitRange
public import WeilConjectures.CategoryTheory.DerivedCategory.Products
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Cohomology of unbounded complexes with acyclic cohomology sheaves

-/

@[expose] public section

universe v u

open CategoryTheory Category Limits Opposite Pretriangulated

namespace CategoryTheory.Functor

variable {𝒞 : Type*} [Category 𝒞]

/-- If the successor transitions `G (k + 1) ⟶ G k` of a tower are isomorphisms for `k ≥ n₀`,
then so are all transitions `G b ⟶ G a` for `n₀ ≤ a ≤ b`. -/
lemma isIso_map_homOfLE_op_of_isIso_succ (G : ℕᵒᵖ ⥤ 𝒞) (n₀ : ℕ)
    (hG : ∀ k : ℕ, n₀ ≤ k → IsIso (G.map (homOfLE k.le_succ).op)) {a b : ℕ} (hab : a ≤ b)
    (ha : n₀ ≤ a) : IsIso (G.map (homOfLE hab).op) := by
  induction b, hab using Nat.le_induction with
  | base =>
    have : IsIso (homOfLE (le_refl a)).op := inferInstanceAs (IsIso (𝟙 (op a)))
    infer_instance
  | succ b hab ih =>
    have := hG b (ha.trans hab)
    have e : (homOfLE (hab.trans b.le_succ)).op =
        (homOfLE b.le_succ).op ≫ (homOfLE hab).op := rfl
    rw [e, G.map_comp]
    infer_instance

end CategoryTheory.Functor

namespace DerivedCategory

variable {R : Type v} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)]
  [Abelian.HasKInjectiveResolutions (ModuleCat.{v} R)]

/-- **Milnor sequence for an essentially constant tower.** Let `c` be a homotopy limit cone over
a tower `F` in `D(R)` whose transitions are isomorphisms on `Hᵐ` and on `H^{m-1}`. Then all
legs of `c` are isomorphisms on `Hᵐ`: in the Milnor triangle, `1 - t` is surjective on
`H^{m-1}(∏ Fₙ)`, so that `Hᵐ(c.pt)` is the kernel of `1 - t` on `Hᵐ(∏ Fₙ)`, that is, the
inverse limit of the constant tower `Hᵐ(Fₙ)`. -/
theorem isIso_homologyFunctor_map_π_of_isHomotopyLimit_of_isIso
    {F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{v} R)} {c : Cone F} (hc : IsHomotopyLimit c) (m : ℤ)
    (h₀ : ∀ (a b : ℕ) (hab : a ≤ b),
      IsIso ((homologyFunctor (ModuleCat.{v} R) m).map (F.map (homOfLE hab).op)))
    (h₁ : ∀ (a b : ℕ) (hab : a ≤ b),
      IsIso ((homologyFunctor (ModuleCat.{v} R) (m - 1)).map (F.map (homOfLE hab).op)))
    (n : ℕ) : IsIso ((homologyFunctor (ModuleCat.{v} R) m).map (c.π.app (op n))) := by
  let P := Fan.mk (∏ᶜ fun n : ℕ ↦ F.obj (op n)) (Pi.π fun n : ℕ ↦ F.obj (op n))
  let hP : IsLimit P := productIsProduct _
  obtain ⟨δ, hT⟩ := hc.exists_distTriang hP
  let H := homologyFunctor (ModuleCat.{v} R) m
  let H' := homologyFunctor (ModuleCat.{v} R) (m - 1)
  let hPH : IsLimit (Fan.mk (H.obj P.pt) fun n ↦ H.map (P.proj n)) :=
    isLimitFanMkObjOfIsLimit H _ _ hP
  let hPH' : IsLimit (Fan.mk (H'.obj P.pt) fun n ↦ H'.map (P.proj n)) :=
    isLimitFanMkObjOfIsLimit H' _ _ hP
  -- `1 - t` is surjective on `H^{m-1}(∏ Fₙ)`
  have hepi : Epi (H'.map (𝟙 P.pt - towerShift hP)) := by
    rw [H'.map_sub, H'.map_id]
    refine ModuleCat.epi_one_sub_of_epi (F := F ⋙ H') hPH' _ (fun k ↦ ?_) fun k ↦ ?_
    · dsimp only [Fan.mk, Fan.proj, Functor.comp_map, Discrete.natTrans_app]
      rw [← H'.map_comp, ← H'.map_comp]
      exact congrArg H'.map (towerShift_proj hP k)
    · have := h₁ k (k + 1) k.le_succ
      dsimp only [Functor.comp_map]
      infer_instance
  have hδ := (HomologySequence.epi_homologyMap_mor₂_iff _ hT (m - 1) m (by lia)).1 hepi
  have hmono : Mono (H.map (Fan.IsLimit.lift hP fun n ↦ c.π.app (op n))) :=
    (HomologySequence.mono_homologyMap_mor₁_iff _ hT (m - 1) m (by lia)).2 hδ
  have hex := (ShortComplex.moduleCat_exact_iff _).1 (HomologySequence.exact₂ _ hT m)
  have hz : H.map (Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)) ≫
      H.map (𝟙 P.pt - towerShift hP) = 0 :=
    (H.map_comp _ _).symm.trans ((congrArg H.map (comp_distTriang_mor_zero₁₂ _ hT)).trans
      (H.map_zero _ _))
  have hsub (y : H.obj P.pt) : H.map (𝟙 P.pt - towerShift hP) y = y - H.map (towerShift hP) y := by
    rw [H.map_sub, H.map_id]
    rfl
  -- notation for the tower `Hᵐ(Fₙ)`
  let A (k : ℕ) := H.obj (F.obj (op k))
  let pr (k : ℕ) : H.obj P.pt ⟶ A k := H.map (P.proj k)
  let f (k : ℕ) : A (k + 1) ⟶ A k := H.map (F.map (homOfLE k.le_succ).op)
  have hext (y y' : H.obj P.pt) (h : ∀ k, pr k y = pr k y') : y = y' :=
    ModuleCat.ext_of_isLimit_fan hPH h
  have hf (k : ℕ) : Function.Bijective (f k).hom := by
    have := h₀ k (k + 1) k.le_succ
    exact (ConcreteCategory.isIso_iff_bijective (f k)).1 inferInstance
  have htm (k : ℕ) : H.map (towerShift hP) ≫ pr k = pr (k + 1) ≫ f k := by
    simp only [pr, f, ← H.map_comp, towerShift_proj]
  have ht (k : ℕ) (y : H.obj P.pt) : pr k (H.map (towerShift hP) y) = f k (pr (k + 1) y) := by
    have := ConcreteCategory.congr_hom (htm k) y
    rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
  have hliftm (k : ℕ) :
      H.map (Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)) ≫ pr k = H.map (c.π.app (op k)) := by
    simp only [pr, ← H.map_comp, Fan.IsLimit.fac]
  have hlift (k : ℕ) (x : H.obj c.pt) :
      pr k (H.map (Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)) x) =
        H.map (c.π.app (op k)) x := by
    have := ConcreteCategory.congr_hom (hliftm k) x
    rwa [ConcreteCategory.comp_apply] at this
  -- elements of the kernel of `1 - t` are determined by any of their components
  have hker (y : H.obj P.pt) (hy : H.map (𝟙 P.pt - towerShift hP) y = 0) (k : ℕ) :
      pr k y = f k (pr (k + 1) y) := by
    rw [← ht]
    rw [hsub, sub_eq_zero] at hy
    exact congrArg (pr k) hy
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero _).2 fun x₀ hxx' ↦ ?_, fun z ↦ ?_⟩
  · let y := H.map (Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)) x₀
    have hy : H.map (𝟙 P.pt - towerShift hP) y = 0 := by
      have := ConcreteCategory.congr_hom hz x₀
      rwa [ConcreteCategory.comp_apply] at this
    have hk (k : ℕ) : pr k y = 0 ↔ pr (k + 1) y = 0 := by
      rw [hker y hy k]
      exact ⟨fun h ↦ (hf k).1 (h.trans (map_zero _).symm), fun h ↦ by rw [h, map_zero]⟩
    have h0 (k : ℕ) : pr k y = 0 ↔ pr 0 y = 0 := by
      induction k with
      | zero => rfl
      | succ k ih => rw [← hk, ih]
    have hy0 : y = 0 := hext _ _ fun k ↦ by
      rw [map_zero]
      exact (h0 k).2 ((h0 n).1 (by rw [hlift]; exact hxx'))
    exact (ModuleCat.mono_iff_injective _).1 hmono (hy0.trans (map_zero _).symm)
  · let g (k : ℕ) : A k ⟶ A 0 := H.map (F.map (homOfLE (Nat.zero_le k)).op)
    have hg (k : ℕ) : Function.Bijective (g k).hom := by
      have := h₀ 0 k (Nat.zero_le k)
      exact (ConcreteCategory.isIso_iff_bijective (g k)).1 inferInstance
    have hgf (k : ℕ) (a : A (k + 1)) : g k (f k a) = g (k + 1) a := by
      have e : (homOfLE (Nat.zero_le (k + 1))).op =
          (homOfLE k.le_succ).op ≫ (homOfLE (Nat.zero_le k)).op := rfl
      simp only [g, f, e, F.map_comp, H.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
      rfl
    let w := g n z
    let y (k : ℕ) : A k := (Function.surjInv (hg k).2) w
    have hgy (k : ℕ) : g k (y k) = w := Function.surjInv_eq (hg k).2 w
    obtain ⟨Y, hY⟩ := ModuleCat.exists_proj_eq_of_isLimit_fan hPH y
    have hYk (k : ℕ) : pr k Y = y k := hY k
    have hYker : H.map (𝟙 P.pt - towerShift hP) Y = 0 := by
      rw [hsub, sub_eq_zero]
      refine hext _ _ fun k ↦ ?_
      rw [ht, hYk, hYk]
      exact (hg k).1 (by rw [hgf, hgy, hgy])
    obtain ⟨x, hx⟩ := hex Y hYker
    refine ⟨x, ?_⟩
    rw [← hlift]
    exact ((congrArg (pr n) hx).trans (hYk n)).trans ((hg n).1 (by rw [hgy]))

end DerivedCategory

namespace CategoryTheory.Pretriangulated

variable {𝒯 : Type*} [Category 𝒯] [HasZeroObject 𝒯] [HasShift 𝒯 ℤ] [Preadditive 𝒯]
  [∀ n : ℤ, (shiftFunctor 𝒯 n).Additive] [Pretriangulated 𝒯]

/-- Every tower in a pretriangulated category with countable products has a homotopy limit
cone: complete `1 - t : ∏ Fₙ ⟶ ∏ Fₙ` to a distinguished triangle. -/
lemma exists_isHomotopyLimit [HasLimitsOfShape (Discrete ℕ) 𝒯] (F : ℕᵒᵖ ⥤ 𝒯) :
    ∃ c : Cone F, IsHomotopyLimit c := by
  let P := Fan.mk (∏ᶜ fun n : ℕ ↦ F.obj (op n)) (Pi.π fun n : ℕ ↦ F.obj (op n))
  let hP : IsLimit P := productIsProduct _
  obtain ⟨M, p, δ, hT⟩ := distinguished_cocone_triangle₁ (𝟙 P.pt - towerShift hP)
  have hp : p ≫ towerShift hP = p := by
    have : p ≫ (𝟙 P.pt - towerShift hP) = 0 := comp_distTriang_mor_zero₁₂ _ hT
    rw [Preadditive.comp_sub, comp_id, sub_eq_zero] at this
    exact this.symm
  let c : Cone F := Cone.mk M (NatTrans.ofOpSequence (fun n ↦ p ≫ P.proj n) fun n ↦ by
    dsimp
    rw [id_comp, assoc, ← towerShift_proj hP n, ← assoc, hp])
  have hlift : Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) = p :=
    Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
      rw [Fan.IsLimit.fac]
      rfl
  exact ⟨c, P, hP, δ, by rwa [hlift]⟩

end CategoryTheory.Pretriangulated

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- The tower `n ↦ τ^{≥ -n} K` of the truncations of an object `K` of `D(C)`. -/
noncomputable def truncGETower (K : DerivedCategory C) : ℕᵒᵖ ⥤ DerivedCategory C :=
  Functor.ofOpSequence (X := fun n : ℕ ↦ (TStructure.t.truncGE (-(n : ℤ))).obj K)
    fun n ↦ (TStructure.t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by lia)).app K

instance (K : DerivedCategory C) (n : ℕ) : ((truncGETower K).obj (op n)).IsGE (-(n : ℤ)) :=
  inferInstanceAs (((TStructure.t.truncGE (-(n : ℤ))).obj K).IsGE (-(n : ℤ)))

/-- The cone over the tower `n ↦ τ^{≥ -n} K` with point `K` given by the truncation maps. -/
noncomputable def truncGETowerCone (K : DerivedCategory C) : Cone (truncGETower K) :=
  Cone.mk K (NatTrans.ofOpSequence (fun n ↦ (TStructure.t.truncGEπ (-(n : ℤ))).app K)
    fun n ↦ by
      dsimp [truncGETower]
      rw [id_comp, Functor.ofOpSequence_map_homOfLE_succ, TStructure.t.π_natTransTruncGEOfLE_app])

@[simp]
lemma truncGETowerCone_π_app (K : DerivedCategory C) (n : ℕ) :
    (truncGETowerCone K).π.app (op n) = (TStructure.t.truncGEπ (-(n : ℤ))).app K :=
  rfl

lemma truncGETower_map_succ (K : DerivedCategory C) (n : ℕ) :
    (truncGETower K).map (homOfLE n.le_succ).op =
      (TStructure.t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by lia)).app K :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

end DerivedCategory

namespace CategoryTheory.Functor

section Products

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete ℕ) C]
  {R : Type v} [Ring R] [HasDerivedCategory (ModuleCat.{v} R)]
  [Abelian.HasKInjectiveResolutions (ModuleCat.{v} R)]

/-- The unbounded right derived functor of an additive functor `F : C ⥤ ModuleCat R` preserving
countable products preserves countable products: it is computed by applying `F` termwise to
K-injective complexes, these are closed under products, and products of complexes of modules are
products in `D(R)` since products of modules are exact. -/
lemma preservesLimitsOfShape_discrete_nat_rightDerivedFunctor (F : C ⥤ ModuleCat.{v} R)
    [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F] :
    PreservesLimitsOfShape (Discrete ℕ) F.rightDerivedFunctor := by
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let a : G ⋙ DerivedCategory.Q ≅
      q ⋙ (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors _).symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _
  let β : G ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    a.hom ≫ Functor.whiskerLeft q F.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C) F.rightDerivedFunctor).hom
  have hβ (I : CochainComplex C ℤ) [I.IsKInjective] : IsIso (β.app I) := by
    dsimp [β, a]
    infer_instance
  have hfamily (K : ℕ → DerivedCategory C) :
      PreservesLimit (Discrete.functor K) F.rightDerivedFunctor := by
    choose I hI e using fun n ↦ DerivedCategory.exists_iso_Q_obj_of_isKInjective (K n)
    have : ∀ n, (I n).IsKInjective := hI
    have : ∀ n, IsIso (β.app (I n)) := fun n ↦ hβ (I n)
    have : (∏ᶜ I).IsKInjective := CochainComplex.isKInjective_of_isLimitFan (productIsProduct I)
    have : IsIso (β.app (∏ᶜ I)) := hβ _
    have hQ := DerivedCategory.isLimitFanMkQObjOfIsKInjective (productIsProduct I)
    let hK : IsLimit (Fan.mk (DerivedCategory.Q.obj (∏ᶜ I))
        fun n ↦ DerivedCategory.Q.map (Pi.π I n) ≫ (e n).some.inv) :=
      Fan.IsLimit.ofIsos hQ (fun n ↦ (e n).some) (Iso.refl _) fun n ↦ by simp
    have hG : IsLimit (Fan.mk (G.obj (∏ᶜ I)) fun n ↦ G.map (Pi.π I n)) :=
      isLimitFanMkObjOfIsLimit G _ _ (productIsProduct I)
    have hQG := DerivedCategory.isLimitFanMkQObj hG
    have hR : IsLimit (Fan.mk (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj (∏ᶜ I)))
        fun n ↦ F.rightDerivedFunctor.map (DerivedCategory.Q.map (Pi.π I n) ≫ (e n).some.inv)) :=
      Fan.IsLimit.ofIsos hQG
        (fun n ↦ F.rightDerivedFunctor.mapIso (e n).some ≪≫ (asIso (β.app (I n))).symm)
        (asIso (β.app (∏ᶜ I))).symm fun n ↦ by
          have hn := β.naturality (Pi.π I n)
          dsimp at hn ⊢
          rw [IsIso.inv_comp_eq, ← F.rightDerivedFunctor.map_comp_assoc, assoc, Iso.inv_hom_id,
            comp_id, ← reassoc_of% hn, IsIso.hom_inv_id, comp_id]
    exact preservesLimit_of_preserves_limit_cone hK ((isLimitMapConeFanMkEquiv _ _ _).symm hR)
  exact preservesLimitsOfShape_of_discrete _

end Products

end CategoryTheory.Functor
