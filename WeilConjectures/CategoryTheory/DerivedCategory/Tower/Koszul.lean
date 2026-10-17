/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.ConeTower
public import WeilConjectures.CategoryTheory.DerivedCategory.KoszulProZero
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The intrinsic Koszul completion and its comparison with the adic completion

Let `A` be a monoidal closed braided Grothendieck abelian category with functorial flat
resolutions, `Λ` a commutative ring, `F : ModuleCat Λ ⥤ A` an exact functor and
`η : 𝟙_ A ⟶ F Λ` a morphism (for sheaves of `Λ`-modules: the constant sheaf functor and its unit
isomorphism). Let `f = (f₁, …, f_r)` be a sequence in `Λ` and `I = (f₁, …, f_r)`.

* A tower `T` of cochain complexes of `Λ`-modules with an augmentation `Λ[0] ⟶ T` gives a
  coefficient tower `F(T)` of `A` with an augmentation from the unit
  (`DerivedCategory.coefficientTower`, `DerivedCategory.coefficientAugmentation`).
* For the Koszul tower `Qₘ = K(Λ; f₁ᵐ, …, f_rᵐ)` (`ExteriorAlgebra.koszulCochainTower`) this
  gives the **intrinsic Koszul completion** `K^{∧,Kos} = R lim_m (K ⊗ᴸ Qₘ)`
  (`DerivedCategory.koszulCompletion`) with the map `κ_K : K ⟶ K^{∧,Kos}` induced by the
  augmentations (`DerivedCategory.koszulCompletionMap`); `K` is *intrinsically derived
  `I`-complete* when `κ_K` is an isomorphism (`DerivedCategory.IsKoszulComplete`).
  Blueprint `def-weil-pbc-intrinsic-koszul-completion`.
* For the quotient tower `Pₙ = Λ ⧸ Iⁿ` this gives the derived limit `R lim_n Kₙ` of the
  reduction tower `Kₙ = K ⊗ᴸ Pₙ` (`DerivedCategory.adicCompletion`) with the completion map
  `comp_K` (`DerivedCategory.adicCompletionMap`, Blueprint `def-weil-pbc-completion-map`).
* **Blueprint `lemma-weil-pbc-koszul-quotient-limit`**: the comparison maps `Qₘ ⟶ Pₘ` induce
  a functorial isomorphism `c_K : K^{∧,Kos} ≅ R lim_n Kₙ`
  (`DerivedCategory.koszulToAdicCompletionIso`) with `c_K ∘ κ_K = comp_K`
  (`DerivedCategory.koszulCompletionMap_comp_koszulToAdicCompletion`), for `Λ` Noetherian. The
  cones of `Qₘ ⟶ Pₘ` form a pro-zero tower in `D(Λ)`
  (`ExteriorAlgebra.isProZero_mappingConeFunctor_koszulCochainToQuot`), hence in `D(A)` after
  applying the exact functor `F`, and pro-zero cones have zero derived limit
  (`DerivedCategory.isIso_rlim_map_reductionTowerMap_app`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex

namespace CochainComplex.mappingCone

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison isomorphism `H (cone φ) ≅ cone (H φ)` is natural in `φ`. -/
@[reassoc]
lemma map_mapHomologicalComplexIso_hom {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁)
    (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂) (H : C ⥤ D)
    [H.Additive] :
    (H.mapHomologicalComplex _).map (map φ₁ φ₂ a b comm) ≫ (mapHomologicalComplexIso φ₂ H).hom =
      (mapHomologicalComplexIso φ₁ H).hom ≫
        map ((H.mapHomologicalComplex _).map φ₁) ((H.mapHomologicalComplex _).map φ₂)
          ((H.mapHomologicalComplex _).map a) ((H.mapHomologicalComplex _).map b)
          (by simp only [← Functor.map_comp, comm]) := by
  rw [← Iso.inv_comp_eq]
  ext n
  dsimp [mapHomologicalComplexIso]
  simp only [mapHomologicalComplexXIso_eq φ₁ H n (n + 1) rfl,
    mapHomologicalComplexXIso_eq φ₂ H n (n + 1) rfl, ext_from_iff _ (n + 1) n rfl,
    ext_to_iff _ _ (n + 1) rfl, mapHomologicalComplexXIso'_hom, mapHomologicalComplexXIso'_inv,
    map, Preadditive.comp_add, Preadditive.add_comp, Category.assoc, inl_v_fst_v_assoc,
    inr_f_fst_v_assoc, inl_v_snd_v_assoc, inr_f_snd_v_assoc, inl_v_fst_v, inr_f_fst_v,
    inl_v_snd_v, inr_f_snd_v, zero_comp, comp_zero, add_zero, zero_add, Category.comp_id,
    ← Functor.map_comp, ← Functor.map_comp_assoc, Functor.mapHomologicalComplex_obj_X,
    Functor.mapHomologicalComplex_map_f]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp [inl_v_desc_f_assoc, inr_f_desc_f_assoc, Cochain.comp_v _ _ (zero_add (-1)) (n + 1)
      (n + 1) n (by lia) (by lia), ← Functor.map_comp, ← Functor.map_comp_assoc]

end CochainComplex.mappingCone

namespace DerivedCategory

open CochainComplex

section Transfer

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] [HasDerivedCategory C]
  [HasDerivedCategory D]

/-- An exact functor sends a tower of cones which is pro-zero in the derived category to a tower
of cones which is pro-zero in the derived category. -/
lemma isProZero_mappingConeFunctor_whiskerRight {X Y : ℕᵒᵖ ⥤ CochainComplex C ℤ} (u : X ⟶ Y)
    (hu : (mappingConeFunctor u ⋙ Q).IsProZero) (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (mappingConeFunctor (Functor.whiskerRight u (G.mapHomologicalComplex _)) ⋙ Q).IsProZero := by
  intro n
  obtain ⟨m, h, hm⟩ := hu n
  refine ⟨m, h, ?_⟩
  have hQ : Q.map ((G.mapHomologicalComplex _).map
      ((mappingConeFunctor u).map (homOfLE h).op)) = 0 := by
    rw [← cancel_epi (G.mapDerivedCategoryFactors.hom.app _), comp_zero,
      ← G.mapDerivedCategoryFactors_hom_naturality]
    rw [show Q.map ((mappingConeFunctor u).map (homOfLE h).op) = 0 from hm, Functor.map_zero,
      zero_comp]
  have e := mappingCone.map_mapHomologicalComplexIso_hom (u.app (op m)) (u.app (op n))
    (X.map (homOfLE h).op) (Y.map (homOfLE h).op) (u.naturality _).symm G
  rw [← cancel_epi (Q.map (mappingCone.mapHomologicalComplexIso (u.app (op m)) G).hom),
    comp_zero]
  change Q.map _ ≫ Q.map (mappingCone.map _ _ _ _ _) = 0
  rw [← Q.map_comp]
  erw [← e]
  rw [Q.map_comp]
  erw [hQ]
  rw [zero_comp]

end Transfer

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [Abelian.HasFunctorialFlatResolution A]
  {Λ : Type w} [CommRing Λ] (F : ModuleCat.{w} Λ ⥤ A) [F.Additive]
  (η : 𝟙_ A ⟶ F.obj (ModuleCat.of Λ Λ))

local instance : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A

section Coefficients

/-- The map `𝟙 ⟶ F(Λ[0])` from the unit of the category of complexes of `A`, induced by `η`. -/
noncomputable def coefficientUnit :
    𝟙_ (CochainComplex A ℤ) ⟶
      (F.mapHomologicalComplex (.up ℤ)).obj ((single _ (.up ℤ) 0).obj (ModuleCat.of Λ Λ)) :=
  (single A (.up ℤ) 0).map η ≫
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app _

/-- The coefficient tower `F(T)` of `A` attached to a tower `T` of complexes of `Λ`-modules. -/
noncomputable abbrev coefficientTower (T : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{w} Λ) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex A ℤ :=
  T ⋙ F.mapHomologicalComplex _

/-- The augmentation `𝟙 ⟶ F(Tₘ)` of the coefficient tower `F(T)` induced by an augmentation
`Λ[0] ⟶ Tₘ` of `T`. -/
noncomputable def coefficientAugmentation {T : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{w} Λ) ℤ}
    (ε : (Functor.const ℕᵒᵖ).obj ((single _ (.up ℤ) 0).obj (ModuleCat.of Λ Λ)) ⟶ T) :
    (Functor.const ℕᵒᵖ).obj (𝟙_ (CochainComplex A ℤ)) ⟶ coefficientTower F T where
  app m := coefficientUnit F η ≫ (F.mapHomologicalComplex _).map (ε.app m)
  naturality m m' h := by
    have := ε.naturality h
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Functor.comp_map,
      Category.assoc, ← Functor.map_comp, ← this]

lemma coefficientAugmentation_comp {T T' : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{w} Λ) ℤ}
    (ε : (Functor.const ℕᵒᵖ).obj ((single _ (.up ℤ) 0).obj (ModuleCat.of Λ Λ)) ⟶ T)
    (φ : T ⟶ T') :
    coefficientAugmentation F η ε ≫ Functor.whiskerRight φ (F.mapHomologicalComplex _) =
      coefficientAugmentation F η (ε ≫ φ) := by
  ext m : 2
  simp [coefficientAugmentation]

end Coefficients

variable {r : ℕ} (f : Fin r → Λ)

/-- The Koszul coefficient tower `Qₘ = F(K(Λ; f₁ᵐ, …, f_rᵐ))` in degrees `[-r, 0]`. -/
noncomputable abbrev koszulCoefficientTower : ℕᵒᵖ ⥤ CochainComplex A ℤ :=
  coefficientTower F (ExteriorAlgebra.koszulCochainTower f)

/-- The quotient coefficient tower `Pₙ = F(Λ ⧸ Iⁿ)` in degree `0`. -/
noncomputable abbrev quotCoefficientTower (I : Ideal Λ) : ℕᵒᵖ ⥤ CochainComplex A ℤ :=
  coefficientTower F (ExteriorAlgebra.quotCochainTower I)

/-- **Blueprint `def-weil-pbc-intrinsic-koszul-completion`.** The intrinsic Koszul completion
`K^{∧,Kos} = R lim_m (K ⊗ᴸ Qₘ)` of `K ∈ D(A)`, where `Qₘ = K(Λ; f₁ᵐ, …, f_rᵐ)` is the Koszul
complex in degrees `[-r, 0]` whose transition map `Q_{m+1} ⟶ Qₘ` is the tensor product over `j`
of the two-term chain maps with degree-zero component the identity and degree-minus-one
component the multiplication by `fⱼ` (`ExteriorAlgebra.koszulCochainTower`, made of the
exterior powers of the diagonal maps). -/
noncomputable def koszulCompletion : DerivedCategory A ⥤ DerivedCategory A :=
  reductionTower (koszulCoefficientTower F f) ⋙ rlim A

/-- **Blueprint `def-weil-pbc-intrinsic-koszul-completion`** (the map `κ`). The map
`κ_K : K ⟶ K^{∧,Kos}` induced by the augmentations `Λ ⟶ Qₘ`. -/
noncomputable def koszulCompletionMap : 𝟭 (DerivedCategory A) ⟶ koszulCompletion F f :=
  completionMap (coefficientAugmentation F η (ExteriorAlgebra.koszulCochainAug f))

/-- **Blueprint `def-weil-pbc-intrinsic-koszul-completion`** (completeness). An object `K` is
*intrinsically derived `I`-complete* when `κ_K : K ⟶ K^{∧,Kos}` is an isomorphism. -/
def IsKoszulComplete (K : DerivedCategory A) : Prop :=
  IsIso ((koszulCompletionMap F η f).app K)

/-- The derived limit `R lim_n Kₙ` of the reduction tower `Kₙ = K ⊗ᴸ Pₙ`, `Pₙ = F(Λ ⧸ Iⁿ)`
(Blueprint `def-weil-pbc-adic-derived-inverse-limit`, see also
`DerivedCategory.adicRlimExplicit` for the product-cone model). -/
noncomputable def adicCompletion (I : Ideal Λ) : DerivedCategory A ⥤ DerivedCategory A :=
  reductionTower (quotCoefficientTower F I) ⋙ rlim A

/-- **Blueprint `def-weil-pbc-completion-map`** (for the quotient tower). The completion map
`comp_K : K ⟶ R lim_n Kₙ` induced by the quotient maps `K ⟶ Kₙ`. -/
noncomputable def adicCompletionMap (I : Ideal Λ) : 𝟭 (DerivedCategory A) ⟶ adicCompletion F I :=
  completionMap (coefficientAugmentation F η (ExteriorAlgebra.quotCochainAug I))

/-- The comparison map `c_K : K^{∧,Kos} ⟶ R lim_n Kₙ` induced by the comparison maps
`Qₘ ⟶ Pₘ` of coefficient towers. -/
noncomputable def koszulToAdicCompletion :
    koszulCompletion F f ⟶ adicCompletion F (Ideal.span (Set.range f)) :=
  Functor.whiskerRight (reductionTowerMap (Functor.whiskerRight
    (ExteriorAlgebra.koszulCochainToQuot f) (F.mapHomologicalComplex _))) (rlim A)

/-- **Blueprint `lemma-weil-pbc-koszul-quotient-limit`** (the triangle). The comparison map
`c_K` satisfies `c_K ∘ κ_K = comp_K`: both units are induced by the augmentations
`Λ ⟶ Qₘ ⟶ Pₘ`. -/
lemma koszulCompletionMap_comp_koszulToAdicCompletion :
    koszulCompletionMap F η f ≫ koszulToAdicCompletion F f =
      adicCompletionMap F η (Ideal.span (Set.range f)) := by
  rw [koszulCompletionMap, koszulToAdicCompletion, completionMap_comp,
    coefficientAugmentation_comp, ExteriorAlgebra.koszulCochainAug_comp_koszulCochainToQuot]
  rfl

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F] [IsNoetherianRing Λ]

/-- **Blueprint `lemma-weil-pbc-koszul-quotient-limit`** (the isomorphism). For `Λ`
Noetherian, the comparison map `c_K : K^{∧,Kos} ⟶ R lim_n Kₙ` is an isomorphism: the cones of
`Qₘ ⟶ Pₘ` form a pro-zero tower. -/
instance isIso_koszulToAdicCompletion : IsIso (koszulToAdicCompletion F f) := by
  have : ∀ K, IsIso ((koszulToAdicCompletion F f).app K) := fun K ↦
    isIso_rlim_map_reductionTowerMap_app _ (isProZero_mappingConeFunctor_whiskerRight _
      (ExteriorAlgebra.isProZero_mappingConeFunctor_koszulCochainToQuot f) F) K
  exact NatIso.isIso_of_isIso_app _

/-- **Blueprint `lemma-weil-pbc-koszul-quotient-limit`.** The functorial isomorphism
`c_K : K^{∧,Kos} ≅ R lim_n Kₙ`, with `c_K ∘ κ_K = comp_K`
(`DerivedCategory.koszulCompletionMap_comp_koszulToAdicCompletion`). -/
noncomputable def koszulToAdicCompletionIso :
    koszulCompletion F f ≅ adicCompletion F (Ideal.span (Set.range f)) :=
  asIso (koszulToAdicCompletion F f)

/-- An object is intrinsically derived complete if and only if its completion map
`comp_K : K ⟶ R lim_n Kₙ` is an isomorphism. -/
lemma isKoszulComplete_iff (K : DerivedCategory A) :
    IsKoszulComplete F η f K ↔ IsIso ((adicCompletionMap F η (Ideal.span (Set.range f))).app K) := by
  rw [IsKoszulComplete, ← koszulCompletionMap_comp_koszulToAdicCompletion, NatTrans.comp_app]
  constructor
  · intro h
    infer_instance
  · intro h
    exact IsIso.of_isIso_comp_right _ ((koszulToAdicCompletion F f).app K)

end DerivedCategory
