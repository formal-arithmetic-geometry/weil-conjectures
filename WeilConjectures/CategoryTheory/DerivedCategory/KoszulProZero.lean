/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.KoszulCochainTower
public import WeilConjectures.CategoryTheory.DerivedCategory.ConeTowerHomology

/-!
# The Koszul tower is pro-isomorphic to the quotient tower

Let `R` be a Noetherian ring, `f = (f₁, …, f_r)` and `I = (f₁, …, f_r)`. The comparison maps
`K(f^m) ⟶ (R ⧸ Iᵐ)[0]` from the Koszul tower to the quotient tower
(`ExteriorAlgebra.koszulCochainToQuot`) have a pro-zero tower of mapping cones in the derived
category `D(R)` (`ExteriorAlgebra.isProZero_mappingConeFunctor_koszulCochainToQuot`). This is the
algebraic input of Blueprint `lemma-weil-pbc-koszul-quotient-limit`:

* in negative degrees the homology of the Koszul tower is pro-zero by the Artin–Rees lemma
  (`ExteriorAlgebra.exists_homologyMap_koszulTower_eq_zero`);
* in degree `0` the map `H⁰(K(f^m)) = R ⧸ (f₁ᵐ, …, f_rᵐ) ⟶ R ⧸ Iᵐ` is surjective, and its kernel
  is killed by the transition to any level `a` with `Iᵇ ⊆ (f₁ᵃ, …, f_rᵃ)`.

The homology of the cones is then pro-zero by the long exact homology sequences
(`DerivedCategory.exists_homologyFunctor_map_mappingConeFunctor_eq_zero`), and the cones are
bounded, so the tower of cones is pro-zero (`DerivedCategory.isProZero_of_homology`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite HomologicalComplex CochainComplex DerivedCategory

namespace ExteriorAlgebra

variable {R : Type u} [CommRing R] {r : ℕ}

section Chain

lemma isZero_koszulCochainTower_X_of_lt (f : Fin r → R) (m : ℕ) {p : ℤ} (hp : p < -r) :
    IsZero (((koszulCochainTower f).obj (op m)).X p) := by
  have hn : r < (-p).toNat := by lia
  have : Fact (r < (-p).toNat) := ⟨hn⟩
  refine IsZero.of_iso ?_ (((koszulTower f).obj (op m)).extendXIso koszulEmbedding
    (i := (-p).toNat) (by rw [koszulEmbedding_f]; lia))
  exact ModuleCat.isZero_of_subsingleton _

lemma exactAt_koszulCochainTower (f : Fin r → R) (m : ℕ) {p : ℤ} (hp : 0 < p ∨ p < -r) :
    ((koszulCochainTower f).obj (op m)).ExactAt p := by
  refine ShortComplex.exact_of_isZero_X₂ _ ?_
  rcases hp with hp | hp
  · exact isZero_koszulCochainTower_X f m hp
  · exact isZero_koszulCochainTower_X_of_lt f m hp

lemma koszulCochainTower_d_zero_one (f : Fin r → R) (m : ℕ) :
    ((koszulCochainTower f).obj (op m)).d 0 1 = 0 :=
  (isZero_koszulCochainTower_X f m (by lia)).eq_of_tgt _ _

instance (f : Fin r → R) (m : ℕ) : IsIso (((koszulCochainTower f).obj (op m)).iCycles 0) :=
  ((koszulCochainTower f).obj (op m)).isIso_iCycles 0 1 (by simp)
    (koszulCochainTower_d_zero_one f m)

lemma koszulCochainTower_d_neg_one_zero (f : Fin r → R) (m : ℕ) :
    ((koszulCochainTower f).obj (op m)).d (-1) 0 =
      (((koszulTower f).obj (op m)).extendXIso koszulEmbedding (i := 1) (by simp)).hom ≫
        ModuleCat.ofHom (koszulBoundary R r (f ^ m) 0) ≫ (koszulCochainXZeroIso f m).inv := by
  rw [koszulCochainTower, Functor.comp_obj, ComplexShape.Embedding.extendFunctor_obj,
    extend_d_eq _ koszulEmbedding (i := 1) (j := 0) (by simp) koszulEmbedding_f_zero]
  rfl

/-- Every element of `⋀⁰ Rʳ` that lies in `(f₁ᵐ, …, f_rᵐ)` (read through `⋀⁰ Rʳ ≅ R`) gives the
zero class in `H⁰(K(f^m))`. -/
lemma homologyπ_eq_zero_of_mem (f : Fin r → R) (m : ℕ)
    (c : ((koszulCochainTower f).obj (op m)).cycles 0)
    (hc : exteriorPower.zeroEquiv R _ ((koszulCochainXZeroIso f m).hom
      (((koszulCochainTower f).obj (op m)).iCycles 0 c)) ∈ Ideal.span (Set.range (f ^ m))) :
    ((koszulCochainTower f).obj (op m)).homologyπ 0 c = 0 := by
  set K := (koszulCochainTower f).obj (op m)
  have hmem : (koszulCochainXZeroIso f m).hom (K.iCycles 0 c) ∈
      LinearMap.range (koszulBoundary R r (f ^ m) 0) := by
    rw [← ker_koszulAug, LinearMap.mem_ker, koszulAug_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact hc
  obtain ⟨y, hy⟩ := hmem
  let y' : K.X (-1) :=
    (((koszulTower f).obj (op m)).extendXIso koszulEmbedding (i := 1) (by simp)).inv y
  have hc' : c = K.toCycles (-1) 0 y' := by
    apply (ModuleCat.mono_iff_injective (K.iCycles 0)).1 inferInstance
    rw [← ModuleCat.comp_apply, toCycles_i, koszulCochainTower_d_neg_one_zero]
    simp only [y', ModuleCat.comp_apply, Iso.inv_hom_id_apply, ModuleCat.hom_ofHom]
    rw [show koszulBoundary R r (f ^ m) 0 y = _ from hy, Iso.hom_inv_id_apply]
  rw [hc', ← ModuleCat.comp_apply, toCycles_comp_homologyπ]
  rfl

end Chain

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

local notation "H" => DerivedCategory.homologyFunctor (ModuleCat.{u} R)

lemma homologyFunctor_map_Q_map_eq_zero_iff {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : K ⟶ L) (p : ℤ) : (H p).map (Q.map g) = 0 ↔ homologyMap g p = 0 := by
  rw [← cancel_mono ((homologyFunctorFactors _ p).hom.app L), zero_comp,
    homologyFunctorFactors_hom_naturality, ← cancel_epi ((homologyFunctorFactors _ p).inv.app K),
    comp_zero, Iso.inv_hom_id_app_assoc]

lemma homologyFunctorFactors_hom_app_apply {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : K ⟶ L) (p : ℤ) (x : (H p).obj (Q.obj K)) :
    (homologyFunctorFactors _ p).hom.app L ((H p).map (Q.map g) x) =
      homologyMap g p ((homologyFunctorFactors _ p).hom.app K x) := by
  rw [← ModuleCat.comp_apply, homologyFunctorFactors_hom_naturality, ModuleCat.comp_apply]

lemma isZero_homologyFunctor_koszulCochainTower (f : Fin r → R) (m : ℕ) {p : ℤ}
    (hp : 0 < p ∨ p < -r) : IsZero ((H p).obj (Q.obj ((koszulCochainTower f).obj (op m)))) :=
  ((exactAt_koszulCochainTower f m hp).isZero_homology).of_iso
    ((homologyFunctorFactors _ p).app _)

lemma isZero_homologyFunctor_single (M : ModuleCat.{u} R) {p : ℤ} (hp : p ≠ 0) :
    IsZero ((H p).obj (Q.obj ((single _ (.up ℤ) 0).obj M))) :=
  (isZero_single_obj_homology _ _ _ hp).of_iso ((homologyFunctorFactors _ p).app _)

/-- In negative degrees the homology tower of the Koszul tower is pro-zero. -/
lemma exists_homologyFunctor_map_koszulCochainTower_eq_zero [IsNoetherianRing R] (f : Fin r → R)
    (n a : ℕ) : ∃ (b : ℕ) (hab : a ≤ b), (H (-(n + 1 : ℕ))).map
      (Q.map ((koszulCochainTower f).map (homOfLE hab).op)) = 0 := by
  obtain ⟨k, hk⟩ := exists_homologyMap_koszulTower_eq_zero f a n
  refine ⟨k + a, Nat.le_add_left a k, ?_⟩
  rw [homologyFunctor_map_Q_map_eq_zero_iff]
  have hj : koszulEmbedding.f (n + 1) = -(n + 1 : ℕ) := by rw [koszulEmbedding_f]
  have := extendHomologyIso_hom_naturality ((koszulTower f).map (homOfLE
    (Nat.le_add_left a k)).op) koszulEmbedding hj
  rw [hk, comp_zero, ← cancel_mono (extendHomologyIso _ koszulEmbedding hj).hom, zero_comp] at *
  exact this

variable (r) in
/-- The comparison map `H⁰(K(f^m)) ⟶ H⁰((R ⧸ Iᵐ)[0]) = R ⧸ Iᵐ` is the degree `0` map. -/
lemma singleObjHomologySelfIso_homologyMap_koszulCochainToQuot (f : Fin r → R) (m : ℕ)
    (c : ((koszulCochainTower f).obj (op m)).cycles 0) :
    (singleObjHomologySelfIso _ _ _).hom (homologyMap (koszulCochainToQuotApp r f m) 0
      (((koszulCochainTower f).obj (op m)).homologyπ 0 c)) =
      koszulQuot _ m ((koszulCochainXZeroIso f m).hom
        (((koszulCochainTower f).obj (op m)).iCycles 0 c)) := by
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, homologyπ_naturality_assoc,
    homologyπ_singleObjHomologySelfIso_hom, ← singleObjCyclesSelfIso_hom, ← cyclesMap_i_assoc]
  simp [koszulCochainToQuotApp_f]

/-- In degree `0`, the comparison map of homology `H⁰(K(f^m)) ⟶ H⁰((R ⧸ Iᵐ)[0])` is surjective. -/
lemma homologyFunctor_map_koszulCochainToQuot_surjective (f : Fin r → R) (m : ℕ) :
    Function.Surjective ((H 0).map (Q.map ((koszulCochainToQuot f).app (op m)))) := by
  intro μ
  set K := (koszulCochainTower f).obj (op m)
  set e := (homologyFunctorFactors (ModuleCat.{u} R) 0).hom
  obtain ⟨w, hw⟩ := koszulAug_surjective (r := r) (Ideal.span (Set.range f) ^ m)
    ((singleObjHomologySelfIso _ _ _).hom (e.app _ μ))
  let c : K.cycles 0 := inv (K.iCycles 0) ((koszulCochainXZeroIso f m).inv w)
  refine ⟨e.inv.app _ (K.homologyπ 0 c), ?_⟩
  apply (ModuleCat.mono_iff_injective (e.app _ ≫ (singleObjHomologySelfIso _ _ _).hom)).1
    inferInstance
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, homologyFunctorFactors_hom_app_apply,
    ← ModuleCat.comp_apply (e.inv.app K) (e.app K), Iso.inv_hom_id_app]
  erw [singleObjHomologySelfIso_homologyMap_koszulCochainToQuot r f m c]
  simp only [c, ← ModuleCat.comp_apply, IsIso.inv_hom_id, Category.id_comp, Iso.inv_hom_id]
  exact hw

/-- In degree `0`, the transition maps of the homology of the Koszul tower eventually kill the
kernel of the comparison map to the quotient tower: if `Iᵇ ⊆ (f₁ᵃ, …, f_rᵃ)`, an element of
`H⁰(K(f^b)) = R ⧸ (f^b)` which vanishes in `R ⧸ Iᵇ` vanishes in `R ⧸ (f^a)`. -/
lemma exists_homologyFunctor_map_koszulCochainTower_eq_zero_of_eq_zero (f : Fin r → R) (a : ℕ) :
    ∃ (b : ℕ) (hab : a ≤ b), ∀ x : (H 0).obj (Q.obj ((koszulCochainTower f).obj (op b))),
      (H 0).map (Q.map ((koszulCochainToQuot f).app (op b))) x = 0 →
        (H 0).map (Q.map ((koszulCochainTower f).map (homOfLE hab).op)) x = 0 := by
  have hrad : Ideal.span (Set.range f) ≤ (Ideal.span (Set.range (f ^ a))).radical := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨a, Ideal.subset_span ⟨i, rfl⟩⟩
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (Submodule.fg_span (Set.finite_range f))
  refine ⟨N + a, Nat.le_add_left a N, fun x hx ↦ ?_⟩
  set e := (homologyFunctorFactors (ModuleCat.{u} R) 0).hom
  set K := (koszulCochainTower f).obj (op (N + a))
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ 0)).1 inferInstance (e.app _ x)
  apply (ModuleCat.mono_iff_injective (e.app _)).1 inferInstance
  rw [homologyFunctorFactors_hom_app_apply, map_zero, ← hc, ← ModuleCat.comp_apply,
    homologyπ_naturality, ModuleCat.comp_apply]
  apply homologyπ_eq_zero_of_mem
  rw [← ModuleCat.comp_apply, cyclesMap_i, ModuleCat.comp_apply, koszulCochainTower_map_f_zero]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  have h0 := congr_arg (e.app _) hx
  rw [homologyFunctorFactors_hom_app_apply, map_zero, ← hc] at h0
  have h1 := congr_arg (singleObjHomologySelfIso _ _ _).hom h0
  erw [singleObjHomologySelfIso_homologyMap_koszulCochainToQuot r f (N + a) c, map_zero] at h1
  simp only [koszulQuot, ModuleCat.hom_ofHom, koszulAug_apply,
    Ideal.Quotient.eq_zero_iff_mem] at h1
  refine hN (Ideal.pow_le_pow_right (Nat.le_add_right N a) h1)

/-- **The Koszul tower is pro-isomorphic to the quotient tower.** For a Noetherian ring `R`,
the tower of mapping cones of the comparison maps `K(f^m) ⟶ (R ⧸ Iᵐ)[0]`,
`I = (f₁, …, f_r)`, is pro-zero in the derived category `D(R)`. -/
theorem isProZero_mappingConeFunctor_koszulCochainToQuot [IsNoetherianRing R] (f : Fin r → R) :
    (mappingConeFunctor (koszulCochainToQuot f) ⋙ Q).IsProZero := by
  set u := koszulCochainToQuot f
  have hY (m : ℕᵒᵖ) {p : ℤ} (hp : p ≠ 0) :
      IsZero ((H p).obj (Q.obj ((quotCochainTower r (Ideal.span (Set.range f))).obj m))) :=
    isZero_homologyFunctor_single _ hp
  have hX (m : ℕᵒᵖ) {p : ℤ} (hp : 0 < p ∨ p < -r) :
      IsZero ((H p).obj (Q.obj ((koszulCochainTower f).obj m))) :=
    isZero_homologyFunctor_koszulCochainTower f m.unop hp
  have elim {M : ModuleCat.{u} R} (h : IsZero M) (x : M) : x = 0 :=
    have := ModuleCat.isZero_iff_subsingleton.1 h
    Subsingleton.elim _ _
  refine isProZero_of_homology _ (-(r : ℤ) - 1) 0 (fun m ↦ ?_) (fun m ↦ ?_) (fun p a ↦ ?_)
  · rw [isGE_iff]
    intro i hi
    exact isZero_homologyFunctor_obj_mappingCone u m i (i + 1) rfl (hY m (by lia))
      (hX m (by lia))
  · rw [isLE_iff]
    intro i hi
    exact isZero_homologyFunctor_obj_mappingCone u m i (i + 1) rfl (hY m (by lia))
      (hX m (by lia))
  · refine exists_homologyFunctor_map_mappingConeFunctor_eq_zero u p (p + 1) rfl
      (fun a ↦ ?_) (fun a ↦ ?_) a
    · by_cases h₁ : 0 < p + 1 ∨ p + 1 < -r
      · exact ⟨a, le_rfl, fun x _ ↦ by rw [elim (hX _ h₁) x, map_zero]⟩
      by_cases h₂ : p + 1 = 0
      · obtain ⟨b, hab, hb⟩ := exists_homologyFunctor_map_koszulCochainTower_eq_zero_of_eq_zero f a
        rw [h₂]
        exact ⟨b, hab, hb⟩
      · obtain ⟨n, hn⟩ : ∃ n : ℕ, p + 1 = -(n + 1 : ℕ) := ⟨(-(p + 1) - 1).toNat, by lia⟩
        obtain ⟨b, hab, hb⟩ := exists_homologyFunctor_map_koszulCochainTower_eq_zero f n a
        rw [hn]
        exact ⟨b, hab, fun x _ ↦ by rw [hb]; rfl⟩
    · by_cases hp : p = 0
      · subst hp
        refine ⟨a, le_rfl, fun y ↦ ?_⟩
        exact homologyFunctor_map_koszulCochainToQuot_surjective f a _
      · exact ⟨a, le_rfl, fun y ↦ ⟨0, by rw [elim (hY _ hp) y, map_zero, map_zero]⟩⟩

end ExteriorAlgebra
