/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.Koszul
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Retraction
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone

/-!
# Finite reduction of the adic completion

Let `A`, `F : ModuleCat Λ ⥤ A`, `η : 𝟙_ A ≅ F Λ`, `f = (f₁, …, f_r)` and `I = (f₁, …, f_r)` be as
in `WeilConjectures.CategoryTheory.DerivedCategory.Tower.Koszul`, with `Λ` Noetherian, and let
`a ≥ 1`. Put `Pₐ = F(Λ ⧸ Iᵃ)[0]`. This file proves Blueprint
`lemma-weil-pbc-adic-completion-reduction`: if `Pₐ` is perfect (only its dualizability in
`D(A)` is used), projection to level `a` induces a functorial isomorphism
`(R lim_n Kₙ) ⊗ᴸ Pₐ ≅ K ⊗ᴸ Pₐ = Kₐ` (`DerivedCategory.adicCompletionReductionIso`).

Following the blueprint, the quotient tower is replaced by the Koszul tower `Qₘ`
(`DerivedCategory.koszulToAdicCompletionIso`). Tensoring with the dualizable object `Pₐ`
commutes with the derived limit. For `m ≥ a` the complex `Qₘ ⊗ Pₐ` has zero differential, and
it retracts onto its degree-zero part `Pₐ`; every composite of `a` successive transition maps
factors through this retraction, since in negative degrees it is a multiple of some `fⱼᵃ ∈ Iᵃ`.
Hence the tower `K ⊗ᴸ Qₘ ⊗ᴸ Pₐ` is pro-isomorphic to the constant tower `K ⊗ᴸ Pₐ`
(`CategoryTheory.Pretriangulated.IsHomotopyLimit.isIso_π_comp_of_retraction`).

The killing of the negative-degree terms is formalized for any additive functor
`G : ModuleCat Λ ⥤ A` sending the `Λ`-linear maps in `J • Hom` to zero
(`DerivedCategory.KillsIdeal`), here `G = F(-) ⊗ F(Λ ⧸ Iᵃ)` and `J = Iᵃ`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex Pretriangulated

namespace ExteriorAlgebra

variable {R : Type u} [CommRing R] {r : ℕ}

section SmulTop

variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

lemma smulRight_mem_smul_top (J : Ideal R) (φ : M →ₗ[R] R) {y : N}
    (hy : y ∈ J • (⊤ : Submodule R N)) :
    φ.smulRight y ∈ J • (⊤ : Submodule R (M →ₗ[R] N)) := by
  induction hy using Submodule.smul_induction_on with
  | smul c hc z _ =>
    have : φ.smulRight (c • z) = c • φ.smulRight z := by ext; simp [smul_comm c]
    rw [this]
    exact Submodule.smul_mem_smul hc trivial
  | add y z hy hz =>
    have : φ.smulRight (y + z) = φ.smulRight y + φ.smulRight z := by ext; simp
    rw [this]
    exact add_mem hy hz

/-- A linear map out of a finite free module whose image lies in `J • N` lies in `J • Hom`. -/
lemma mem_smul_top_of_forall_mem [Module.Free R M] [Module.Finite R M] (J : Ideal R)
    (g : M →ₗ[R] N) (hg : ∀ x, g x ∈ J • (⊤ : Submodule R N)) :
    g ∈ J • (⊤ : Submodule R (M →ₗ[R] N)) := by
  let b := Module.Free.chooseBasis R M
  have : g = ∑ i, (b.coord i).smulRight (g (b i)) := b.ext fun j ↦ by
    simp [Finsupp.single_apply, Fintype.sum_eq_single j]
  rw [this]
  exact Submodule.sum_mem _ fun i _ ↦ smulRight_mem_smul_top J _ (hg _)

end SmulTop

instance (n : ℕ) : Module.Free R (⋀[R]^n (Fin r →₀ R)) :=
  Module.Free.of_basis ((Finsupp.basisSingleOne (R := R) (ι := Fin r)).exteriorPower n)

instance (n : ℕ) : Module.Finite R (⋀[R]^n (Fin r →₀ R)) :=
  Module.Finite.of_basis ((Finsupp.basisSingleOne (R := R) (ι := Fin r)).exteriorPower n)

lemma koszulBoundary_eq_sum (g : Fin r → R) (n : ℕ) :
    koszulBoundary R r g n = ∑ j, g j • koszulBoundary R r (Pi.single j 1) n := by
  ext x
  have h : Finsupp.linearCombination R g =
      ∑ j, g j • Finsupp.linearCombination R (Pi.single j (1 : R)) := by
    ext i
    simp [Finset.sum_pi_single, Pi.single_apply]
  simp only [koszulBoundary, LinearMap.codRestrict_apply, LinearMap.coe_comp,
    Function.comp_apply, Submodule.coe_subtype, LinearMap.coe_fn_sum, Finset.sum_apply,
    LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower]
  rw [h, map_sum]
  simp

/-- The Koszul differential of `K(g)` is a combination of the `gⱼ`. -/
lemma koszulBoundary_mem_smul_top (g : Fin r → R) (n : ℕ) :
    koszulBoundary R r g n ∈
      Ideal.span (Set.range g) • (⊤ : Submodule R (_ →ₗ[R] ⋀[R]^n (Fin r →₀ R))) := by
  rw [koszulBoundary_eq_sum]
  exact Submodule.sum_mem _ fun j _ ↦
    Submodule.smul_mem_smul (Ideal.subset_span ⟨j, rfl⟩) trivial

/-- In positive degrees the transition maps `koszulMap c` are combinations of the `cⱼ`. -/
lemma koszulMap_mem_smul_top' (c : Fin r → R) (n : ℕ) :
    koszulMap c (n + 1) ∈ Ideal.span (Set.range c) •
      (⊤ : Submodule R (⋀[R]^(n + 1) (Fin r →₀ R) →ₗ[R] ⋀[R]^(n + 1) (Fin r →₀ R))) :=
  mem_smul_top_of_forall_mem _ _ (koszulMap_mem_smul_top c n)

end ExteriorAlgebra

namespace DerivedCategory

open ExteriorAlgebra

section Kill

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A]
  {Λ : Type w} [CommRing Λ] (G : ModuleCat.{w} Λ ⥤ A) [G.Additive] (J : Ideal Λ)

/-- An additive functor `G : ModuleCat Λ ⥤ A` *kills* the ideal `J` if it sends every linear map
in `J • Hom(X, Y)` to zero (for instance `M ⊗ F(-)` for an object `M` killed by `J`). -/
def KillsIdeal : Prop :=
  ∀ {X Y : ModuleCat.{w} Λ} (g : X →ₗ[Λ] Y), g ∈ J • (⊤ : Submodule Λ (X →ₗ[Λ] Y)) →
    G.map (ModuleCat.ofHom g) = 0

variable {r : ℕ} (f : Fin r → Λ)

/-- The tower `G(K(f^m))` of complexes of `A`. -/
noncomputable abbrev koszulKillTower : ℕᵒᵖ ⥤ CochainComplex A ℤ :=
  koszulCochainTower f ⋙ G.mapHomologicalComplex _

/-- The inverse `⋀⁰ Rʳ ≅ R` of `ExteriorAlgebra.koszulUnit`. -/
noncomputable def koszulCounit : ModuleCat.of Λ (⋀[Λ]^0 (Fin r →₀ Λ)) ⟶ ModuleCat.of Λ Λ :=
  ModuleCat.ofHom (exteriorPower.zeroEquiv Λ (Fin r →₀ Λ)).toLinearMap

@[simp]
lemma koszulUnit_koszulCounit : koszulUnit (r := r) ≫ koszulCounit (Λ := Λ) = 𝟙 _ := by
  ext x
  simp [koszulUnit, koszulCounit]

@[simp]
lemma koszulCounit_koszulUnit : koszulCounit (Λ := Λ) ≫ koszulUnit (r := r) = 𝟙 _ := by
  ext x
  simp [koszulUnit, koszulCounit]

variable {G J}

lemma koszulKillTower_d_eq_zero (hG : KillsIdeal G J) (m : ℕ)
    (hm : Ideal.span (Set.range (f ^ m)) ≤ J) (p q : ℤ) :
    ((koszulKillTower G f).obj (op m)).d p q = 0 := by
  by_cases hpq : p + 1 = q
  · by_cases hq : q = 0
    · subst hq
      obtain rfl : p = -1 := by lia
      change G.map (((koszulCochainTower f).obj (op m)).d (-1) 0) = 0
      rw [koszulCochainTower_d_neg_one_zero, G.map_comp, G.map_comp,
        hG _ (Submodule.smul_mono_left hm (koszulBoundary_mem_smul_top _ 0)), zero_comp, comp_zero]
    · by_cases hq' : 0 < q
      · exact (G.map_isZero (isZero_koszulCochainTower_X f m hq')).eq_of_tgt _ _
      · obtain ⟨n, hn⟩ : ∃ n : ℕ, q = -(n + 1 : ℕ) := ⟨(-q - 1).toNat, by lia⟩
        change G.map (((koszulCochainTower f).obj (op m)).d p q) = 0
        rw [koszulCochainTower, Functor.comp_obj, ComplexShape.Embedding.extendFunctor_obj,
          extend_d_eq _ koszulEmbedding (i := n + 2) (j := n + 1) (by simp; lia)
            (by simp; lia), G.map_comp, G.map_comp]
        have : ((koszulTower f).obj (op m)).d (n + 2) (n + 1) =
            ModuleCat.ofHom (koszulBoundary Λ r (f ^ m) (n + 1)) := by
          simp [koszulTower, koszulComplex, ChainComplex.of_d]
        rw [this, hG _ (Submodule.smul_mono_left hm (koszulBoundary_mem_smul_top _ _)), zero_comp,
          comp_zero]
  · exact HomologicalComplex.shape _ _ _ (by simpa using hpq)

/-- The projection `G(K(f^m)) ⟶ G(Λ)[0]` to the degree-zero term, a morphism of complexes when
`(f₁ᵐ, …, f_rᵐ) ⊆ J` and `G` kills `J`. -/
noncomputable def koszulKillProj (hG : KillsIdeal G J) (m : ℕ)
    (hm : Ideal.span (Set.range (f ^ m)) ≤ J) :
    (koszulKillTower G f).obj (op m) ⟶ (single A (.up ℤ) 0).obj (G.obj (ModuleCat.of Λ Λ)) :=
  mkHomToSingle (G.map ((koszulCochainXZeroIso f m).hom ≫ koszulCounit)) fun i _ ↦ by
    rw [koszulKillTower_d_eq_zero f hG m hm, zero_comp]

lemma koszulKillProj_f (hG : KillsIdeal G J) (m : ℕ) (hm : Ideal.span (Set.range (f ^ m)) ≤ J) :
    (koszulKillProj f hG m hm).f 0 =
      G.map ((koszulCochainXZeroIso f m).hom ≫ koszulCounit) ≫ (singleObjXSelf _ 0 _).inv :=
  mkHomToSingle_f _ _

variable (G) in
/-- The inclusion `G(Λ)[0] ⟶ G(K(f^m))` of the degree-zero term. -/
noncomputable def koszulKillIncl (m : ℕ) :
    (single A (.up ℤ) 0).obj (G.obj (ModuleCat.of Λ Λ)) ⟶ (koszulKillTower G f).obj (op m) :=
  mkHomFromSingle (G.map (koszulUnit ≫ (koszulCochainXZeroIso f m).inv)) fun k hk ↦
    (G.map_isZero (isZero_koszulCochainTower_X f m (by simp at hk; lia))).eq_of_tgt _ _

lemma koszulKillIncl_f (m : ℕ) :
    (koszulKillIncl G f m).f 0 =
      (singleObjXSelf _ 0 _).hom ≫ G.map (koszulUnit ≫ (koszulCochainXZeroIso f m).inv) :=
  mkHomFromSingle_f _ _

@[reassoc]
lemma koszulKillIncl_proj (hG : KillsIdeal G J) (m : ℕ)
    (hm : Ideal.span (Set.range (f ^ m)) ≤ J) :
    koszulKillIncl G f m ≫ koszulKillProj f hG m hm = 𝟙 _ := by
  refine from_single_hom_ext ?_
  rw [comp_f, koszulKillIncl_f, koszulKillProj_f, Category.assoc, ← G.map_comp_assoc,
    Category.assoc, Iso.inv_hom_id_assoc, koszulUnit_koszulCounit, G.map_id, Category.id_comp,
    Iso.hom_inv_id, id_f]

@[reassoc]
lemma koszulKillTower_map_proj (hG : KillsIdeal G J) {m m' : ℕ} (h : m' ≤ m)
    (hm : Ideal.span (Set.range (f ^ m)) ≤ J) (hm' : Ideal.span (Set.range (f ^ m')) ≤ J) :
    (koszulKillTower G f).map (homOfLE h).op ≫ koszulKillProj f hG m' hm' =
      koszulKillProj f hG m hm := by
  refine to_single_hom_ext ?_
  change G.map (((koszulCochainTower f).map (homOfLE h).op).f 0) ≫ _ = _
  rw [comp_f, koszulKillProj_f, koszulKillProj_f, koszulCochainTower_map_f_zero,
    ← G.map_comp_assoc]
  simp

@[reassoc]
lemma koszulKillIncl_map (m m' : ℕ) (h : m' ≤ m) :
    koszulKillIncl G f m ≫ (koszulKillTower G f).map (homOfLE h).op = koszulKillIncl G f m' := by
  refine from_single_hom_ext ?_
  change _ ≫ G.map (((koszulCochainTower f).map (homOfLE h).op).f 0) = _
  rw [koszulKillIncl_f, koszulKillIncl_f, koszulCochainTower_map_f_zero, Category.assoc,
    ← G.map_comp]
  simp

/-- If `G` kills `J ⊇ (f₁ᴺ, …, f_rᴺ)`, every transition map `G(K(f^{m + N})) ⟶ G(K(f^m))`
factors through the degree-zero term `G(Λ)[0]`. -/
@[reassoc]
lemma koszulKillTower_map_eq (hG : KillsIdeal G J) {m N : ℕ}
    (hm : Ideal.span (Set.range (f ^ (m + N))) ≤ J) (hN : Ideal.span (Set.range (f ^ N)) ≤ J) :
    (koszulKillTower G f).map (homOfLE (Nat.le_add_right m N)).op =
      koszulKillProj f hG (m + N) hm ≫ koszulKillIncl G f m := by
  ext p
  by_cases hp : p = 0
  · subst hp
    change G.map (((koszulCochainTower f).map _).f 0) = _
    rw [comp_f, koszulKillProj_f, koszulKillIncl_f, koszulCochainTower_map_f_zero,
      Category.assoc, Iso.inv_hom_id_assoc, ← G.map_comp, Category.assoc,
      koszulCounit_koszulUnit_assoc]
  · rw [comp_f, ((single A (.up ℤ) 0).obj _).isZero_single_obj_X _ _ _ hp |>.eq_of_src
      ((koszulKillIncl G f m).f p) 0, comp_zero]
    by_cases hp' : 0 < p
    · exact (G.map_isZero (isZero_koszulCochainTower_X f _ hp')).eq_of_src _ _
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, p = -(n + 1 : ℕ) := ⟨(-p - 1).toNat, by lia⟩
      subst hn
      change G.map (((koszulCochainTower f).map _).f _) = 0
      rw [koszulCochainTower, Functor.comp_map, ComplexShape.Embedding.extendFunctor_map,
        extendMap_f _ koszulEmbedding (i := n + 1) (by simp), koszulTower_map_f,
        G.map_comp, G.map_comp]
      simp only [unop_op, Nat.add_sub_cancel_left]
      rw [hG _ (Submodule.smul_mono_left hN (koszulMap_mem_smul_top' _ n)), zero_comp, comp_zero]

end Kill

section Monoidal

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [Abelian.HasFunctorialFlatResolution A]

local instance : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A

/-- The comparison `Q X ⊗ᴸ Q Y ⟶ Q (X ⊗ Y)` is an isomorphism when `X` is K-flat. -/
lemma isIso_μ_Q_of_kFlat_left (X Y : CochainComplex A ℤ)
    (hX : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat X) :
    IsIso (Functor.LaxMonoidal.μ (Q : CochainComplex A ℤ ⥤ DerivedCategory A) X Y) := by
  have := DerivedMonoidal.isIso_counit_app_app_of_kFlat_left Qh
    (HomotopyCategory.quasiIso A (.up ℤ)) ((HomotopyCategory.quotient A (.up ℤ)).obj X)
    ((HomotopyCategory.quotient A (.up ℤ)).obj Y)
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hX)
  have h : IsIso (Functor.LaxMonoidal.μ Qh ((HomotopyCategory.quotient A (.up ℤ)).obj X)
      ((HomotopyCategory.quotient A (.up ℤ)).obj Y)) := this
  change IsIso ((_ ⊗ₘ _) ≫ (Functor.LaxMonoidal.μ Qh _ _ ≫ Qh.map _) ≫ _)
  infer_instance

variable {Λ : Type w} [CommRing Λ] [Linear Λ A] [MonoidalLinear Λ A]
  (F : ModuleCat.{w} Λ ⥤ A) [F.Additive] [F.Linear Λ]
  (η : 𝟙_ A ⟶ F.obj (ModuleCat.of Λ Λ)) [IsIso η] {r : ℕ} (f : Fin r → Λ) (a : ℕ)

/-- The coefficient `F(Λ ⧸ Iᵃ)`, `I = (f₁, …, f_r)`. -/
noncomputable abbrev quotObj : A :=
  F.obj ((Ideal.quotPowFunctor (Ideal.span (Set.range f))).obj (op a))

/-- The complex `Pₐ = F(Λ ⧸ Iᵃ)[0]`. -/
noncomputable abbrev quotComplex : CochainComplex A ℤ :=
  (single A (.up ℤ) 0).obj (quotObj F f a)

/-- The functor `F(-) ⊗ F(Λ ⧸ Iᵃ)`. -/
noncomputable abbrev reductionFunctor : ModuleCat.{w} Λ ⥤ A :=
  F ⋙ (curriedTensor A).flip.obj (quotObj F f a)

lemma smul_id_quotObj {c : Λ} (hc : c ∈ Ideal.span (Set.range f) ^ a) :
    c • 𝟙 (quotObj F f a) = 0 := by
  rw [← F.map_id, ← Functor.map_smul]
  convert F.map_zero _ _
  ext x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk _ (c * y) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ hc)

lemma killsIdeal_reductionFunctor :
    KillsIdeal (reductionFunctor F f a) (Ideal.span (Set.range f) ^ a) := by
  intro X Y g hg
  induction hg using Submodule.smul_induction_on with
  | smul c hc h _ =>
    change F.map (ModuleCat.ofHom (c • h)) ▷ quotObj F f a = 0
    rw [show ModuleCat.ofHom (c • h) = c • ModuleCat.ofHom h from rfl, Functor.map_smul,
      MonoidalLinear.smul_whiskerRight, ← Category.comp_id (F.map (ModuleCat.ofHom h) ▷ _),
      ← Linear.comp_smul, ← MonoidalCategory.whiskerLeft_id, ← MonoidalLinear.whiskerLeft_smul,
      smul_id_quotObj F f a hc, MonoidalPreadditive.whiskerLeft_zero, comp_zero]
  | add g h _ _ hg hh =>
    rw [show ModuleCat.ofHom (g + h) = ModuleCat.ofHom g + ModuleCat.ofHom h from rfl,
      Functor.map_add, hg, hh, add_zero]

lemma span_pow_le {m : ℕ} (h : a ≤ m) :
    Ideal.span (Set.range (f ^ m)) ≤ Ideal.span (Set.range f) ^ a := by
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  rw [Pi.pow_apply, ← Nat.sub_add_cancel h, pow_add]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.subset_span ⟨j, rfl⟩) a)

variable (hflat : ∀ (X : ModuleCat.{w} Λ) [Module.Free Λ X] [Module.Finite Λ X],
  ObjectProperty.flat (F.obj X))

include hflat in
lemma kFlat_koszulCoefficientTower (m : ℕ) :
    (HomologicalComplex.quasiIso A (.up ℤ)).kFlat ((koszulCoefficientTower F f).obj (op m)) := by
  have : ((koszulCoefficientTower F f).obj (op m)).IsStrictlyLE 0 :=
    (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi ↦
      F.map_isZero (isZero_koszulCochainTower_X f m hi)
  have : ((koszulCoefficientTower F f).obj (op m)).IsStrictlyGE (-r) :=
    (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi ↦
      F.map_isZero (isZero_koszulCochainTower_X_of_lt f m hi)
  refine CochainComplex.kFlat_of_bounded_of_flat _ (-r) 0 fun p ↦ ?_
  by_cases hp : 0 < p
  · exact ObjectProperty.flat_of_isZero (F.map_isZero (isZero_koszulCochainTower_X f m hp))
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = -(n : ℤ) := ⟨(-p).toNat, by lia⟩
    exact ObjectProperty.prop_of_iso _ (F.mapIso (((koszulTower f).obj (op m)).extendXIso
      koszulEmbedding (i := n) (by simp))).symm (hflat _)

/-- `Qₘ ⊗ Pₐ ≅ F(K(f^m)) ⊗ F(Λ ⧸ Iᵃ)`, computed termwise. -/
noncomputable def quotTensorIso (m : ℕ) :
    (koszulCoefficientTower F f).obj (op m) ⊗ quotComplex F f a ≅
      (koszulKillTower (reductionFunctor F f a) f).obj (op m) :=
  CochainComplex.mapBifunctorSingle₂Iso (curriedTensor A) (quotObj F f a) _

@[reassoc]
lemma quotTensorIso_hom_naturality {m m' : ℕ} (h : m' ≤ m) :
    (koszulCoefficientTower F f).map (homOfLE h).op ▷ quotComplex F f a ≫
      (quotTensorIso F f a m').hom =
      (quotTensorIso F f a m).hom ≫ (koszulKillTower (reductionFunctor F f a) f).map
        (homOfLE h).op :=
  CochainComplex.mapBifunctorSingle₂Iso_hom_naturality _ _ _

/-- `F(Λ) ⊗ F(Λ ⧸ Iᵃ) ≅ F(Λ ⧸ Iᵃ)`, through `η`. -/
noncomputable def unitQuotIso :
    (single A (.up ℤ) 0).obj ((reductionFunctor F f a).obj (ModuleCat.of Λ Λ)) ≅
      quotComplex F f a :=
  (single A (.up ℤ) 0).mapIso (whiskerRightIso (asIso η).symm _ ≪≫ λ_ _)

/-- The map `Qₘ ⊗ᴸ Pₐ ⟶ Pₐ` projecting onto the degree-zero part, for `m ≥ a`. -/
noncomputable def reductionProj (m : ℕ) (hm : a ≤ m) :
    Q.obj ((koszulCoefficientTower F f).obj (op m)) ⊗ Q.obj (quotComplex F f a) ⟶
      Q.obj (quotComplex F f a) :=
  Functor.LaxMonoidal.μ Q _ _ ≫ Q.map ((quotTensorIso F f a m).hom ≫
    koszulKillProj f (killsIdeal_reductionFunctor F f a) m (span_pow_le f a hm) ≫
      (unitQuotIso F η f a).hom)

include hflat in
/-- The inclusion `Pₐ ⟶ Qₘ ⊗ᴸ Pₐ` of the degree-zero part. -/
noncomputable def reductionIncl (m : ℕ) :
    Q.obj (quotComplex F f a) ⟶
      Q.obj ((koszulCoefficientTower F f).obj (op m)) ⊗ Q.obj (quotComplex F f a) :=
  have := isIso_μ_Q_of_kFlat_left _ (quotComplex F f a) (kFlat_koszulCoefficientTower F f hflat m)
  Q.map ((unitQuotIso F η f a).inv ≫ koszulKillIncl (reductionFunctor F f a) f m ≫
    (quotTensorIso F f a m).inv) ≫ inv (Functor.LaxMonoidal.μ Q _ _)

include hflat in
lemma reductionIncl_proj (m : ℕ) (hm : a ≤ m) :
    reductionIncl F η f a hflat m ≫ reductionProj F η f a m hm = 𝟙 _ := by
  simp only [reductionIncl, reductionProj, Category.assoc, IsIso.inv_hom_id_assoc,
    ← Q.map_comp, Iso.inv_hom_id_assoc, koszulKillIncl_proj_assoc, Iso.inv_hom_id, Q.map_id]

lemma whiskerRight_reductionProj {m m' : ℕ} (h : m' ≤ m) (hm' : a ≤ m') :
    Q.map ((koszulCoefficientTower F f).map (homOfLE h).op) ▷ Q.obj (quotComplex F f a) ≫
      reductionProj F η f a m' hm' = reductionProj F η f a m (hm'.trans h) := by
  simp only [reductionProj, Functor.LaxMonoidal.μ_natural_left_assoc, ← Q.map_comp,
    reassoc_of% quotTensorIso_hom_naturality,
    koszulKillTower_map_proj_assoc]

include hflat in
lemma reductionIncl_whiskerRight {m m' : ℕ} (h : m' ≤ m) :
    reductionIncl F η f a hflat m ≫
      Q.map ((koszulCoefficientTower F f).map (homOfLE h).op) ▷ Q.obj (quotComplex F f a) =
      reductionIncl F η f a hflat m' := by
  have := isIso_μ_Q_of_kFlat_left _ (quotComplex F f a) (kFlat_koszulCoefficientTower F f hflat m)
  have := isIso_μ_Q_of_kFlat_left _ (quotComplex F f a)
    (kFlat_koszulCoefficientTower F f hflat m')
  simp only [reductionIncl, Category.assoc, IsIso.inv_comp_eq,
    Functor.LaxMonoidal.μ_natural_left, IsIso.hom_inv_id_assoc, ← Q.map_comp]
  congr 2
  rw [Iso.inv_comp_eq, ← reassoc_of% quotTensorIso_hom_naturality, Iso.hom_inv_id_assoc,
    koszulKillIncl_map]

include hflat in
lemma whiskerRight_eq_reductionProj_reductionIncl {m N : ℕ} (hm : a ≤ m + N) (hN : a ≤ N) :
    Q.map ((koszulCoefficientTower F f).map (homOfLE (Nat.le_add_right m N)).op) ▷
      Q.obj (quotComplex F f a) =
      reductionProj F η f a (m + N) hm ≫ reductionIncl F η f a hflat m := by
  have := isIso_μ_Q_of_kFlat_left _ (quotComplex F f a) (kFlat_koszulCoefficientTower F f hflat m)
  rw [← cancel_mono (Functor.LaxMonoidal.μ Q _ _), Functor.LaxMonoidal.μ_natural_left]
  simp only [reductionProj, reductionIncl, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
    ← Q.map_comp]
  congr 2
  rw [Iso.inv_hom_id_assoc, ← koszulKillTower_map_eq_assoc f (killsIdeal_reductionFunctor F f a)
    _ (span_pow_le f a hN), ← quotTensorIso_hom_naturality_assoc, Iso.hom_inv_id,
    Category.comp_id]

end Monoidal

end DerivedCategory
