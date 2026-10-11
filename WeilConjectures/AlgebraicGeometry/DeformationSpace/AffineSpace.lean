/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone

/-!
# The deformation to the normal cone of the zero section of affine space

For the standard pair `(𝔸^n_B ⟶ B, 0)`, the deformation space of the zero section is
`𝔸^n_{𝔸¹_B} = 𝔸^n_B ×_B 𝔸¹_B`, with coordinates `u_k = x_k / t`, so that `x_k = t u_k`. This is
blueprint `sk-lem-geometry` (4).

## Main statements

- `AlgebraicGeometry.Scheme.Hom.deformationSpaceToAffineSpace`: the morphism
  `D_0 𝔸^n_B ⟶ 𝔸^n_{𝔸¹_B}`
  given by the coordinates `u_k = x_k t⁻¹`.
-/

@[expose] public section

universe u

open CategoryTheory Limits LaurentPolynomial

namespace AlgebraicGeometry.AffineSpace

variable (m : Type u) (S : Scheme.{u})

/-- The coordinate `x_k` of `𝔸^m_S` restricted to an open. -/
noncomputable def coordRes' (O : (𝔸(m; S)).Opens) (k : m) : Γ(𝔸(m; S), O) :=
  (𝔸(m; S)).presheaf.map (homOfLE le_top).op (coord S k)

lemma opensRange_map_ι (W : S.Opens) :
    (map m W.ι).opensRange = (𝔸(m; S) ↘ S) ⁻¹ᵁ W := by
  ext x
  have := Scheme.Pullback.range_fst (𝔸(m; S) ↘ S) W.ι
  have h : Set.range (map m W.ι) = Set.range (pullback.fst (𝔸(m; S) ↘ S) W.ι) := by
    rw [← (isPullback_map (n := m) W.ι).isoPullback_hom_fst, Scheme.Hom.comp_base,
      TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso
        (isPullback_map (n := m) W.ι).isoPullback.hom.base).2, Set.image_univ]
  change x ∈ Set.range _ ↔ _
  rw [h, this, Scheme.Opens.range_ι]
  rfl

lemma preimage_preimage_map_ι (W : S.Opens) :
    map m W.ι ⁻¹ᵁ ((𝔸(m; S) ↘ S) ⁻¹ᵁ W) = ⊤ := by
  rw [← opensRange_map_ι, Scheme.Hom.preimage_opensRange]

lemma bijective_appLE_map_ι (W : S.Opens) :
    Function.Bijective ((map m W.ι).appLE ((𝔸(m; S) ↘ S) ⁻¹ᵁ W) ⊤
      (preimage_preimage_map_ι m S W).ge) := by
  have : IsIso ((map m W.ι).app ((𝔸(m; S) ↘ S) ⁻¹ᵁ W)) :=
    Scheme.Hom.isIso_app _ _ (opensRange_map_ι m S W).ge
  have : IsIso ((𝔸(m; W)).presheaf.map
      (homOfLE (preimage_preimage_map_ι m S W).ge : (⊤ : (𝔸(m; W)).Opens) ⟶ _).op) := by
    rw [show (homOfLE (preimage_preimage_map_ι m S W).ge : (⊤ : (𝔸(m; W)).Opens) ⟶ _) =
      eqToHom (preimage_preimage_map_ι m S W).symm from rfl]
    infer_instance
  rw [Scheme.Hom.appLE]
  exact ConcreteCategory.bijective_of_isIso _

/-- **Sections of affine space over an affine open of the base.** For an affine open `W ⊆ S`,
`Γ(𝔸^m_S, p⁻¹ W) = Γ(S, W)[x_1, …, x_m]`. -/
theorem bijective_eval₂Hom_app_preimage {W : S.Opens} (hW : IsAffineOpen W) :
    Function.Bijective (MvPolynomial.eval₂Hom ((𝔸(m; S) ↘ S).app W).hom
      (coordRes' m S ((𝔸(m; S) ↘ S) ⁻¹ᵁ W))) := by
  have : IsAffine W.toScheme := hW
  set A := (map m W.ι).appLE ((𝔸(m; S) ↘ S) ⁻¹ᵁ W) ⊤ (preimage_preimage_map_ι m S W).ge
  set θ := W.ι.appLE W ⊤ W.ι_preimage_self.ge
  have hθ : Function.Bijective θ.hom := ConcreteCategory.bijective_of_isIso _
  have hE : Function.Bijective (MvPolynomial.eval₂Hom (𝔸(m; W) ↘ W).appTop.hom (coord W)) := by
    have h := isoOfIsAffine_hom_appTop (n := m) (S := W.toScheme)
    have : MvPolynomial.eval₂Hom (𝔸(m; W) ↘ W).appTop.hom (coord W) =
        ((Scheme.ΓSpecIso _).inv ≫ (isoOfIsAffine m W.toScheme).hom.appTop).hom := by
      rw [h, Iso.inv_hom_id_assoc, CommRingCat.hom_ofHom]
    rw [this]
    exact ConcreteCategory.bijective_of_isIso _
  have hmap : Function.Bijective (MvPolynomial.map (σ := m) θ.hom) :=
    ⟨MvPolynomial.map_injective _ hθ.1, MvPolynomial.map_surjective _ hθ.2⟩
  have key : A.hom.comp (MvPolynomial.eval₂Hom ((𝔸(m; S) ↘ S).app W).hom
      (coordRes' m S ((𝔸(m; S) ↘ S) ⁻¹ᵁ W))) =
      (MvPolynomial.eval₂Hom (𝔸(m; W) ↘ W).appTop.hom (coord W)).comp
        (MvPolynomial.map θ.hom) := by
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) fun k ↦ ?_
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C]
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_congr_hom (map_over (n := m) W.ι) _ _ _
          (by simp), ← Scheme.Hom.appLE_comp_appLE (𝔸(m; W.toScheme) ↘ W.toScheme) W.ι W ⊤ ⊤
          W.ι_preimage_self.ge le_top, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X, coordRes']
      rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
      have := map_appTop_coord (n := m) W.ι k
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at this
      exact this
  have hA : Function.Bijective A.hom := bijective_appLE_map_ι m S W
  rw [← Function.Bijective.of_comp_iff' hA, ← RingHom.coe_comp, key, RingHom.coe_comp]
  exact hE.comp hmap
end AlgebraicGeometry.AffineSpace

namespace AlgebraicGeometry.Scheme.Hom

open AffineZariskiSite

variable (n : Type u) (B : Scheme.{u})

/-- The coordinate `x_k` of `𝔸^n_B`, restricted to an affine open. -/
noncomputable def coordRes (U : (𝔸(n; B)).AffineZariskiSite) (k : n) : Γ(𝔸(n; B), U.1) :=
  (𝔸(n; B)).presheaf.map (homOfLE le_top).op (AffineSpace.coord B k)

lemma coordRes_mem (U : (𝔸(n; B)).AffineZariskiSite) (k : n) :
    coordRes n B U k ∈ (AffineSpace.zeroSection n B).ker.siteIdeal U := by
  rw [IdealSheafData.siteIdeal, Scheme.Hom.ker_apply, RingHom.mem_ker, coordRes,
    ← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  change (B.presheaf.map _).hom ((AffineSpace.zeroSection n B).appTop _) = 0
  rw [AffineSpace.zeroSection_appTop_coord, map_zero]

/-- The coordinate `u_k = x_k t⁻¹` on the chart of the deformation space over `U`. -/
noncomputable def uCoord (U : (𝔸(n; B)).AffineZariskiSite) (k : n) :
    (AffineSpace.zeroSection n B).ker.reesPresheaf.obj (.op U) :=
  ⟨LaurentPolynomial.C (coordRes n B U k) * T (-1),
    Ideal.C_mul_T_neg_one_mem_extendedReesAlgebra (coordRes_mem n B U k)⟩

lemma map_uCoord {U U' : (𝔸(n; B)).AffineZariskiSite} (i : U ⟶ U') (k : n) :
    ((AffineSpace.zeroSection n B).ker.reesPresheaf.map i.op).hom (uCoord n B U' k) =
      uCoord n B U k := by
  apply Subtype.ext
  change Ideal.laurentMap _ (LaurentPolynomial.C (coordRes n B U' k) * T (-1)) =
    LaurentPolynomial.C (coordRes n B U k) * T (-1)
  rw [map_mul, Ideal.laurentMap_C, Ideal.laurentMap_T]
  congr 2
  change ((𝔸(n; B)).presheaf.map _ ≫ (𝔸(n; B)).presheaf.map _).hom _ = _
  rw [← Functor.map_comp]
  rfl

/-- The chart `Spec Γ(U)[t, I t⁻¹] ⟶ 𝔸^n_{𝔸¹_B}` of the coordinates `u_k = x_k t⁻¹`. -/
noncomputable def deformationSpaceToAffineSpaceChart (U : (𝔸(n; B)).AffineZariskiSite) :
    (relativeGluingData (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf).functor.obj
      U ⟶ 𝔸(n; 𝔸(ULift.{u} (Fin 1); B)) :=
  AffineSpace.homOfVector
    (colimit.ι (relativeGluingData
      (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf).functor U ≫
      deformationSpaceProj (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B))
    fun k ↦ (ΓSpecIso _).inv (uCoord n B U k)

set_option backward.isDefEq.respectTransparency false in
lemma map_comp_deformationSpaceToAffineSpaceChart {U U' : (𝔸(n; B)).AffineZariskiSite}
    (i : U ⟶ U') :
    (relativeGluingData (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf).functor.map
      i ≫ deformationSpaceToAffineSpaceChart n B U' = deformationSpaceToAffineSpaceChart n B U := by
  rw [deformationSpaceToAffineSpaceChart, deformationSpaceToAffineSpaceChart,
    AffineSpace.comp_homOfVector, ← Category.assoc, colimit.w]
  congr 1
  funext k
  have h := congr($(Scheme.ΓSpecIso_inv_naturality
    ((AffineSpace.zeroSection n B).ker.reesPresheaf.map i.op)) (uCoord n B U' k))
  refine h.symm.trans ?_
  change (ΓSpecIso _).inv (((AffineSpace.zeroSection n B).ker.reesPresheaf.map i.op).hom
    (uCoord n B U' k)) = _
  rw [map_uCoord]
  rfl

/-- **The standard pair.** The morphism `D_0 𝔸^n_B ⟶ 𝔸^n_{𝔸¹_B}` from the deformation space of
the zero section, given by the coordinates `u_k = x_k t⁻¹` over `𝔸¹_B`. -/
noncomputable def deformationSpaceToAffineSpace :
    (AffineSpace.zeroSection n B).ker.deformationSpace ⟶ 𝔸(n; 𝔸(ULift.{u} (Fin 1); B)) :=
  colimit.desc _
    { pt := _
      ι := { app U := deformationSpaceToAffineSpaceChart n B U
             naturality _ _ i := (map_comp_deformationSpaceToAffineSpaceChart n B i).trans
              (Category.comp_id _).symm } }

@[reassoc (attr := simp)]
lemma ι_deformationSpaceToAffineSpace (U : (𝔸(n; B)).AffineZariskiSite) :
    colimit.ι (relativeGluingData
      (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf).functor U ≫
      deformationSpaceToAffineSpace n B = deformationSpaceToAffineSpaceChart n B U :=
  colimit.ι_desc _ _

@[reassoc (attr := simp)]
lemma deformationSpaceToAffineSpace_over :
    deformationSpaceToAffineSpace n B ≫ 𝔸(n; 𝔸(ULift.{u} (Fin 1); B)) ↘ _ =
      deformationSpaceProj (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B) :=
  colimit.hom_ext fun U ↦ by
    rw [ι_deformationSpaceToAffineSpace_assoc, deformationSpaceToAffineSpaceChart,
      AffineSpace.homOfVector_over]

set_option backward.isDefEq.respectTransparency false in
lemma reesToQuotientPolynomial_comp_deformationSpaceToAffineSpace :
    relativeGluingMap (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf
      (AffineSpace.zeroSection n B).ker.coequifibered_toQuotientPolynomialAlgebra
      (AffineSpace.zeroSection n B).ker.reesToQuotientPolynomial ≫
        deformationSpaceToAffineSpace n B =
      (relativeGluingMap (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf
        (AffineSpace.zeroSection n B).ker.coequifibered_toQuotientPolynomialAlgebra
        (AffineSpace.zeroSection n B).ker.reesToQuotientPolynomial ≫
          deformationSpaceProj (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B)) ≫
        AffineSpace.zeroSection n _ := by
  refine colimit.hom_ext fun U ↦ AffineSpace.hom_ext ?_ fun k ↦ ?_
  · simp only [Category.assoc, deformationSpaceToAffineSpace_over, AffineSpace.zeroSection_over,
      Category.comp_id]
  · conv_rhs => simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.zeroSection_appTop_coord, map_zero]
    rw [ι_relativeGluingMap_assoc, ι_deformationSpaceToAffineSpace,
      deformationSpaceToAffineSpaceChart, AffineSpace.comp_homOfVector,
      AffineSpace.homOfVector_appTop_coord, Function.comp_apply]
    have h := congr($(Scheme.ΓSpecIso_inv_naturality
      ((AffineSpace.zeroSection n B).ker.reesToQuotientPolynomial.app (.op U))) (uCoord n B U k))
    refine h.symm.trans ?_
    change (ΓSpecIso ((AffineSpace.zeroSection n B).ker.quotientPolynomialAlgebra.obj (.op U))).inv
      (Ideal.extendedReesAlgebraToPolynomial _ _ Ideal.mk_ker.ge
      ⟨_, Ideal.C_mul_T_neg_one_mem_extendedReesAlgebra (coordRes_mem n B U k)⟩) = 0
    exact (congrArg _ (Ideal.extendedReesAlgebraToPolynomial_C_mul_T_neg_one
      (I := (AffineSpace.zeroSection n B).ker.siteIdeal U) _ Ideal.mk_ker.ge
      (coordRes_mem n B U k))).trans (map_zero _)

/-- The section `s̃` of the deformation space of the zero section is the zero section of
`𝔸^n_{𝔸¹_B}` in the coordinates `u_k`. -/
lemma deformationSpaceSection_comp_deformationSpaceToAffineSpace :
    (AffineSpace.zeroSection n B).deformationSpaceSection ≫ deformationSpaceToAffineSpace n B =
      AffineSpace.zeroSection n _ := by
  rw [deformationSpaceSection, Category.assoc,
    reesToQuotientPolynomial_comp_deformationSpaceToAffineSpace, ← Category.assoc,
    ← Category.assoc, ← deformationSpaceSection,
    deformationSpaceSection_deformationSpaceProj (AffineSpace.zeroSection_over n B),
    Category.id_comp]

end AlgebraicGeometry.Scheme.Hom
