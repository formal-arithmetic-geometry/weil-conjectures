/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportedExteriorProductNaturality
public import WeilConjectures.CategoryTheory.Triangulated.BinaryBiproductCone

/-!
# K-flat support-acyclic resolutions

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
def-pur-supported-exterior-product.md (blueprint: proposition-purity-vector-bundles).

Two K-flat representatives of a bounded below complex are connected by a K-flat homotopy pushout
of a K-flat roof, followed by a further K-flat resolution on which the support unit is invertible.

## Main statements

- `exists_kFlat_quasiIso_pushout`: K-flat homotopy pushouts of quasi-isomorphisms.
- `exists_common_kFlat_supportResolution`: two K-flat representatives map to a common
  K-flat representative on which the support unit is invertible.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [HasSmallSiteSheafify C]

omit [Abelian.HasFunctorialFlatResolution C] [HasSmallSiteSheafify C] in
/-- A homotopy pushout of a span of quasi-isomorphisms between K-flat complexes: the mapping
cone of `R ⟶ P ⊞ P'` receives quasi-isomorphisms from `P` and `P'` which agree on `R` in the
derived category, and it is K-flat. -/
theorem exists_kFlat_quasiIso_pushout {T : Scheme.{u}}
    {R P P' : CochainComplex (Sheaf T.smallEtaleTopology C) ℤ} (s : R ⟶ P) (a : R ⟶ P')
    [IsIso (DerivedCategory.Q.map s)] [IsIso (DerivedCategory.Q.map a)]
    (hR : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat R)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hP' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P') :
    ∃ (H : CochainComplex (Sheaf T.smallEtaleTopology C) ℤ) (b : P ⟶ H) (c : P' ⟶ H),
      IsIso (DerivedCategory.Q.map b) ∧ IsIso (DerivedCategory.Q.map c) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat H ∧
      DerivedCategory.Q.map s ≫ DerivedCategory.Q.map b =
        DerivedCategory.Q.map a ≫ DerivedCategory.Q.map c := by
  let φ : R ⟶ P ⊞ P' := biprod.lift s (-a)
  let ψ := CochainComplex.mappingCone.inr φ
  have : PreservesBinaryBiproducts (DerivedCategory.Q (C := Sheaf T.smallEtaleTopology C)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let e := DerivedCategory.Q.mapBiprod P P'
  have hT : Pretriangulated.Triangle.mk
      (biprod.lift (DerivedCategory.Q.map s) (DerivedCategory.Q.map (-a)))
      (e.inv ≫ DerivedCategory.Q.map ψ)
      (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle φ)).mor₃ ∈
        distTriang _ := by
    refine Pretriangulated.isomorphic_distinguished _
      (DerivedCategory.mappingCone_triangle_distinguished φ) _
      (Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_)
    · simp only [e, φ, Pretriangulated.Triangle.mk_mor₁, Iso.symm_hom, Iso.refl_hom,
        Category.id_comp, Functor.mapBiprod_inv, biprod.lift_desc]
      rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add]
      exact congrArg DerivedCategory.Q.map biprod.lift_eq.symm
    · simp only [Pretriangulated.Triangle.mk_mor₂, Iso.symm_hom, Iso.refl_hom, Category.comp_id]
      rfl
    · simp
  obtain ⟨θ, h₁, h₂⟩ := Pretriangulated.exists_iso_of_distTriang_biprod_lift _ _ _ _ hT
  have hinl : biprod.inl ≫ e.inv = DerivedCategory.Q.map (biprod.inl : P ⟶ P ⊞ P') := by
    simp [e]
  have hinr : biprod.inr ≫ e.inv = DerivedCategory.Q.map (biprod.inr : P' ⟶ P ⊞ P') := by
    simp [e]
  have hc : DerivedCategory.Q.map (biprod.inr ≫ ψ) ≫ θ.hom = 𝟙 _ := by
    rw [Functor.map_comp, ← hinr, Category.assoc, Category.assoc, ← Category.assoc e.inv]
    exact h₁
  have hb : DerivedCategory.Q.map (biprod.inl ≫ ψ) ≫ θ.hom =
      inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map a := by
    rw [Functor.map_comp, ← hinl, Category.assoc, Category.assoc, ← Category.assoc e.inv, h₂,
      Functor.map_neg, Preadditive.comp_neg, neg_neg]
  refine ⟨CochainComplex.mappingCone φ, biprod.inl ≫ ψ, biprod.inr ≫ ψ, ?_, ?_, ?_, ?_⟩
  · have : IsIso (DerivedCategory.Q.map (biprod.inl ≫ ψ) ≫ θ.hom) := by
      rw [hb]
      infer_instance
    exact IsIso.of_isIso_comp_right _ θ.hom
  · have : IsIso (DerivedCategory.Q.map (biprod.inr ≫ ψ) ≫ θ.hom) := by
      rw [hc]
      infer_instance
    exact IsIso.of_isIso_comp_right _ θ.hom
  · have h₃ := (HomotopyCategory.quasiIso (Sheaf T.smallEtaleTopology C)
      (.up ℤ)).kFlat.ext_of_isTriangulatedClosed₃
      _ (HomotopyCategory.mappingCone_triangleh_distinguished φ)
      ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hR)
      ((HomotopyCategory.kFlat_quotient_obj_iff _).2 (CochainComplex.kFlat_biprod hP hP'))
    exact (HomotopyCategory.kFlat_quotient_obj_iff _).1 h₃
  · rw [← cancel_mono θ.hom, Category.assoc, Category.assoc, hb, hc, IsIso.hom_inv_id_assoc,
      Category.comp_id]

section Resolution

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

omit [HasSmallSiteSheafify C] in
/-- Every object of the derived category with bounded below cohomology has a K-flat
representative on which the support unit is invertible, provided K-flat complexes with
bounded below cohomology admit quasi-isomorphisms to such representatives. -/
theorem exists_kFlat_supportResolution_iso
    (hres : ∀ (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P → ∀ n : ℤ,
        (DerivedCategory.Q.obj P).IsGE n →
      ∃ (I : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ) (φ : P ⟶ I), QuasiIso φ ∧
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat I ∧
        IsIso (exteriorSupportResolutionUnit C i I))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C)) (n : ℤ) (hn : K.IsGE n) :
    ∃ (I : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ) (_ : DerivedCategory.Q.obj I ≅ K),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat I ∧
        IsIso (exteriorSupportResolutionUnit C i I) := by
  obtain ⟨P, π, hπ, -, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat
    (DerivedCategory.Q.objPreimage K)
  have : IsIso (DerivedCategory.Q.map π) := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := π)).2 hπ
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map π) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have : (DerivedCategory.Q.obj P).IsGE n := DerivedCategory.TStructure.t.isGE_of_iso e.symm n
  obtain ⟨I, φ, hφ, hI, hu⟩ := hres P hP n this
  have : IsIso (DerivedCategory.Q.map φ) := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := φ)).2 hφ
  exact ⟨I, (asIso (DerivedCategory.Q.map φ)).symm ≪≫ e, hI, hu⟩

omit [HasSmallSiteSheafify C] in
/-- Two K-flat representatives of the same object with bounded below cohomology admit
quasi-isomorphisms to a common K-flat complex on which the support unit is invertible,
compatibly with the given identification, provided K-flat complexes with bounded below
cohomology admit quasi-isomorphisms to such complexes. -/
theorem exists_common_kFlat_supportResolution
    (hres : ∀ (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P → ∀ n : ℤ,
        (DerivedCategory.Q.obj P).IsGE n →
      ∃ (I : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ) (φ : P ⟶ I), QuasiIso φ ∧
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat I ∧
        IsIso (exteriorSupportResolutionUnit C i I))
    {P P' : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ}
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hP' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P')
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P') (n : ℤ)
    (hn : (DerivedCategory.Q.obj P).IsGE n) :
    ∃ (G : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ) (b : P ⟶ G) (c : P' ⟶ G),
      IsIso (DerivedCategory.Q.map b) ∧ IsIso (DerivedCategory.Q.map c) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat G ∧
      IsIso (exteriorSupportResolutionUnit C i G) ∧
      DerivedCategory.Q.map b = e.hom ≫ DerivedCategory.Q.map c := by
  obtain ⟨X', s', hs', g', hfac⟩ := DerivedCategory.right_fac e.hom
  obtain ⟨R, π, hπ, -, hR⟩ := CochainComplex.exists_quasiIso_flat_kFlat X'
  have : IsIso (DerivedCategory.Q.map π) := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := π)).2 hπ
  have hga : DerivedCategory.Q.map g' = DerivedCategory.Q.map s' ≫ e.hom := by
    rw [hfac, IsIso.hom_inv_id_assoc]
  have : IsIso (DerivedCategory.Q.map (π ≫ s')) := by
    rw [Functor.map_comp]
    infer_instance
  have : IsIso (DerivedCategory.Q.map (π ≫ g')) := by
    rw [Functor.map_comp, hga]
    infer_instance
  obtain ⟨H, b, c, hb, hc, hH, hcomm⟩ :=
    exists_kFlat_quasiIso_pushout C (π ≫ s') (π ≫ g') hR hP hP'
  have : (DerivedCategory.Q.obj H).IsGE n :=
    DerivedCategory.TStructure.t.isGE_of_iso (asIso (DerivedCategory.Q.map b)) n
  obtain ⟨G, t, ht, hG, hu⟩ := hres H hH n this
  have : IsIso (DerivedCategory.Q.map t) := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := t)).2 ht
  have hbc : DerivedCategory.Q.map b = e.hom ≫ DerivedCategory.Q.map c := by
    rw [← cancel_epi (DerivedCategory.Q.map (π ≫ s')), hcomm]
    simp only [Functor.map_comp, hga, Category.assoc]
  refine ⟨G, b ≫ t, c ≫ t, ?_, ?_, hG, hu, ?_⟩
  · rw [Functor.map_comp]
    infer_instance
  · rw [Functor.map_comp]
    infer_instance
  · rw [Functor.map_comp, Functor.map_comp, hbc, Category.assoc]

end Resolution

end AlgebraicGeometry.Etale
