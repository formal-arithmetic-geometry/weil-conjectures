/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.KoszulTower
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# The Koszul tower as a tower of cochain complexes

Let `R` be a commutative ring and `f = (f₁, …, f_r)` a finite sequence in `R`. This file places
the Koszul tower `m ↦ K_•(f₁ᵐ, …, f_rᵐ)` (`ExteriorAlgebra.koszulTower`) in cohomological
degrees `[-r, 0]`, as a tower of cochain complexes `ExteriorAlgebra.koszulCochainTower f`
(the term of degree `-n` is `⋀ⁿ Rʳ`), and constructs

* the augmentation `R[0] ⟶ K(f^m)`, the identity `R ≅ ⋀⁰ Rʳ` in degree `0`
  (`ExteriorAlgebra.koszulCochainAug`);
* the comparison map `K(f^m) ⟶ (R ⧸ Iᵐ)[0]` to the quotient tower, where `I = (f₁, …, f_r)`,
  induced by the quotient maps `R ⟶ R ⧸ Iᵐ` in degree `0`
  (`ExteriorAlgebra.koszulCochainToQuot`), well defined because `(f₁ᵐ, …, f_rᵐ) ⊆ Iᵐ`.

The composite of the augmentation and the comparison map is the quotient map
`R[0] ⟶ (R ⧸ Iᵐ)[0]` (`ExteriorAlgebra.koszulCochainAug_comp_koszulCochainToQuot`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite HomologicalComplex

namespace ExteriorAlgebra

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The embedding `n ↦ -n` of chain complexes indexed by `ℕ` into cochain complexes indexed
by `ℤ`. -/
abbrev koszulEmbedding : ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.up ℤ) :=
  ComplexShape.embeddingUpIntLE 0

lemma koszulEmbedding_f (n : ℕ) : koszulEmbedding.f n = -(n : ℤ) := by simp

lemma koszulEmbedding_f_zero : koszulEmbedding.f 0 = 0 := by simp

/-- The Koszul tower `m ↦ K(f₁ᵐ, …, f_rᵐ)` in cohomological degrees `[-r, 0]`. -/
noncomputable def koszulCochainTower (f : Fin r → R) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  koszulTower f ⋙ koszulEmbedding.extendFunctor _

/-- The degree `0` term of `K(f^m)` is `⋀⁰ Rʳ`. -/
noncomputable def koszulCochainXZeroIso (f : Fin r → R) (m : ℕ) :
    ((koszulCochainTower f).obj (op m)).X 0 ≅ ModuleCat.of R (⋀[R]^0 (Fin r →₀ R)) :=
  ((koszulTower f).obj (op m)).extendXIso koszulEmbedding koszulEmbedding_f_zero

lemma isZero_koszulCochainTower_X (f : Fin r → R) (m : ℕ) {p : ℤ} (hp : 0 < p) :
    IsZero (((koszulCochainTower f).obj (op m)).X p) :=
  ((koszulTower f).obj (op m)).isZero_extend_X koszulEmbedding p fun i h ↦ by
    rw [koszulEmbedding_f] at h
    lia

lemma koszulCochainTower_map_f_zero (f : Fin r → R) {m m' : ℕᵒᵖ} (h : m ⟶ m') :
    ((koszulCochainTower f).map h).f 0 =
      (koszulCochainXZeroIso f m.unop).hom ≫ (koszulCochainXZeroIso f m'.unop).inv := by
  dsimp only [koszulCochainTower, Functor.comp_map, ComplexShape.Embedding.extendFunctor_map]
  rw [extendMap_f _ _ koszulEmbedding_f_zero, koszulTower_map_f, koszulMap_zero]
  rfl

/-- The unit `R ≅ ⋀⁰ Rʳ` of the exterior algebra in degree `0`. -/
noncomputable def koszulUnit : ModuleCat.of R R ⟶ ModuleCat.of R (⋀[R]^0 (Fin r →₀ R)) :=
  ModuleCat.ofHom (exteriorPower.zeroEquiv R (Fin r →₀ R)).symm.toLinearMap

variable (r) in
/-- The augmentation `R[0] ⟶ K(f^m)`: the identity `R ≅ ⋀⁰ Rʳ` in degree `0`. -/
noncomputable def koszulCochainAugApp (f : Fin r → R) (m : ℕ) :
    (single (ModuleCat.{u} R) (.up ℤ) 0).obj (ModuleCat.of R R) ⟶
      (koszulCochainTower f).obj (op m) :=
  mkHomFromSingle (koszulUnit ≫ (koszulCochainXZeroIso f m).inv) fun k hk ↦
    (isZero_koszulCochainTower_X f m (by simp at hk; lia)).eq_of_tgt _ _

lemma koszulCochainAugApp_f (f : Fin r → R) (m : ℕ) :
    (koszulCochainAugApp r f m).f 0 =
      (singleObjXSelf _ 0 _).hom ≫ koszulUnit ≫ (koszulCochainXZeroIso f m).inv :=
  mkHomFromSingle_f _ _

/-- The augmentation `R[0] ⟶ K(f^m)` of the Koszul tower, a morphism of towers from the
constant tower `R[0]`. -/
noncomputable def koszulCochainAug (f : Fin r → R) :
    (Functor.const ℕᵒᵖ).obj ((single (ModuleCat.{u} R) (.up ℤ) 0).obj (ModuleCat.of R R)) ⟶
      koszulCochainTower f where
  app m := koszulCochainAugApp r f m.unop
  naturality m m' h := from_single_hom_ext (by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, comp_f,
      koszulCochainAugApp_f, koszulCochainTower_map_f_zero, Category.assoc, Iso.inv_hom_id_assoc])

variable (r) in
/-- The quotient tower `n ↦ (R ⧸ Iⁿ)[0]` of cochain complexes. -/
noncomputable def quotCochainTower (I : Ideal R) : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  Ideal.quotPowFunctor I ⋙ single _ _ 0

/-- The degree `0` map `⋀⁰ Rʳ ≅ R ⟶ R ⧸ Iᵐ`. -/
noncomputable def koszulQuot (I : Ideal R) (m : ℕ) :
    ModuleCat.of R (⋀[R]^0 (Fin r →₀ R)) ⟶ (Ideal.quotPowFunctor I).obj (op m) :=
  ModuleCat.ofHom (koszulAug (I ^ m))

lemma koszulUnit_koszulQuot (I : Ideal R) (m : ℕ) :
    koszulUnit (r := r) ≫ koszulQuot I m = ModuleCat.ofHom (Submodule.mkQ (I ^ m)) := by
  ext x
  simp [koszulUnit, koszulQuot, koszulAug_apply]
  rfl

variable (r) in
/-- The comparison map `K(f^m) ⟶ (R ⧸ Iᵐ)[0]` for `I = (f₁, …, f_r)`, induced in degree `0` by
the quotient map `⋀⁰ Rʳ ≅ R ⟶ R ⧸ Iᵐ`; it is well defined because `(f₁ᵐ, …, f_rᵐ) ⊆ Iᵐ`. -/
noncomputable def koszulCochainToQuotApp (f : Fin r → R) (m : ℕ) :
    (koszulCochainTower f).obj (op m) ⟶ (quotCochainTower r (Ideal.span (Set.range f))).obj (op m) :=
  mkHomToSingle ((koszulCochainXZeroIso f m).hom ≫ koszulQuot _ m) fun i hi ↦ by
    obtain rfl : i = -1 := by simp at hi; lia
    rw [extend_d_eq _ koszulEmbedding (i := 1) (j := 0) (by simp) koszulEmbedding_f_zero]
    simp only [koszulCochainXZeroIso, Category.assoc, Iso.inv_hom_id_assoc]
    convert comp_zero
    ext x
    have hle : Ideal.span (Set.range (f ^ m)) ≤ Ideal.span (Set.range f) ^ m := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact Ideal.pow_mem_pow (Ideal.subset_span ⟨j, rfl⟩) m
    have := LinearMap.congr_fun (koszulAug_comp_koszulBoundary (f ^ m) hle) x
    simpa [koszulTower, koszulComplex, koszulQuot] using this

lemma koszulCochainToQuotApp_f (f : Fin r → R) (m : ℕ) :
    (koszulCochainToQuotApp r f m).f 0 =
      ((koszulCochainXZeroIso f m).hom ≫ koszulQuot _ m) ≫ (singleObjXSelf _ 0 _).inv :=
  mkHomToSingle_f _ _

/-- The comparison map `K(f^m) ⟶ (R ⧸ Iᵐ)[0]` from the Koszul tower to the quotient tower, for
`I = (f₁, …, f_r)`. -/
noncomputable def koszulCochainToQuot (f : Fin r → R) :
    koszulCochainTower f ⟶ quotCochainTower r (Ideal.span (Set.range f)) where
  app m := koszulCochainToQuotApp r f m.unop
  naturality m m' h := to_single_hom_ext (by
    simp only [comp_f, koszulCochainToQuotApp_f, koszulCochainTower_map_f_zero, Category.assoc,
      Iso.inv_hom_id_assoc, quotCochainTower, Functor.comp_map, single_map_f_self]
    simp only [← Category.assoc]
    congr 2
    ext x
    rfl)

/-- The composite of the augmentation of the Koszul tower and the comparison map to the quotient
tower is the quotient map `R[0] ⟶ (R ⧸ Iᵐ)[0]`. -/
lemma koszulCochainAug_comp_koszulCochainToQuot (f : Fin r → R) :
    koszulCochainAug f ≫ koszulCochainToQuot f =
      { app m := (single _ _ 0).map ((Ideal.quotPowCone (Ideal.span (Set.range f))).π.app m)
        naturality m m' h := by
          rw [Functor.const_obj_map, Category.id_comp, ← Functor.map_comp, Cone.w]
          rfl } := by
  ext m : 2
  refine from_single_hom_ext ?_
  simp only [NatTrans.comp_app, comp_f, koszulCochainAug, koszulCochainToQuot,
    koszulCochainAugApp_f, koszulCochainToQuotApp_f, Category.assoc, Iso.inv_hom_id_assoc,
    single_map_f_self]
  rw [reassoc_of% (koszulUnit_koszulQuot (r := r) (Ideal.span (Set.range f)) m.unop)]
  rfl

end ExteriorAlgebra
