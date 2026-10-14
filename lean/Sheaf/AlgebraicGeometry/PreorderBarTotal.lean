/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Unnormalized bar totals of diagrams on preorders

Source: the unnormalized bar construction in the proof of
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: def-sc-preorder-bar-total).

The simplicial degree p term is the coproduct of D(i₀) over strings
 i₀ ≤ ⋯ ≤ iₚ. The total places this degree in cohomological degree -p.
Every object and map below is constructed directly from coproducts and Mathlib's
alternating face map complex; no existence theorem supplies the data.
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory.PreorderBar

variable {I : Type u} [Preorder I] {C : Type w} [Category.{v} C]
  [HasCoproducts.{u} C] (D : I ⥤ C)

noncomputable def obj (n : SimplexCategory) : C :=
  ∐ (fun σ : Fin (n.len + 1) →o I ↦ D.obj (σ 0))

noncomputable def map {n m : SimplexCategory} (α : m ⟶ n) : obj D n ⟶ obj D m :=
  Sigma.desc (fun σ : Fin (n.len + 1) →o I ↦
    D.map (homOfLE (σ.monotone (Fin.zero_le (α.toOrderHom 0)))) ≫
      Sigma.ι (fun τ : Fin (m.len + 1) →o I ↦ D.obj (τ 0))
        (σ.comp α.toOrderHom))

@[reassoc (attr := simp)]
lemma ι_map {n m : SimplexCategory} (α : m ⟶ n)
    (σ : Fin (n.len + 1) →o I) :
    Sigma.ι (fun τ : Fin (n.len + 1) →o I ↦ D.obj (τ 0)) σ ≫ map D α =
      D.map (homOfLE (σ.monotone (Fin.zero_le (α.toOrderHom 0)))) ≫
        Sigma.ι (fun τ : Fin (m.len + 1) →o I ↦ D.obj (τ 0))
          (σ.comp α.toOrderHom) := by
  simp [map]

lemma map_id (n : SimplexCategory) : map D (𝟙 n) = 𝟙 (obj D n) := by
  apply Sigma.hom_ext
  intro σ
  simp only [ι_map]
  change D.map (𝟙 (σ 0)) ≫
    Sigma.ι (fun τ : Fin (n.len + 1) →o I ↦ D.obj (τ 0)) σ = _
  simp [obj]

lemma map_comp {n m k : SimplexCategory} (α : m ⟶ n) (β : k ⟶ m) :
    map D (β ≫ α) = map D α ≫ map D β := by
  apply Sigma.hom_ext
  intro σ
  simp only [ι_map, ι_map_assoc]
  rw [← D.map_comp_assoc]
  congr 1

noncomputable def simplicial : SimplicialObject C where
  obj n := obj D n.unop
  map α := map D α.unop
  map_id n := map_id D n.unop
  map_comp α β := map_comp D α.unop β.unop

noncomputable def augmentation (c : Cocone D) :
    simplicial D ⟶ (SimplicialObject.const C).obj c.pt where
  app n := Sigma.desc (fun σ : Fin (n.unop.len + 1) →o I ↦ c.ι.app (σ 0))
  naturality {n m} α := by
    apply Sigma.hom_ext
    intro σ
    dsimp [simplicial]
    simp only [ι_map_assoc, Sigma.ι_desc, Category.comp_id]
    exact c.w _

noncomputable def augmented (c : Cocone D) : SimplicialObject.Augmented C where
  left := simplicial D
  right := c.pt
  hom := augmentation D c

variable {J : Type u} [Preorder J] (E : J ⥤ C) (f : I →o J)

def orderFunctor : I ⥤ J where
  obj := f
  map α := homOfLE (f.monotone (leOfHom α))

set_option backward.isDefEq.respectTransparency false in
noncomputable def reindex (φ : D ⟶ orderFunctor f ⋙ E) :
    simplicial D ⟶ simplicial E where
  app n := Sigma.desc (fun σ : Fin (n.unop.len + 1) →o I ↦
    φ.app (σ 0) ≫
      Sigma.ι (fun τ : Fin (n.unop.len + 1) →o J ↦ E.obj (τ 0)) (f.comp σ))
  naturality {n m} α := by
    apply Sigma.hom_ext
    intro σ
    dsimp [simplicial]
    simp only [ι_map_assoc, Sigma.ι_desc, Category.assoc, Sigma.ι_desc_assoc, ι_map]
    convert! φ.naturality_assoc
        (homOfLE (σ.monotone (Fin.zero_le (α.unop.toOrderHom 0))))
        (Sigma.ι (fun τ : Fin (m.unop.len + 1) →o J ↦ E.obj (τ 0))
          (f.comp (σ.comp α.unop.toOrderHom))) using 1

/-- Reindexing bar strings commutes with composition of order maps. -/
lemma reindex_comp {K : Type u} [Preorder K] (H : K ⥤ C) (g : J →o K)
    (φ : D ⟶ orderFunctor f ⋙ E) (ψ : E ⟶ orderFunctor g ⋙ H)
    (χ : D ⟶ orderFunctor (g.comp f) ⋙ H)
    (hχ : ∀ i : I, χ.app i = φ.app i ≫ ψ.app (f i)) :
    reindex D E f φ ≫ reindex E H g ψ = reindex D H (g.comp f) χ := by
  ext n
  apply Sigma.hom_ext
  intro σ
  simp only [NatTrans.comp_app, reindex, Sigma.ι_desc_assoc, Sigma.ι_desc,
    Category.assoc, hχ]
  rfl

variable [Preadditive C] [HasZeroObject C] [HasCoproducts.{0} C]

instance barTotalShape :
    TotalComplexShape (ComplexShape.down ℕ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) where
  π pq := pq.2 - pq.1
  ε₁ _ := 1
  ε₂ pq := (-1 : ℤˣ) ^ pq.1
  rel₁ := by
    intro p p' h q
    change p' + 1 = p at h
    change q - (p : ℤ) + 1 = q - (p' : ℤ)
    lia
  rel₂ := by
    intro p q q' h
    change q + 1 = q' at h
    change q - (p : ℤ) + 1 = q' - (p : ℤ)
    lia
  ε₂_ε₁ := by
    intro p p' q q' hp _
    obtain rfl : p = p' + 1 := hp.symm
    simp [pow_succ]

noncomputable def bicomplex (D : I ⥤ CochainComplex C ℤ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.up ℤ) :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj (simplicial D)

noncomputable def total (D : I ⥤ CochainComplex C ℤ) : CochainComplex C ℤ :=
  (bicomplex D).total (ComplexShape.up ℤ)

noncomputable def totalMap (D : I ⥤ CochainComplex C ℤ)
    (E : J ⥤ CochainComplex C ℤ) (f : I →o J) (φ : D ⟶ orderFunctor f ⋙ E) :
    total D ⟶ total E :=
  HomologicalComplex₂.total.map
    (AlgebraicTopology.AlternatingFaceMapComplex.map (reindex D E f φ)) (ComplexShape.up ℤ)

omit [HasZeroObject C] in
/-- Total bar maps commute with composition of order maps. -/
lemma totalMap_comp {K : Type u} [Preorder K]
    (D : I ⥤ CochainComplex C ℤ) (E : J ⥤ CochainComplex C ℤ)
    (H : K ⥤ CochainComplex C ℤ) (f : I →o J) (g : J →o K)
    (φ : D ⟶ orderFunctor f ⋙ E) (ψ : E ⟶ orderFunctor g ⋙ H)
    (χ : D ⟶ orderFunctor (g.comp f) ⋙ H)
    (hχ : ∀ i : I, χ.app i = φ.app i ≫ ψ.app (f i)) :
    totalMap D E f φ ≫ totalMap E H g ψ = totalMap D H (g.comp f) χ := by
  dsimp [totalMap]
  rw [← HomologicalComplex₂.total.map_comp]
  congr 1
  change (AlgebraicTopology.alternatingFaceMapComplex _).map (reindex D E f φ) ≫
    (AlgebraicTopology.alternatingFaceMapComplex _).map (reindex E H g ψ) = _
  rw [← Functor.map_comp, reindex_comp D E f H g φ ψ χ hχ]
  rfl

noncomputable abbrev singleColumn (T : CochainComplex C ℤ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.up ℤ) :=
  (ChainComplex.single₀ (CochainComplex C ℤ)).obj T

noncomputable def collapseX (T : CochainComplex C ℤ) (n : ℤ) :
    ((singleColumn T).total (ComplexShape.up ℤ)).X n ⟶ T.X n :=
  (singleColumn T).totalDesc (fun p q h ↦ match p with
    | 0 => eqToHom (congrArg T.X (by
        change q - (0 : ℕ) = n at h
        simpa using h))
    | _ + 1 => 0)

omit [HasCoproducts.{u} C] in
@[reassoc (attr := simp)]
lemma ι_collapseX (T : CochainComplex C ℤ) (n q : ℤ)
    (h : q - (0 : ℕ) = n) :
    (singleColumn T).ιTotal (ComplexShape.up ℤ) 0 q n h ≫ collapseX T n =
      eqToHom (congrArg T.X (by simpa using h)) := by
  simp [collapseX]

set_option backward.isDefEq.respectTransparency false in
noncomputable def collapse (T : CochainComplex C ℤ) :
    (singleColumn T).total (ComplexShape.up ℤ) ⟶ T where
  f := collapseX T
  comm' n n' hn := by
    obtain rfl : n' = n + 1 := hn.symm
    apply HomologicalComplex₂.total.hom_ext
    intro p q h
    cases p with
    | zero =>
      have hq : q = n := by
        change q - (0 : ℕ) = n at h
        simpa using h
      subst q
      simp only [HomologicalComplex₂.total_d, Preadditive.comp_add,
        Preadditive.add_comp, HomologicalComplex₂.ι_D₁_assoc,
        HomologicalComplex₂.ι_D₂_assoc, ι_collapseX_assoc]
      have hd₁ : (singleColumn T).d₁ (ComplexShape.up ℤ) 0 n (n + 1) = 0 := by
        simp [HomologicalComplex₂.d₁]
      rw [hd₁, CategoryTheory.Limits.zero_comp, zero_add]
      rw [HomologicalComplex₂.d₂_eq (singleColumn T) (ComplexShape.up ℤ) 0
        (by simp : (ComplexShape.up ℤ).Rel n (n + 1)) (n + 1) (by
          change (n + 1) - (0 : ℕ) = n + 1
          simp)]
      simp only [Linear.units_smul_comp, Category.assoc, ι_collapseX,
        eqToHom_refl]
      have hs : ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (0, n) = 1 := rfl
      rw [hs, one_smul]
      simp
    | succ p =>
      have hz : IsZero ((singleColumn T).X (p + 1)) :=
        HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 T (p + 1)
          (by lia)
      exact ((HomologicalComplex.eval C (ComplexShape.up ℤ) q).map_isZero hz).eq_of_src _ _

omit [HasCoproducts.{u} C] in
/-- Collapsing the total complex of a single column is an actual isomorphism.

Source: the unnormalized-bar-total paragraph of
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-preorder-bar-total-single-collapse).

Proof: In total degree n only column zero can be nonzero. Its diagonal inclusion
is inverse to collapse; every other diagonal summand is a zero object. -/
lemma collapse_isIso (T : CochainComplex C ℤ) : IsIso (collapse T) := by
  have hi (n : ℤ) : IsIso ((collapse T).f n) := by
    refine ⟨⟨(singleColumn T).ιTotal (ComplexShape.up ℤ) 0 n n
      (by change n - (0 : ℕ) = n; simp), ?_, ?_⟩⟩
    · apply HomologicalComplex₂.total.hom_ext
      intro p q h
      cases p with
      | zero =>
        have hq : q = n := by
          change q - (0 : ℕ) = n at h
          simpa using h
        subst q
        simp [collapse]
      | succ p =>
        have hz : IsZero ((singleColumn T).X (p + 1)) :=
          HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 T (p + 1)
            (by lia)
        exact ((HomologicalComplex.eval C (ComplexShape.up ℤ) q).map_isZero hz).eq_of_src _ _
    · simp [collapse]
  exact HomologicalComplex.Hom.isIso_of_components _

noncomputable def totalAugmentation (D : I ⥤ CochainComplex C ℤ) (c : Cocone D) :
    total D ⟶ c.pt :=
  HomologicalComplex₂.total.map
    (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (augmented D c))
    (ComplexShape.up ℤ) ≫ collapse c.pt

omit [HasCoproducts.{u} C] in
lemma collapse_naturality {T T' : CochainComplex C ℤ} (g : T ⟶ T') :
    HomologicalComplex₂.total.map ((ChainComplex.single₀ (CochainComplex C ℤ)).map g)
      (ComplexShape.up ℤ) ≫ collapse T' = collapse T ≫ g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  cases p with
  | zero =>
    have hq : q = n := by
      change q - (0 : ℕ) = n at h
      simpa using h
    subst q
    simp [HomologicalComplex₂.ιTotal_map_assoc, collapse]
  | succ p =>
    have hz : IsZero ((singleColumn T).X (p + 1)) :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 T (p + 1) (by lia)
    exact ((HomologicalComplex.eval C (ComplexShape.up ℤ) q).map_isZero hz).eq_of_src _ _

omit [Preadditive C] [HasZeroObject C] [HasCoproducts.{0} C] in
lemma augmentation_reindex (c : Cocone D) (c' : Cocone E)
    (φ : D ⟶ orderFunctor f ⋙ E) (g : c.pt ⟶ c'.pt)
    (hg : ∀ j : I, φ.app j ≫ c'.ι.app (f j) = c.ι.app j ≫ g) :
    reindex D E f φ ≫ augmentation E c' =
      augmentation D c ≫ (SimplicialObject.const C).map g := by
  ext n
  apply Sigma.hom_ext
  intro σ
  simp only [NatTrans.comp_app, reindex, augmentation, Sigma.ι_desc_assoc,
    Category.assoc, Sigma.ι_desc]
  exact hg (σ 0)

lemma totalAugmentation_naturality (D : I ⥤ CochainComplex C ℤ)
    (E : J ⥤ CochainComplex C ℤ) (f : I →o J)
    (c : Cocone D) (c' : Cocone E) (φ : D ⟶ orderFunctor f ⋙ E)
    (g : c.pt ⟶ c'.pt)
    (hg : ∀ j : I, φ.app j ≫ c'.ι.app (f j) = c.ι.app j ≫ g) :
    totalMap D E f φ ≫ totalAugmentation E c' = totalAugmentation D c ≫ g := by
  let ψ : augmented D c ⟶ augmented E c' := {
    left := reindex D E f φ
    right := g
    w := augmentation_reindex D E f c c' φ g hg }
  have h := AlgebraicTopology.AlternatingFaceMapComplex.ε.naturality ψ
  have ht := congrArg (fun k ↦ HomologicalComplex₂.total.map k (ComplexShape.up ℤ)) h
  dsimp [ψ, AlgebraicTopology.alternatingFaceMapComplex] at ht
  simp only [HomologicalComplex₂.total.map_comp] at ht
  dsimp [totalMap, totalAugmentation]
  rw [← Category.assoc, ht, Category.assoc, collapse_naturality]
  simp only [Category.assoc]
  rfl

end CategoryTheory.PreorderBar

namespace CategoryTheory.PreorderBar

variable {I : Type u} [Preorder I] {C : Type w} [Category.{v} C]
  [Preadditive C] [HasZeroObject C] [HasCoproducts.{u} C] [HasCoproducts.{0} C]

omit [HasCoproducts.{u} C] [HasCoproducts.{0} C] in
private lemma isZero_sigma {K : Type*} (M : K → C) [HasCoproduct M]
    (hz : ∀ k : K, IsZero (M k)) : IsZero (∐ M) :=
  (colimit.isColimit (Discrete.functor M)).isZero_pt
    ((Discrete.functor M).isZero (fun k ↦ hz k.as))

/-- Evaluation of a bar column is the corresponding coproduct of evaluated pieces. -/
noncomputable def columnXIso (D : I ⥤ CochainComplex C ℤ) (p : ℕ) (q : ℤ) :
    ((bicomplex D).X p).X q ≅
      ∐ (fun σ : Fin (p + 1) →o I ↦ (D.obj (σ 0)).X q) :=
  PreservesCoproduct.iso (HomologicalComplex.eval C (ComplexShape.up ℤ) q)
    (fun σ : Fin (p + 1) →o I ↦ D.obj (σ 0))

/-- The generator of a total term indexed by a bar string and a diagonal pair. -/
noncomputable def ιTerm (D : I ⥤ CochainComplex C ℤ)
    (p : ℕ) (q n : ℤ) (h : q - (p : ℤ) = n) (σ : Fin (p + 1) →o I) :
    (D.obj (σ 0)).X q ⟶ (total D).X n :=
  Sigma.ι (fun τ : Fin (p + 1) →o I ↦ (D.obj (τ 0)).X q) σ ≫
    (columnXIso D p q).inv ≫ (bicomplex D).ιTotal (ComplexShape.up ℤ) p q n h

omit [HasZeroObject C] in
/-- Total-term maps agree if they agree on these generators. -/
lemma ιTerm_hom_ext (D : I ⥤ CochainComplex C ℤ) (n : ℤ) {A : C}
    (f g : (total D).X n ⟶ A)
    (h : ∀ (p : ℕ) (q : ℤ) (hpq : q - (p : ℤ) = n) (σ : Fin (p + 1) →o I),
      ιTerm D p q n hpq σ ≫ f = ιTerm D p q n hpq σ ≫ g) : f = g := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  apply (cancel_epi (columnXIso D p q).inv).1
  apply Sigma.hom_ext
  intro σ
  simpa only [ιTerm, Category.assoc] using h p q hpq σ

/-- A common upper bound on the diagram bounds its bar total, since total degree is q-p.
Source: the common-stage-bound paragraph of `lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-preorder-bar-total-bounded). -/
theorem bounded_total (D : I ⥤ CochainComplex C ℤ) (b : ℤ)
    (hb : ∀ j : I, ∀ q : ℤ, b < q → IsZero ((D.obj j).X q)) :
    ∀ n : ℤ, b < n → IsZero ((total D).X n) := by
  intro n hn
  apply isZero_sigma
  rintro ⟨⟨p, q⟩, hpq⟩
  change q - (p : ℤ) = n at hpq
  apply IsZero.of_iso _ (columnXIso D p q)
  apply isZero_sigma
  intro σ
  exact hb (σ 0) q (by lia)

end CategoryTheory.PreorderBar
