/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.BicosimplicialShuffleObjects
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import Sheaf.Algebra.Homology.UniversalShuffleEvaluation

/-! # Assembly of the augmentation-preserving bicosimplicial shuffle equivalence

Source: the current blueprint, sec-six-functors-basics, direct-images proof (3).
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization).
-/

@[expose] public section
set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicTopology
open scoped Simplicial

namespace AlgebraicTopology.BicosimplicialShuffle

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
private lemma diagonalInclusion_map
    {X Y : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ} (f : X ⟶ Y)
    (n r m : ℕ) (h : n + r = m) :
    diagonalInclusion X n r m h ≫ (diagonalMap f).f m =
      (f.app (⦋n⦌, ⦋n⦌)).f r ≫ diagonalInclusion Y n r m h := by
  simp [diagonalInclusion, diagonalMap, diagonalBicomplex,
    HomologicalComplex₂.ιTotal_map]

set_option backward.isDefEq.respectTransparency false in
private lemma successiveInclusion_map
    {X Y : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ} (f : X ⟶ Y)
    (a b r m : ℕ) (h : a + b + r = m) :
    successiveInclusion X a b r m h ≫ (successiveMap f).f m =
      (f.app (⦋a⦌, ⦋b⦌)).f r ≫ successiveInclusion Y a b r m h := by
  simp only [successiveInclusion, successiveMap, Category.assoc,
    HomologicalComplex₂.ιTotal_map]
  rw [← Category.assoc, ← HomologicalComplex.comp_f, HomologicalComplex₂.ιTotal_map]
  simp [tripleComplex, cosimplicialTotal, HomologicalComplex.comp_f, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private lemma shuffleTerm_natural
    {X Y : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ} (f : X ⟶ Y)
    (n r m : ℕ) (h : n + r = m) (μ : Finset (Fin n)) :
    (f.app (⦋n⦌, ⦋n⦌)).f r ≫ shuffleTerm Y n r m h μ =
      shuffleTerm X n r m h μ ≫ (successiveMap f).f m := by
  simp only [shuffleTerm, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    Category.assoc, successiveInclusion_map]
  congr 1
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact (congrArg (fun g ↦ g.f r)
    (f.naturality ((shuffleSurjection n μ, shuffleSurjection n μᶜ) :
      (⦋n⦌, ⦋n⦌) ⟶ (⦋μ.card⦌, ⦋μᶜ.card⦌)))).symm

set_option backward.isDefEq.respectTransparency false in
private lemma shuffle_natural
    (S : ∀ X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ,
      diagonalTotal X ⟶ successiveTotal X)
    (hS : ∀ (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ)
      (n r m : ℕ) (h : n + r = m),
      diagonalInclusion X n r m h ≫ (S X).f m =
        ∑ μ : Finset (Fin n), shuffleTerm X n r m h μ)
    {X Y : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ} (f : X ⟶ Y) :
    diagonalMap f ≫ S Y = S X ≫ successiveMap f := by
  classical
  apply HomologicalComplex.Hom.ext
  funext m
  apply HomologicalComplex₂.total.hom_ext
  intro n r h
  change diagonalInclusion X n r m h ≫ ((diagonalMap f).f m ≫ (S Y).f m) =
    diagonalInclusion X n r m h ≫ ((S X).f m ≫ (successiveMap f).f m)
  rw [← Category.assoc, diagonalInclusion_map, Category.assoc, hS,
    ← Category.assoc, hS, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro μ _
  exact shuffleTerm_natural f n r m h μ

set_option backward.isDefEq.respectTransparency false in
private lemma total_zero_map
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (M : CochainComplex C ℕ) (i : M ⟶ K.X 0) (hi : i ≫ K.d 0 1 = 0) :
    ∃ j : M ⟶ K.total (ComplexShape.up ℕ),
      ∀ m, j.f m = i.f m ≫ K.ιTotal (ComplexShape.up ℕ) 0 m m (Nat.zero_add m) := by
  refine ⟨CochainComplex.ofHom
    (fun m ↦ i.f m ≫ K.ιTotal (ComplexShape.up ℕ) 0 m m (Nat.zero_add m)) ?_,
    fun _ ↦ rfl⟩
  intro m
  have hz := congrArg (fun f : M ⟶ K.X 1 ↦ f.f m) hi
  dsimp at hz
  change _ ≫ (K.D₁ _ m (m + 1) + K.D₂ _ m (m + 1)) = _
  simp only [Preadditive.comp_add, Category.assoc, HomologicalComplex₂.ι_D₁,
    HomologicalComplex₂.ι_D₂]
  rw [K.d₁_eq (ComplexShape.up ℕ) (show (ComplexShape.up ℕ).Rel 0 1 from rfl)
      m (m + 1) (by dsimp; omega),
    K.d₂_eq (ComplexShape.up ℕ) 0 (show (ComplexShape.up ℕ).Rel m (m + 1) from rfl)
      (m + 1) (by dsimp; omega)]
  have hε₁ : ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (0, m) = 1 := rfl
  have hε₂ : ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (0, m) = 1 := rfl
  rw [hε₁, hε₂, one_smul, one_smul]
  rw [← Category.assoc, hz, zero_comp, zero_add, i.comm_assoc]

set_option backward.isDefEq.respectTransparency false in
private lemma derived_iso_of_homotopy_equiv [HasDerivedCategory.{w} C]
    {K L : CochainComplex C ℕ} (e : HomotopyEquiv K L) :
    ∃ eD : DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat) ≅
      DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat),
      eD.hom = DerivedCategory.Q.map
        ((ComplexShape.embeddingUpNat.extendFunctor C).map e.hom) := by
  have he : HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ)
      ((ComplexShape.embeddingUpNat.extendFunctor C).map e.hom) :=
    (HomologicalComplex.homotopyEquivalences_extendMap_iff _ _).mpr
      e.homotopyEquivalences_hom
  have hq := homotopyEquivalences_le_quasiIso
    C (ComplexShape.up ℤ) _ he
  have : QuasiIso ((ComplexShape.embeddingUpNat.extendFunctor C).map e.hom) := hq
  exact ⟨asIso (DerivedCategory.Q.map
    ((ComplexShape.embeddingUpNat.extendFunctor C).map e.hom)), rfl⟩

set_option backward.isDefEq.respectTransparency false in
private lemma shuffle_zero
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) (r : ℕ) :
    (∑ μ : Finset (Fin 0), shuffleTerm X 0 r r (Nat.zero_add r) μ) =
      successiveInclusion X 0 0 r r (Nat.zero_add r) := by
  classical
  rw [Fintype.sum_unique]
  have hd : (default : Finset (Fin 0)) = ∅ := Subsingleton.elim _ _
  rw [hd]
  have hα : shuffleSurjection 0 ∅ = 𝟙 ⦋0⦌ := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    apply Fin.ext
    simp [shuffleSurjection]
  have aux (ν : Finset (Fin 0)) (h : 0 + ν.card + r = r) :
      (X.map (shuffleSurjection 0 ∅, shuffleSurjection 0 ν)).f r ≫
        successiveInclusion X 0 ν.card r r h =
      successiveInclusion X 0 0 r r (Nat.zero_add r) := by
    have hν : ν = ∅ := Subsingleton.elim _ _
    subst ν
    rw [hα]
    change (X.map (𝟙 (⦋0⦌, ⦋0⦌))).f r ≫ _ = _
    simp only [X.map_id, HomologicalComplex.id_f, Category.id_comp, Finset.card_empty]
  have hsign : shuffleSign 0 ∅ = 1 := by simp [shuffleSign]
  simpa only [shuffleTerm, hsign, one_smul, Finset.card_empty] using aux (∅ : Finset (Fin 0))ᶜ _

set_option backward.isDefEq.respectTransparency false in
private lemma total_corner_zero
    {A : Type*} [Category A] [Preadditive A] [HasFiniteCoproducts A]
    (K : HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    {M : A} (i : M ⟶ (K.X 0).X 0)
    (h₁ : i ≫ (K.d 0 1).f 0 = 0) (h₂ : i ≫ (K.X 0).d 0 1 = 0) :
    (i ≫ K.ιTotal (ComplexShape.up ℕ) 0 0 0 rfl) ≫
      (K.total (ComplexShape.up ℕ)).d 0 1 = 0 := by
  change _ ≫ (K.D₁ _ 0 1 + K.D₂ _ 0 1) = 0
  simp only [Preadditive.comp_add, Category.assoc, HomologicalComplex₂.ι_D₁,
    HomologicalComplex₂.ι_D₂]
  rw [K.d₁_eq (ComplexShape.up ℕ) (show (ComplexShape.up ℕ).Rel 0 1 from rfl) 0 1 rfl,
    K.d₂_eq (ComplexShape.up ℕ) 0 (show (ComplexShape.up ℕ).Rel 0 1 from rfl) 1 rfl]
  simp [← Category.assoc, h₁, h₂]

set_option backward.isDefEq.respectTransparency false in
private lemma diagonal_coface_zero
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ)
    (M : CochainComplex C ℕ) (i : M ⟶ X.obj (⦋0⦌, ⦋0⦌))
    (h₁ : i ≫ (X.map ((SimplexCategory.δ (0 : Fin 2), 𝟙 ⦋0⦌) :
        (⦋0⦌, ⦋0⦌) ⟶ (⦋1⦌, ⦋0⦌)) -
      X.map ((SimplexCategory.δ (1 : Fin 2), 𝟙 ⦋0⦌) :
        (⦋0⦌, ⦋0⦌) ⟶ (⦋1⦌, ⦋0⦌))) = 0)
    (h₂ : i ≫ (X.map ((𝟙 ⦋0⦌, SimplexCategory.δ (0 : Fin 2)) :
        (⦋0⦌, ⦋0⦌) ⟶ (⦋0⦌, ⦋1⦌)) -
      X.map ((𝟙 ⦋0⦌, SimplexCategory.δ (1 : Fin 2)) :
        (⦋0⦌, ⦋0⦌) ⟶ (⦋0⦌, ⦋1⦌))) = 0) :
    i ≫ (diagonalBicomplex X).d 0 1 = 0 := by
  rw [Preadditive.comp_sub, sub_eq_zero] at h₁ h₂
  have he : i ≫ X.map ((SimplexCategory.δ (0 : Fin 2),
        SimplexCategory.δ (0 : Fin 2)) : (⦋0⦌, ⦋0⦌) ⟶ (⦋1⦌, ⦋1⦌)) =
      i ≫ X.map ((SimplexCategory.δ (1 : Fin 2),
        SimplexCategory.δ (1 : Fin 2)) : (⦋0⦌, ⦋0⦌) ⟶ (⦋1⦌, ⦋1⦌)) := by
    calc
      _ = i ≫ X.map ((SimplexCategory.δ (0 : Fin 2), 𝟙 ⦋0⦌) : (⦋0⦌, ⦋0⦌) ⟶ (⦋1⦌, ⦋0⦌)) ≫
          X.map ((𝟙 ⦋1⦌, SimplexCategory.δ (0 : Fin 2)) : (⦋1⦌, ⦋0⦌) ⟶ (⦋1⦌, ⦋1⦌)) := by
        simp only [← X.map_comp]; congr 2
      _ = i ≫ X.map ((SimplexCategory.δ (1 : Fin 2), 𝟙 ⦋0⦌) : (⦋0⦌, ⦋0⦌) ⟶ (⦋1⦌, ⦋0⦌)) ≫
          X.map ((𝟙 ⦋1⦌, SimplexCategory.δ (0 : Fin 2)) : (⦋1⦌, ⦋0⦌) ⟶ (⦋1⦌, ⦋1⦌)) := by
        rw [← Category.assoc, h₁, Category.assoc]
      _ = i ≫ X.map ((𝟙 ⦋0⦌, SimplexCategory.δ (0 : Fin 2)) : (⦋0⦌, ⦋0⦌) ⟶ (⦋0⦌, ⦋1⦌)) ≫
          X.map ((SimplexCategory.δ (1 : Fin 2), 𝟙 ⦋1⦌) : (⦋0⦌, ⦋1⦌) ⟶ (⦋1⦌, ⦋1⦌)) := by
        simp only [← X.map_comp]; congr 2
      _ = i ≫ X.map ((𝟙 ⦋0⦌, SimplexCategory.δ (1 : Fin 2)) : (⦋0⦌, ⦋0⦌) ⟶ (⦋0⦌, ⦋1⦌)) ≫
          X.map ((SimplexCategory.δ (1 : Fin 2), 𝟙 ⦋1⦌) : (⦋0⦌, ⦋1⦌) ⟶ (⦋1⦌, ⦋1⦌)) := by
        rw [← Category.assoc, h₂, Category.assoc]
      _ = _ := by simp only [← X.map_comp]; congr 2
  simpa [diagonalBicomplex, AlternatingCofaceMapComplex.obj,
    AlternatingCofaceMapComplex.objD, CochainComplex.of.d, Fin.sum_univ_two, Preadditive.comp_sub,
    CosimplicialObject.δ, sub_eq_zero, ← sub_eq_add_neg] using he

set_option backward.isDefEq.respectTransparency false in
private lemma augmentation_maps
    (S : ∀ X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ,
      diagonalTotal X ⟶ successiveTotal X)
    (hS : ∀ (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ)
      (n r m : ℕ) (h : n + r = m),
      diagonalInclusion X n r m h ≫ (S X).f m =
        ∑ μ : Finset (Fin n), shuffleTerm X n r m h μ)
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ)
    (M : CochainComplex C ℕ) (i : M ⟶ X.obj (⦋0⦌, ⦋0⦌))
    (h₁ : i ≫ (X.map ((SimplexCategory.δ (0 : Fin 2), 𝟙 ⦋0⦌) :
        (⦋0⦌, ⦋0⦌) ⟶ (⦋1⦌, ⦋0⦌)) -
      X.map ((SimplexCategory.δ (1 : Fin 2), 𝟙 ⦋0⦌) :
        (⦋0⦌, ⦋0⦌) ⟶ (⦋1⦌, ⦋0⦌))) = 0)
    (h₂ : i ≫ (X.map ((𝟙 ⦋0⦌, SimplexCategory.δ (0 : Fin 2)) :
        (⦋0⦌, ⦋0⦌) ⟶ (⦋0⦌, ⦋1⦌)) -
      X.map ((𝟙 ⦋0⦌, SimplexCategory.δ (1 : Fin 2)) :
        (⦋0⦌, ⦋0⦌) ⟶ (⦋0⦌, ⦋1⦌))) = 0) :
    ∃ (jD : M ⟶ diagonalTotal X) (jT : M ⟶ successiveTotal X),
      (∀ m : ℕ, jD.f m = i.f m ≫ diagonalInclusion X 0 m m (Nat.zero_add m)) ∧
      (∀ m : ℕ, jT.f m = i.f m ≫ successiveInclusion X 0 0 m m
        (Nat.zero_add m)) ∧ jD ≫ S X = jT := by
  obtain ⟨jD, hjD⟩ := total_zero_map (diagonalBicomplex X) M i
    (diagonal_coface_zero X M i h₁ h₂)
  have ht : (i ≫ (tripleComplex X).ιTotal (ComplexShape.up ℕ) 0 0 0 rfl) ≫
      (cosimplicialTotal X).d 0 1 = 0 := by
    apply total_corner_zero
    · simpa [tripleComplex, AlternatingCofaceMapComplex.obj,
        AlternatingCofaceMapComplex.objD, CochainComplex.of.d, Fin.sum_univ_two,
        alternatingCofaceMapComplex, AlternatingCofaceMapComplex.map,
        CosimplicialObject.δ, ← sub_eq_add_neg] using h₁
    · simpa [tripleComplex, AlternatingCofaceMapComplex.obj,
        AlternatingCofaceMapComplex.objD, CochainComplex.of.d, Fin.sum_univ_two,
        alternatingCofaceMapComplex, CosimplicialObject.δ, ← sub_eq_add_neg] using h₂
  obtain ⟨jT, hjT⟩ := total_zero_map (cosimplicialTotal X) M
    (i ≫ (tripleComplex X).ιTotal (ComplexShape.up ℕ) 0 0 0 rfl) ht
  refine ⟨jD, jT, hjD, ?_, ?_⟩
  · intro m
    simpa [successiveInclusion, Category.assoc] using hjT m
  · ext m
    change jD.f m ≫ (S X).f m = jT.f m
    calc
      _ = i.f m ≫ (diagonalInclusion X 0 m m (Nat.zero_add m) ≫ (S X).f m) := by
        rw [hjD m, Category.assoc]; rfl
      _ = i.f m ≫ successiveInclusion X 0 0 m m (Nat.zero_add m) := by
        rw [hS, shuffle_zero]
      _ = _ := by simpa [successiveInclusion, Category.assoc] using (hjT m).symm

/-- The specified shuffle defines natural homotopy equivalences, natural derived
isomorphisms, and strictly preserves augmentations supported in cosimplicial degree zero.
The component equation characterizes S on every coproduct inclusion, so the existential
map is the prescribed finite signed shuffle, with no arbitrary comparison map chosen.

Source: current blueprint, sec-six-functors-basics,
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), formal input.
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization).

Proof:
1. In Fun(Δ × Δ, Ab), put R_i(j) = ℤ[Hom(i,j)]. Pointwise kernels and cokernels
make this category abelian. Additive Yoneda identifies maps R_i → F with F(i),
so R_i and their finite sums are projective; the sum over all (i,x) surjects onto F.
2. Put P_n = R_(n,n) and Q_n = ⊕_(a+b=n) R_(a,b), with diagonal and signed separate
alternating-deletion boundaries. Cosimplicial identities give square zero; both
augment to the constant ℤ. At (p,q) these are the free pair-string complex and
the total tensor of the two free simplex complexes of
lem-sfb-simplex-lattice-shuffle-boundary.
3. Prepending the minimum vertex gives ∂h+h∂ = 1-eε. On the tensor use
H(u⊗v) = h_p(u)⊗v + (-1)^a E_p(u)⊗h_q(v), with E=eε. Expanding gives
∂H+H∂ = 1-E_p⊗E_q. Thus P,Q are pointwise exact projective resolutions.
4. The cited simplex-lattice shuffle boundary identity assembles the signed sums
into an augmentation-preserving natural chain map σ:Q→P, with distinguished
generator value Σ ε(μ,ν)(α_μ,α_ν).
5. Apply lem-weil-pbc-injective-resolution-lift-exists in the opposite abelian
category, in order Q^op,P^op, obtaining τ:P→Q. The two augmented composites
are homotopic to identities by new-t4-augmented-resolution-lift-homotopy.
6. A map between representables is a finite integral sum of arrows in the reverse
direction. Evaluate it contravariantly on any C-valued diagram, and evaluate
finite sums by transposed matrices of finite biproducts. Bilinearity and
functoriality preserve compositions, hence the chain and homotopy equations.
The evaluated σ is exactly the displayed S, and the evaluated τ is its homotopy inverse.
7. Use the same matrices in every internal degree r. Their entries commute with
the internal differential. Maps preserve n=a+b; homotopies lower n by one, so
the additional internal terms (-1)^(n-1)d_r H + (-1)^n H d_r cancel. This proves
the full total-complex homotopy equivalence. All sums are finite by nonnegativity,
as in def-sp-double-complex-total.
8. Extend by zero to integer cochain degrees and apply localization Q of
def-weil-abstract-derived-category. The homotopy equations give inverse derived
maps; the finite matrix formulas give naturality of the derived isomorphism.
9. If (f₀-f₁)i=(g₀-g₁)i=0, the diagonal difference also kills i by commutation
of the two directions. Thus degree-zero inclusions define j_D,j_T. The sole
empty shuffle has sign 1 and identity surjections, giving j_D ≫ S = j_T strictly.
No step excludes zero objects, constant objects or one constant direction. -/
theorem exists_shuffle [HasDerivedCategory.{w} C] :
    ∃ S : ∀ X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ,
        diagonalTotal X ⟶ successiveTotal X,
      (∀ (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ)
        (n r m : ℕ) (h : n + r = m),
        diagonalInclusion X n r m h ≫ (S X).f m =
          ∑ μ : Finset (Fin n), shuffleTerm X n r m h μ) ∧
      (∀ (X Y : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) (f : X ⟶ Y),
        diagonalMap f ≫ S Y = S X ≫ successiveMap f) ∧
      (∀ X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ,
        ∃ e : HomotopyEquiv (diagonalTotal X) (successiveTotal X), e.hom = S X) ∧
      (∃ e : ∀ X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ,
          (DerivedCategory.Q.obj ((diagonalTotal X).extend ComplexShape.embeddingUpNat)) ≅
          (DerivedCategory.Q.obj ((successiveTotal X).extend ComplexShape.embeddingUpNat)),
        (∀ X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ,
          (e X).hom = DerivedCategory.Q.map
            ((ComplexShape.embeddingUpNat.extendFunctor C).map (S X))) ∧
        (∀ (X Y : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) (f : X ⟶ Y),
          DerivedCategory.Q.map
              ((ComplexShape.embeddingUpNat.extendFunctor C).map (diagonalMap f)) ≫
              (e Y).hom =
            (e X).hom ≫ DerivedCategory.Q.map
              ((ComplexShape.embeddingUpNat.extendFunctor C).map (successiveMap f)))) ∧
      (∀ (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ)
        (M : CochainComplex C ℕ) (i : M ⟶ X.obj (⦋0⦌, ⦋0⦌)),
        i ≫ (X.map ((SimplexCategory.δ (0 : Fin 2), 𝟙 ⦋0⦌) :
            (⦋0⦌, ⦋0⦌) ⟶ (⦋1⦌, ⦋0⦌)) -
          X.map ((SimplexCategory.δ (1 : Fin 2), 𝟙 ⦋0⦌) :
            (⦋0⦌, ⦋0⦌) ⟶ (⦋1⦌, ⦋0⦌))) = 0 →
        i ≫ (X.map ((𝟙 ⦋0⦌, SimplexCategory.δ (0 : Fin 2)) :
            (⦋0⦌, ⦋0⦌) ⟶ (⦋0⦌, ⦋1⦌)) -
          X.map ((𝟙 ⦋0⦌, SimplexCategory.δ (1 : Fin 2)) :
            (⦋0⦌, ⦋0⦌) ⟶ (⦋0⦌, ⦋1⦌))) = 0 →
        ∃ (jD : M ⟶ diagonalTotal X) (jT : M ⟶ successiveTotal X),
          (∀ m : ℕ, jD.f m = i.f m ≫ diagonalInclusion X 0 m m (Nat.zero_add m)) ∧
          (∀ m : ℕ, jT.f m = i.f m ≫ successiveInclusion X 0 0 m m
            (Nat.zero_add m)) ∧
          jD ≫ S X = jT) := by
  classical
  obtain ⟨P, Q, p, q, εP, εQ, zP, zQ, _hproj, hP, hQ, hε, _hexact⟩ :=
    FreeBisimplex.projective_resolutions.{0}
  let := HasDerivedCategory.standard
    (SimplexCategory × SimplexCategory ⥤ AddCommGrpCat.{0})
  obtain ⟨e, _eD, hσ, _haug⟩ :=
    FreeBisimplex.universal_shuffle_homotopy_inverse P Q p q εP εQ hP hQ hε
  obtain ⟨F, hS⟩ := evaluate_universal_shuffle (C := C) P Q p q hP hQ e hσ
  let S := fun X ↦ (F X).hom
  have hN := fun X Y f ↦ shuffle_natural S hS (X := X) (Y := Y) f
  refine ⟨S, hS, hN, (fun X ↦ ⟨F X, rfl⟩), ?_, augmentation_maps S hS⟩
  have hd := fun X ↦ derived_iso_of_homotopy_equiv (F X)
  choose d hd using hd
  have hd' : ∀ X, (d X).hom = DerivedCategory.Q.map
      ((ComplexShape.embeddingUpNat.extendFunctor C).map (S X)) := by
    intro X
    exact hd X
  refine ⟨d, hd', ?_⟩
  intro X Y f
  rw [hd', hd']
  simpa only [Functor.map_comp] using congrArg
    (fun g ↦ DerivedCategory.Q.map
      ((ComplexShape.embeddingUpNat.extendFunctor C).map g)) (hN X Y f)


end AlgebraicTopology.BicosimplicialShuffle
