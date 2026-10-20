/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Gluing tensor comparisons along a stupid tail

Source: Stacks Project, Tag 06XY, derived tensor exactness and the finite
stupid-truncation argument in Lemma 15.60.9; Tag 08IB, Tor comparison.
(blueprint: lem-pc-tensor-comparison-stupid-tail).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex

namespace CochainComplex

private lemma tensor_single_quasiIso_iff
    {R : Type u} [CommRing R] (B : ModuleCat.{u} R)
    {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (f : X ⟶ Y) :
    QuasiIso (f ▷ (single (ModuleCat R) (.up ℤ) 0).obj B) ↔
      QuasiIso (((tensorRight B).mapHomologicalComplex (.up ℤ)).map f) := by
  let e := map₂HomologicalComplexFlipObjSingleIso (curriedTensor (ModuleCat R)) B
  exact quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm)

private lemma tensor_exchange_quasiIso_iff
    {R : Type u} [CommRing R]
    {E X L N : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : E ⟶ X) (g : L ⟶ N) (hf : QuasiIso f) (hg : QuasiIso g)
    (hE : (quasiIso (ModuleCat R) (.up ℤ)).kFlat E)
    (hL : (quasiIso (ModuleCat R) (.up ℤ)).kFlat L) :
    QuasiIso (f ▷ N) ↔ QuasiIso (X ◁ g) := by
  have : QuasiIso (f ▷ L) := hL.whiskerRight hf
  have : QuasiIso (E ◁ g) := hE.whiskerLeft hg
  have heq := whisker_exchange f g
  constructor
  · intro h
    have : QuasiIso (f ▷ N) := h
    have : QuasiIso ((f ▷ L) ≫ (X ◁ g)) := by
      rw [← heq]
      infer_instance
    exact quasiIso_of_comp_left (f ▷ L) (X ◁ g)
  · intro h
    have : QuasiIso (X ◁ g) := h
    have : QuasiIso ((E ◁ g) ≫ (f ▷ N)) := by
      rw [heq]
      infer_instance
    exact quasiIso_of_comp_left (E ◁ g) (f ▷ N)

private lemma tensor_cone_acyclic_iff
    {R : Type u} [CommRing R]
    (X : CochainComplex (ModuleCat.{u} R) ℤ)
    {L N : CochainComplex (ModuleCat.{u} R) ℤ} (g : L ⟶ N) :
    (X ⊗ mappingCone g).Acyclic ↔ QuasiIso (X ◁ g) := by
  rw [mappingCone.quasiIso_iff_acyclic]
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic,
    ← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  exact (HomotopyCategory.subcategoryAcyclic (ModuleCat R)).prop_iff_of_iso
    ((HomotopyCategory.quotient _ _).mapIso
      (mapBifunctorMappingCone₂Iso X g (curriedTensor (ModuleCat R))))

private lemma exists_stupid_tail_triangle
    {R : Type u} [CommRing R] (Q : CochainComplex (ModuleCat.{u} R) ℤ) (k : ℤ)
    (hbelow : ∀ n : ℤ, n < k → IsZero (Q.X n)) :
    ∃ S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ),
      ∃ _σ : ∀ n, (S.map (eval _ (.up ℤ) n)).Splitting,
        S.X₁ = Q.stupidTrunc (ComplexShape.embeddingUpIntGE (k + 1)) ∧
        S.X₂ = Q ∧ S.X₃ = (single (ModuleCat R) (.up ℤ) k).obj (Q.X k) := by
  let A := ModuleCat.{u} R
  let e := ComplexShape.embeddingUpIntGE (k + 1)
  let G := (single A (.up ℤ) k).obj (Q.X k)
  let i := Q.ιStupidTrunc e
  have hd : ∀ n : ℤ, (ComplexShape.up ℤ).Rel n k → Q.d n k ≫ 𝟙 (Q.X k) = 0 := by
    intro n hn
    exact (hbelow n (by simp only [ComplexShape.up_Rel] at hn; omega)).eq_of_src _ _
  let q : Q ⟶ G := mkHomToSingle (𝟙 (Q.X k)) hd
  have hiq : i ≫ q = 0 := by
    apply to_single_hom_ext
    apply IsZero.eq_of_src
    apply Q.isZero_stupidTrunc_X e
    intro n
    simp only [e, ComplexShape.embeddingUpIntGE_f]
    omega
  let S := ShortComplex.mk i q hiq
  refine ⟨S, ?_, rfl, rfl, rfl⟩
  intro n
  by_cases hn : n = k
  · subst n
    apply ShortComplex.Splitting.ofIsZeroOfIsIso
    · apply Q.isZero_stupidTrunc_X e
      intro n
      simp only [e, ComplexShape.embeddingUpIntGE_f]
      omega
    · change IsIso (q.f k)
      dsimp [q]
      rw [mkHomToSingle_f]
      simp only [Category.id_comp]
      infer_instance
  · apply ShortComplex.Splitting.ofIsIsoOfIsZero
    · change IsIso (i.f n)
      by_cases hkn : k + 1 ≤ n
      · obtain ⟨m, hm⟩ := Int.le.dest hkn
        exact Q.isIso_ιStupidTrunc_f e (i := m) (by
          simp only [e, ComplexShape.embeddingUpIntGE_f]
          omega)
      · have hQ := hbelow n (by omega)
        have hT : IsZero ((Q.stupidTrunc e).X n) := by
          apply Q.isZero_stupidTrunc_X e
          intro m
          simp only [e, ComplexShape.embeddingUpIntGE_f]
          omega
        exact ⟨⟨0, hT.eq_of_src _ _, hQ.eq_of_src _ _⟩⟩
    · exact isZero_single_obj_X (.up ℤ) k (Q.X k) n hn

/-- The comparison for a complex follows from comparisons for its bottom term
and its next stupid tail. No Tor vanishing or upper bound is assumed here.

Source: Stacks Project, Tag 06XY, Lemma 15.60.9 (the degreewise split stupid-tail
sequence), Lemma 15.60.12 and Definition 15.60.13 (K-flat model independence and
exact derived tensor); Tag 08IB, derived-to-ordinary tensor comparison.
(blueprint: lem-pc-tensor-comparison-stupid-tail).

Proof:
1. Choose a K-flat resolution g : L -> B[0] using the proved ordinary-module
   flat-resolution instance. For a K-flat resolution a : E -> X, K-flatness
   makes a tensor L and E tensor g quasi-isomorphisms. The tensor exchange
   square and two-out-of-three show that a tensor B[0] is a quasi-isomorphism
   exactly when X tensor g is. The one-term tensor isomorphism identifies
   a tensor B[0] with the termwise tensor map in the hypotheses.
2. Tensoring a cone is isomorphic to the cone of the tensor map. Thus the
   hypotheses make T tensor Cone(g) and S tensor Cone(g) acyclic, where
   T = sigma_{>=k+1} Q and S = Q.X k[-k]. Construct T -> Q -> S using the
   truncation inclusion and the projection onto degree k. The projection is
   a chain map because Q vanishes below k. In degree k the projection is an
   isomorphism and T vanishes; above k the inclusion is an isomorphism and S
   vanishes; below k all three terms vanish. Hence this sequence is degreewise
   split and its homotopy-category triangle is distinguished.
3. Total tensor with Cone(g) is triangulated. Acyclic complexes form a
   triangulated subcategory, so Q tensor Cone(g) is acyclic as well. Apply
   the cone and exchange equivalences to the specified f : P -> Q, then the
   one-term tensor isomorphism, to obtain the stated termwise quasi-isomorphism.
   No upper bound on Q or Tor-vanishing hypothesis is used. -/
theorem quasiIso_tensor_of_stupid_tail
    {R : Type u} [CommRing R] {B : Type u} [CommRing B] [Algebra R B]
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) (k : ℤ)
    (hbelow : ∀ n : ℤ, n < k → IsZero (Q.X n))
    (hsingle : ∀ (P : CochainComplex.KFlat (ModuleCat.{u} R))
      (f : P.obj ⟶ (HomologicalComplex.single (ModuleCat.{u} R)
        (ComplexShape.up ℤ) k).obj (Q.X k)), QuasiIso f →
      QuasiIso ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f))
    (htail : ∀ (P : CochainComplex.KFlat (ModuleCat.{u} R))
      (f : P.obj ⟶ Q.stupidTrunc (ComplexShape.embeddingUpIntGE (k + 1))), QuasiIso f →
      QuasiIso ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f))
    (P : CochainComplex.KFlat (ModuleCat.{u} R)) (f : P.obj ⟶ Q)
    (hf : QuasiIso f) :
    QuasiIso ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) := by
  classical
  let A := ModuleCat.{u} R
  let N := (single A (.up ℤ) 0).obj (ModuleCat.of R B)
  let W := quasiIso A (.up ℤ)
  let L : W.localizerMorphismKFlat.LeftResolution N := Classical.arbitrary _
  have hg : QuasiIso L.w := L.hw
  have hL := L.X₁.property
  have houter (X : CochainComplex A ℤ)
      (hX : ∀ (E : CochainComplex.KFlat A) (a : E.obj ⟶ X), QuasiIso a →
        QuasiIso (((tensorRight (ModuleCat.of R B)).mapHomologicalComplex (.up ℤ)).map a)) :
      (X ⊗ mappingCone L.w).Acyclic := by
    let E : W.localizerMorphismKFlat.LeftResolution X := Classical.arbitrary _
    have ha : QuasiIso E.w := E.hw
    apply (tensor_cone_acyclic_iff X L.w).2
    apply (tensor_exchange_quasiIso_iff E.w L.w ha hg E.X₁.property hL).1
    exact (tensor_single_quasiIso_iff (ModuleCat.of R B) E.w).2 (hX E.X₁ E.w ha)
  have hT := houter _ htail
  have hG := houter _ hsingle
  obtain ⟨S, σ, h₁, h₂, h₃⟩ := exists_stupid_tail_triangle Q k hbelow
  let H := HomotopyCategory.quotient A (.up ℤ)
  let F := ((curriedTensor A).bifunctorMapHomotopyCategory
    (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj (H.obj (mappingCone L.w))
  have hdist : trianglehOfDegreewiseSplit S σ ∈ distTriang (HomotopyCategory A (.up ℤ)) :=
    (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit _).2
      ⟨S, σ, ⟨Iso.refl _⟩⟩
  have hac : (Q ⊗ mappingCone L.w).Acyclic := by
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
    have ht := (HomotopyCategory.subcategoryAcyclic A).ext_of_isTriangulatedClosed₂ _
      (F.map_distinguished _ hdist)
    change HomotopyCategory.subcategoryAcyclic A (H.obj (S.X₁ ⊗ mappingCone L.w)) →
      HomotopyCategory.subcategoryAcyclic A (H.obj (S.X₃ ⊗ mappingCone L.w)) →
      HomotopyCategory.subcategoryAcyclic A (H.obj (S.X₂ ⊗ mappingCone L.w)) at ht
    rw [h₂] at ht
    apply ht
    · rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic, h₁]
      exact hT
    · rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic, h₃]
      exact hG
  apply (tensor_single_quasiIso_iff (ModuleCat.of R B) f).1
  apply (tensor_exchange_quasiIso_iff f L.w hf hg P.property hL).2
  exact (tensor_cone_acyclic_iff Q L.w).1 hac

end CochainComplex
