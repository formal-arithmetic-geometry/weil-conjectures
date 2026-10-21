/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Projections from fibres of split difference maps

Source: Stacks Project, Tag 08DG (lemma-glue), the split restriction calculation;
Tag 05RS (lemma-cohomology-homological)
(blueprint: lem-sp-derived-split-fibre-projections).

The arbitrary triangle `T` and specified isomorphisms `β` and `γ` include both the
literal biproduct triangles and their presentations by isomorphic vertices.
`Functor.biprodComparison` is the canonical cohomology identification with the biproduct
of the cohomology objects. Monicity together with the image equalities states that
cohomology of the first arrow identifies its source with the indicated graph kernel.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

private theorem projection_isIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang (DerivedCategory A))
    {B P : DerivedCategory A} (β : T.obj₂ ≅ B) [Epi T.mor₂]
    (j : P ⟶ B) (π : B ⟶ P)
    (hj : (j ≫ β.inv) ≫ T.mor₂ = 0) (hjπ : j ≫ π = 𝟙 P)
    (hf : T.mor₁ ≫ β.hom = (T.mor₁ ≫ β.hom ≫ π) ≫ j) :
    IsIso (T.mor₁ ≫ β.hom ≫ π) := by
  have : Mono T.mor₁ := T.mono₁ hT (T.mor₃_eq_zero_of_epi₂ hT inferInstance)
  obtain ⟨k, hk⟩ := T.coyoneda_exact₂ hT (j ≫ β.inv) hj
  have hk' : k ≫ T.mor₁ ≫ β.hom = j := by
    rw [← Category.assoc, ← hk]
    simp
  refine ⟨⟨k, ?_, ?_⟩⟩
  · apply (cancel_mono (T.mor₁ ≫ β.hom)).1
    simpa only [Category.assoc, hk', Category.id_comp] using hf.symm
  · simpa only [Category.assoc, hjπ] using congrArg (fun a ↦ a ≫ π) hk'

private theorem graph_image_kernel_fst
    {A : Type u} [Category.{v} A] [Abelian A] {X Y : A} (h : X ⟶ Y) :
    imageSubobject (biprod.lift (𝟙 X) h) =
      kernelSubobject (biprod.desc h (-𝟙 Y)) := by
  let j : X ⟶ X ⊞ Y := biprod.lift (𝟙 X) h
  let d : X ⊞ Y ⟶ Y := biprod.desc h (-𝟙 Y)
  have : IsSplitMono j := IsSplitMono.mk' ⟨biprod.fst, by simp [j]⟩
  change imageSubobject j = kernelSubobject d
  rw [imageSubobject_mono]
  apply le_antisymm
  · exact Subobject.mk_le_of_comm
      (factorThruKernelSubobject d j (by simp [j, d, biprod.lift_desc]))
      (factorThruKernelSubobject_comp_arrow _ _ _)
  · let k := (kernelSubobject d).arrow
    have hk : k ≫ biprod.snd = k ≫ biprod.fst ≫ h := by
      apply Eq.symm
      apply sub_eq_zero.mp
      simpa [d, biprod.desc_eq, Preadditive.comp_add, Preadditive.comp_neg,
        Category.assoc, sub_eq_add_neg] using kernelSubobject_arrow_comp d
    exact Subobject.le_mk_of_comm (k ≫ biprod.fst) (by
      change (k ≫ biprod.fst) ≫ j = k
      ext <;> simp [j, Category.assoc, hk])

private theorem graph_image_kernel_snd
    {A : Type u} [Category.{v} A] [Abelian A] {X Y : A} (r : Y ⟶ X) :
    imageSubobject (biprod.lift r (𝟙 Y)) =
      kernelSubobject (biprod.desc (𝟙 X) (-r)) := by
  let j : Y ⟶ X ⊞ Y := biprod.lift r (𝟙 Y)
  let d : X ⊞ Y ⟶ X := biprod.desc (𝟙 X) (-r)
  have : IsSplitMono j := IsSplitMono.mk' ⟨biprod.snd, by simp [j]⟩
  change imageSubobject j = kernelSubobject d
  rw [imageSubobject_mono]
  apply le_antisymm
  · exact Subobject.mk_le_of_comm
      (factorThruKernelSubobject d j (by simp [j, d, biprod.lift_desc]))
      (factorThruKernelSubobject_comp_arrow _ _ _)
  · let k := (kernelSubobject d).arrow
    have hk : k ≫ biprod.fst = k ≫ biprod.snd ≫ r := by
      apply sub_eq_zero.mp
      simpa [d, biprod.desc_eq, Preadditive.comp_add, Preadditive.comp_neg,
        Category.assoc, sub_eq_add_neg] using kernelSubobject_arrow_comp d
    exact Subobject.le_mk_of_comm (k ≫ biprod.snd) (by
      change (k ≫ biprod.snd) ≫ j = k
      ext <;> simp [j, Category.assoc, hk])

/-- Projections from the fibre of either signed split difference map, including
specified identifications of the middle and final vertices.

Source: Stacks Project, Tag 08DG (lemma-glue), split restriction calculation, and
Tag 05RS (lemma-cohomology-homological)
(blueprint: lem-sp-derived-split-fibre-projections).

Proof plan:
1. Cohomology is additive: cycles, boundaries, and their quotients commute with
   binary direct sums. Under `Functor.biprodComparison`, the two cohomology arrows have
   components `(H(p), H(q))` and `(H(h), -1)` or `(1, -H(r))`.
2. The second arrow has section `(0, -1)` in the first case and `(1, 0)` in the
   second. Its cohomology is therefore split epic in every integer degree.
   In the long exact sequence (`lem-sf-derived-homology-long-exact`), the connecting
   arrows in degrees n and n-1 vanish because they follow split epimorphisms.
   Exactness then makes the cohomology of the first arrow a kernel of the second.
3. The graph `(1, H(h))` is also a kernel of `(H(h), -1)`: a pair `(a, b)` killed
   by the latter satisfies b = H(h)a and factors uniquely through the graph via a.
4. Comparing these kernels gives an inverse to H(p). Cancelling the monic kernel
   inclusion verifies both inverse identities. Thus H(p) identifies H(G) with
   this graph, which is exactly its image subobject.
5. `lem-weil-pbc-unbounded-derived-iso-cohomology` makes p an isomorphism.
   The triangle identity f followed by d is zero
   (`lem-weil-pbc-hom-into-triangle-exact`) gives q = p followed by h in the
   derived category itself.
6. For `(1, -H(r))`, the graph `(H(r), 1)` is a kernel: a killed pair satisfies
   a = H(r)b and factors uniquely through the graph via b. Kernel comparison
   gives both inverse identities for H(q), and the asserted graph image.
7. Cohomological detection of isomorphisms makes q an isomorphism; the triangle
   identity gives p = q followed by r. Split epicity was established in step 2.
8. Conjugate by the specified vertex isomorphisms. The section becomes
   γ followed by the displayed section followed by β inverse. Cohomology carries
   these isomorphisms to isomorphisms, transporting the kernel and its inclusion
   to the computed graph. An identification α of the first vertex precomposes
   both projections with α and preserves their identities and invertibility.
-/
theorem split_fibre_projections
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang (DerivedCategory A))
    (X Y : DerivedCategory A) (β : T.obj₂ ≅ X ⊞ Y) :
    (∀ (h : X ⟶ Y) (γ : T.obj₃ ≅ Y),
      T.mor₂ ≫ γ.hom = β.hom ≫ biprod.desc h (-𝟙 Y) →
        IsIso (T.mor₁ ≫ β.hom ≫ biprod.fst) ∧
        T.mor₁ ≫ β.hom ≫ biprod.snd = (T.mor₁ ≫ β.hom ≫ biprod.fst) ≫ h ∧
        ∀ n : ℤ,
          IsSplitEpi ((homologyFunctor A n).map T.mor₂) ∧
          Mono ((homologyFunctor A n).map T.mor₁) ∧
          imageSubobject
              ((homologyFunctor A n).map (T.mor₁ ≫ β.hom) ≫
                Functor.biprodComparison (homologyFunctor A n) X Y) =
            kernelSubobject
              (biprod.desc ((homologyFunctor A n).map h)
                (-𝟙 ((homologyFunctor A n).obj Y))) ∧
          imageSubobject
              ((homologyFunctor A n).map (T.mor₁ ≫ β.hom) ≫
                Functor.biprodComparison (homologyFunctor A n) X Y) =
            imageSubobject
              (biprod.lift (𝟙 ((homologyFunctor A n).obj X))
                ((homologyFunctor A n).map h))) ∧
    (∀ (r : Y ⟶ X) (γ : T.obj₃ ≅ X),
      T.mor₂ ≫ γ.hom = β.hom ≫ biprod.desc (𝟙 X) (-r) →
        IsIso (T.mor₁ ≫ β.hom ≫ biprod.snd) ∧
        T.mor₁ ≫ β.hom ≫ biprod.fst = (T.mor₁ ≫ β.hom ≫ biprod.snd) ≫ r ∧
        ∀ n : ℤ,
          IsSplitEpi ((homologyFunctor A n).map T.mor₂) ∧
          Mono ((homologyFunctor A n).map T.mor₁) ∧
          imageSubobject
              ((homologyFunctor A n).map (T.mor₁ ≫ β.hom) ≫
                Functor.biprodComparison (homologyFunctor A n) X Y) =
            kernelSubobject
              (biprod.desc (𝟙 ((homologyFunctor A n).obj X))
                (-((homologyFunctor A n).map r))) ∧
          imageSubobject
              ((homologyFunctor A n).map (T.mor₁ ≫ β.hom) ≫
                Functor.biprodComparison (homologyFunctor A n) X Y) =
            imageSubobject
              (biprod.lift ((homologyFunctor A n).map r)
                (𝟙 ((homologyFunctor A n).obj Y)))) := by
  constructor
  · intro h γ hd
    have : IsSplitEpi T.mor₂ := IsSplitEpi.mk' {
      section_ := γ.hom ≫ (-biprod.inr) ≫ β.inv
      id := by
        apply (cancel_mono γ.hom).1
        simp [Category.assoc, hd] }
    have hz : (T.mor₁ ≫ β.hom) ≫ biprod.desc h (-𝟙 Y) = 0 := by
      rw [Category.assoc, ← hd, ← Category.assoc,
        comp_distTriang_mor_zero₁₂ T hT, zero_comp]
    have hpq : T.mor₁ ≫ β.hom ≫ biprod.snd =
        (T.mor₁ ≫ β.hom ≫ biprod.fst) ≫ h := by
      apply Eq.symm
      apply sub_eq_zero.mp
      simpa [biprod.desc_eq, Preadditive.comp_add, Preadditive.comp_neg,
        Category.assoc, sub_eq_add_neg] using hz
    have hp : IsIso (T.mor₁ ≫ β.hom ≫ biprod.fst) :=
      projection_isIso T hT β (biprod.lift (𝟙 X) h) biprod.fst
        (by
          apply (cancel_mono γ.hom).1
          simp [Category.assoc, hd, biprod.lift_desc])
        (by simp)
        (by ext <;> simp [Category.assoc, hpq])
    refine ⟨hp, hpq, ?_⟩
    intro n
    let F := homologyFunctor A n
    have hm : Mono (F.map T.mor₁) := by
      exact mono_of_mono_fac (F.map_comp T.mor₁ (β.hom ≫ biprod.fst)).symm
    have hg : F.map (T.mor₁ ≫ β.hom) ≫ Functor.biprodComparison F X Y =
        F.map (T.mor₁ ≫ β.hom ≫ biprod.fst) ≫ biprod.lift (𝟙 (F.obj X)) (F.map h) := by
      ext
      · simp [Functor.map_comp, Category.assoc]
      · simp only [Category.assoc, Functor.biprodComparison_snd, biprod.lift_snd]
        rw [← F.map_comp, Category.assoc, hpq, F.map_comp]
    have hi : imageSubobject
          (F.map (T.mor₁ ≫ β.hom) ≫ Functor.biprodComparison F X Y) =
        imageSubobject (biprod.lift (𝟙 (F.obj X)) (F.map h)) := by
      rw [hg, imageSubobject_iso_comp]
    exact ⟨inferInstance, hm, hi.trans (graph_image_kernel_fst (F.map h)), hi⟩
  · intro r γ hd
    have : IsSplitEpi T.mor₂ := IsSplitEpi.mk' {
      section_ := γ.hom ≫ biprod.inl ≫ β.inv
      id := by
        apply (cancel_mono γ.hom).1
        simp [Category.assoc, hd] }
    have hz : (T.mor₁ ≫ β.hom) ≫ biprod.desc (𝟙 X) (-r) = 0 := by
      rw [Category.assoc, ← hd, ← Category.assoc,
        comp_distTriang_mor_zero₁₂ T hT, zero_comp]
    have hpq : T.mor₁ ≫ β.hom ≫ biprod.fst =
        (T.mor₁ ≫ β.hom ≫ biprod.snd) ≫ r := by
      apply sub_eq_zero.mp
      simpa [biprod.desc_eq, Preadditive.comp_add, Preadditive.comp_neg,
        Category.assoc, sub_eq_add_neg] using hz
    have hq : IsIso (T.mor₁ ≫ β.hom ≫ biprod.snd) :=
      projection_isIso T hT β (biprod.lift r (𝟙 Y)) biprod.snd
        (by
          apply (cancel_mono γ.hom).1
          simp [Category.assoc, hd, biprod.lift_desc])
        (by simp)
        (by ext <;> simp [Category.assoc, hpq])
    refine ⟨hq, hpq, ?_⟩
    intro n
    let F := homologyFunctor A n
    have hm : Mono (F.map T.mor₁) := by
      exact mono_of_mono_fac (F.map_comp T.mor₁ (β.hom ≫ biprod.snd)).symm
    have hg : F.map (T.mor₁ ≫ β.hom) ≫ Functor.biprodComparison F X Y =
        F.map (T.mor₁ ≫ β.hom ≫ biprod.snd) ≫ biprod.lift (F.map r) (𝟙 (F.obj Y)) := by
      ext
      · simp only [Category.assoc, Functor.biprodComparison_fst, biprod.lift_fst]
        rw [← F.map_comp, Category.assoc, hpq, F.map_comp]
      · simp [Functor.map_comp, Category.assoc]
    have hi : imageSubobject
          (F.map (T.mor₁ ≫ β.hom) ≫ Functor.biprodComparison F X Y) =
        imageSubobject (biprod.lift (F.map r) (𝟙 (F.obj Y))) := by
      rw [hg, imageSubobject_iso_comp]
    exact ⟨inferInstance, hm, hi.trans (graph_image_kernel_snd (F.map r)), hi⟩

end DerivedCategory
