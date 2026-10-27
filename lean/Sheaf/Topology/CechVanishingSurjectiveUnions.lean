/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sheaves.Flasque
import WeilConjectures.Topology.Sheaves.CechFlasque
import Mathlib.Topology.Order.UpperLowerSetTopology
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-! # Čech vanishing from surjectivity onto unions of cover intersections

Source: Stacks Project, Cohomology of Sheaves, Tag 0A36, lemma-vanishing-ravi.
(blueprint: lem-sfb-cech-vanishing-surjective-unions)

The complex is the recorded general-site `SiteCechComplex`, specialized to the open site.
Any choice of its universal fibre products is allowed. The index, space, and coefficient
universes are independent. No finiteness or separation condition is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

private abbrev RaviPoint (I : Type v) := ULift.{w} {J : Finset I // J.Nonempty}

private instance raviTopology (I : Type v) : TopologicalSpace (RaviPoint.{v, w} I) :=
  Topology.upperSet _

private def raviBasic {I : Type v} (J : Finset I) : Opens (RaviPoint.{v, w} I) :=
  ⟨{A | J ⊆ A.down.val}, by
    intro A B h hJ
    exact fun i hi ↦ h (hJ hi)⟩

private def raviImage {Y : Type u} [TopologicalSpace Y] {I : Type v}
    (V : I → Opens Y) (Z : Opens (RaviPoint.{v, w} I)) : Opens Y :=
  ⨆ J : {J : Finset I // J.Nonempty}, ⨆ (_ : (ULift.up J : RaviPoint I) ∈ Z),
    J.val.inf' J.property V

private theorem raviImage_mono {Y : Type u} [TopologicalSpace Y] {I : Type v}
    (V : I → Opens Y) : Monotone (raviImage.{u, v, w} V) := by
  intro Z W h
  exact iSup_mono fun J ↦ iSup_le fun hJ ↦ le_iSup_of_le (h hJ) le_rfl

private theorem raviImage_le {Y : Type u} [TopologicalSpace Y] {I : Type v}
    (V : I → Opens Y) (Z : Opens (RaviPoint.{v, w} I)) :
    raviImage V Z ≤ ⨆ i, V i := by
  refine iSup_le fun J ↦ iSup_le fun _ ↦ ?_
  obtain ⟨i, hi⟩ := J.property
  exact (Finset.inf'_le _ hi).trans (le_iSup V i)

private theorem raviImage_basic {Y : Type u} [TopologicalSpace Y] {I : Type v}
    (V : I → Opens Y) (J : Finset I) (hJ : J.Nonempty) :
    raviImage.{u, v, w} V (raviBasic J) = J.inf' hJ V := by
  apply le_antisymm
  · refine iSup_le fun K ↦ iSup_le fun hK ↦ ?_
    exact Finset.le_inf' hJ V fun i hi ↦ Finset.inf'_le _ (hK hi)
  · exact le_iSup_of_le ⟨J, hJ⟩ (le_iSup_of_le (show J ⊆ J from le_rfl) le_rfl)

private theorem raviImage_inf {Y : Type u} [TopologicalSpace Y] {I : Type v}
    (V : I → Opens Y) (Z W : Opens (RaviPoint.{v, w} I)) :
    raviImage V (Z ⊓ W) = raviImage V Z ⊓ raviImage V W := by
  classical
  apply le_antisymm
  · exact le_inf (raviImage_mono V inf_le_left) (raviImage_mono V inf_le_right)
  · intro x hx
    obtain ⟨J, hxJ⟩ := Opens.mem_iSup.mp hx.1
    obtain ⟨hJ, hxJ⟩ := Opens.mem_iSup.mp hxJ
    obtain ⟨K, hxK⟩ := Opens.mem_iSup.mp hx.2
    obtain ⟨hK, hxK⟩ := Opens.mem_iSup.mp hxK
    let L : {J : Finset I // J.Nonempty} :=
      ⟨J.val ∪ K.val, J.property.mono Finset.subset_union_left⟩
    apply Opens.mem_iSup.mpr
    refine ⟨L, Opens.mem_iSup.mpr ⟨?_, ?_⟩⟩
    · exact ⟨Z.isOpen Finset.subset_union_left hJ, W.isOpen Finset.subset_union_right hK⟩
    · have hle : J.val.inf' J.property V ⊓ K.val.inf' K.property V ≤
          L.val.inf' L.property V := by
        apply Finset.le_inf' L.property V
        intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · exact inf_le_left.trans (Finset.inf'_le _ hi)
        · exact inf_le_right.trans (Finset.inf'_le _ hi)
      exact hle ⟨hxJ, hxK⟩

private def raviFunctor {Y : Type u} [TopologicalSpace Y] {I : Type v}
    (V : I → Opens Y) : Opens (RaviPoint.{v, w} I) ⥤ Opens Y :=
  (raviImage_mono V).functor

private theorem raviFunctor_continuous {Y : Type u} [TopologicalSpace Y] {I : Type v}
    (V : I → Opens Y) :
    (raviFunctor.{u, v, w} V).IsContinuous
      (Opens.grothendieckTopology (RaviPoint.{v, w} I)) (Opens.grothendieckTopology Y) := by
  let T := raviFunctor.{u, v, w} V
  apply Functor.isContinuous_of_coverPreserving
  · constructor
    intro F Z R x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ _
    have h := hx (homOfLE (inf_le_left : Y₁ ⊓ Y₂ ≤ Y₁))
      (homOfLE (inf_le_right : Y₁ ⊓ Y₂ ≤ Y₂)) hg₁ hg₂ (Subsingleton.elim _ _)
    have hle : X ≤ T.obj (Y₁ ⊓ Y₂) := by
      change X ≤ raviImage V (Y₁ ⊓ Y₂)
      rw [raviImage_inf]
      exact le_inf f₁.le f₂.le
    change F.obj.map (T.map (homOfLE inf_le_left)).op (x g₁ hg₁) =
      F.obj.map (T.map (homOfLE inf_le_right)).op (x g₂ hg₂) at h
    have hh := congrArg (F.obj.map (homOfLE hle).op) h
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply] at hh
    convert hh using 1 <;> congr 2
  · constructor
    intro Z R hR y hy
    obtain ⟨J, hyJ⟩ := Opens.mem_iSup.mp hy
    obtain ⟨hJ, hyJ⟩ := Opens.mem_iSup.mp hyJ
    obtain ⟨W, f, hf, hJW⟩ := hR (ULift.up J) hJ
    refine ⟨T.obj W, T.map f, ?_, ?_⟩
    · exact ⟨W, f, 𝟙 _, hf, Subsingleton.elim _ _⟩
    · exact Opens.mem_iSup.mpr ⟨J, Opens.mem_iSup.mpr ⟨hJW, hyJ⟩⟩

private theorem raviImage_iSup {Y : Type u} [TopologicalSpace Y] {I : Type v}
    (V : I → Opens Y) (Z : Opens (RaviPoint.{v, w} I)) :
    raviImage V Z = ⨆ J : {J : {J : Finset I // J.Nonempty} | ULift.up J ∈ Z},
      J.val.val.inf' J.val.property V := by
  apply le_antisymm
  · refine iSup_le fun J ↦ iSup_le fun hJ ↦ ?_
    exact le_iSup (fun K : {J : {J : Finset I // J.Nonempty} | ULift.up J ∈ Z} ↦
      K.val.val.inf' K.val.property V) ⟨J, hJ⟩
  · exact iSup_le fun J ↦ le_iSup_of_le J.val (le_iSup_of_le J.property le_rfl)

private theorem raviImage_tuple {Y : Type u} [TopologicalSpace Y] {I : Type v}
    (V : I → Opens Y) (p : ℕ) (t : Fin (p + 1) → I) :
    raviImage.{u, v, w} V (⨅ k, raviBasic {t k}) = ⨅ k, V (t k) := by
  classical
  let J := Finset.univ.image t
  have hJ : J.Nonempty := ⟨t 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  have he : (⨅ k, raviBasic.{v, w} {t k}) = raviBasic J := by
    ext A
    simp only [Opens.coe_iInf, Set.mem_iInter, raviBasic,
      Finset.singleton_subset_iff]
    exact ⟨fun h i hi ↦ by obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi; exact h k,
      fun h k ↦ h (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)⟩
  rw [he, raviImage_basic V J hJ]
  apply le_antisymm
  · exact le_iInf fun k ↦ Finset.inf'_le V
      (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  · apply Finset.le_inf' hJ V
    intro i hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
    exact iInf_le _ k

private theorem raviImage_eq_product {Y : Type u} [TopologicalSpace Y] {I : Type v}
    (V : I → Opens Y) {U : Opens Y} (a : ∀ i, V i ⟶ U)
    (K : SiteCechComplex V a) (p : ℕ) (t : Fin (p + 1) → I) :
    (raviFunctor.{u, v, w} V).obj (⨅ k, raviBasic {t k}) = K.W p t := by
  rw [show (raviFunctor V).obj _ = raviImage V _ from rfl, raviImage_tuple]
  apply le_antisymm
  · obtain ⟨b, _, _⟩ := K.universal p t (⨅ k, V (t k))
      (fun k ↦ homOfLE (iInf_le _ k)) (fun _ ↦ Subsingleton.elim _ _)
    exact b.le
  · exact le_iInf fun k ↦ (K.pr p t k).le

private noncomputable def raviCochainIso {Y : Type u} [TopologicalSpace Y] {I : Type v}
    (V : I → Opens Y) {U : Opens Y} (a : ∀ i, V i ⟶ U)
    (K : SiteCechComplex V a) (F : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{w}) (p : ℕ) :
    (K.complex F).X p ≅
      ((TopCat.Presheaf.cechComplex (X := TopCat.of (RaviPoint.{v, w} I))
        (fun i ↦ raviBasic {i})).obj
          (((raviFunctor V).op ⋙ F) ⋙ AddCommGrpCat.uliftFunctor.{v, w})).X p :=
  (AddEquiv.piCongrRight fun t ↦
    ((F.mapIso (eqToIso (raviImage_eq_product V a K p t)).op).addCommGroupIsoToAddEquiv.trans
      AddEquiv.ulift.symm)).toAddCommGrpIso

private noncomputable def raviComplexIso {Y : Type u} [TopologicalSpace Y] {I : Type v}
    (V : I → Opens Y) {U : Opens Y} (a : ∀ i, V i ⟶ U)
    (K : SiteCechComplex V a) (F : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    K.complex F ≅
      (TopCat.Presheaf.cechComplex (X := TopCat.of (RaviPoint.{v, w} I))
        (fun i ↦ raviBasic {i})).obj
          (((raviFunctor V).op ⋙ F) ⋙ AddCommGrpCat.uliftFunctor.{v, w}) :=
  HomologicalComplex.Hom.isoOfComponents (raviCochainIso V a K F) (by
    intro p q hpq
    obtain rfl : p + 1 = q := hpq
    apply AddCommGrpCat.ext
    intro s
    funext t
    apply ULift.ext
    change (((TopCat.Presheaf.cechComplex (X := TopCat.of (RaviPoint.{v, w} I))
      (fun i ↦ raviBasic {i})).obj
        (((raviFunctor V).op ⋙ F) ⋙ AddCommGrpCat.uliftFunctor.{v, w})).d p (p + 1)
          ((raviCochainIso V a K F p).hom s) t).down = _
    rw [TopCat.Presheaf.cechComplex_d_apply]
    simp only [ConcreteCategory.comp_apply, SiteCechComplex.complex, CochainComplex.of_d]
    change (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
      (ULift.up (F.map ((raviFunctor V).map
        (homOfLE (le_iInf fun k ↦
          iInf_le (fun k ↦ raviBasic.{v, w} {t k}) (j.succAbove k)))).op
            (F.map (eqToHom (raviImage_eq_product V a K p (t ∘ j.succAbove))).op
              (s (t ∘ j.succAbove)))) : ULift.{v} _)).down =
      F.map (eqToHom (raviImage_eq_product V a K (p + 1) t)).op
        (K.differentialValue F p s t)
    rw [show (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
      (ULift.up (F.map ((raviFunctor V).map
        (homOfLE (le_iInf fun k ↦
          iInf_le (fun k ↦ raviBasic.{v, w} {t k}) (j.succAbove k)))).op
            (F.map (eqToHom (raviImage_eq_product V a K p (t ∘ j.succAbove))).op
              (s (t ∘ j.succAbove)))) : ULift.{v} _)).down = _ from
        (map_sum AddEquiv.ulift _ _)]
    simp only [SiteCechComplex.differentialValue, map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    change F.map ((raviFunctor V).map (homOfLE (le_iInf fun k ↦
      iInf_le (fun k ↦ raviBasic.{v, w} {t k}) (j.succAbove k)))).op
        (F.map (eqToHom (raviImage_eq_product V a K p (t ∘ j.succAbove))).op
          (s (t ∘ j.succAbove))) =
      F.map (eqToHom (raviImage_eq_product V a K (p + 1) t)).op
        (F.map (K.indexMap t j.succAbove).op (s (t ∘ j.succAbove)))
    exact (F.map_comp_apply _ _ _).symm.trans
      ((congrArg (fun f ↦ F.map f (s (t ∘ j.succAbove)))
        (Subsingleton.elim _ _)).trans (F.map_comp_apply _ _ _)))

/-- Surjectivity of sections onto every union of finite nonempty intersections of a fixed
open cover implies the vanishing of its positive Čech cohomology.

Source: Stacks Project, Cohomology of Sheaves, Tag 0A36, lemma-vanishing-ravi.
(blueprint: lem-sfb-cech-vanishing-surjective-unions)

The set `S` is a family of finite nonempty subsets of `I`. Its union of intersections is
`W`; `hWU` names its inclusion into `U`, which follows from `hU`. Thus this inclusion is
not an additional restriction on `S`. In particular `S = ∅` gives `W = ⊥`.
`K.cohomologyFunctor` uses all ordered tuples, with repetitions, and the alternating
restriction differential. The universal-property data `K` merely choose the intersections.

Proof:
1. Let P be the space of nonempty subsets A of I, with basis B_J consisting of A containing
   the finite nonempty subset J. Then B_J ∩ B_L = B_(J ∪ L), and B_J ⊆ B_L iff L ⊆ J,
   by testing the point J. An open containing J contains B_J. Consequently B_J is contained
   in a union of opens iff it is contained in one member of the union.
2. Send an open Z of P to T(Z), the union of U_J over all J with B_J ⊆ Z. Then
   T(B_J) = U_J, T(∅) = ∅, and T(P) = U, including I empty.
3. T preserves arbitrary unions by step 1. It preserves binary intersections because
   U_J ∩ U_L = U_(J ∪ L) and B_(J ∪ L) = B_J ∩ B_L. Hence it preserves covers and
   their pullbacks along open inclusions.
4. By lem-weil-pbc-site-continuous-pushforward-sheaf, precomposition gives the abelian
   sheaf G(Z) = F(T(Z)) on P. No continuous map of underlying spaces is required.
5. For Z ⊆ Z', hres extends any section of G(Z) to F(U). Restricting this extension to
   T(Z') proves that G is flasque, by def-sc-zariski-flasque. This includes Z empty.
6. The B_{i} cover P. For every ordered tuple, their intersection B_J maps to the
   corresponding intersection U_J, where J is the set of tuple entries. The resulting
   identification of section products respects each omitted-entry restriction, and hence
   the alternating differential. Thus the two Čech complexes are canonically isomorphic;
   the universal properties of K identify its chosen fibre products with these opens.
7. Apply lem-sfb-flasque-open-cover-cech-acyclic (Stacks 09SZ) to G. Transport its vanishing
   across the complex isomorphism of step 6 to obtain the asserted cohomology vanishing.
-/
theorem isZero_siteCech_of_surjective_unions
    (Y : Type u) [TopologicalSpace Y]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{w})
    {I : Type v} (V : I → Opens Y) (U : Opens Y) (hU : (⨆ i, V i) = U)
    (hres : ∀ (S : Set {J : Finset I // J.Nonempty}) (W : Opens Y),
      W = (⨆ J : S, J.val.val.inf' J.val.property V) →
      ∀ hWU : W ≤ U, Function.Surjective (F.obj.map (homOfLE hWU).op))
    (K : SiteCechComplex V (fun i ↦ homOfLE ((le_iSup V i).trans hU.le)))
    (p : ℕ) (hp : 0 < p) :
    IsZero ((K.cohomologyFunctor p).obj F.obj) := by
  classical
  let T := raviFunctor.{u, v, w} V
  have := raviFunctor_continuous.{u, v, w} V
  let G₀ : CategoryTheory.Sheaf (Opens.grothendieckTopology (RaviPoint.{v, w} I))
      AddCommGrpCat.{w} :=
    ⟨T.op ⋙ F.obj, T.op_comp_isSheaf _ _ F⟩
  let G : CategoryTheory.Sheaf (Opens.grothendieckTopology (RaviPoint.{v, w} I))
      AddCommGrpCat.{max v w} :=
    ⟨G₀.obj ⋙ AddCommGrpCat.uliftFunctor.{v, w},
      CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf _ _ _ G₀.property⟩
  have hs (Z : Opens (RaviPoint.{v, w} I)) :
      Function.Surjective (F.obj.map
        (homOfLE ((raviImage_le V Z).trans hU.le)).op) :=
    hres _ _ (raviImage_iSup V Z) _
  have : TopCat.Presheaf.IsFlasque (X := TopCat.of (RaviPoint.{v, w} I)) G.obj := by
    constructor
    intro Z W i
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    obtain ⟨t, ht⟩ := hs W.unop s.down
    refine ⟨ULift.up (F.obj.map
      (homOfLE ((raviImage_le V Z.unop).trans hU.le)).op t), ?_⟩
    apply ULift.ext
    change F.obj.map (T.map i.unop).op
      (F.obj.map (homOfLE ((raviImage_le V Z.unop).trans hU.le)).op t) = s.down
    change F.obj.map (homOfLE (raviImage_mono V i.unop.le)).op
      (F.obj.map (homOfLE ((raviImage_le V Z.unop).trans hU.le)).op t) = s.down
    rw [← Functor.map_comp_apply]
    convert ht using 1
    congr 2
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hG := TopCat.Sheaf.exactAt_cechComplex_of_isFlasque
    (X := TopCat.of (RaviPoint.{v, w} I)) (fun i ↦ raviBasic {i}) q G
  exact ((hG.of_iso (raviComplexIso V _ K F.obj).symm).isZero_homology)

end TopCat.Sheaf
