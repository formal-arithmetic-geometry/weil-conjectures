/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Connected
import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
import Sheaf.CategoryTheory.ExtOneExtensionClassification
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Comma.Final
import Mathlib.CategoryTheory.Comma.LocallySmall
import Mathlib.CategoryTheory.Limits.Comma
import Sheaf.CategoryTheory.ArrowExactColimits
import WeilConjectures.CategoryTheory.PushoutShortExactSequence

/-!
# Filtered-colimit hull of an FP2 weak Serre subcategory

Source: blueprint latest, sec-six-functors-basics/sk-prop-ind-heart/
sk-prop-ind-heart.proof.md, Canonical presentations, Filtered colimits and direct sums,
Kernels and cokernels, and Extensions (blueprint: lem-sfb-fp2-ind-realization).

`ObjectProperty.ind` uses small filtered diagrams with arbitrary transition maps.
The degree-one Ext functor is the standard small model for Yoneda extension classes:
the proved `nonempty_yonedaDerivedExtComparison` identifies it naturally with the quotient
of actual short exact sequences, carrying Baer addition. Thus its continuity expresses
exactly continuity of Yoneda Ext, without an additional comparison hypothesis.
-/

@[expose] public section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

private theorem ind_filtered_closure
    {B : Type u} [Category.{v} B] [LocallySmall.{w} B]
    (P : ObjectProperty B) (hHom : P ≤ isFinitelyPresentable.{w} B)
    (I : Type w) [SmallCategory I] [IsFiltered I] :
    (ind.{w} P).IsClosedUnderColimitsOfShape I where
  colimitsOfShape_le X hX := by
    rw [← ind_ind hHom]
    obtain ⟨pres⟩ := hX
    exact ⟨I, inferInstance, inferInstance, pres.toColimitPresentation, pres.prop_diag_obj⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem presentation_final
    {B : Type u} [Category.{v} B] (P : ObjectProperty B)
    (hHom : P ≤ isFinitelyPresentable.{w} B)
    {I : Type w} [SmallCategory I] [IsFiltered I] {X : B}
    (p : P.ColimitOfShape I X) : p.toCostructuredArrow.Final := by
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun f ↦ ?_, fun {f j} g₁ g₂ ↦ ?_⟩
  · have : IsFinitelyPresentable.{w} (P.ι.obj f.left) := hHom _ f.left.property
    obtain ⟨j, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit p.isColimit f.hom
    exact ⟨j, ⟨CostructuredArrow.homMk (ObjectProperty.homMk g) hg⟩⟩
  · have : IsFinitelyPresentable.{w} f.left.obj := hHom _ f.left.property
    have : PreservesFilteredColimitsOfSize.{w, w}
        (coyoneda.obj (Opposite.op f.left.obj)) :=
      isFinitelyPresentable_iff_preservesFilteredColimitsOfSize.mp
        (hHom _ f.left.property)
    have : PreservesColimit p.diag (coyoneda.obj (Opposite.op f.left.obj)) := inferInstance
    obtain ⟨k, a, h⟩ := exists_eq_of_preservesColimit_coyoneda_self p.isColimit
      g₁.left.hom g₂.left.hom ((CostructuredArrow.w g₁).trans (CostructuredArrow.w g₂).symm)
    exact ⟨k, a, by cat_disch⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ind_arrow_presentation
    {B : Type u} [Category.{v} B] [LocallySmall.{w} B]
    (P : ObjectProperty B) (hHom : P ≤ isFinitelyPresentable.{w} B)
    {X Y : B} (f : X ⟶ Y) (hX : ind.{w} P X) (hY : ind.{w} P Y) :
    ind.{w} (fun a : Arrow B ↦ P a.left ∧ P a.right) (Arrow.mk f) := by
  classical
  obtain ⟨I, _, _, pX, hX⟩ := hX
  obtain ⟨J, _, _, pY, hY⟩ := hY
  let qX : P.ColimitOfShape I X := ⟨pX, hX⟩
  let qY : P.ColimitOfShape J Y := ⟨pY, hY⟩
  let L := qX.toCostructuredArrow ⋙ CostructuredArrow.map f
  let R := qY.toCostructuredArrow
  have : R.Final := presentation_final P hHom qY
  let K := Comma L R
  have : Small.{w} K := small_of_surjective
    (f := fun k : Σ i, Σ j, L.obj i ⟶ R.obj j ↦ (⟨k.1, k.2.1, k.2.2⟩ : K))
    (by rintro ⟨i, j, g⟩; exact ⟨⟨i, j, g⟩, rfl⟩)
  let D : K ⥤ Arrow B :=
    { obj k := Arrow.mk k.hom.left.hom
      map {k l} a := Arrow.homMk (pX.diag.map a.left) (pY.diag.map a.right)
        (by simpa [L, R] using congrArg (fun b ↦ b.left.hom) a.w) }
  let c : Cocone D :=
    { pt := Arrow.mk f
      ι.app k := Arrow.homMk (pX.ι.app k.left) (pY.ι.app k.right)
        (by simpa [L, R, D, qX, qY] using k.hom.w.symm)
      ι.naturality k l a := by
        ext
        · exact pX.ι.naturality a.left
        · exact pY.ι.naturality a.right }
  have hc : IsColimit c := Comma.fstSndJointlyReflectColimit
    ((Functor.Final.isColimitWhiskerEquiv (Comma.fst L R) _).symm pX.isColimit)
    ((Functor.Final.isColimitWhiskerEquiv (Comma.snd L R) _).symm pY.isColimit)
  exact of_essentiallySmall_index ⟨D, c.ι, hc⟩ (fun k ↦ ⟨hX k.left, hY k.right⟩)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ind_biprod
    {B : Type u} [Category.{v} B] [Abelian B]
    (P : ObjectProperty B) [P.IsClosedUnderExtensions]
    {X Y : B} (hX : ind.{w} P X) (hY : ind.{w} P Y) : ind.{w} P (X ⊞ Y) := by
  classical
  obtain ⟨I, _, _, pX, hX⟩ := hX
  obtain ⟨J, _, _, pY, hY⟩ := hY
  let p := pX.reindex (Prod.fst I J)
  let q := pY.reindex (Prod.snd I J)
  let D := (pointwiseBinaryBicone p.diag q.diag).pt
  let c : Cocone D :=
    { pt := X ⊞ Y
      ι.app k := biprod.map (p.ι.app k) (q.ι.app k)
      ι.naturality k l a := by
        apply biprod.hom_ext'
        · simp [D]
        · simp [D] }
  let cX (s : Cocone D) : Cocone p.diag :=
    { pt := s.pt
      ι.app k := biprod.inl ≫ s.ι.app k
      ι.naturality k l a := by
        simpa [D, ← Category.assoc] using congrArg (fun z ↦ biprod.inl ≫ z) (s.w a) }
  let cY (s : Cocone D) : Cocone q.diag :=
    { pt := s.pt
      ι.app k := biprod.inr ≫ s.ι.app k
      ι.naturality k l a := by
        simpa [D, ← Category.assoc] using congrArg (fun z ↦ biprod.inr ≫ z) (s.w a) }
  have hc : IsColimit c :=
    { desc s := biprod.desc (p.isColimit.desc (cX s)) (q.isColimit.desc (cY s))
      fac s k := by
        apply biprod.hom_ext' <;> simp [c, cX, cY, p.isColimit.fac, q.isColimit.fac]
      uniq s m hm := by
        apply biprod.hom_ext'
        · apply p.isColimit.hom_ext
          intro k
          have h := congrArg (fun z ↦ biprod.inl ≫ z) (hm k)
          simpa [c, cX, p.isColimit.fac, ← Category.assoc] using h
        · apply q.isColimit.hom_ext
          intro k
          have h := congrArg (fun z ↦ biprod.inr ≫ z) (hm k)
          simpa [c, cY, q.isColimit.fac, ← Category.assoc] using h }
  exact ⟨I × J, inferInstance, inferInstance, ⟨D, c.ι, hc⟩,
    fun k ↦ P.prop_biprod (hX k.1) (hY k.2)⟩

private theorem finite_coproduct_closure
    {B : Type u} [Category.{v} B] [Abelian B]
    (P : ObjectProperty B) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    [P.IsClosedUnderExtensions] : P.IsClosedUnderFiniteCoproducts := by
  have : P.IsClosedUnderBinaryCoproducts := .mk' (by
    rintro _ ⟨F, hF⟩
    exact P.prop_of_iso
      (biprod.isoCoprod _ _ ≪≫ (HasColimit.isoOfNatIso (diagramIsoPair F)).symm)
      (P.prop_biprod (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)))
  exact .mk'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ind_kernel_cokernel
    {B : Type u} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{w} B]
    (P : ObjectProperty B) [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    (hHom : P ≤ isFinitelyPresentable.{w} B) :
    (ind.{w} P).IsClosedUnderKernels ∧ (ind.{w} P).IsClosedUnderCokernels := by
  have hk {X Y : B} (f : X ⟶ Y) (hX : ind.{w} P X) (hY : ind.{w} P Y) :
      ind.{w} P (kernel f) := by
    obtain ⟨I, _, _, p, hp⟩ := ind_arrow_presentation P hHom f hX hY
    have := (arrow_exact_colimits B I).1
    exact ⟨I, inferInstance, inferInstance, p.map (ker (C := B)),
      fun i ↦ P.prop_kernel _ (hp i).1 (hp i).2⟩
  have hc {X Y : B} (f : X ⟶ Y) (hX : ind.{w} P X) (hY : ind.{w} P Y) :
      ind.{w} P (cokernel f) := by
    obtain ⟨I, _, _, p, hp⟩ := ind_arrow_presentation P hHom f hX hY
    have := (arrow_exact_colimits B I).2
    exact ⟨I, inferInstance, inferInstance, p.map (coker B),
      fun i ↦ P.prop_cokernel _ (hp i).1 (hp i).2⟩
  constructor
  · constructor
    rintro Z ⟨f, k, h, hP⟩
    exact (ind.{w} P).prop_of_iso
      ((kernelIsKernel f).conePointUniqueUpToIso h) (hk f hP.1 hP.2)
  · constructor
    rintro Z ⟨f, k, h, hP⟩
    exact (ind.{w} P).prop_of_iso
      ((cokernelIsCokernel f).coconePointUniqueUpToIso h) (hc f hP.1 hP.2)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ind_extension_finite_quotient
    {B : Type u} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{w} B]
    (P : ObjectProperty B) [P.IsClosedUnderExtensions]
    [(ind.{w} P).IsClosedUnderCokernels]
    (hExt : ∀ C : B, P C →
      PreservesFilteredColimitsOfSize.{w, w} (Abelian.extFunctorObj.{w} C 1))
    (S : ShortComplex B) (hS : S.ShortExact)
    (hN : ind.{w} P S.X₁) (hC : P S.X₃) : ind.{w} P S.X₂ := by
  classical
  let := HasDerivedCategory.standard B
  obtain ⟨I, _, _, p, hp⟩ := hN
  have := hExt S.X₃ hC
  obtain ⟨i, ξ, hξ⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (Abelian.extFunctorObj.{w} S.X₃ 1 ⋙ forget AddCommGrpCat)
      p.isColimit) hS.extClass
  obtain ⟨E, a, b, z, h, hξ'⟩ :=
    (ext_one_extension_classification.{w, w, max u v, max u v, v, v, u, u}
      (p.diag.obj i) S.X₃).1 ξ
  let T := ShortComplex.mk a b z
  obtain ⟨q, hz, hq, _, hU, m, hm₁, _, hm₃⟩ :=
    (pushout_short_exact_sequence T h (p.ι.app i)).2
  let U := ShortComplex.mk (pushout.inl (p.ι.app i) a) q hz
  have hclass : hU.extClass = hS.extClass := by
    have hn := h.extClass_naturality hU m
    rw [hm₁, hm₃, Abelian.Ext.mk₀_id_comp, hξ'] at hn
    exact hn.symm.trans hξ
  obtain ⟨e, _, _⟩ :=
    (ext_one_extension_classification.{w, w, max u v, max u v, v, v, u, u} S.X₁ S.X₃).2.1
    U.X₂ S.X₂ U.f U.g U.zero hU S.f S.g S.zero hS |>.mp hclass
  apply (ind.{w} P).prop_of_iso e
  have hE : P E := P.prop_X₂_of_shortExact h (hp i) hC
  exact (ind.{w} P).prop_of_isColimit_cokernelCofork
    (Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout (p.ι.app i) a)
    (P.le_ind _ (hp i)) (ind_biprod P ⟨I, inferInstance, inferInstance, p, hp⟩
      (P.le_ind _ hE))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ind_extension_closure
    {B : Type u} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{w} B]
    (P : ObjectProperty B) [P.IsClosedUnderExtensions]
    [(ind.{w} P).IsClosedUnderCokernels]
    (hHom : P ≤ isFinitelyPresentable.{w} B)
    (hExt : ∀ C : B, P C →
      PreservesFilteredColimitsOfSize.{w, w} (Abelian.extFunctorObj.{w} C 1)) :
    (ind.{w} P).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS hN hC := by
    obtain ⟨I, _, _, p, hp⟩ := hC
    have := IsFiltered.isConnected I
    have := ind_filtered_closure P hHom I
    apply (ind.{w} P).prop_of_isColimit
      (p.isColimit.pullbackOfHasExactColimitsOfShape S.g)
    intro i
    exact (ind.{w} P).prop_of_iso (pullbackObjIso _ _ i).symm
      ((ind.{w} P).prop_of_iso (pullbackSymmetry S.g (p.ι.app i))
        (ind_extension_finite_quotient P hExt (S.pullback (p.ι.app i))
          (hS.pullback _) hN (hp i)))

/-- The small filtered-colimit hull of an essentially small FP2 weak Serre class
contains zero and the original class, and is closed under filtered colimits,
coproducts, kernels, cokernels and every ambient short exact extension.

Source: blueprint latest, sk-prop-ind-heart.proof.md, Canonical presentations,
Filtered colimits and direct sums, Kernels and cokernels, and Extensions
(blueprint: lem-sfb-fp2-ind-realization).

The Hom hypothesis is finite presentability, equivalently preservation of small
filtered colimits by `coyoneda.obj (op C)`. The Ext hypothesis uses `extFunctorObj C 1`.
Its canonical natural identification with Yoneda classes is supplied by the proved
`nonempty_yonedaDerivedExtComparison`, whose naturality identifies postcomposition
with pushout and whose Baer-sum clause identifies the group laws. It is not assumed.
All indexing categories in the hypotheses, the hull and the conclusions use `w`.

Proof plan, following the ten steps of the node:
1. Choose a small skeleton of the original full subcategory. Extension closure
   gives finite biproducts, and cokernels of differences give coequalizers. Hence
   its finite colimits are ambient finite colimits.
2. Apply `lem-sfb-ind-fp-idempotence` (`ObjectProperty.ind_ind`) using the Hom
   hypothesis to flatten small filtered presentations. Constant singleton diagrams
   give containment of the original class and zero.
3. Finite products of filtered indices present finite sums stagewise. The filtered
   poset of finite subsets presents an arbitrary coproduct, including the empty one.
4. For each hull object B, the small category of maps C -> B from skeleton objects
   is filtered by zero, sums and cokernels. Hom continuity and
   `lem-weil-pbc-filtered-colimit-sets-elementwise` prove its tautological colimit is B.
5. Present an arbitrary arrow B -> B' on the small category of finite-stage squares.
   Componentwise sums and cokernels of differences make this category filtered.
6. Both vertex projections are final: factor maps by Hom continuity and equalize
   parallel maps by cokernels. Use the dual of
   `lem-weil-pbc-initial-functor-cofiltered-criterion` to identify the arrow colimit.
7. Grothendieck exactness and `lem-sfb-arrow-exact-colimits` identify its kernel
   and cokernel with filtered colimits of kernels and cokernels in the original class.
8. Pull any ambient extension back to each quotient stage. Apply the opposite of
   `lem-weil-pbc-pushout-short-exact-sequence`. Ext continuity and the elementwise
   filtered-colimit lemma descend its Yoneda class to a kernel stage. The middle
   object at that stage is in the original class; pushing out recovers the pullback.
9. Push this finite-stage extension out over the small filtered undercategory of
   the chosen kernel stage. Its projection is final by the dual initial-functor
   criterion, and the pushout universal property computes the colimit as the pullback.
10. The quotient-stage pullbacks are kernels of (q,-c_a). Exact filtered colimits
    identify their colimit with the kernel of (q,-1), namely the original middle
    object. Step 2 finishes. All skeleton, square, product, finite-subset and
    undercategory indices remain small in the same universe. -/
theorem fp2_ind_realization
    (B : Type u) [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{w} B]
    (P : ObjectProperty B) [EssentiallySmall.{w} P.FullSubcategory]
    [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    (hHom : P ≤ isFinitelyPresentable.{w} B)
    (hExt : ∀ C : B, P C →
      PreservesFilteredColimitsOfSize.{w, w} (Abelian.extFunctorObj.{w} C 1)) :
    (ind.{w} P).ContainsZero ∧ P ≤ ind.{w} P ∧
    (∀ (I : Type w) [SmallCategory I] [IsFiltered I],
      (ind.{w} P).IsClosedUnderColimitsOfShape I) ∧
    (∀ I : Type w, (ind.{w} P).IsClosedUnderColimitsOfShape (Discrete I)) ∧
    (ind.{w} P).IsClosedUnderKernels ∧ (ind.{w} P).IsClosedUnderCokernels ∧
    (ind.{w} P).IsClosedUnderExtensions := by
  have hzero : (ind.{w} P).ContainsZero := by
    obtain ⟨Z, hZ, hP⟩ := P.exists_prop_of_containsZero
    exact ⟨Z, hZ, P.le_ind _ hP⟩
  obtain ⟨hk, hc⟩ := ind_kernel_cokernel P hHom
  have he := ind_extension_closure P hHom hExt
  have := finite_coproduct_closure (ind.{w} P)
  refine ⟨hzero, P.le_ind, ind_filtered_closure P hHom, ?_, hk, hc, he⟩
  intro I
  have := ind_filtered_closure P hHom (Finset (Discrete I))
  apply IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  apply (ind.{w} P).prop_of_iso
    (colimit.isoColimitCocone (CoproductsFromFiniteFiltered.liftToFinsetColimitCocone F)).symm
  change ind.{w} P (colimit (CoproductsFromFiniteFiltered.liftToFinsetObj F))
  apply (ind.{w} P).prop_colimit
  intro S
  change ind.{w} P (∐ fun x : S ↦ F.obj x.val)
  exact (ind.{w} P).prop_coproduct (fun j ↦ hF j.val)

end CategoryTheory.ObjectProperty
