/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Category.Preorder
public import WeilConjectures.Data.PNat.DvdOrder
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Integer torsion under an exact fully faithful left adjoint

Source: Stacks Project, Modules on Sites, Tags 03DA and 03DB, and Categories, Tag 0038
(blueprint: lem-weil-pbc-exact-faithful-torsion).

The auxiliary declarations construct the integer-kernel diagram and its canonical cocone.
They apply both to module sheaves and to their underlying abelian sheaves. Colimits are
represented by `ColimitCocone`, so the statement is independent of a choice of colimit.
-/

@[expose] public section

set_option autoImplicit false

universe u v uC vC uD vD r s w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

section IntegerKernels

variable {E : Type u} [Category.{v} E] [Preadditive E] [HasKernels E]

/-- Divisibility makes the smaller kernel inclusion annihilated by the larger integer.
Source: Tags 03DA and 03DB (blueprint: lem-weil-pbc-exact-faithful-torsion), proof step 1.
Proof: write `m = n * k`. Composition with `m` identities is `k` times composition with
`n` identities, which vanishes by the kernel condition. -/
theorem integerKernelTransition_condition (F : E) (n m : PNat.DvdOrder)
    (h : n.val ∣ m.val) : kernel.ι (n.val • 𝟙 F) ≫ (m.val • 𝟙 F) = 0 := by
  obtain ⟨k, hk⟩ := h
  rw [hk, mul_comm n.val k, mul_smul, Preadditive.comp_nsmul,
    kernel.condition, nsmul_zero]

/-- The canonical inclusion between integer kernels for a divisibility relation.
Source: Tags 03DA and 03DB (blueprint: lem-weil-pbc-exact-faithful-torsion), proof step 1. -/
noncomputable def integerKernelTransition (F : E) (n m : PNat.DvdOrder)
    (h : n.val ∣ m.val) : kernel (n.val • 𝟙 F) ⟶ kernel (m.val • 𝟙 F) :=
  kernel.lift (m.val • 𝟙 F) (kernel.ι (n.val • 𝟙 F))
    (integerKernelTransition_condition F n m h)

/-- Identity law for the integer-kernel inclusions.
Source: Tags 03DA and 03DB (blueprint: lem-weil-pbc-exact-faithful-torsion), proof step 1.
Proof: compose both sides with the target kernel inclusion. The kernel lift equation gives
that inclusion on both sides, so its monicity gives equality. -/
theorem integerKernelTransition_id (F : E) (n : PNat.DvdOrder) :
    integerKernelTransition F n n (dvd_refl n.val) = 𝟙 _ := by
  apply (cancel_mono (kernel.ι (n.val • 𝟙 F))).1
  simp [integerKernelTransition]

/-- Composition law for the integer-kernel inclusions.
Source: Tags 03DA and 03DB (blueprint: lem-weil-pbc-exact-faithful-torsion), proof step 1.
Proof: compose with the last kernel inclusion. Two applications of the kernel lift equation
reduce both sides to the first kernel inclusion. Cancel the last, monic inclusion. -/
theorem integerKernelTransition_comp (F : E) (n m k : PNat.DvdOrder)
    (hnm : n.val ∣ m.val) (hmk : m.val ∣ k.val) :
    integerKernelTransition F n k (dvd_trans hnm hmk) =
      integerKernelTransition F n m hnm ≫ integerKernelTransition F m k hmk := by
  apply (cancel_mono (kernel.ι (k.val • 𝟙 F))).1
  simp [integerKernelTransition, Category.assoc]

/-- Positive integer kernels with the canonical inclusions, ordered by divisibility.
Source: Tags 03DA and 03DB (blueprint: lem-weil-pbc-exact-faithful-torsion), proof step 1. -/
noncomputable def integerKernelDiagram (F : E) : PNat.DvdOrder ⥤ E where
  obj n := kernel (n.val • 𝟙 F)
  map {n m} h := integerKernelTransition F n m h.down.down
  map_id n := integerKernelTransition_id F n
  map_comp {n m k} hnm hmk :=
    integerKernelTransition_comp F n m k hnm.down.down hmk.down.down

/-- The integer-kernel inclusions commute with every transition.
Source: Tags 03DA and 03DB (blueprint: lem-weil-pbc-exact-faithful-torsion), proof step 1.
Proof: each transition is the kernel lift of the earlier inclusion. Its composite with the
later inclusion is therefore the earlier inclusion by the kernel lift equation. -/
theorem integerKernelDiagram_inclusions (F : E) (n m : PNat.DvdOrder) (h : n ⟶ m) :
    (integerKernelDiagram F).map h ≫ kernel.ι (m.val • 𝟙 F) =
      kernel.ι (n.val • 𝟙 F) ≫ 𝟙 F := by
  simp [integerKernelDiagram, integerKernelTransition]

/-- The canonical cocone from all integer kernels to the original object.
Source: Tags 03DA and 03DB (blueprint: lem-weil-pbc-exact-faithful-torsion), proof step 1. -/
noncomputable def integerKernelCocone (F : E) : Cocone (integerKernelDiagram F) where
  pt := F
  ι :=
    { app := fun n ↦ kernel.ι (n.val • 𝟙 F)
      naturality := fun n m h ↦ integerKernelDiagram_inclusions F n m h }

/-- Torsion means that the canonical map from the colimit of all positive integer kernels
is invertible. Source: Tags 03DA and 03DB
(blueprint: lem-weil-pbc-exact-faithful-torsion), statement and proof steps 1 and 2.
The existential ranges over colimit cocones, each determined up to its unique compatible
isomorphism. Thus it does not impose any uniform annihilating integer. -/
def IsIntegerTorsion (F : E) : Prop :=
  ∃ c : ColimitCocone (integerKernelDiagram F), IsIso (c.isColimit.desc (integerKernelCocone F))

end IntegerKernels

set_option backward.isDefEq.respectTransparency false in
private theorem integerKernelComparison
    {E : Type u} [Category.{v} E] [Preadditive E] [HasKernels E]
    {G : Type uD} [Category.{vD} G] [Preadditive G] [HasKernels G]
    (A : E ⥤ G) [A.Additive]
    [∀ (X Y : E) (f : X ⟶ Y), PreservesLimit (parallelPair f 0) A]
    (F : E) :
    ∃ alpha : integerKernelDiagram F ⋙ A ≅ integerKernelDiagram (A.obj F),
      ∀ n : PNat.DvdOrder,
        alpha.hom.app n ≫ kernel.ι (n.val • 𝟙 (A.obj F)) =
          A.map (kernel.ι (n.val • 𝟙 F)) := by
  let e (n : PNat.DvdOrder) :
      A.obj (kernel (n.val • 𝟙 F)) ≅ kernel (n.val • 𝟙 (A.obj F)) :=
    PreservesKernel.iso A (n.val • 𝟙 F) ≪≫ kernelIsoOfEq (by simp)
  have he (n : PNat.DvdOrder) :
      (e n).hom ≫ kernel.ι (n.val • 𝟙 (A.obj F)) =
        A.map (kernel.ι (n.val • 𝟙 F)) := by
    simp [e]
  refine ⟨NatIso.ofComponents e ?_, he⟩
  intro n m h
  apply (cancel_mono (kernel.ι (m.val • 𝟙 (A.obj F)))).1
  simp only [Category.assoc, he]
  rw [integerKernelDiagram_inclusions, Category.comp_id, he]
  change A.map ((integerKernelDiagram F).map h) ≫ _ = _
  rw [← A.map_comp, integerKernelDiagram_inclusions, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem integerKernelColimitComparison
    {E : Type u} [Category.{v} E] [Preadditive E] [HasKernels E]
    {G : Type uD} [Category.{vD} G] [Preadditive G] [HasKernels G]
    (A : E ⥤ G) (F : E)
    [PreservesColimit (integerKernelDiagram F) A]
    (alpha : integerKernelDiagram F ⋙ A ≅ integerKernelDiagram (A.obj F))
    (ha : ∀ n : PNat.DvdOrder,
      alpha.hom.app n ≫ kernel.ι (n.val • 𝟙 (A.obj F)) =
        A.map (kernel.ι (n.val • 𝟙 F)))
    (c : ColimitCocone (integerKernelDiagram F))
    (d : ColimitCocone (integerKernelDiagram (A.obj F))) :
    ∃ theta : A.obj c.cocone.pt ≅ d.cocone.pt,
      (∀ n : PNat.DvdOrder, A.map (c.cocone.ι.app n) ≫ theta.hom =
        alpha.hom.app n ≫ d.cocone.ι.app n) ∧
      theta.hom ≫ d.isColimit.desc (integerKernelCocone (A.obj F)) =
        A.map (c.isColimit.desc (integerKernelCocone F)) := by
  let hc := isColimitOfPreserves A c.isColimit
  let hd := (IsColimit.precomposeHomEquiv alpha d.cocone).symm d.isColimit
  let theta := hc.coconePointUniqueUpToIso hd
  have ht (n : PNat.DvdOrder) :
      A.map (c.cocone.ι.app n) ≫ theta.hom =
        alpha.hom.app n ≫ d.cocone.ι.app n := by
    exact hc.comp_coconePointUniqueUpToIso_hom hd n
  refine ⟨theta, ht, ?_⟩
  apply hc.hom_ext
  intro n
  change A.map (c.cocone.ι.app n) ≫ theta.hom ≫ _ = _
  rw [← Category.assoc, ht, Category.assoc, d.isColimit.fac]
  change alpha.hom.app n ≫ kernel.ι _ = _
  rw [ha]
  change _ = A.map (c.cocone.ι.app n) ≫ _
  rw [← A.map_comp, c.isColimit.fac]
  rfl

private theorem integerTorsion_iff
    {E : Type u} [Category.{v} E] [Preadditive E] [HasKernels E]
    {G : Type uD} [Category.{vD} G] [Preadditive G] [HasKernels G]
    (A : E ⥤ G) [A.Additive]
    [∀ (X Y : E) (f : X ⟶ Y), PreservesLimit (parallelPair f 0) A]
    (F : E)
    [PreservesColimit (integerKernelDiagram F) A] [A.ReflectsIsomorphisms]
    [HasColimit (integerKernelDiagram F)]
    [HasColimit (integerKernelDiagram (A.obj F))] :
    IsIntegerTorsion F ↔ IsIntegerTorsion (A.obj F) := by
  obtain ⟨alpha, ha⟩ := integerKernelComparison A F
  constructor
  · rintro ⟨c, hi⟩
    have := hi
    let d : ColimitCocone (integerKernelDiagram (A.obj F)) :=
      ⟨colimit.cocone _, colimit.isColimit _⟩
    obtain ⟨theta, _, ht⟩ := integerKernelColimitComparison A F alpha ha c d
    refine ⟨d, ?_⟩
    apply (isIso_comp_left_iff theta.hom _).mp
    rw [ht]
    infer_instance
  · rintro ⟨d, hi⟩
    have := hi
    let c : ColimitCocone (integerKernelDiagram F) :=
      ⟨colimit.cocone _, colimit.isColimit _⟩
    obtain ⟨theta, _, ht⟩ := integerKernelColimitComparison A F alpha ha c d
    refine ⟨c, ?_⟩
    apply (isIso_iff_of_reflects_iso _ A).mp
    rw [← ht]
    infer_instance

private theorem torsion_wEqualsLocallyBijective
    {C : Type uC} [Category.{vC} C] [Small.{w} C] [LocallySmall.{w} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}] :
    J.WEqualsLocallyBijective AddCommGrpCat.{w} := by
  have : PreservesFilteredColimitsOfSize.{w, w}
      (CategoryTheory.forget AddCommGrpCat.{w}) := preservesFilteredColimitsOfSize_shrink _
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} := fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})

/-- An additive fully faithful functor preserving kernels and having a right adjoint
preserves the entire integer-kernel colimit and reflects torsion of underlying abelian sheaves.
Source: Modules on Sites, Tags 03DA and 03DB; Categories, Tag 0038
(blueprint: lem-weil-pbc-exact-faithful-torsion).

Proof, following the seven steps of the node:
1. Positive integers ordered by divisibility form a nonempty filtered category: `1` is an
object, `nm` receives arrows from `n` and `m`, and parallel arrows are equal. The kernel lift
construction gives `integerKernelDiagram F` and its cocone `integerKernelCocone F`.
The module-sheaf colimit theorem supplies colimits of these diagrams for `F` and `A.obj F`.
2. By `lem-weil-pbc-module-sheaves-colimits-forgetful`, forgetting coefficients preserves
kernels and colimits. It consequently identifies the integer diagrams, their transitions,
and the canonical maps with those for underlying abelian sheaves. It reflects invertibility:
the inverse of an invertible underlying map is linear, since applying the injective original
map to `v(a*y)` and `a*v(y)` gives the same value. Thus underlying torsion is equivalent to
invertibility of the canonical module-sheaf map.
3. Additivity gives `A.map (n • 𝟙 F) = n • 𝟙 (A.obj F)`. Kernel preservation and uniqueness
of kernels supply the canonical isomorphisms `alpha.app n`, characterized by their composites
with the kernel inclusions.
4. For `n ∣ m`, both composites through the comparison and transition have composite
`A.map (kernel.ι (n.val • 𝟙 F))` with the last kernel inclusion. Monicity gives naturality,
so these isomorphisms form the diagram isomorphism `alpha`.
5. By `lem-weil-pbc-left-adjoint-preserves-colimits`, the given right adjoint makes `A` preserve
colimits. Transport along `alpha` and uniqueness of colimits give `theta`. Its equation on
all colimit legs characterizes it; its inverse comes from the inverse diagram isomorphism.
6. Compose the two canonical arrows to `A.obj F` with every image colimit leg. Both give
`A.map (kernel.ι (n.val • 𝟙 F))`. The colimit universal property gives the displayed equation
identifying `A(c_F)` with `c_AF` through `theta`.
7. A functor preserves invertibility. Conversely, fullness lifts an inverse of `A(c_F)` to
a map in the source; faithfulness proves both inverse identities there. Combine this with
steps 2 and 6. No single positive integer is assumed to kill `F`.
-/
theorem exact_fullyFaithful_integerTorsion
    {C : Type uC} [Category.{vC} C] [Small.{w} C] [LocallySmall.{w} C]
    {D : Type uD} [Category.{vD} D] [Small.{w} D] [LocallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
    (R : Sheaf J RingCat.{r}) (S : Sheaf K RingCat.{s})
    (A : ringedSiteModules.{w} R ⥤ ringedSiteModules.{w} S)
    [A.Additive] [A.Full] [A.Faithful] [A.IsLeftAdjoint]
    [∀ (X Y : ringedSiteModules.{w} R) (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) A]
    (F : ringedSiteModules.{w} R) :
    ∃ alpha : integerKernelDiagram F ⋙ A ≅ integerKernelDiagram (A.obj F),
      (∀ n : PNat.DvdOrder,
        alpha.hom.app n ≫ kernel.ι (n.val • 𝟙 (A.obj F)) =
          A.map (kernel.ι (n.val • 𝟙 F))) ∧
      Nonempty (ColimitCocone (integerKernelDiagram F)) ∧
      Nonempty (ColimitCocone (integerKernelDiagram (A.obj F))) ∧
      (∀ (c : ColimitCocone (integerKernelDiagram F))
        (d : ColimitCocone (integerKernelDiagram (A.obj F))),
        ∃ theta : A.obj c.cocone.pt ≅ d.cocone.pt,
          (∀ n : PNat.DvdOrder,
            A.map (c.cocone.ι.app n) ≫ theta.hom =
              alpha.hom.app n ≫ d.cocone.ι.app n) ∧
          theta.hom ≫ d.isColimit.desc (integerKernelCocone (A.obj F)) =
            A.map (c.isColimit.desc (integerKernelCocone F))) ∧
      (IsIntegerTorsion ((SheafOfModules.toSheaf.{w} R).obj F) ↔
        IsIntegerTorsion ((SheafOfModules.toSheaf.{w} S).obj (A.obj F))) := by
  classical
  have := torsion_wEqualsLocallyBijective J
  have := torsion_wEqualsLocallyBijective K
  have : PreservesColimitsOfSize.{w, w} (SheafOfModules.toSheaf.{w} R) :=
    { preservesColimitsOfShape := fun {I} _ ↦
        ((moduleSheaves_colimits_forgetful R).2.2.2.2.2 I).2.1 }
  have : PreservesColimitsOfSize.{w, w} (SheafOfModules.toSheaf.{w} S) :=
    { preservesColimitsOfShape := fun {I} _ ↦
        ((moduleSheaves_colimits_forgetful S).2.2.2.2.2 I).2.1 }
  have : PreservesColimitsOfSize.{0, 0} (SheafOfModules.toSheaf.{w} R) :=
    preservesSmallestColimits_of_preservesColimits _
  have : PreservesColimitsOfSize.{0, 0} (SheafOfModules.toSheaf.{w} S) :=
    preservesSmallestColimits_of_preservesColimits _
  obtain ⟨alpha, ha⟩ := integerKernelComparison A F
  refine ⟨alpha, ha, ?_, ?_, integerKernelColimitComparison A F alpha ha, ?_⟩
  · exact ⟨⟨colimit.cocone _, colimit.isColimit _⟩⟩
  · exact ⟨⟨colimit.cocone _, colimit.isColimit _⟩⟩
  · exact (integerTorsion_iff (SheafOfModules.toSheaf.{w} R) F).symm.trans
      ((integerTorsion_iff A F).trans
        (integerTorsion_iff (SheafOfModules.toSheaf.{w} S) (A.obj F)))

end CategoryTheory
