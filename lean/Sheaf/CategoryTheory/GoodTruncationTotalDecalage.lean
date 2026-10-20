/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.CategoryTheory.FilteredComplexDecalageComplex
public import Sheaf.CategoryTheory.DoubleComplexTotal
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Sheaf.CategoryTheory.GoodTruncationTotalImage
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Good horizontal truncation and the shifted-cycle total complex

Source: Stacks Project, Derived Categories, Tag 015X.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

private theorem total_map_mono
    {M N : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (f : M ⟶ N) [Mono f] : Mono (total.map f (ComplexShape.up ℤ)) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  let p := ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let a : Discrete.functor (M.toGradedObject.mapObjFun p n) ⟶
      Discrete.functor (N.toGradedObject.mapObjFun p n) :=
    Discrete.natTrans (fun j ↦ (f.f j.as.val.1).f j.as.val.2)
  exact MorphismProperty.IsStableUnderColimitsOfShape.condition
    (W := MorphismProperty.monomorphisms C)
    _ _ (M.toGradedObject.cofanMapObj p n) (N.toGradedObject.cofanMapObj p n)
    (M.toGradedObject.isColimitCofanMapObj p n)
    (N.toGradedObject.isColimitCofanMapObj p n) a
    (fun j ↦ by change Mono ((f.f j.as.val.1).f j.as.val.2); infer_instance)
    ((total.map f (ComplexShape.up ℤ)).f n)
    (fun j ↦ by
      exact ιTotal_map M N f (ComplexShape.up ℤ) j.as.val.1 j.as.val.2 n j.as.property)

private theorem decalage_iso_of_image
    {K S : CochainComplex C ℤ} (L : DecreasingFiltration K) (a : ℤ)
    (i : S ⟶ K) [Mono i]
    (hi : ∀ n, imageSubobject (i.f n) = L.decalageStep a n) :
    ∃ d : S ≅ L.decalageComplex a, i = d.hom ≫ L.decalageι a := by
  let dn (n : ℤ) : S.X n ≅ (L.decalageComplex a).X n :=
    Subobject.isoOfMkEq (i.f n) (Subobject.mk ((L.decalageι a).f n))
      (by rw [← imageSubobject_mono, ← imageSubobject_mono, L.decalageι_image]; exact hi n) ≪≫
        Subobject.underlyingIso ((L.decalageι a).f n)
  have hn (n : ℤ) : (dn n).hom ≫ (L.decalageι a).f n = i.f n := by
    simp [dn]
  let d : S ≅ L.decalageComplex a := HomologicalComplex.Hom.isoOfComponents dn (by
    intro n m h
    apply (cancel_mono ((L.decalageι a).f m)).mp
    simp only [Category.assoc]
    rw [hn, ← (L.decalageι a).comm n m, ← Category.assoc, hn]
    exact i.comm n m)
  refine ⟨d, ?_⟩
  apply HomologicalComplex.hom_ext
  intro n
  exact (hn n).symm

/-- Horizontal good truncation totalizes to the shifted-cycle subcomplex.
Source: Stacks Project, Derived Categories, Tag 015X, second filtration.
(blueprint: lem-sp-good-truncation-total-decalage).

Proof. Totalization preserves monomorphisms because coproducts are exact in a
Grothendieck abelian category. Apply the degreewise good-cut image identity,
which is exactly the intersection defining decalage. Each monic inclusion
therefore has the same subobject as the corresponding decalage term and gives a
canonical degreewise isomorphism. Cancel the monic ambient inclusions to check
the differential equation and assemble the complex isomorphism.

For the degreewise identity, in degree m write the first-quadrant total as the finite direct sum of
M^(p,m-p), for 0<=p<=m. Its vertical filtration m-q is the sum over p<=q; the next
vertical step removes the boundary summand p=q. On the outgoing total differential,
modulo that next step only the horizontal differential out of p=q remains. The
vertical differential and all differentials out of p<q land in the next step.
Consequently, intersecting the first step with the inverse image of the next step
retains the full summands p<q and replaces p=q by its horizontal kernel. These are
exactly the terms of the total of the good horizontal truncation. The coproduct
inclusions and the kernel universal property construct maps in both directions;
check their composites on all summands to obtain inverse degreewise maps. The
inclusion into the full total is monic; cancel it to check that these maps commute
with the differential. The resulting complex isomorphism satisfies the displayed
inclusion equation. Empty diagonals give zero objects; when q=0 only the boundary
kernel remains, and when q>m the entire degree-m total is retained. -/
theorem good_truncation_total_decalage
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    (M : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (hM : ∀ p r : ℤ, p < 0 ∨ r < 0 → IsZero ((M.X p).X r))
    (q : ℤ) (hq : 0 ≤ q)
    (L : CategoryTheory.DecreasingFiltration (M.total (ComplexShape.up ℤ)))
    (hL : ∀ p m : ℤ, L.complexStep p m = (M.secondFiltration m).step p) :
    ∃ d : HomologicalComplex₂.total (CochainComplex.truncLE M q) (ComplexShape.up ℤ) ≅
        L.decalageComplex (-q),
      HomologicalComplex₂.total.map (CochainComplex.ιTruncLE M q)
          (ComplexShape.up ℤ) = d.hom ≫ L.decalageι (-q)  := by
  have : Mono (CochainComplex.ιTruncLE M q) := by
    dsimp only [CochainComplex.ιTruncLE]
    infer_instance
  have : Mono (total.map (CochainComplex.ιTruncLE M q) (ComplexShape.up ℤ)) :=
    total_map_mono _
  apply decalage_iso_of_image L (-q) (total.map (CochainComplex.ιTruncLE M q)
    (ComplexShape.up ℤ))
  intro n
  simp only [CategoryTheory.DecreasingFiltration.decalageStep,
    CategoryTheory.DecreasingFiltration.decalage_complexStep, hL]
  simpa only [sub_eq_add_neg, add_comm (-q) n] using
    good_truncation_total_image M hM q hq n

end HomologicalComplex₂
