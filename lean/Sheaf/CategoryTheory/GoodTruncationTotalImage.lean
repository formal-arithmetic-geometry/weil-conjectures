/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Sheaf.CategoryTheory.GoodTruncationTotalBoundaryImage
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # The degreewise image of the total good-truncation inclusion

Source: Stacks Project, Derived Categories, Tag 015X.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂

set_option backward.isDefEq.respectTransparency false

private theorem total_map_isIso_at
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    {M N : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (f : M ⟶ N) (n : ℤ)
    (hf : ∀ p r : ℤ, p + r = n → IsIso ((f.f p).f r)) :
    IsIso ((total.map f (ComplexShape.up ℤ)).f n) := by
  let p := ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let a : Discrete.functor (M.toGradedObject.mapObjFun p n) ⟶
      Discrete.functor (N.toGradedObject.mapObjFun p n) :=
    Discrete.natTrans (fun j ↦ (f.f j.as.val.1).f j.as.val.2)
  exact MorphismProperty.IsStableUnderColimitsOfShape.condition
    (W := MorphismProperty.isomorphisms C)
    _ _ (M.toGradedObject.cofanMapObj p n) (N.toGradedObject.cofanMapObj p n)
    (M.toGradedObject.isColimitCofanMapObj p n)
    (N.toGradedObject.isColimitCofanMapObj p n) a
    (fun j ↦ hf _ _ j.as.property)
    ((total.map f (ComplexShape.up ℤ)).f n)
    (fun j ↦ by
      exact ιTotal_map M N f (ComplexShape.up ℤ) j.as.val.1 j.as.val.2 n j.as.property)

/-- The good horizontal cut has the boundary-kernel image in each total degree.
Source: Stacks Project, Derived Categories, Tag 015X, second filtration.
(blueprint: lem-sp-good-truncation-total-image).

Proof. If q<=n use the finite-diagonal boundary-kernel identity. If n<q, every
nonzero term of the degree-n diagonal lies in a horizontal degree p<q, where
the good-truncation inclusion is an isomorphism. For p>=q the vertical index is
negative: the target term is zero, and so is the source by monicity. Stability
of isomorphisms under coproducts makes the total inclusion invertible in this
degree. Both second filtration indices n-q and n-q+1 are at most zero, so the
intersection is the top subobject, equal to the image of the invertible inclusion.

The finite-diagonal identity has the following description. In degree n the total
is the finite direct sum of M^(p,n-p), 0<=p<=n.
The second filtration at n-q is its direct sum over p<=q. Inside it, the inverse
image of the next vertical step under the total differential is the kernel of
its composite with projection onto the remaining boundary summand at p=q+1.
All vertical differentials and horizontal differentials from p<q already land
in that next step. Thus this kernel retains the full terms with p<q and replaces
the boundary p=q term by its horizontal kernel. Evaluating the horizontal good
truncation gives exactly these terms. The finite direct-sum inclusions and kernel
lifts show both containments of the displayed subobjects. Terms with p>q in the
cut vanish, while omitted negative-index terms vanish by hM. For n<0 the diagonal
is empty; for q>n the entire diagonal remains; for q=0 only the horizontal kernel
on the boundary remains. These descriptions prove the same equality in all cases. -/
theorem good_truncation_total_image
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    (M : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (hM : ∀ p r : ℤ, p < 0 ∨ r < 0 → IsZero ((M.X p).X r))
    (q : ℤ) (hq : 0 ≤ q) (n : ℤ) :
    imageSubobject ((total.map (CochainComplex.ιTruncLE M q)
      (ComplexShape.up ℤ)).f n) =
      (M.secondFiltration n).step (n - q) ⊓
        (Subobject.pullback ((M.total (ComplexShape.up ℤ)).d n (n + 1))).obj
          ((M.secondFiltration (n + 1)).step (n - q + 1))  := by
  by_cases hqn : q ≤ n
  · exact good_truncation_total_boundary_image M hM q hq n hqn
  have hι : Mono (CochainComplex.ιTruncLE M q) := by
    dsimp only [CochainComplex.ιTruncLE]
    infer_instance
  have hf (p r : ℤ) (hpr : p + r = n) :
      IsIso (((CochainComplex.ιTruncLE M q).f p).f r) := by
    by_cases hp : p < q
    · have : IsIso ((CochainComplex.ιTruncLE M q).f p) :=
        CochainComplex.isIso_ιTruncLE_f M q p hp
      exact inferInstance
    · have hz := hM p r (Or.inr (by omega))
      exact (IsZero.of_mono (((CochainComplex.ιTruncLE M q).f p).f r) hz).isIso hz _
  have : IsIso ((total.map (CochainComplex.ιTruncLE M q) (ComplexShape.up ℤ)).f n) :=
    total_map_isIso_at _ n hf
  have htop := (Subobject.isIso_iff_mk_eq_top
    ((total.map (CochainComplex.ιTruncLE M q) (ComplexShape.up ℤ)).f n)).mp
      (by infer_instance)
  have hs (m k : ℤ) (hk : k ≤ 0) : (M.secondFiltration m).step k = ⊤ := by
    apply top_unique
    rw [← M.secondFiltration_zero hM m]
    exact (M.secondFiltration m).antitone_step hk
  rw [imageSubobject_mono, htop, hs n (n-q) (by omega),
    hs (n+1) (n-q+1) (by omega)]
  rw [Subobject.pullback_top]
  simp

end HomologicalComplex₂
