module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# A compatible presentability cardinal for a Grothendieck weak-Serre pair

Source: Hall--Neeman--Rydh, arXiv:1405.1888v2, Lemma A.6 (1), (2), (4),
and the first two paragraphs of the proof of Theorem A.3.
(blueprint: lem-sfb-weak-serre-presentable-cardinal-package)

The colimit clauses below spell out the universal property of the canonical
inclusions from every presentable subobject. Their index types are subtypes of
`Subobject`, with its inherited partial order; `Small` means small up to equivalence.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory

open Limits

/-- A common uncountable regular presentability cardinal, with Serre closure,
smallness, density by all presentable subobjects, and epimorphism lifts.
Source: Hall--Neeman--Rydh, arXiv:1405.1888v2, Lemma A.6 (1), (2), (4),
and proof of Theorem A.3, first two paragraphs.
(blueprint: lem-sfb-weak-serre-presentable-cardinal-package)

Proof: Choose exact module reflectors for both Grothendieck categories using
`lem-sfb-grothendieck-presentables-module-size`. Write H for the image of the
free rank-one module for A. Choose an uncountable regular cardinal larger than
both rings and the underlying module G_B(H). The module-size characterization
makes H ambient-presentable. For a subobject of F(M), pull its G-image back
along the unit M -> GF(M); exactness of F and the triangle identity identify
its F-image with that subobject. Quotients are F(M/P). Regularity and finite
support give closure under coproducts of fewer than the chosen cardinal.
Small modules admit a small family of codes, giving essential smallness.
Every G(c) is the filtered union of its small submodules, whose F-images are
presentable subobjects covering c. Well-poweredness
(`lem-pur-kinjective-set-of-subobjects`) makes the full poset of presentable
subobjects small. The image of any small coproduct is an upper bound, so this
poset is cardinal-filtered, including for the empty family. Presentability
factors each presentable subobject through the preceding module presentation,
which proves the colimit universal property over the full poset.
For an epi x -> y and n -> y, form the pullback t. Its projection to n is epic;
if n -> y is monic, its projection to x is monic
(`lem-sfb-abelian-pullback-epi-mono`). Present t by presentable subobjects.
Exact filtered colimits identify the colimit of their images in n with n.
Presentability of n makes one image all of n, giving the desired lift and the
monic refinement. For an extension with presentable ends k,n, this lifting
argument gives a presentable subobject m of its middle term surjecting onto n.
The map k plus m onto the middle term is epic, proving extension closure.
The inclusion A -> B preserves coproducts by assumption and cokernels by
weak-Serre closure, hence all small colimits by their coproduct-and-cokernel
construction. Fullness then makes ambient presentability imply intrinsic
presentability. Conversely every intrinsically presentable object is a quotient
of fewer than the chosen cardinal copies of H. The same quotient and coproduct
in B prove ambient presentability. This gives the intersection equality and
identifies each intrinsic subobject colimit with its ambient colimit. -/
theorem weakSerre_presentable_cardinal_package
    {B : Type u} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
    (A : ObjectProperty B) [A.IsClosedUnderIsomorphisms] [A.ContainsZero]
    [A.IsClosedUnderKernels] [A.IsClosedUnderCokernels] [A.IsClosedUnderExtensions]
    [Abelian A.FullSubcategory] [IsGrothendieckAbelian.{v} A.FullSubcategory]
    (hcoprod : ∀ (I : Type v), A.IsClosedUnderColimitsOfShape (Discrete I)) :
    ∃ (κ : Cardinal.{v}) (_ : Fact κ.IsRegular),
      Cardinal.aleph0 < κ ∧
      (EssentiallySmall.{v} (isCardinalPresentable B κ).FullSubcategory ∧
        EssentiallySmall.{v} (isCardinalPresentable A.FullSubcategory κ).FullSubcategory ∧
        (isCardinalPresentable B κ).IsSerreClass ∧
        (isCardinalPresentable A.FullSubcategory κ).IsSerreClass) ∧
      (∀ a : A.FullSubcategory,
        IsCardinalPresentable a κ ↔ IsCardinalPresentable a.obj κ) ∧
      (∀ X : B,
        Small.{v} {s : Subobject X // IsCardinalPresentable (s : B) κ} ∧
        IsCardinalFiltered {s : Subobject X // IsCardinalPresentable (s : B) κ} κ ∧
        ∀ (Y : B)
          (f : ∀ s : {s : Subobject X // IsCardinalPresentable (s : B) κ},
            (s.val : B) ⟶ Y),
          (∀ (s t : {s : Subobject X // IsCardinalPresentable (s : B) κ})
            (h : s.val ≤ t.val), Subobject.ofLE s.val t.val h ≫ f t = f s) →
          ∃! g : X ⟶ Y, ∀ s : {s : Subobject X // IsCardinalPresentable (s : B) κ},
            s.val.arrow ≫ g = f s) ∧
      (∀ X : A.FullSubcategory,
        Small.{v} {s : Subobject X // IsCardinalPresentable (s : A.FullSubcategory) κ} ∧
        IsCardinalFiltered {s : Subobject X // IsCardinalPresentable (s : A.FullSubcategory) κ} κ ∧
        ∀ (Y : A.FullSubcategory)
          (f : ∀ s : {s : Subobject X // IsCardinalPresentable (s : A.FullSubcategory) κ},
            (s.val : A.FullSubcategory) ⟶ Y),
          (∀ (s t : {s : Subobject X // IsCardinalPresentable (s : A.FullSubcategory) κ})
            (h : s.val ≤ t.val), Subobject.ofLE s.val t.val h ≫ f t = f s) →
          ∃! g : X ⟶ Y, ∀ s : {s : Subobject X // IsCardinalPresentable (s : A.FullSubcategory) κ},
            s.val.arrow ≫ g = f s) ∧
      (∀ (X : A.FullSubcategory) (Y : B)
          (f : ∀ s : {s : Subobject X // IsCardinalPresentable (s : A.FullSubcategory) κ},
            ((s.val : A.FullSubcategory).obj) ⟶ Y),
          (∀ (s t : {s : Subobject X // IsCardinalPresentable (s : A.FullSubcategory) κ})
            (h : s.val ≤ t.val), (Subobject.ofLE s.val t.val h).hom ≫ f t = f s) →
          ∃! g : X.obj ⟶ Y,
            ∀ s : {s : Subobject X // IsCardinalPresentable (s : A.FullSubcategory) κ},
            s.val.arrow.hom ≫ g = f s) ∧
      (∀ (x y n : B) (p : x ⟶ y) (f : n ⟶ y), Epi p →
        IsCardinalPresentable n κ →
        ∃ (m : B) (q : m ⟶ n) (a : m ⟶ x),
          IsCardinalPresentable m κ ∧ Epi q ∧ a ≫ p = q ≫ f ∧
          (Mono f → Mono a)) := by
  sorry

end CategoryTheory
