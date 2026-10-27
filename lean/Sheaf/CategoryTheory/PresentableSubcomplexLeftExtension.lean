module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Abelian.Refinements
import WeilConjectures.CategoryTheory.PushoutShortExactSequence

/-!
# One-degree extension of a presentable partial subcomplex

Source: Hall--Neeman--Rydh, arXiv:1405.1888v2, proof of Theorem A.3,
downward induction after (1)--(3).
(blueprint: lem-sfb-presentable-subcomplex-left-extension)

A partial complex is encoded by a complex zero outside `[i,b]`. Retention is
expressed by degreewise isomorphisms commuting with the inclusions into `Z`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Extend a partial subcomplex one degree left, retaining its terms and differentials
and the weak-Serre cohomology and cycle-image invariants.
Source: Hall--Neeman--Rydh, arXiv:1405.1888v2, proof of Theorem A.3 after (1)--(3).
(blueprint: lem-sfb-presentable-subcomplex-left-extension)

Proof: Write `Y` for cycles and `X` for boundaries of `Z`. Put `K = cycles N i`,
`L = K ×_{Yⁱ} Xⁱ`, and `J = image (K → Hⁱ Z)`. Subobject closure puts `K,L` in
`S = B^κ`, and the hypothesis puts `J` in `A ∩ S`.
The quotient `E = Zⁱ⁻¹/Xⁱ⁻¹` maps epimorphically to `Xⁱ`, with kernel `Hⁱ⁻¹ Z`.
Use the small-lift hypothesis to obtain `M ↪ E` in `S` mapping epically to `L`.
Its kernel `T` is `M ×_E Hⁱ⁻¹ Z`; hence `T` is presentable and embeds into that
cohomology object. Presentability factors this embedding through one subobject
`P` in the assumed filtered presentation, with `P` in `A ∩ S`.
Push out `0 → T → M → L → 0` along `T → P`, using
`lem-weil-pbc-pushout-short-exact-sequence`, to obtain `0 → P → Q → L → 0`.
Extension closure puts `Q` in `S`. The induced map `Q → E` is monic: its kernel
maps to zero in `L`, so factors through `P`, whose map into `E` is monic.
Lift once more along `Zⁱ⁻¹ ↠ E` to obtain `Nnew ↪ Zⁱ⁻¹` in `S` with `Nnew ↠ Q`.
Its differential lands in `Nⁱ` with image exactly `L`. Its cycles map epically
onto `P`, by `lem-sp-abelian-refinements`, so their image in `Hⁱ⁻¹ Z` is `P`.
The new degree-i cohomology is `K/L ≅ J`. All higher cohomology is unchanged,
as all terms and differentials in degrees at least `i` are retained.
The kernels, images and quotient identifications use `def-sp-abelian` and
`def-weil-abstract-derived-category`; the presentations and their factorization
use `def-weil-pbc-category-colimit`. -/
theorem presentable_subcomplex_left_extension
    {B : Type u} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
    (A : ObjectProperty B) [A.IsClosedUnderIsomorphisms] [A.ContainsZero]
    [A.IsClosedUnderKernels] [A.IsClosedUnderCokernels] [A.IsClosedUnderExtensions]
    [Abelian A.FullSubcategory] [IsGrothendieckAbelian.{v} A.FullSubcategory]
    (hcoprod : ∀ (I : Type v), A.IsClosedUnderColimitsOfShape (Discrete I))
    (κ : Cardinal.{v}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    [(isCardinalPresentable B κ).IsClosedUnderSubobjects]
    [(isCardinalPresentable B κ).IsClosedUnderQuotients]
    [(isCardinalPresentable B κ).IsClosedUnderExtensions]
    (hpresentation : ∀ (X : B), A X →
      ∃ (J : Type v) (_ : SmallCategory J) (_ : IsCardinalFiltered J κ)
        (F : J ⥤ B) (ι : F ⟶ (Functor.const J).obj X),
        Nonempty (IsColimit (Cocone.mk X ι)) ∧
        (∀ j : J, Mono (ι.app j)) ∧
        ∀ j : J, A (F.obj j) ∧ IsCardinalPresentable (F.obj j) κ)
    (hlift : ∀ (X Y n : B) (p : X ⟶ Y) (f : n ⟶ Y), Epi p →
      IsCardinalPresentable n κ →
      ∃ (m : B) (a : m ⟶ X) (q : m ⟶ n),
        IsCardinalPresentable m κ ∧ Epi q ∧ a ≫ p = q ≫ f ∧ (Mono f → Mono a))
    (Z : CochainComplex B ℤ) (hZ : ∀ j : ℤ, A (Z.homology j))
    (i b : ℤ) (hib : i ≤ b) (N : CochainComplex B ℤ) (n : N ⟶ Z)
    (hn : ∀ j : ℤ, Mono (n.f j))
    (hbelow : ∀ j : ℤ, j < i → IsZero (N.X j))
    (habove : ∀ j : ℤ, b < j → IsZero (N.X j))
    (hsmall : ∀ j : ℤ, IsCardinalPresentable (N.X j) κ)
    (hcohom : ∀ j : ℤ, i < j → A (N.homology j) ∧
      IsCardinalPresentable (N.homology j) κ)
    (himage : A (image (HomologicalComplex.cyclesMap n i ≫ Z.homologyπ i)) ∧
      IsCardinalPresentable (image (HomologicalComplex.cyclesMap n i ≫ Z.homologyπ i)) κ) :
    ∃ (M : CochainComplex B ℤ) (m : M ⟶ Z),
      (∀ j : ℤ, Mono (m.f j)) ∧
      (∀ j : ℤ, j < i - 1 → IsZero (M.X j)) ∧
      (∀ j : ℤ, b < j → IsZero (M.X j)) ∧
      (∀ j : ℤ, IsCardinalPresentable (M.X j) κ) ∧
      (∀ j : ℤ, i - 1 < j → A (M.homology j) ∧
        IsCardinalPresentable (M.homology j) κ) ∧
      (A (image (HomologicalComplex.cyclesMap m (i - 1) ≫ Z.homologyπ (i - 1))) ∧
        IsCardinalPresentable
          (image (HomologicalComplex.cyclesMap m (i - 1) ≫ Z.homologyπ (i - 1))) κ) ∧
      ∃ e : ∀ (j : ℤ), i ≤ j → (N.X j ≅ M.X j),
        (∀ (j : ℤ) (hj : i ≤ j), (e j hj).hom ≫ m.f j = n.f j) ∧
        ∀ (j k : ℤ) (hj : i ≤ j) (hk : i ≤ k),
          (e j hj).hom ≫ M.d j k = N.d j k ≫ (e k hk).hom := by
  sorry

end CategoryTheory
