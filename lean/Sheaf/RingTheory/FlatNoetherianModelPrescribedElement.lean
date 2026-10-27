module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.RingTheory.ColimitFlatRingMap
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FiniteType

/-!
# A flat Noetherian model with a prescribed element

Source: Stacks Project, Tag 056Y, `lemma-slice-given-element`, second proof paragraph;
Tag 02JO, flatness descent for finite presentations.
(blueprint: lem-trf-flat-noetherian-model-prescribed-section)
-/

@[expose] public section

universe u v

namespace Algebra

/-- A flat finitely presented algebra and a chosen element descend to a flat finitely
presented algebra over a finite type integer subring, with both model rings Noetherian.

Source: Stacks Project, Tag 056Y, `lemma-slice-given-element`, second proof paragraph.
(blueprint: lem-trf-flat-noetherian-model-prescribed-section)

Proof:
1. Choose a finite polynomial presentation of `B` over `A`, and a polynomial representing
   `a`. Generate a subring `R` of `A` over the integers by all coefficients in the relations
   and in this polynomial. The same relations define a finitely presented `R`-algebra `C`;
   the quotient and tensor universal properties give `A ⊗[R] C ≃ₐ[A] B`, carrying the
   representative of `a` to `a` (Tags 00F3, 00R0 and 00CX).
2. The finite type integer subrings of `A` containing `R` form a nonempty directed set:
   adjoining the union of two finite sets gives an upper bound. Their union is `A`, since
   every element can be adjoined to `R`. Compatible maps on these subrings glue uniquely
   to a ring map on `A`, verifying the colimit property of def-weil-pbc-category-colimit.
3. Apply lem-weil-pbc-colimit-flat-ring-map, namely
   `RingHom.exists_eventually_flat_of_colimit_flat`, with initial lower algebra `R`,
   upper algebra `C`, and map `R → C`. Its limit map identifies with the given flat map
   `A → B` under `A ⊗[R] R ≃ₐ[A] A` and the isomorphism of step 1. It supplies a finite
   type integer subring `A₀` containing `R` for which `B₀ = A₀ ⊗[R] C` is flat over `A₀`.
4. Finite presentation persists under this base change by
   lem-weil-pbc-finite-presentation-base-change-composition. Set `a₀ = 1 ⊗ a_R`.
   Tensor reassociation sends `x ⊗ (y ⊗ c)` to `xy ⊗ c`, with inverse sending
   `x ⊗ c` to `x ⊗ (1 ⊗ c)`. Composing with step 1 gives `e` and `e (1 ⊗ a₀) = a`.
5. Every ideal of the integers is principal by Euclidean division (including the zero
   ideal). Thus the integers are Noetherian. Apply
   lem-weil-pbc-finite-type-algebra-noetherian first to `ℤ → A₀`, then to `A₀ → B₀`;
   the latter map is finite type because it is finitely presented. Both rings are
   Noetherian, as required.
-/
theorem exists_flat_noetherian_model_prescribed_element
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B] (a : B) :
    ∃ A₀ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₀ ∧
      ∃ (B₀ : Type (max u v)) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
        Module.Flat A₀ B₀ ∧ Algebra.FinitePresentation A₀ B₀ ∧
        IsNoetherianRing A₀ ∧ IsNoetherianRing B₀ ∧
        ∃ (a₀ : B₀) (e : TensorProduct A₀ A B₀ ≃ₐ[A] B),
          e (TensorProduct.tmul A₀ (1 : A) a₀) = a := by
  sorry

end Algebra
