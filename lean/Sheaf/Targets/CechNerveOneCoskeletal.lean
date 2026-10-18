import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal

/-!
# The relative Čech nerve is one-coskeletal

Source: literature/stacks-project/simplicial.tex, Tag 018I (blueprint:
lem-trf-cech-nerve-one-coskeletal)

The theorem below records the explicit one-coskeletality and vertex-tuple
extension property of the relative Čech nerve of a map of presheaves.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u v

namespace CategoryTheory

/-- The relative Čech nerve of a map of presheaves is one-coskeletal, with the
explicit degree-zero compatibility and augmented vertex-tuple extension
property described in Stacks Tag 018I and Tag 018J (blueprint:
lem-trf-cech-nerve-one-coskeletal).

(blueprint: lem-trf-cech-nerve-one-coskeletal)

The proof constructs the nerve objectwise as tuples in the fibre product,
checks the truncated maps by their two face maps and degeneracy, extends a
compatible vertex map by its tuple of vertices in every degree, and proves
uniqueness coordinatewise.  The restriction bijection then gives the
coskeleton universal property and its canonical isomorphism.  Finally the
augmentation equality is checked objectwise from naturality.  The argument
uses the simplicial-object and skeleton/coskeleton interfaces recorded by
`def-weil-pbc-simplicial-object` and `def-weil-pbc-simplicial-coskeleton`.
-/
theorem cechNerve_one_coskeletal
    {C : Type u} [Category.{v, u} C]
    (F G : Cᵒᵖ ⥤ Type u) (f : F ⟶ G) :
    let P := Cᵒᵖ ⥤ Type u
    let E := (Arrow.mk f).cechNerve
    IsIso ((SimplicialObject.coskAdj (C := P) 1).unit.app E) ∧
      ∀ (T : SimplicialObject P),
        Function.Bijective
          (fun h : T ⟶ E => (SimplicialObject.truncation 1).map h) ∧
        Nonempty ((T ⟶ E) ≃
          {g : T.obj (Opposite.op ⦋0⦌) ⟶ F //
            T.map (SimplexCategory.δ 0).op ≫ g ≫ f =
              T.map (SimplexCategory.δ 1).op ≫ g ≫ f}) ∧
        ∀ (a : T ⟶ (SimplicialObject.const P).obj G)
          (g : T.obj (Opposite.op ⦋0⦌) ⟶ F),
          g ≫ f = a.app (Opposite.op ⦋0⦌) →
          ∃ H : T ⟶ E,
            (H.app (Opposite.op ⦋0⦌) ≫
                Limits.WidePullback.π (fun _ : Fin 1 => f) 0 = g ∧
              H ≫ (Arrow.mk f).augmentedCechNerve.hom = a ∧
              ∀ (q : ℕ) (i : Fin (q + 1)),
                H.app (Opposite.op ⦋q⦌) ≫
                    Limits.WidePullback.π (fun _ : Fin (q + 1) => f) i =
                  T.map (SimplexCategory.const ⦋0⦌ ⦋q⦌ i).op ≫ g) ∧
            ∀ H' : T ⟶ E,
              (H'.app (Opposite.op ⦋0⦌) ≫
                  Limits.WidePullback.π (fun _ : Fin 1 => f) 0 = g ∧
                H' ≫ (Arrow.mk f).augmentedCechNerve.hom = a) → H' = H := by
  sorry

end CategoryTheory
