module

public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory

/-!
# Property-(P) devissage for a dg algebra

Source: Stacks Project, dga.tex, Tag 0FQE, remark-P-resolution
(blueprint: lem-sfb-dg-property-p-devissage).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.DgAlgebra

/-- An isomorphism-invariant property of objects of the derived category of right dg
modules holds everywhere if it is closed under small coproducts and the two-out-of-three
rule for distinguished triangles, and holds on every shift of the regular module.
Source: Stacks Project, dga.tex, Tag 0FQE, remark-P-resolution
(blueprint: lem-sfb-dg-property-p-devissage).

Proof:
1. For a representative of an arbitrary object M, choose a property-(P) resolution
   q : P → M by lem-sfb-dg-property-p-resolution. Its exhaustive filtration starts at
   zero, has graded-split inclusions, and has quotients that are small direct sums of
   shifts of A. The image of q in the localization is an isomorphism.
2. The empty coproduct gives the property at zero. Induct on the filtration stages.
   Every quotient has the property by the shift hypothesis and coproduct closure,
   using lem-sfb-dg-sequential-colimit-triangle to compute derived coproducts.
   By lem-sfb-dg-derived-admissible-triangles, each graded-split short exact sequence
   of successive filtration stages gives a distinguished triangle. Two-out-of-three
   therefore gives the property at the next stage.
3. The degreewise colimit of the filtration is P. By
   lem-sfb-dg-sequential-colimit-triangle there is a distinguished telescope triangle
   S → S → P → S[1], where S is the coproduct of the filtration stages and the first
   arrow is one minus the shift along the inclusions. Coproduct closure gives the
   property at S, so two-out-of-three gives the property at P.
4. Transport along the localized isomorphism q to obtain the property at M.
   The filtration is sequential, but its free quotients may have arbitrary small
   cardinalities. No countability, boundedness or commutativity is used. -/
theorem property_p_devissage (A : Algebra.{u}) [DerivedStructure A]
    (P : Derived A → Prop)
    (hiso : ∀ (M N : Derived A), (M ≅ N) → P M → P N)
    (hcoproducts : ∀ (I : Type u) (M : I → Derived A), (∀ i : I, P (M i)) → P (∐ M))
    (htriangles : ∀ (T : Triangle (Derived A)), T ∈ distTriang (Derived A) →
      (P T.obj₁ → P T.obj₂ → P T.obj₃) ∧
      (P T.obj₁ → P T.obj₃ → P T.obj₂) ∧
      (P T.obj₂ → P T.obj₃ → P T.obj₁))
    (hregular : ∀ n : ℤ, P (((Q A).obj (regular A))⟦n⟧)) :
    ∀ M : Derived A, P M := by
  sorry

end CategoryTheory.DgAlgebra
