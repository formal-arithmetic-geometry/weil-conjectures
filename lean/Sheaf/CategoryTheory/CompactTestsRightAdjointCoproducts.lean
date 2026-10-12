module

public import Sheaf.CategoryTheory.CompactObject
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.EssentiallySmall

@[expose] public section

universe u v uC uD wC wD

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- An adjunction whose left adjoint takes a small detecting family of compact objects
 to compact objects has a coproduct-preserving right adjoint.
Source: Stacks Project, Tag 0A9R, adjunction Hom calculation and conclusion.
(blueprint: lem-sc-compact-tests-right-adjoint-coproducts).

Proof. For a u-small family K form the coproduct comparison for c. Compactness of
G s identifies Hom(G s, the coproduct of c(K i)) with the direct sum of Hom(G s,c(K i)).
Adjunction identifies these summands with Hom(R(G s),K i). Compactness of R(G s)
identifies their sum with Hom(R(G s), the coproduct of K i), and adjunction identifies
this with Hom(G s,c(the coproduct of K i)). Naturality of adjunction on each
coprojection says the composite bijection is postcomposition with the comparison.
The detecting hypothesis makes that comparison an isomorphism. Adjoint functors
between preadditive categories are additive since they preserve finite biproducts.

For a family in any larger indexing universe with an existing coproduct B in D,
its nonzero indices form a u-small set. Indeed, each coprojection has a retraction
which is the identity on that summand and zero on the others. The corresponding
nonzero idempotents in End(B) are distinct, so these indices inject into the u-small
set End(B). Shrink that support to Type u. Its coproduct is B: removing zero terms
and reindexing preserve the universal property. Since c is a right adjoint, it
preserves the terminal object, which in a preadditive category with an initial
object is also zero. Thus the same removal and reindexing apply to c(K i).
The u-small case now proves preservation for the original family. This argument
also covers the empty family; compactness identifies its Hom groups with zero. -/
theorem compactTests_rightAdjoint_preservesCoproducts
    {C : Type uC} [Category.{wC} C] [Preadditive C] [HasCoproducts.{u} C]
    {D : Type uD} [Category.{wD} D] [Preadditive D] [HasCoproducts.{u} D]
    [LocallySmall.{u} D]
    (R : C ⥤ D) (c : D ⥤ C) (adj : R ⊣ c)
    (S : Type u) (G : S → C)
    (hcompact : ∀ s, IsCompactObject (G s) ∧ IsCompactObject (R.obj (G s)))
    (hdetect : ∀ (A B : C) (g : A ⟶ B),
      (∀ s, Function.Bijective (fun a : G s ⟶ A ↦ a ≫ g)) → IsIso g) :
    ∀ I : Type v, PreservesColimitsOfShape (Discrete I) c := by
  sorry

end CategoryTheory
