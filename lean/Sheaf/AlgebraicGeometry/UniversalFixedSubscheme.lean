module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Sheaf.AlgebraicGeometry.ConstantSourceClosedFactorizationLocus
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # The universal fixed subscheme of a group scheme action

Source: Milne, Algebraic Groups (2017), Theorem 7.1 and proof, printed pp.138--139
(blueprint: lem-sfb-universal-fixed-subscheme).

Fixedness is tested after every algebra extension, including nonreduced algebras.
The action and products are Mathlib's internal action and cartesian products in
schemes over the field. The final condition tests arbitrary schemes over the field.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry

/-- The universally fixed points of a separated finite-type group scheme action
are represented by a closed subscheme, on which the action is trivial. A map from
any scheme over the field factors through this subscheme precisely when its pullback
to the product with the group is invariant. The unique lifts on algebra-valued points
give the identification with the fixed subfunctor by composition with the inclusion;
this identification is natural because restriction is precomposition by `algSpec.map`.

Source: Milne, Algebraic Groups (2017), Theorem 7.1 and its proof, printed pp.138--139,
including the preceding largest fixed closed subscheme formulation
(blueprint: lem-sfb-universal-fixed-subscheme).

Proof plan:
1. Set X = Y times Y. Its finite-type hypotheses follow from
   lem-sfb-finite-type-composition-base-change. Its diagonal is the product of two
   copies of the closed diagonal of Y, after rearranging factors. Factor this product
   into two base changes of that diagonal, closed by
   lem-weil-pbc-closed-immersion-base-change. Their composite is closed by the affine
   quotient criterion of def-weil-closed-immersion: a quotient of a quotient is a
   quotient (Stacks 01QS). Thus X is separated as well as finite type.
2. Apply lem-sfb-constant-source-closed-factorization-locus to the source G,
   parameter Y, target X, closed diagonal Y into X, and family (action, projection).
   A pair of maps factors through the diagonal exactly when the maps agree, by
   def-pc-fibre-product. This gives the asserted factorization criterion for every W.
3. For a point y over an algebra A, equality of the two maps on G times Spec A
   implies the displayed fixedness after each A-algebra extension by precomposition.
   Conversely cover that product by affine charts Spec R, using
   lem-weil-pbc-affine-opens-basis. The projection makes R an A-algebra, and the
   other projection supplies a point of G(R). The fixedness test for this algebra
   says that the two maps agree on the chart. They agree globally by
   lem-weil-pbc-scheme-morphism-gluing, retaining all nilpotents.
4. The closed immersion is a monomorphism by lem-pc-proper-monomorphism-closed,
   so lifts are unique. Steps 2 and 3 identify its algebra-valued points with the
   fixed subfunctor. Composition makes this identification natural. Finally use
   W = F and the inclusion i in step 2: its identity factorization gives the
   restricted-action equality. No smoothness or reducedness assumption is used. -/
theorem exists_universal_fixed_subscheme {k : Type u} [Field k]
    (G Y : Over (Spec (.of k))) [GrpObj G]
    [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [ModObj G Y] :
    ∃ (F : Over (Spec (.of k))) (i : F ⟶ Y),
      IsClosedImmersion i.left ∧
      (∀ (A : CommAlgCat.{u} k) (y : (algSpec (.of k)).obj (op A) ⟶ Y),
        (∃! z : (algSpec (.of k)).obj (op A) ⟶ F, z ≫ i = y) ↔
          ∀ (A' : CommAlgCat.{u} k) (f : A ⟶ A')
            (g : (algSpec (.of k)).obj (op A') ⟶ G),
            g • ((algSpec (.of k)).map f.op ≫ y) = (algSpec (.of k)).map f.op ≫ y) ∧
      (G ◁ i) ≫ ModObj.smul (M := G) (X := Y) = snd G F ≫ i ∧
      ∀ (W : Over (Spec (.of k))) (v : W ⟶ Y),
        (∃ w : W ⟶ F, w ≫ i = v) ↔
          (G ◁ v) ≫ ModObj.smul (M := G) (X := Y) = snd G W ≫ v := by
  sorry

end AlgebraicGeometry
