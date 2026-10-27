module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Limits

import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import Sheaf.AlgebraicGeometry.IrreducibleProductOverField
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Finite constant component quotient of an affine algebraic group

Source: Milne, Algebraic Groups (2017), Section 2(g), Proposition 2.37(b),(d),
printed pp.51-52, its preceding construction and Remark 2.39(a)
(blueprint: lem-sfb-finite-constant-component-quotient).

The coproduct cocone `j` and its group-operation equations specify the constant group scheme.
The isomorphism `e` identifies it over the base field with the spectrum of the product ring;
the coprojections become the spectra of the coordinate evaluations. Thus the operations
are specified as scheme morphisms, including on schemes with nilpotents.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- An affine finite type group scheme over an algebraically closed field has a finite
constant group quotient whose nonempty fibres are precisely its connected components.
No reducedness, smoothness, commutativity or characteristic assumption is required.

Source: Milne, Algebraic Groups (2017), Section 2(g), Proposition 2.37(b),(d),
printed pp.51-52, its preceding construction and Remark 2.39(a)
(blueprint: lem-sfb-finite-constant-component-quotient).

Proof:
1. By lem-sfb-group-neutral-component-translates, the components are finitely many clopen
subschemes, each a rational translate of the identity component C. By
lem-sfb-locally-algebraic-group-identity-component, C is geometrically irreducible, as are
its translates over every field extension (def-pc-geometrically-irreducible). These are
the original open subschemes, with their full structure sheaves.
2. By lem-sc-irreducible-product-over-field, the product of two component subschemes is
irreducible and connected. Its image under multiplication is in one component. Define
the product of the two labels to be that component; inversion similarly defines inverse.
Every component contains a rational point, and its product label is the label of the
product of representatives. Surjectivity of the rational-point label map descends all
the group laws, with C as identity.
3. Form the coproduct of copies of Spec k indexed by this finite group P using
lem-weil-pbc-scheme-coproduct-family. By lem-weil-pbc-open-fibre-product and
 def-pc-fibre-product, its square is covered by the disjoint pair components. Define
multiplication on the (a,b) piece by the structure map followed by the (ab) coprojection.
Glue these maps using lem-weil-pbc-scheme-morphism-gluing; define inverse and unit by
the inverse and identity labels. Check the group laws on each piece, using the group
laws of P and uniqueness of the k-map to Spec k. By
lem-weil-pbc-finite-affine-coproduct-spectrum this coproduct is Spec(k^P), with inclusions
induced by evaluation. It is affine and finite type (def-weil-finite-type-morphism):
the finitely many coordinate idempotents generate the product algebra over k.
4. On each clopen component of G, take its structure map followed by its coprojection.
Glue by lem-weil-pbc-scheme-morphism-gluing to obtain c. On each component product,
multiplication lands in the product component by step 2 and factors through its open
subscheme by lem-weil-pbc-morphism-factors-through-open-subscheme. Both sides of the
homomorphism equation there are the structure map followed by the product coprojection.
Gluing uniqueness proves equality of scheme morphisms globally. The inverse and unit
compatibilities follow in the same way, so c is a group-scheme homomorphism.
5. The fibre over a label is its original nonempty component, proving surjectivity and
the connected-component assertion (def-weil-connected-scheme). The identity label is C,
so its fibre is the component of the identity point. No step replaces G by its reduction. -/
theorem GrpObj.exists_finiteConstantComponentQuotient
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G] [IsAffine G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    ∃ P : GrpCat.{u}, Finite P ∧
      ∃ (Q : Grp (Over (Spec (.of k))))
        (j : P → (𝟙_ (Over (Spec (.of k))) ⟶ Q.X)),
        Nonempty (IsColimit (Cofan.mk Q.X j)) ∧
        j 1 = 1 ∧ (∀ a b : P, j (a * b) = j a * j b) ∧
        (∀ a : P, j a⁻¹ = (j a)⁻¹) ∧
        (∃ e : Q.X ≅ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (P → k)))),
          ∀ a : P, (j a).left ≫ e.hom.left =
            Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : P ↦ k) a))) ∧
        IsAffine Q.X.left ∧ LocallyOfFiniteType Q.X.hom ∧ QuasiCompact Q.X.hom ∧
        ∃ c : G ⟶ Q.X, IsMonHom c ∧ Surjective c.left ∧
          (∀ a : P, (c.left ⁻¹' Set.range (j a).left).Nonempty ∧
            ∀ x : G.left, x ∈ c.left ⁻¹' Set.range (j a).left →
              c.left ⁻¹' Set.range (j a).left = connectedComponent x) ∧
          c.left ⁻¹' Set.range (j 1).left = connectedComponent (GrpObj.onePoint G) := by
  sorry

end AlgebraicGeometry
