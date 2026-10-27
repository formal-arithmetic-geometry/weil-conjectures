module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Maximal-domain laws for a rational extension of an action

Source: Milne, Algebraic Groups (2017), Proposition 8.25, p.154, and Milne,
A Proof of the Barsotti-Chevalley Theorem (2013), Definition 4.2 and Lemma 4.3
(blueprint: lem-sfb-rational-action-domain-laws).

`ModObj G Y` is the regular scheme action, including its unit and associativity
identities. A value of the maximal representative is expressed by a lift of the
entire k-point through its open domain, followed by equality of scheme morphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- A regular action on a dense open has a unique rational extension. Its maximal
representative obeys the unit law wherever defined and the composition law whenever
both successive actions are defined, including definedness of the product action.

Source: Milne, Algebraic Groups (2017), Proposition 8.25, p.154, referring to Milne,
A Proof of the Barsotti-Chevalley Theorem (2013), Definition 4.2 and Lemma 4.3
(blueprint: lem-sfb-rational-action-domain-laws).

Proof:
1. The product T = G × X is reduced: on affine product charts apply
   lem-wf-affine-product-reduced. The projection to X is open by
   lem-sc-scheme-over-field-universally-open. Every nonempty open in T therefore
   meets G × Y, so G × Y is dense.
2. The action followed by j defines a partial map on G × Y. By
   lem-sfb-rational-map-maximal-representative it has a unique rational class and
   maximal representative p, extending that morphism on all of G × Y.
3. Pull the domain back along z ↦ (e,z). Its morphism agrees with the identity on
   Y by the regular unit law. Reducedness and separatedness give equality on the
   whole common domain, again by lem-sfb-rational-map-maximal-representative.
4. For a fixed h, on the domain of z ↦ h·z use the morphism
   L(u,z) = (u h⁻¹,h·z). The inverse image O of the domain of p contains G × Y.
   On O, p ∘ L agrees with the action on G × Y, by regular associativity and
   (u h⁻¹)h = u. Thus it is another representative of the same rational class.
   Maximality gives O contained in the domain of p and equality there. If h·x
   and g·(h·x) are defined, (gh,x) belongs to O. Evaluation proves definedness
   and the asserted equality. -/
theorem existsUnique_rational_action_domain_laws
    (k : Type u) [Field k] [IsAlgClosed k]
    (G X Y : Over (Spec (.of k))) [GrpObj G] [ModObj G Y]
    [IsIntegral G.left] [Smooth G.hom]
    [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [IsIntegral X.left]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (j : Y ⟶ X) [IsOpenImmersion j.left] (hj : Dense (Set.range j.left)) :
    ∃! α : Scheme.RationalMap (G ⊗ X).left X.left,
      ∃ p : Scheme.PartialMap (G ⊗ X).left X.left,
        p.toRationalMap = α ∧ p.domain = α.domain ∧
        (∃ i : (G ⊗ Y).left ⟶ p.domain.toScheme,
          i ≫ p.domain.ι = (G ◁ j).left ∧
          i ≫ p.hom = (ModObj.smul (M := G) (X := Y) ≫ j).left) ∧
        (∀ (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
          (t : Spec (.of k) ⟶ p.domain.toScheme),
          t ≫ p.domain.ι = (lift (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G) x).left →
          t ≫ p.hom = x.left) ∧
        (∀ (g h : 𝟙_ (Over (Spec (.of k))) ⟶ G)
          (x y z : 𝟙_ (Over (Spec (.of k))) ⟶ X)
          (t v : Spec (.of k) ⟶ p.domain.toScheme),
          t ≫ p.domain.ι = (lift h x).left → t ≫ p.hom = y.left →
          v ≫ p.domain.ι = (lift g y).left → v ≫ p.hom = z.left →
          ∃ w : Spec (.of k) ⟶ p.domain.toScheme,
            w ≫ p.domain.ι = (lift (g * h) x).left ∧ w ≫ p.hom = z.left) := by
  sorry

end AlgebraicGeometry
