module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Global units modulo relatively integrally closed constants

Source: Stacks Project, Varieties, Tag 04L7, alternative (1), with Tags 04L4--04L6.
(blueprint: lem-sfb-relatively-closed-constants-units-fg)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Global units modulo nonzero constants form a finitely generated abelian group when
`X` is connected and reduced, locally of finite type over `k`, has finitely many
irreducible components, and `k` is integrally closed in its global sections.
The scalar map is the canonical map induced by the structure morphism.

Source: Stacks Project, Varieties, Tag 04L7, alternative (1).
(blueprint: lem-sfb-relatively-closed-constants-units-fg)

Proof:
1. Choose an algebraic closure `K/k`. By lem-sfb-geometric-connected-component-surjective,
   choose a nonempty connected component `Y` of the reduced geometric base change.
   It is reduced, locally of finite type over `K`, has finitely many irreducible
   components, and maps surjectively to `X`.
2. Pullback of global sections is injective: a section pulling back to zero vanishes
   in every residue field by surjectivity and injectivity of residue-field maps.
   Reducedness detects zero sections, using
   lem-weil-pbc-reduced-induced-closed-subscheme with the identity closed immersion.
3. Give each irreducible component of `Y` its reduced induced structure. These are
   integral and locally of finite type over `K`, since affine prime quotients preserve
   finite type. Apply lem-sfb-integral-units-finite-valuation-map to each component.
   Restriction followed by these maps gives a homomorphism from the units of `Y`
   to a finite product of copies of the integers.
4. Its kernel is exactly the nonzero constants. A kernel element is constant on each
   component. The constants agree on intersecting components by evaluation in a
   residue field. The intersection graph of this finite closed cover is connected:
   otherwise its graph components give a nontrivial clopen partition of `Y`.
   Reducedness then shows that the section equals the common constant globally.
5. Compose with pullback from `X`. If a unit maps to a constant in `K`, it satisfies
   a monic polynomial over `k`, since `K/k` is algebraic. Injectivity of pullback
   descends this polynomial identity to `X`. Relative integral closedness makes the
   unit a nonzero constant in `k`. Conversely these constants lie in the kernel.
   Thus the quotient embeds in the finite product of integers. By
   lem-weil-subgroup-finite-free-abelian-group-free it is free of finite rank, hence
   finitely generated; lifting finite generators gives the claimed units. -/
theorem relatively_closed_constants_units_fg
    (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [ConnectedSpace X] [IsReduced X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (hcomponents : (irreducibleComponents X).Finite)
    (hclosed : @IsIntegrallyClosedIn k Γ(X, ⊤) _ _
      (((ΓSpecIso (CommRingCat.of k)).inv ≫
        (X ↘ Spec (CommRingCat.of k)).appTop).hom.toAlgebra)) :
    Group.FG (Γ(X, ⊤)ˣ ⧸
      (Units.map (((ΓSpecIso (CommRingCat.of k)).inv ≫
        (X ↘ Spec (CommRingCat.of k)).appTop).hom.toMonoidHom)).range) := by
  sorry

end AlgebraicGeometry.Scheme
