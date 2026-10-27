module

public import Sheaf.RepresentationTheory.FiniteModuleSplitGrothendieck
public import Mathlib.RepresentationTheory.Induced
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Brauer induction by one-dimensional subgroup representations

Source: ILO, Exposé X, Proposition 1.2, printed p.138, representation lifting before (5).
The Brauer induction input is the monomial-character consequence of Serre, Part II, Chapter 10.
(blueprint: lem-per-brauer-monomial-induction)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RepresentationTheory

/-- The line representation attached to a subgroup character: h acts by multiplication by χ(h).
Source: ILO X 1.2, p.138, representation lifting before (5).
(blueprint: lem-per-brauer-monomial-induction) -/
noncomputable def subgroupLineRepresentation
    (F : Type u) [Field F] {G : Type v} [Group G]
    (H : Subgroup G) (χ : H →* Fˣ) : Representation F H F :=
  (Algebra.lsmul F F F).toMonoidHom.comp ((Units.coeHom F).comp χ)

/-- The induced line as a finite-dimensional module over the group algebra.
Source: ILO X 1.2, p.138, representation lifting before (5).
Mathlib's induced space is (F[G] ⊗[F] F)_H, with diagonal H-action and G acting by
right inverse translation on the first factor. Its generator e_g is the class of
[g⁻¹] ⊗ 1. The coinvariant relation gives e_(gh) = χ(h)e_g, and the G-action gives
a e_g = e_(ag). Conversely [g] ⊗ c maps to c e_(g⁻¹); the coinvariant relations
are exactly the stated relations. Thus this is the node's quotient, with its specified action.
(blueprint: lem-per-brauer-monomial-induction) -/
noncomputable def monomialInducedFiniteAlgebraModule
    (F : Type u) [Field F] {G : Type v} [Group G] [Finite G]
    (H : Subgroup G) (χ : H →* Fˣ) :
    FiniteAlgebraModule.{u, max u v, max u v} F (MonoidAlgebra F G) where
  space := ModuleCat.of F (Representation.IndV H.subtype (subgroupLineRepresentation F H χ))
  finite := inferInstance
  action := (Representation.ind H.subtype (subgroupLineRepresentation F H χ)).asAlgebraHom

/-- Every integral representation class is an integral sum of classes induced from lines.
Source: ILO X 1.2, printed p.138, representation lifting before (5); Serre, Part II,
Chapter 10, Brauer induction and its monomial-character consequence.

Proof: (1) Over ℂ, character decomposition and character orthogonality make the character
map on the split Grothendieck group injective (lem-per-finite-group-character-decomposition,
lem-per-finite-group-character-orthogonality); ℂ is algebraically closed by
lem-weil-complex-algebraically-closed. (2) The elementary unit-character identity
(lem-per-brauer-elementary-unit-character) places the unit class in the subgroup generated
by representations induced from elementary subgroups. (3) The tensor identity and additivity
(lem-per-finite-group-induction-calculus) make this subgroup an ideal, so it is the whole
group. (4) Decompose each elementary-subgroup representation into irreducibles, apply
lem-per-elementary-group-monomial, and use induction additivity and transitivity to obtain
an integral combination of induced lines. (5) Choose an algebraic closure A of ℚ. Apply
lem-per-finite-group-algclosed-scalar-extension to A → ℂ and A → F: its isomorphisms of
representation groups, bijections on line characters, and compatibility with induction
transport the integral formula to F, without assuming an embedding F → ℂ. (6) The quotient
comparison in monomialInducedFiniteAlgebraModule identifies these generators with exactly
the stated e_(gh) = χ(h)e_g model. All sums are finite, and coefficients are integers.
(blueprint: lem-per-brauer-monomial-induction) -/
theorem brauer_monomial_induction
    (F : Type u) [Field F] [IsAlgClosed F] [CharZero F]
    (G : Type v) [Group G] [Finite G]
    (x : FiniteModuleSplitGrothendieck.{u, max u v, max u v} F (MonoidAlgebra F G)) :
    ∃ (n : ℕ) (H : Fin n → Subgroup G) (χ : (i : Fin n) → H i →* Fˣ)
      (a : Fin n → ℤ),
      x = ∑ i, a i • QuotientAddGroup.mk
        (FreeAbelianGroup.of (monomialInducedFiniteAlgebraModule F (H i) (χ i))) := by
  sorry

end RepresentationTheory
