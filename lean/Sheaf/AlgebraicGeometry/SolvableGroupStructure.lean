module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Perfect

/-! # Structure terminology for solvable algebraic groups

Source: Milne, Algebraic Groups, Chapters 1, 5, 14 and 16
(blueprint: def-sfb-solvable-group-structure).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.SolvableGroupStructure

/-- Affine algebraic groups have affine underlying schemes and finite type structure maps.
Source: Milne, Chapter 1 (blueprint: def-sfb-solvable-group-structure). -/
def IsAlgebraic {k : Type u} [Field k] (G : Grp (Over (Spec (.of k)))) : Prop :=
  IsAffine G.X.left ∧ LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom

/-- Scalar extension of a group scheme, with the transported group structure. This is the
recorded `MultiplicativeType.baseChange` of def-sfb-tori-multiplicative-type, not a second
definition. Source: Milne, Section 1 (blueprint: def-sfb-solvable-group-structure). -/
noncomputable abbrev extend {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K] :
    Grp (Over (Spec (.of k))) ⥤ Grp (Over (Spec (.of K))) :=
  MultiplicativeType.baseChange

/-- A torus becomes a finite product of G_m after algebraic closure. This is the recorded
`MultiplicativeType.IsTorus` of def-sfb-tori-multiplicative-type, not a second definition.
Source: Milne, Chapter 12 (blueprint: def-sfb-solvable-group-structure). -/
abbrev IsTorus {k : Type u} [Field k] (G : Grp (Over (Spec (.of k)))) : Prop :=
  MultiplicativeType.IsTorus G

/-- Smooth geometric matrix unipotence in a faithful finite-dimensional representation.
The closed immersion expresses faithfulness scheme-theoretically.
Source: Milne, Corollary 14.12 (blueprint: def-sfb-solvable-group-structure). -/
def IsUnipotent {k : Type u} [Field k] (G : Grp (Over (Spec (.of k)))) : Prop :=
  Smooth G.X.hom ∧ ∃ (n : ℕ) (r : G.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k),
    IsClosedSubgroupScheme r ∧
    ∀ (F : Type u) [Field F] [Algebra k F] [IsAlgClosed F]
      (x : (Spec (.of F)).asOver (Spec (.of k)) ⟶ G.X),
      ∃ N : ℕ, 0 < N ∧
        ((GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k F (x ≫ r)).val - 1) ^ N = 0

/-- Solvability is a finite closed subnormal series from G to the trivial group.
Commutativity of each group-scheme quotient is expressed by factorization of all
commutators, on all test algebras, through the next closed normal subgroup.
Source: Milne, Section 6 and Chapter 16 (blueprint: def-sfb-solvable-group-structure). -/
def IsSolvable {k : Type u} [Field k] (G : Grp (Over (Spec (.of k)))) : Prop :=
  ∃ (n : ℕ) (S : Fin (n + 1) → Grp (Over (Spec (.of k)))),
    Nonempty (S 0 ≅ G) ∧ Nonempty (S (Fin.last n) ≅ Grp.trivial _) ∧
    ∀ a : Fin n, ∃ j : (S a.succ).X ⟶ (S a.castSucc).X,
      IsClosedSubgroupScheme j ∧ IsNormalSubgroupScheme j ∧
      ∀ (R : Type u) [CommRing R] [Algebra k R]
        (x y : (Spec (.of R)).asOver (Spec (.of k)) ⟶ (S a.castSucc).X),
        ∃ z : (Spec (.of R)).asOver (Spec (.of k)) ⟶ (S a.succ).X,
          z ≫ j = x * y * x⁻¹ * y⁻¹

/-- A represented fppf quotient: q is an fppf cover and i identifies its kernel.
These conditions identify its represented sheaf with the fppf sheafification of
A ↦ H(A)/U(A): locally lift along q; two lifts differ by a unique kernel point.
Source: Milne, Chapter 5 (blueprint: def-sfb-solvable-group-structure). -/
def IsFppfQuotient {k : Type u} [Field k]
    {U H Q : Grp (Over (Spec (.of k)))} (i : U.X ⟶ H.X) (q : H ⟶ Q) : Prop :=
  Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
    LocallyOfFinitePresentation q.hom.hom.left ∧
    ∃ e : U.X ≅ CategoryTheory.GrpObj.ker q.hom.hom,
      e.hom ≫ CategoryTheory.GrpObj.kerι q.hom.hom = i

end AlgebraicGeometry.SolvableGroupStructure
