module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Rational parabolic subgroups

Source: Milne, Algebraic Groups (2017), Definition 17.15, printed p.356,
and Chapter 25(a), printed pp.544--546.
(blueprint: def-sfb-rational-parabolic-subgroup)

The quotient is specified by an fppf projection and its right-coset fibres on all
schemes. These conditions identify its represented sheaf with the fppf sheafification
of the right-coset presheaf: the projection locally lifts every section, and two lifts
have the same image precisely when their ratio belongs to the subgroup.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- A rational parabolic is smooth, geometrically connected and closed, with proper
represented fppf right-coset quotient. Properness includes finite type. The flat,
surjective, locally finitely presented projection supplies fppf local lifts, and the
last clause is the right-coset relation, including on nonreduced test schemes.
Source: Milne, Definition 17.15, p.356, and Chapter 25(a), pp.544--546.
(blueprint: def-sfb-rational-parabolic-subgroup) -/
def IsParabolicGroupScheme {k : Type u} [Field k]
    {P G : Grp (Over (Spec (.of k)))} (i : P ⟶ G) : Prop :=
  IsClosedSubgroupScheme i.hom.hom ∧ Smooth P.X.hom ∧
    ConnectedSpace ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj P).X.left ∧
    ∃ (Q : Over (Spec (.of k))) (q : G.X ⟶ Q),
      IsProper Q.hom ∧ Flat q.left ∧ Surjective q.left ∧
      LocallyOfFinitePresentation q.left ∧
      ∀ (T : Over (Spec (.of k))) (a b : T ⟶ G.X),
        a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ Set.range (fun p : T ⟶ P.X ↦ p ≫ i.hom.hom)

/-- A minimal rational parabolic has no strictly smaller rational parabolic subgroup.
It may be the whole group. Source: Milne, Theorems 25.6 and 25.8, pp.545--546,
with the author's p.545 erratum.
(blueprint: def-sfb-rational-parabolic-subgroup) -/
def IsMinimalParabolicGroupScheme {k : Type u} [Field k]
    {P G : Grp (Over (Spec (.of k)))} (i : P ⟶ G) : Prop :=
  IsParabolicGroupScheme i ∧
    ∀ (Q : Grp (Over (Spec (.of k)))) (j : Q ⟶ P),
      IsClosedSubgroupScheme j.hom.hom → IsParabolicGroupScheme (j ≫ i) → IsIso j

end AlgebraicGeometry
