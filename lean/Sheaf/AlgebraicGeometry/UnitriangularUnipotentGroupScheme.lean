module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

/-! # Unitriangular unipotence without a smoothness hypothesis

Source: Milne, Algebraic Groups (2017), Theorem 14.5(a),(b), pp.281--282
(blueprint: def-sfb-unitriangular-unipotent-group-scheme).

A closed embedding in GL_n satisfying the unitriangular equations on all algebras
is exactly a closed embedding in its closed unitriangular subgroup U_n.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A group scheme is unipotent if it embeds as a closed group subscheme in U_n
for some positive n. The equations are tested on every algebra, not only on fields.
A map to GL_n satisfying them factors through its closed subscheme defined by
x_aa - 1 and x_ab for b < a, and the factored map remains a closed immersion.
Source: Milne, Theorem 14.5(a),(b), pp.281--282
(blueprint: def-sfb-unitriangular-unipotent-group-scheme). -/
def IsUnitriangularUnipotentGroupScheme {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k)))) : Prop :=
  ∃ n : ℕ, 0 < n ∧
    ∃ r : G.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k,
      IsClosedSubgroupScheme r ∧
      ∀ (A : Type u) [CommRing A] [Algebra k A]
        (x : (Spec (.of A)).asOver (Spec (.of k)) ⟶ G.X),
        (∀ a : Fin n,
          (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (x ≫ r)).val
            ⟨a⟩ ⟨a⟩ = 1) ∧
        ∀ a b : Fin n, b < a →
          (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (x ≫ r)).val
            ⟨a⟩ ⟨b⟩ = 0

end AlgebraicGeometry
