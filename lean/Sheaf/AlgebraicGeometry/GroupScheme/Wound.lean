module

public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import Mathlib.Topology.Connected.Basic

/-! # Wound unipotent groups

Source: Conrad, The structure of solvable groups over general fields (2014),
Definition 2.1, printed p.10 (blueprint: def-sfb-wound-unipotent-group).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-- A smooth connected unipotent affine algebraic group is wound if every scheme map
from the affine line is constant at a rational point. No homomorphism condition is
imposed on the test map. Source: Conrad, Definition 2.1, printed p.10
(blueprint: def-sfb-wound-unipotent-group). -/
def IsWoundGroup {k : Type u} [Field k] (G : Grp (Over (Spec (.of k)))) : Prop :=
  SolvableGroupStructure.IsAlgebraic G ∧
    SolvableGroupStructure.IsUnipotent G ∧ ConnectedSpace G.X.left ∧
    ∀ f : StandardGroupSchemes.additive k ⟶ G.X,
      ∃ c : 𝟙_ (Over (Spec (.of k))) ⟶ G.X,
        f = toUnit (StandardGroupSchemes.additive k) ≫ c

end AlgebraicGeometry
