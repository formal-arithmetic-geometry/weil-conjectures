module

public import WeilConjectures.AlgebraicGeometry.Curve

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Geometric data for a zero-dimensional base change, independently of any sheaf.
Source: Stacks Project, Tags 00KH, 00FV and 01JT; the point description in
lem-weil-pbc-zero-dimensional-base-change-points.
(blueprint: lem-weil-pbc-zero-dimensional-base-change-geometric-points).

Proof: Nullstellensatz identifies every residue field of C with k. The local
Artinian pieces remain local Artinian after extending to k', with residue field k'.
Thus projection induces a bijection on points, and C' has dimension at most zero.
Finite type and separatedness are stable under base change, giving IsCurve f'.
At each point of C', the canonical residue-field morphism Spec k' → C' gives the
chosen geometric point. For the empty scheme the equivalence and family are empty.
An arbitrary cartesian square is isomorphic to the canonical fibre product, so
transport these constructions across that isomorphism. -/
theorem zeroDimensional_baseChange_geometric_points {k k' : Type u}
    [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] {C C' : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f] (hC : topologicalKrullDim C ≤ 0)
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) :
    IsCurve f' ∧ topologicalKrullDim C' ≤ 0 ∧
      ∃ b : C' ≃ C, (∀ c', b c' = ι' c') ∧
        ∃ s : C' → (Spec (.of k') ⟶ C'), ∀ c', s c' default = c' := by
  sorry

end AlgebraicGeometry
