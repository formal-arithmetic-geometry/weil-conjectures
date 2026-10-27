module

public import Sheaf.Geometry.Manifold.HermitianDolbeaultData
public import Mathlib.Topology.Algebra.Support

/-!
# Dolbeault differentials and formal adjoints without global integrability

Source: Kong, Notes on Complex Geometry, §§3.1, 6.1 and 6.4, Proposition 6.12
(blueprint: def-sfb-formal-dolbeault-operators).

The forms, metric, volume and integral pairing are the existing coordinate constructions.
Exterior differentiation is normalized in every degree, including degree zero. Adjointness
is tested with a compactly supported first input and an arbitrary smooth second input.
Thus it determines the adjoint on all smooth forms, without global L² assumptions.
-/

@[expose] public section

noncomputable section

universe u

namespace ComplexManifold

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Model n) M]
    [MeasurableSpace M]

/-- Smooth formal adjoint for the actual metric integral pairing. The first input has
compact support, while the second is any smooth form; this determines the adjoint on all
smooth forms rather than just on compactly supported ones.
Source: Kong §6.1, Lemmas 6.1–6.2, localized integration by parts
(blueprint: def-sfb-formal-dolbeault-operators). -/
def IsSmoothFormalAdjoint (g : HermitianMetric n M) (μ : MetricVolume g)
    (D S : smoothForms (n := n) (M := M) →ₗ[ℂ] smoothForms (n := n) (M := M)) : Prop :=
  ∀ α η : smoothForms (n := n) (M := M),
    HasCompactSupport (fun x : M ↦ fun k : ℕ ↦ α.val k x) →
      l2Pair g μ (D α) η = l2Pair g μ α (S η)

/-- A presentation of the type components of exterior differentiation and their smooth
formal adjoints on a possibly noncompact manifold. The bidegrees and coordinate exterior
derivative equations fix the differentials. The compact-test equations fix the adjoints
on arbitrary smooth forms. No differential relation or Kähler identity is assumed.
The degree-zero normalization says that exterior differentiation has no degree-zero output.
Source: Kong §§3.1, 6.1 and 6.4, Proposition 6.12
(blueprint: def-sfb-formal-dolbeault-operators). -/
structure FormalDolbeaultOperators (g : HermitianMetric n M) (μ : MetricVolume g) where
  dbar : smoothForms (n := n) (M := M) →ₗ[ℂ] smoothForms (n := n) (M := M)
  del : smoothForms (n := n) (M := M) →ₗ[ℂ] smoothForms (n := n) (M := M)
  dAdjoint : smoothForms (n := n) (M := M) →ₗ[ℂ] smoothForms (n := n) (M := M)
  dbarAdjoint : smoothForms (n := n) (M := M) →ₗ[ℂ] smoothForms (n := n) (M := M)
  dbar_type : ∀ (p q : ℤ) (α : smoothForms (n := n) (M := M)),
    α ∈ typeForms p q → dbar α ∈ typeForms p (q + 1)
  del_type : ∀ (p q : ℤ) (α : smoothForms (n := n) (M := M)),
    α ∈ typeForms p q → del α ∈ typeForms (p + 1) q
  exterior_zero : ∀ α : smoothForms (n := n) (M := M), ((dbar + del) α).val 0 = 0
  exterior_derivative : ∀ (α : smoothForms (n := n) (M := M)) (k : ℕ)
    (e : OpenPartialHomeomorph M (Model n)), e ∈ atlas (Model n) M →
    ∀ z ∈ e.target,
      formCoordinates ((dbar + del) α).val (k + 1) e z =
        extDerivWithin (formCoordinates α.val k e) e.target z
  formal_dAdjoint : IsSmoothFormalAdjoint g μ (dbar + del) dAdjoint
  formal_dbarAdjoint : IsSmoothFormalAdjoint g μ dbar dbarAdjoint

end ComplexManifold
