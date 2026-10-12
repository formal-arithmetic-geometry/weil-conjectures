module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The empty-index case of dense-open component modification gluing.
The component-cover hypothesis forces the target to be empty; the empty open is dense
and the empty coproduct map is an isomorphism.
(blueprint: lem-weil-pbc-dense-open-component-modifications-empty) -/
theorem exists_dense_open_isIso_component_modifications_of_zero
    (X : Scheme.{u}) [IsReduced X]
    (C : Fin 0 → Scheme.{u}) (ι : ∀ i, C i ⟶ X)
    (hC : ∀ i, IsIntegral (C i) ∧ IsClosedImmersion (ι i) ∧
      Set.range (ι i) ∈ irreducibleComponents X)
    (hinj : Function.Injective (fun i => Set.range (ι i)))
    (hcover : ∀ Z ∈ irreducibleComponents X, ∃ i, Set.range (ι i) = Z)
    (Y : Fin 0 → Scheme.{u}) (ν : ∀ i, Y i ⟶ C i)
    (hν : ∀ i, ∃ U : (C i).Opens, Dense (U : Set (C i)) ∧ IsIso (ν i ∣_ U)) :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      IsIso (CategoryTheory.Limits.Sigma.desc (fun i => ν i ≫ ι i) ∣_ U) := by
  sorry

end AlgebraicGeometry
