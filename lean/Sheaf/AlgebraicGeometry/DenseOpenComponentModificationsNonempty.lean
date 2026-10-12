module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Dense-open component modification gluing for a nonempty finite family.
The proof follows the componentwise construction in the parent theorem: remove all
other components, restrict each dense isomorphism, and glue the resulting local
isomorphisms.
(blueprint: lem-weil-pbc-dense-open-component-modifications-nonempty) -/
 theorem exists_dense_open_isIso_component_modifications_of_pos
    (X : Scheme.{u}) [IsReduced X]
    (n : ℕ) (hn : 0 < n) (C : Fin n → Scheme.{u}) (ι : ∀ i, C i ⟶ X)
    (hC : ∀ i, IsIntegral (C i) ∧ IsClosedImmersion (ι i) ∧
      Set.range (ι i) ∈ irreducibleComponents X)
    (hinj : Function.Injective (fun i => Set.range (ι i)))
    (hcover : ∀ Z ∈ irreducibleComponents X, ∃ i, Set.range (ι i) = Z)
    (Y : Fin n → Scheme.{u}) (ν : ∀ i, Y i ⟶ C i)
    (hν : ∀ i, ∃ U : (C i).Opens, Dense (U : Set (C i)) ∧ IsIso (ν i ∣_ U)) :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      IsIso (CategoryTheory.Limits.Sigma.desc (fun i => ν i ≫ ι i) ∣_ U) := by
  sorry

end AlgebraicGeometry
