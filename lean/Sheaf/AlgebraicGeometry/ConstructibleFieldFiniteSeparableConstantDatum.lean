module
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
@[expose] public section
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry Scheme
namespace AlgebraicGeometry
/-- Extraction of a finite trivializing datum over the spectrum of a field.
Source: Stacks Project, Definition 03RU and the proof of Lemma 09Z6.
(blueprint: lem-weil-pbc-constructible-field-finite-separable-constant-step1) -/
theorem constructible_field_finite_separable_constant_datum
    (k : Type u) [Field k]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (G : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))
    (hG : Scheme.IsConstructibleEtaleModuleSheaf G) :
    ∃ d : LocallyConstantDatum G, ∀ i : d.cover.I₀,
      ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty ((G.over (d.cover.etalePrecoverageToEtale i)) ≅
          (constantSheaf
            ((Spec (CommRingCat.of k)).smallEtaleTopology.over
              (d.cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} Λ)).obj M) := by
  sorry
end AlgebraicGeometry
