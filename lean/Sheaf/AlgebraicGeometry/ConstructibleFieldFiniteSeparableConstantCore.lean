module
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
@[expose] public section
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry Scheme
namespace AlgebraicGeometry
/-- A finite trivializing datum on the spectrum of a field yields the finite separable
extension and constant pullback in the target theorem.
Source: Stacks Project, Lemma 02GL and the proof of Lemma 09Z6.
(blueprint: lem-weil-pbc-constructible-field-finite-separable-constant-step3-7) -/
theorem constructible_field_finite_separable_constant_of_datum
    (k : Type u) [Field k]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (G : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))
    (d : LocallyConstantDatum G)
    (hd : ∀ i : d.cover.I₀,
      ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty ((G.over (d.cover.etalePrecoverageToEtale i)) ≅
          (constantSheaf
            ((Spec (CommRingCat.of k)).smallEtaleTopology.over
              (d.cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} Λ)).obj M)) :
    ∃ (K : Type u), ∃ (_ : Field K), ∃ (_ : Algebra k K),
      FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ (M : ModuleCat.{u + 1} Λ), Finite M ∧
        Nonempty
          ((Etale.upperStar (ModuleCat.{u + 1} Λ)
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G ≅
            (constantSheaf (Spec (CommRingCat.of K)).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)).obj M) := by
  sorry
end AlgebraicGeometry
