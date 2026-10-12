module

public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Finite affine free covers can be chosen with zero cokernel.

Proof plan (from Stacks Project, Tag 095N): represent the finitely many elements of each
finite geometric stalk by sections on pointed affine etale neighbourhoods, and map the
corresponding sheafified free modules to `F`.  The cokernel of each finite family is
constructible; its support is constructible, and enlarging a family shrinks that support.
Every point is omitted by one family.  Quasi-compactness of the constructible topology
gives finitely many families with empty intersection of supports.  Their concatenation has
zero geometric stalks in its cokernel, and conservativity of geometric stalks makes that
cokernel a zero object.
(blueprint: lem-weil-pbc-constructible-module-finite-zero-cokernel) -/
theorem exists_affine_free_etale_zero_cokernel
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    let P : X.Etale → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun W =>
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
    ∃ (n : ℕ) (U : Fin n → X.Etale), (∀ i, IsAffine (U i).left) ∧
      ∃ g : (∐ fun i : Fin n => P (U i)) ⟶ F,
        Nonempty (IsZero (cokernel g)) := by sorry


end AlgebraicGeometry.Scheme
