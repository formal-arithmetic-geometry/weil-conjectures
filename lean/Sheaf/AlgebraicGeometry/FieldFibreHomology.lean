module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback to a field preserves the specified single cohomology condition.
Source: blueprint lem-pc-perfect-locus, proof step 4.
(blueprint: new-field-fibre-homology). -/
theorem single_field_fibre_homology
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (i r : ℕ) (hzero : ∀ q : ℕ, q ≠ i → IsZero (P.homology q))
    (hrank : (P.homology i).IsFiniteLocallyFreeOfRank r)
    {R : CommRingCat.{u}} (hR : IsField R) (f : Spec R ⟶ Y) :
      let Q := ((Modules.pullback f).mapHomologicalComplex _).obj P
      (∀ q : ℕ, q ≠ i → IsZero (Q.homology q)) ∧
        (Q.homology i).IsFiniteLocallyFreeOfRank r := by
  sorry

end AlgebraicGeometry.Scheme.Modules
