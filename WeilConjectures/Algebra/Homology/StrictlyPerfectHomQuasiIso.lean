/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact

/-! # A bounded finite free Hom complex preserves quasi-isomorphisms

## References

* Stacks Project, Tag 08DM
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Hom out of a bounded finite free complex preserves every quasi-isomorphism,
without a boundedness hypothesis on its target. -/
theorem quasiIso_homComplex_map_of_bounded_finiteFree
    (X : RingedSpace.{u})
    (E : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ)
    (hbounded : ∃ N : ℤ, ∀ p : ℤ, N < p → IsZero (E.X p))
    (hbelow : ∃ M : ℤ, ∀ p : ℤ, p < M → IsZero (E.X p))
    (hfree : ∀ p : ℤ, ∃ r : ℕ, Nonempty (E.X p ≅
      SheafOfModules.free (R := moduleRings X) (ULift.{u} (Fin r))))
    {G I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ}
    (s : G ⟶ I) [QuasiIso s] :
    QuasiIso (((homComplexFunctor (R := X.sheaf)).obj (op E)).map s) := by
  obtain ⟨N, hN⟩ := hbounded
  obtain ⟨M, hM⟩ := hbelow
  apply quasiIso_homComplex_map_of_bounded_exact_terms
    (Opens.grothendieckTopology X) X.sheaf E
  · refine ⟨M, N, ?_⟩
    intro p hp
    rcases hp with hp | hp
    · exact hM p hp
    · exact hN p hp
  · intro p S hS
    obtain ⟨r, ⟨e⟩⟩ := hfree p
    obtain ⟨hz, hHom, _⟩ :=
      SheafOfModules.finiteFreeInternalHomExact (R := X.sheaf) r (E.X p) e S hS
    exact ⟨hz, hHom⟩

end AlgebraicGeometry
