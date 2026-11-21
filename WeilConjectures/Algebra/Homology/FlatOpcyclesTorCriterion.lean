/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Algebra.FlatTorIdealCriterion
import WeilConjectures.CategoryTheory.OpcyclesTorSurjection
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-!
# Flatness of opcycles from exactness after tensoring

## References

* Stacks Project, More on Algebra, Lemma 15.59.2 (Tag 0653)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace Module.Flat

/-- For a complex of flat modules, if tensoring with every module is exact in degree `a - 1`,
then its degree-`a` opcycles are flat. -/
theorem opcycles_of_exactAt {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat R) ℤ) (a : ℤ)
    (hflat : ∀ i : ℤ, Module.Flat R (P.X i))
    (hexact : ∀ N : ModuleCat R,
      (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1)) :
    Module.Flat R (P.opcycles a) := by
  rw [CategoryTheory.flat_iff_tor_one_quotient_ideal]
  intro I
  obtain ⟨τ, hτ⟩ := CategoryTheory.exists_epi_homology_tensor_to_tor_opcycles R P a hflat
  let N := ModuleCat.of R (R ⧸ I)
  have : Epi (τ.app N) := hτ N
  apply Limits.IsZero.of_epi (τ.app N)
  exact ((hexact N).of_iso
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (ModuleCat R)) N P).symm).isZero_homology

end Module.Flat
