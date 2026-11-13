/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.ConstructibleFieldFiniteSeparableConstantDatum
import WeilConjectures.AlgebraicGeometry.ConstructibleFieldFiniteSeparableConstantCore

/-!
# Constructible sheaves over a field become constant after finite separable extension

## References

* Stacks Project, Tag 09Z6 and Tag 03RU
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry

/-- A constructible sheaf of modules on the spectrum of a field becomes constant after
finite separable extension. (Stacks, Tag 09Z6, Tag 03RU and Tag 02GL) -/
theorem constructible_field_finite_separable_constant
    (k : Type u) [Field k]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (G : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))
    (hG : Scheme.IsConstructibleEtaleModuleSheaf G) :
    ∃ (K : Type u), ∃ (_ : Field K), ∃ (_ : Algebra k K),
      FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ (M : ModuleCat.{u + 1} Λ), Finite M ∧
        Nonempty
          ((Etale.upperStar (ModuleCat.{u + 1} Λ)
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G ≅
            (constantSheaf (Spec (CommRingCat.of K)).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)).obj M) := by
  obtain ⟨d, hd⟩ := constructible_field_finite_separable_constant_datum k Λ G hG
  exact constructible_field_finite_separable_constant_of_datum k Λ G d hd

end AlgebraicGeometry
