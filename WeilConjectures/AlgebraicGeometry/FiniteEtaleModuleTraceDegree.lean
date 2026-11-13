/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Linear.FunctorCategory
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceExists
import WeilConjectures.AlgebraicGeometry.DirectImageSplitCoverProduct
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleModuleTraceData

/-!
# Coefficient-linear finite étale trace with prescribed degree

## References

* Stacks Project, Section 03SH, Definition 03SE.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A finite étale map with geometric fibres of cardinality `d` admits a coefficient-linear
trace whose composite with restriction is `d` times the identity. No invertibility of `d`
is assumed, and the coefficients may be any commutative ring.
(Stacks, Section 03SH, Definition 03SE.) -/
theorem exists_finiteEtaleModuleTrace_degree
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (d : ℕ)
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nat.card (f.GeometricFiber s) = d) :
    ∃ t : (f)_*[ModuleCat.{u + 1} R].obj ((f)^*[ModuleCat.{u + 1} R].obj G) ⟶ G,
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G ≫ t =
        (d : R) • 𝟙 G := by
  obtain ⟨h, _⟩ := finiteEtaleModuleTraceData R f G d hdeg
  exact h

end AlgebraicGeometry.Etale
