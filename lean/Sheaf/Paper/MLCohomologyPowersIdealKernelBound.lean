/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Ideal.Operations
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.Paper.PQFCohomology
import Sheaf.AlgebraicGeometry.CohomologyPowersIdealApplication
import Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives
import Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor

/-! # Cohomology reductions: KernelBound
Source: Stacks Project, Lemma 02OB. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Proof: form the short exact sequence 0 -> J^n F -> F -> F/J^n F -> 0,
where J is the extended ideal. The category of scheme modules has enough injectives;
the long exact sequence identifies the kernel of reduction with the image of
H^p(J^n F) -> H^p(F). Apply cohomology_powers_ideal_application in degree p:
its image bound with target exponent zero gives image contained in I^(n-c) H^p(F)
for n >= c. The transition to J^0 F agrees with inclusion into F, since J^0 F = F.
Restriction of scalars preserves this exactness and the underlying images.
Source: Stacks Project, Cohomology of Schemes, Lemma 02OB,
part (1) (blueprint: ml-cohomology-powers-ideal-kernel-bound). -/
theorem ml_cohomology_powers_ideal_kernel_bound
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (I : Ideal A) (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (p : ℕ) :
    ∃ c : ℕ,
      (∀ n : ℕ, 1 ≤ n → c ≤ n →
        LinearMap.ker (((ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).map
          ((RingedSpace.moduleCohomology X.toRingedSpace p).map
          (formalModuleQuotientπ
            ((Scheme.IdealSheafData.ofIdealTop
              (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap f) n F))).hom) ≤
          I ^ (n - c) • (⊤ : Submodule A
            ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
              ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F)))) := by
  sorry

end AlgebraicGeometry
