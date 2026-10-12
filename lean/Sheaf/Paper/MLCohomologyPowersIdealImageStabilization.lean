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

/-! # Cohomology reductions: ImageStabilization
Source: Stacks Project, Lemma 02OB. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Proof: put J = I O_X and apply cohomology_powers_ideal_application in degree
p+1, obtaining c. The exact sequences of 0 -> J^k F -> F -> F/J^k F -> 0
and 0 -> J^n F -> F -> F/J^n F -> 0 form a natural ladder. Write delta_k for
the connecting map and alpha_(k,n) for H^(p+1)(J^k F) -> H^(p+1)(J^n F).
For x in H^p(F/J^k F), delta_k(x) lies in the kernel of the map to H^(p+1)(F).
The kernel equality of the cited lemma says it maps to zero at exponent k-c.
For k >= n+c, the transition to exponent n factors through exponent k-c, so
alpha_(k,n)(delta_k(x)) = 0. Naturality gives delta_n(tau_(k,n)(x)) = 0,
and exactness places tau_(k,n)(x) in the image of H^p(F). Conversely the quotient
maps satisfy tau_(k,n) rho_k = rho_n, giving the reverse inclusion of images.
This argument uses only positive quotient levels, including n = 1 and c = 0.
Source: Stacks Project, Cohomology of Schemes, Lemma 02OB,
part (3) (blueprint: ml-cohomology-powers-ideal-image-stabilization). -/
theorem ml_cohomology_powers_ideal_image_stabilization
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (I : Ideal A) (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (p : ℕ) :
    ∃ c : ℕ,
      (∀ (n k : ℕ), 1 ≤ n → ∀ h : n + c ≤ k,
        Set.range (((RingedSpace.moduleCohomology X.toRingedSpace p).map
          (formalModuleQuotientMap
            ((Scheme.IdealSheafData.ofIdealTop
              (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap f)
            (𝟙 F) (Nat.le_trans (Nat.le_add_right n c) h))).hom) =
        Set.range (((RingedSpace.moduleCohomology X.toRingedSpace p).map
          (formalModuleQuotientπ
            ((Scheme.IdealSheafData.ofIdealTop
              (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap f) n F)).hom)) := by
  sorry

end AlgebraicGeometry
