/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefTowerTraceData

/-! The ordinary constant-section calculation for coefficient quotients. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u})

/-- On ordinary coefficient sheaves the lax scalar unit sends a constant section
of A_m to its quotient in A_n, after the specified restriction compositor.
Source: blueprint prop-coef-integral-dualizing, proof paragraph 2, regular scalar unit.
Proof: expand the ordinary unit-sections isomorphisms. The monoidal restriction
unit on presheaves is the coefficient ring homomorphism. The constant/scalar
comparison sends each sheafification generator to the same generator with the
restricted scalar action. Evaluate at the terminal etale object, use naturality
of the constant-sheaf adjunction unit, and cancel that unit isomorphism. On an
arbitrary lifted residue class the remaining equality is the definition of
finiteDualizingQuotient, so this includes equal levels and nonflat quotients.
There are no derived-category comparisons in this statement.
(blueprint: new-lem-coef-trace-ordinary-quotient) -/
theorem coefTraceOrdinaryQuotient {m n : ℕ} (h : n ≤ m) :
    ((sheafSections (Spec (.of D.k)).smallEtaleTopology
      (ModuleCat.{u + 1} (coefTraceRing l E))).obj (op (etalePoint D.k))).map
        ((Sheaf.restrictScalars (Spec (.of D.k)).smallEtaleTopology
            (coefTraceQuotient l E m)).map
          (Functor.LaxMonoidal.ε (Sheaf.restrictScalars
            (Spec (.of D.k)).smallEtaleTopology (finiteDualizingQuotient l E h))) ≫
          (Sheaf.restrictScalarsCompIso (Spec (.of D.k)).smallEtaleTopology
            (coefTraceQuotient l E m) (finiteDualizingQuotient l E h)
            (coefTraceQuotient l E n) (coefTraceQuotient_comp l E h)).hom.app (𝟙_ _)) ≫
      (coefTraceUnitSectionsIso l E D n).hom =
    (coefTraceUnitSectionsIso l E D m).hom ≫ coefTraceQuotientMap l E h := by
  sorry

end WeilConjectures
