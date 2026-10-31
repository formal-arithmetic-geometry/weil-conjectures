/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClassicalWeilFiltrationTransportData
import WeilConjectures.AlgebraicGeometry.ClassicalRealizationLocalSpectrum

/-! # Punctual purity of a normalized classical realization

Source: blueprint latest, real-mixed-by-curves, paragraph 1; BS Section 6.8.
(blueprint: lem-zl-classical-realization-punctual-purity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]
  [hUnits : Fact (∀ x : (D.geometricFiber Y₀).left,
    IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x))]

/-- Punctual purity agrees for a single classical object and its normalized
realization, independently of any filtration or finite diagram representative.
Source: blueprint latest, real-mixed-by-curves, paragraph 1; Weil II (1.2.6);
BS 6.8.4(1),(4), 6.8.15
(blueprint: lem-zl-classical-realization-punctual-purity).

Proof:
1. Apply zl_classical_realization_local_spectrum to the given R and F at every
closed-point lift. In the forward direction its equivalence takes a classical
eigenvalue for the supplied normalized beta to SfPunctualEigenvalue; apply sf purity.
2. Conversely unpack the finite coefficient field, Weil representative, isomorphism,
residue embedding and eigenvalue witnessing SfPunctualEigenvalue. The same spectrum
lemma supplies a normalized beta. Its equivalence takes the sf eigenvalue to the
classical one, and classical purity gives the required norm equation. Both sides
use the identical closed point, residue cardinality and eigenvalue. Zero fibres
and an empty set of closed points require no additional argument. -/
theorem zl_classical_realization_punctual_purity
    (R : ZlClassicalRealization D l hl Ω Y₀) (F : ZlClassicalWeil D l Ω Y₀)
    (iota : Ω ≃+* ℂ) (w : ℝ) :
    SfIsPunctuallyPureOfWeight D l hl Ω Y₀ iota.toRingHom
        ((R.weil D l hl Ω Y₀).obj F) w ↔
      ZlClassicalPure D l Ω Y₀ iota.toRingHom F w := by
  constructor
  · intro hp y ι hι β hβ α hα
    have hs := zl_classical_realization_local_spectrum D l hl Ω Y₀ R F y ι hι
    exact hp y α ((hs.2 β hβ α).mpr hα)
  · intro hp y α hα
    obtain ⟨E, K, e, ι, hι, hK⟩ := hα
    obtain ⟨⟨β, hβ⟩, hs⟩ :=
      zl_classical_realization_local_spectrum D l hl Ω Y₀ R F y ι hι
    exact hp y ι hι β hβ α ((hs β hβ α).mp ⟨E, K, e, ι, hι, hK⟩)

end WeilConjectures
