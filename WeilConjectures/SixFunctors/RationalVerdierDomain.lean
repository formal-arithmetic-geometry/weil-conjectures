/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DetThmSfCtfStabilityInternalHom
public import WeilConjectures.Topology.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.LocalizingClosureCtfEqualsBc

/-! # The domain of condensed rational Verdier duality

Source: current blueprint thm-coef-rational-verdier, proof paragraph 3;
det-def-localizing-closure-ctf-equals-bc, nonfinite coefficient cases.
(blueprint: lem-coef-rational-verdier-condensed-domain).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures

/-- Bounded constructible complexes over an actual condensed finite coefficient
field have finite Tor amplitude, so the domain restriction loses no objects.
Source: current blueprint rational Verdier duality, proof paragraph 3.
(blueprint: lem-coef-rational-verdier-condensed-domain).

Proof: specialize the nonfinite-coefficient Tor theorem to the continuous-function
ring of E, with its identity coefficient isomorphism. Its third assertion identifies
the intersection of bounded constructibility and finite Tor amplitude with bounded
constructibility itself. This intersection is exactly dctfPred. The proof includes
the empty scheme and the bottom finite intermediate field. -/
theorem coef_rational_verdier_domain (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1)))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    CondensedRing.dctfPred Λ X = constantModelBoundedConstructible Λ X := by
  have h := localizingClosure_ctf_equals_bc l X Λ
    (Or.inr (Or.inr (Or.inl ⟨E, Or.inr hΛ⟩)))
  exact h.1.2.2.1

end WeilConjectures
