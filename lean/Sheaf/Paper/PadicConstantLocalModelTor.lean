/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4 -/
module

public import Sheaf.Paper.ConstantModelTorAmplitude
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension

/-! # Tor intervals for finite constant p-adic scalar models -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Finite constant local models have a uniform scalar Tor interval, on every scheme.

Source: blueprint main-20261015, localizing-closure ctf-equals-bc proof,
Local models and Locality paragraphs
(blueprint: lem-sfb-padic-constant-local-model-tor).

Proof: evaluate coefficients at the point. Constant functions identify the scalar ring
with the indicated DVR or field, including the finite-subextension-valued algebraic
closure. On a cover exhibiting the finite constant model, write its finitely presented
scalar module as the cokernel of a finite scalar matrix. Over a DVR choose a finite
free basis of the kernel of a finite free presentation; over a field choose a finite
basis of the module itself. The constant-to-continuous scalar map is flat for the DVR:
continuous functions with values in the torsion-free DVR are torsion-free, and modules
over a PID are flat. Constant sheafification and the monoidal inverse image are exact.
Consequently the scalar resolution gives a resolution of the local model by finite
free coefficient modules, in degrees -1 and 0, or just degree 0 in the field case.
These bounded flat resolutions compute derived tensor with every test module and
remain concentrated in the same interval. Exact restriction to the trivializing
pro-etale cover commutes with derived tensor; joint conservativity of restriction
therefore gives the same interval before restriction. Transport along the coefficient
isomorphism using exact monoidal scalar restriction. Empty covers and rank zero are
included. No compactness or Noetherian assumption on the scheme is required. -/
theorem padic_constant_local_model_tor
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (c : ℤ)
    (hΛ :
      (c = -1 ∧ (Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
        ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E)))) ∨
      (c = 0 ∧ (Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
        (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))))
    (S : Scheme.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (hN : HasFiniteConstantLocalModel Λ S N) :
    _root_.DerivedCategory.torAmplitudeIn _ c 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj N) := by sorry

end AlgebraicGeometry.ProEtale
