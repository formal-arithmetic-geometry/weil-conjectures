/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.AdicCoefficientDatumCompleted
public import Sheaf.Paper.EtaleOriginWitness
public import Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived

/-!
# Finite proper base change with canonical ring-sheaf coefficients

Source: blueprint theorem 1325; Stacks Project, Pro-etale Cohomology, Section 09C8,
and the finite etale-origin step of Theorem 09C9
(blueprint: thm-weil-pbc-finite-level-proetale).
This is the recorded finite theorem in the normalized ring-sheaf presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable (Λ : Type (t + 1)) [CommRing Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- Coefficient transport along the existing normalized constants-to-functions isomorphism.
Source: Stacks 09C8 (blueprint: thm-weil-pbc-finite-level-proetale). -/
def finiteOriginRestriction (T : Scheme.{t}) :=
  SheafOfModules.restrictScalars.{t + 1} (adicDatumFiniteCoefficientIso T Λ).hom

/-- Additivity of scalar restriction, inherited from the recorded restriction functor.
Source: Stacks 03D3 (blueprint: thm-weil-pbc-finite-level-proetale). -/
instance finiteOriginRestriction_additive (T : Scheme.{t}) :
    (finiteOriginRestriction Λ T).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars.{t + 1}
    (adicDatumFiniteCoefficientIso T Λ).hom).Additive

/-- The normalized coefficient transport preserves kernels and cokernels.
Source: Stacks 03D3, 09C8 (blueprint: thm-weil-pbc-finite-level-proetale).
Proof: scalar restriction changes only the action, leaving the underlying abelian
sheaf and its kernels and sheafified cokernels unchanged. Their universal maps remain
linear. Since the ring map is an isomorphism, this is an equivalence as well. -/
theorem finiteOriginRestriction_exact (T : Scheme.{t}) :
    PreservesFiniteLimits (finiteOriginRestriction Λ T) ∧
      PreservesFiniteColimits (finiteOriginRestriction Λ T) := by
  sorry

/-- Left exactness of the recorded coefficient equivalence.
Source: Stacks 09C8 (blueprint: thm-weil-pbc-finite-level-proetale). -/
instance finiteOriginRestriction_limits (T : Scheme.{t}) :
    PreservesFiniteLimits (finiteOriginRestriction Λ T) :=
  (finiteOriginRestriction_exact Λ T).1

/-- Right exactness of the recorded coefficient equivalence.
Source: Stacks 09C8 (blueprint: thm-weil-pbc-finite-level-proetale). -/
instance finiteOriginRestriction_colimits (T : Scheme.{t}) :
    PreservesFiniteColimits (finiteOriginRestriction Λ T) :=
  (finiteOriginRestriction_exact Λ T).2

/-- The canonical exact transport on the ordinary unbounded derived categories.
Source: Stacks 09C8 (blueprint: thm-weil-pbc-finite-level-proetale). -/
def finiteOriginTransport (T : Scheme.{t}) :=
  (finiteOriginRestriction Λ T).mapDerivedCategory

/-- Canonical pullback of finite constant coefficients, normalized by constant sections.
Source: Stacks 098T, 09C8 (blueprint: thm-weil-pbc-finite-level-proetale). -/
def finiteConstantCoefficientIso {U V : Scheme.{t}} (f : U ⟶ V) :
    (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj (adicLisseConstantRing V Λ) ≅
      adicLisseConstantRing U Λ :=
  letI : ∀ n : ℕᵒᵖ,
      Finite (((Functor.const ℕᵒᵖ).obj (CommRingCat.of Λ)).obj n) :=
    fun _ ↦ inferInstanceAs (Finite Λ)
  @asIso _ _ _ _ ((proEtaleConstantComparison f).app (CommRingCat.of Λ))
    ((proEtale_profinite_coefficient_inverse_image
      ((Functor.const ℕᵒᵖ).obj (CommRingCat.of Λ))).1 U V f (op 0))

variable {X' X Y' Y : Scheme.{t}}
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Constant coefficient identifications agree around a commutative scheme square.
Source: Stacks 07A7, 09C8 (blueprint: thm-weil-pbc-finite-level-proetale).
Proof: apply the finite composition clause of profinite-coefficient-inverse-image to
the constant tower with value Λ. The two composites are its canonical comparison for
the composite scheme arrow. Transport across the square commutativity identifies them. -/
theorem finiteConstantCoefficients_comm (sq : ChosenCartesianSquare g' f' f g) :
    HEq (proEtaleRingCompositeCoefficients g' f (adicLisseConstantRing Y Λ)
      (adicLisseConstantRing X Λ) (adicLisseConstantRing X' Λ)
      (finiteConstantCoefficientIso Λ f) (finiteConstantCoefficientIso Λ g'))
      (proEtaleRingCompositeCoefficients f' g (adicLisseConstantRing Y Λ)
        (adicLisseConstantRing Y' Λ) (adicLisseConstantRing X' Λ)
        (finiteConstantCoefficientIso Λ g) (finiteConstantCoefficientIso Λ f')) := by
  sorry

/-- The witness-independent finite exchange is the actual ringed adjunction mate.
Source: Stacks 07A7, 09C8 (blueprint: thm-weil-pbc-finite-level-proetale). -/
def finiteConstantRingedExchange (sq : ChosenCartesianSquare g' f' f g) :=
  proEtaleAmbientRingedExchange sq (adicLisseConstantRing X Λ) (adicLisseConstantRing Y Λ)
    (adicLisseConstantRing X' Λ) (adicLisseConstantRing Y' Λ)
    (finiteConstantCoefficientIso Λ f) (finiteConstantCoefficientIso Λ g)
    (finiteConstantCoefficientIso Λ g') (finiteConstantCoefficientIso Λ f')
    (finiteConstantCoefficients_comm Λ sq)

/-- Finite proper base change for the exact ringed exchange, on a bounded-below object
with its specified etale-origin witness. The normalized coefficient transport merely
identifies two presentations of the same module sheaves. The forward map has no witness
argument, which gives independence under replacement by an isomorphic witness.
Source: Stacks 09C8 and the finite etale-origin step of 09C9
(blueprint: thm-weil-pbc-finite-level-proetale).
Proof, following the node:
1. Under the normalized coefficient identifications, module pullback is exact sheaf
inverse image, since its scalar extension is along an isomorphism. Its descended
functor is therefore the derived inverse image used in the displayed ringed exchange.
2. The etale antecedent w.L is bounded below and its cohomology is torsion because Λ
is finite. Apply thm-weil-pbc-bounded-below to its etale proper-base-change map.
3. The fully faithful derived site comparison of thm-weil-pbc-site-comparison
transports that isomorphism to the pro-etale site. The adjunction calculation of
lem-weil-pbc-transport-identifies-exchange identifies the transported map with the
canonical ringed exchange; the normalized constants-to-functions comparison preserves
the units and counits that define this mate.
4. Conjugate by w.alpha. Naturality gives the component at W, and the coefficient
transport gives the displayed component. Both transports preserve isomorphisms.
5. The transformation is defined without W's origin witness; replacing w changes
only the certificate of invertibility, so the same forward map is obtained. -/
theorem finiteConstantRingedExchange_isIso [IsProper f]
    (sq : ChosenCartesianSquare g' f' f g)
    (W : ProEtale.FiniteCoefficientDerivedCategoryPlus X Λ)
    (w : ProEtale.EtaleOriginWitness X Λ W) :
    IsIso ((finiteConstantRingedExchange Λ sq).app ((finiteOriginTransport Λ X).obj W.obj)) := by
  sorry

end AlgebraicGeometry.Scheme
