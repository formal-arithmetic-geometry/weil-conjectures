/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude

import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.AlgebraicGeometry.PerfectLocalModelBoundedConstructible
import WeilConjectures.AlgebraicGeometry.PerfectLocalModelFiniteTorAmplitude

/-! # Locally perfect scalar models have bounded constructible cohomology and finite Tor amplitude

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, paragraph (2), local models
(blueprint: lem-sfb-perfect-local-model-ctf).
- quasicompactness gives a finite refinement and uniform bounds;
- exact scalar realization gives finitely presented constant cohomology models;
- bounded flat local models give a uniform Tor interval.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A locally perfect scalar model over an admissible commutative condensed ring on a
Noetherian scheme is bounded with constant-model constructible cohomology and has finite
Tor amplitude over the pulled-back ring. The ambient category is the ordinary unbounded
derived category of internal modules.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (2), local models
(blueprint: lem-sfb-perfect-local-model-ctf).

Proof in words:
1. Choose the cover and bounded finite-projective scalar complexes supplied by
   def-sfb-locally-perfect-scalar-model. Mapping each complex through scalar realization
   preserves its strict lower and upper bounds.
2. Apply lem-sfb-perfect-scalar-change-model with the identity coefficient map to get
   flatness of each realized term. The bounded-flat-model Tor theorem then gives the
   same Tor interval for its image in the derived category. Transport this property
   along the given local model isomorphism.
3. Apply finiteTorAmplitude_of_proetale_cover. Its finite-refinement and exact monoidal
   restriction argument descends these local intervals to one global Tor interval.
4. Apply constructibleHomology_of_isLocallyPerfectScalarModel. This computes homology
   by exact scalar realization and Noetherian finite presentation, independently of
   the uniform Tor interval.
5. Test global Tor amplitude on the tensor unit to obtain bounded homology for Q.
   The boundedness criterion for the standard t-structure gives boundedness of Q.
   Combine this with step 4 and with the global Tor interval from step 3. -/
theorem constantModelBoundedConstructible_finiteTorAmplitude_of_isLocallyPerfectScalarModel
    (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    (S : Scheme.{u}) [IsLocallyNoetherian S] [CompactSpace S]
    (Q : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S)))
    (hQ : IsLocallyPerfectScalarModel Λ S Q) :
    constantModelBoundedConstructible Λ S Q ∧ DerivedCategory.finiteTorAmplitude _ Q := by
  have ht : DerivedCategory.finiteTorAmplitude _ Q := by
    obtain ⟨𝒰, h𝒰⟩ := hQ
    apply finiteTorAmplitude_of_proetale_cover Λ S Q 𝒰
    intro i
    obtain ⟨C, l, h, hl, hh, hp, ⟨e⟩⟩ := h𝒰 i
    have := hl
    have := hh
    have : (sfbScalarModelComplex (𝒰.X i) C).IsStrictlyGE l := by
      unfold sfbScalarModelComplex
      infer_instance
    have : (sfbScalarModelComplex (𝒰.X i) C).IsStrictlyLE h := by
      unfold sfbScalarModelComplex
      infer_instance
    have hf := (sfbPerfectScalarChangeModels (Λ := Λ) (Λ' := Λ) (𝟙 Λ)
      (𝒰.X i) C l h hl hh hp).2.2.2.1
    refine ⟨l, h, ?_⟩
    exact (DerivedCategory.torAmplitudeIn _ l h).prop_of_iso e.symm
      (DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ l h (fun q ↦ (hf q).2.1))
  refine ⟨⟨?_, constructibleHomology_of_isLocallyPerfectScalarModel ell Λ hΛ S Q hQ⟩, ht⟩
  obtain ⟨a, b, hab⟩ := ht
  exact (DerivedCategory.exists_homologyConcentratedIn_iff_bounded Q).1
    ⟨a, b, DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hab⟩

end AlgebraicGeometry.ProEtale
