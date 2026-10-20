/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.IsFiniteLocallyFreeOfCoherentFreeStalks
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.Modules.GenericRank
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Localization.Finiteness
import WeilConjectures.Mathlib.AlgebraicGeometry.Properties

/-!
# Torsion-free coherent modules on regular curves

Source: Stacks Project, Divisors, Tag 0CC4; constant rank on connected schemes
(blueprint: lem-sc-regular-curve-torsionfree-free).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private theorem finite_stalk {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (x : X) :
    Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have : Module.Finite Γ(X, U) Γ(F, U) := finite_sections_of_finiteType F hU
  obtain ⟨f, _, hf⟩ := Scheme.isLocalizedModule_affine_germ F inferInstance U hU ⟨x, hx⟩
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let : Module Γ(X, U) (F.presheaf.stalk x) :=
    Module.compHom _ (X.presheaf.germ U x hx).hom
  let : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let S := (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  let : IsLocalization S (X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hx⟩
  change Γ(F, U) →ₗ[Γ(X, U)] F.presheaf.stalk x at f
  have : IsLocalizedModule S f := hf
  exact Module.Finite.of_isLocalizedModule S (Rₚ := X.presheaf.stalk x) f

/-- On an integral regular scheme of dimension at most one, a coherent module has zero
 torsion subsheaf exactly when it is finite locally free. In that case its rank is constant
 and is the dimension of its generic stalk over the function field. The torsion subsheaf
 is zero exactly when every stalk has no nonzero torsion element, since its stalks are the
 torsion submodules (`lem-sc-torsion-subsheaf-quotient`); torsion-free is written stalkwise,
 in the form of that lemma's quotient clause.
Source: Stacks Project, Divisors, Tag 0CC4
(blueprint: lem-sc-regular-curve-torsionfree-free).

Proof:
1. The affine regularity hypothesis (`def-weil-regular-scheme`) makes every stalk a
Noetherian regular local domain. The dimension bound makes it a field or a DVR, using
`lem-sc-regular-dim1-dvr`. Coherence (`pqf-def-coherent`) makes the module stalk finite.
2. Zero torsion subsheaf implies torsion-free stalks by `lem-sc-torsion-subsheaf-quotient`.
Over a field the finite stalk is free; over a DVR use `lem-sc-dvr-fg-torsionfree-free`.
Then `lem-sc-coherent-free-stalks-locally-free` gives finite local freeness.
3. Conversely free stalks over the domain stalks of `def-pc-integral-scheme` have no
nonzero torsion. By `lem-sc-torsion-subsheaf-quotient` the torsion subsheaf has zero stalks,
and hence is zero.
4. Finite local freeness gives locally constant rank. Integrality makes the space
connected, so this rank is constant. At the generic point its scalar ring is the
function field (`def-sc-function-field`), and the common rank is its vector-space dimension.
-/
theorem regular_curve_torsionfree_iff_finiteLocallyFree (X : Scheme.{u}) [IsIntegral X]
    (hregular : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ IsRegularRing Γ(X, U))
    (hdim : topologicalKrullDim X ≤ 1) (F : X.Modules)
    (hcoherent : RingedSpace.IsCoherent X.toRingedSpace F) :
    ((∀ (x : X) (s : F.presheaf.stalk x) (a : X.presheaf.stalk x),
        a ≠ 0 → a • s = 0 → s = 0) ↔ F.IsFiniteLocallyFree) ∧
    (F.IsFiniteLocallyFree →
      F.IsFiniteLocallyFreeOfRank
        (Module.finrank X.functionField (F.presheaf.stalk (genericPoint X)))) := by
  classical
  choose U hxU hU using hregular
  have hcover : (⨆ x, (U x).1) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hxU x⟩
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_affine_cover hcover
    (fun x ↦ by
      have := hU x
      infer_instance)
  have hreg (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by
    let := hU x
    let : Algebra Γ(X, U x) (X.presheaf.stalk x) :=
      X.presheaf.algebra_section_stalk ⟨x, hxU x⟩
    let P := ((U x).2.primeIdealOf ⟨x, hxU x⟩).asIdeal
    let : P.IsPrime := ((U x).2.primeIdealOf ⟨x, hxU x⟩).isPrime
    let : IsLocalization P.primeCompl (X.presheaf.stalk x) :=
      (U x).2.isLocalization_stalk ⟨x, hxU x⟩
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
        (X.presheaf.stalk x)).toRingEquiv
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro htf
    have hq := (isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hcoherent
    let := hq.1
    let := hq.2
    apply isFiniteLocallyFree_of_coherent_free_stalks F hcoherent
    intro x
    change Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) ∧
      Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x)
    let := finite_stalk F x
    let := hreg x
    let : Module.IsTorsionFree (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      Module.IsTorsionFree.of_smul_eq_zero fun a s h ↦
        or_iff_not_imp_left.mpr (fun ha ↦ htf x s a ha h)
    by_cases hfield : IsField (X.presheaf.stalk x)
    · let := hfield.toField
      exact ⟨inferInstance, inferInstance⟩
    · have hd : ringKrullDim (X.presheaf.stalk x) = 1 := by
        refine le_antisymm ((ringKrullDim_stalk_le_topologicalKrullDim x).trans hdim)
          (not_lt.mp fun hlt ↦ hfield ?_)
        let : Ring.KrullDimLE 0 (X.presheaf.stalk x) :=
          Ring.krullDimLE_iff.mpr (ENat.WithBot.lt_add_one_iff.mp (by simpa using hlt))
        exact Ring.KrullDimLE.isField_of_isDomain
      let := IsRegularLocalRing.isDiscreteValuationRing (X.presheaf.stalk x) hd
      exact ⟨inferInstance, inferInstance⟩
  · intro hf x s a ha has
    let := hf
    obtain ⟨V, I, _, hx, e⟩ := exists_mem_over_iso_free F x
    let b := (exists_basis_stalk_of_over_iso_free e.some hx).choose
    have : Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) := Module.Free.of_basis b
    exact (smul_eq_zero.mp has).resolve_left ha
  · intro hf
    let := hf
    exact isFiniteLocallyFreeOfRank_rank F

end AlgebraicGeometry.Scheme.Modules
