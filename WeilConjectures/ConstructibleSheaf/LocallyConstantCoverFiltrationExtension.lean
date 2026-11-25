/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.ConstructibleSheaf.SylowCoverAssociatedSheaf
import WeilConjectures.RepresentationTheory.InvariantFlagCategoricalFiltration
import WeilConjectures.Mathlib.RepresentationTheory.Invariants
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Cover and filtration

A finite locally constant sheaf `G` of `𝔽_ℓ`-modules on a connected scheme becomes, on a
connected finite étale cover of degree prime to `ℓ`, an iterated extension of constant sheaves
`𝔽_ℓ` (`Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_cover_filtration_sheaf`).

## Implementation details

We use the cover `v : V ⟶ U` attached to an `ℓ`-Sylow subgroup `P` of the monodromy group of
`G`, on which `v^* G` comes from a `P`-representation `M`. A finite `ℓ`-group in characteristic
`ℓ` has nonzero invariants in every nonzero finite-dimensional representation, so induction on
the dimension gives a `P`-stable flag of `M` with one-dimensional trivial successive quotients;
its image under the exact associated-sheaf functor is the required filtration. The filtration is
indexed by all natural numbers, being constant after the last index.

## References

* Stacks Project, Lemma 0A3R, Lemma 0DV5 and Remark 0DV6.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

/-- **A prime-to-ℓ cover with constant successive quotients.** For a finite locally constant
sheaf `G` of `ULift (ZMod ℓ)`-modules on a connected scheme `U`, there is a connected finite
étale cover `v : V ⟶ U` whose geometric fibres all have cardinality `d` prime to `ℓ`, together
with a chain of monomorphisms `0 = W 0 ⟶ W 1 ⟶ ⋯ ⟶ W n ≅ v^* G` whose cokernels are all
isomorphic to the constant sheaf `ULift (ZMod ℓ)`. -/
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_cover_filtration_sheaf
    {U : Scheme.{u}} [ConnectedSpace U] (ℓ : ℕ) [Fact ℓ.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    [IsFiniteLocallyConstantSheaf G] :
    ∃ (V : Scheme.{u}) (v : V ⟶ U) (_ : IsFinite v) (_ : Etale v) (_ : ConnectedSpace V)
      (d : ℕ), ¬ ℓ ∣ d ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
        Nat.card (v.GeometricFiber s) = d) ∧
      (∃ (n : ℕ)
        (W : ℕ → Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
        (ι : ∀ i, W i ⟶ W (i + 1)), IsZero (W 0) ∧
        Nonempty (W n ≅ (v)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj G) ∧
        ∀ i < n, Mono (ι i) ∧ Nonempty (cokernel (ι i) ≅
          (constantSheaf V.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))) := by
  obtain ⟨V, v, hvfin, hvet, hV, d, hd, hfib, P, hPgroup, hPfin, hP,
    M, hM, T, hTadd, hTlim, hTcolim, ⟨eM⟩, ⟨eunit⟩⟩ :=
    Scheme.IsFiniteLocallyConstantSheaf.exists_sylow_cover_associated_sheaf ℓ G
  let := hPgroup
  let := hM
  let := hTadd
  let := hTlim
  let := hTcolim
  obtain ⟨F, h0, hn, hstable, hstep⟩ :=
    (M.ρ.invariants_ne_bot_and_exists_filtration_of_isPGroup hP).2
  obtain ⟨W, ι, hzero, ⟨eW⟩, hquot⟩ :=
    Rep.exists_categorical_filtration_of_invariant_flag ℓ P M F h0 hn hstable hstep
  refine ⟨V, v, hvfin, hvet, hV, d, hd, hfib, Module.finrank (ZMod ℓ) M.V,
    fun i ↦ T.obj (W i), fun i ↦ T.map (ι i), T.map_isZero hzero, ⟨T.mapIso eW ≪≫ eM⟩, ?_⟩
  intro i hi
  obtain ⟨hmono, ⟨equot⟩⟩ := hquot i hi
  let := hmono
  exact ⟨inferInstance, ⟨(PreservesCokernel.iso T (ι i)).symm ≪≫ T.mapIso equot ≪≫ eunit⟩⟩

end AlgebraicGeometry
