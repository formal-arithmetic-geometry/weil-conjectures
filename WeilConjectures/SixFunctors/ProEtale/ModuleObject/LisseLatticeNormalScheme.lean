/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeEmbedding
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UniformizerReduction

/-!
# Lattices of lisse `E`-modules on connected normal schemes

Let `X` be a connected Noetherian scheme whose local rings are integrally closed domains (for
instance a nonempty connected normal scheme of finite type over a field), `ℓ` a prime and
`E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ`, with ring of integers `𝒪_E` and uniformiser `ϖ`.
Every lisse `E_X`-module `L` contains a lisse `𝒪_{E,X}`-submodule `M` with `M[1/ℓ] = L`; the
reductions `Mₙ = M/ϖⁿM` are finite locally constant étale sheaves and `M ≅ lim Mₙ`
(`AlgebraicGeometry.ProEtale.exists_lisse_integral_lattice_of_isIntegrallyClosed_stalk`,
blueprint `lemma-global-lattice-normal-scheme`).

The lattice is
`ProEtale.exists_mono_isLocallyFree_padicIntegers_of_isIntegrallyClosed_stalk`.
The statements on the reductions hold for every locally free `𝒪_{E,X}`-module `M`:

* `AlgebraicGeometry.ProEtale.exists_isFiniteLocallyConstantSheaf_iso_of_isLocallyFree`: the
  reduction `M/ϖⁿM`, which is pro-étale locally `(𝒪_E/ϖⁿ)ʳ`, is `ν^* G` for a finite locally
  constant sheaf `G` on the small étale site of `X`;
* `AlgebraicGeometry.ProEtale.isLimit_cokernelEndPowTowerCone_of_isLocallyFree`: `M` is the limit
  of its reductions, `𝒪_{E,X} = C(-, 𝒪_E)` being the limit of the `C(-, 𝒪_E/ϖⁿ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

/-- **The reductions of a locally free `𝒪_{E,X}`-module are finite locally constant étale
sheaves** (blueprint `lemma-global-lattice-normal-scheme`). Let `M` be a locally free
`𝒪_{E,X}`-module on a Noetherian scheme `X` and `ϖ` a uniformiser of `𝒪_E`. The reduction
`M/ϖⁿM` is, as a sheaf of abelian groups, the pullback `ν^* G` of a finite locally constant sheaf
`G` of abelian groups on the small étale site of `X`.

Pro-étale locally `M/ϖⁿM ≅ (𝒪_E/ϖⁿ)ʳ` is constant with finite value; its descent datum along an
affine weakly étale cover `V = lim Vᵢ ⟶ X` is a locally constant function with values in a finite
set on the quasi-compact `V ×_X V = lim Vᵢ ×_X Vᵢ`, hence comes from a finite stage. -/
theorem exists_isFiniteLocallyConstantSheaf_iso_of_isLocallyFree {X : Scheme.{u}}
    [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))
    (hM : IsLocallyFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) M)
    (ϖ : integers ℓ E.1) (hϖ : IsLocalRing.maximalIdeal (integers ℓ E.1) = Ideal.span {ϖ})
    (n : ℕ) :
    ∃ G : Sheaf X.smallEtaleTopology Ab.{u + 1}, IsFiniteLocallyConstantSheaf G ∧
      Nonempty ((ν^*(X)[Ab.{u + 1}]).obj G ≅
        ((cokernelEndPowTower (padicIntegersSmul ϖ M)).obj (op n)).X) := by
  sorry

/-- **A locally free `𝒪_{E,X}`-module is the limit of its reductions** (blueprint
`lemma-global-lattice-normal-scheme`): for a uniformiser `ϖ` of `𝒪_E`, the cone of the
projections `M ⟶ M/ϖⁿM` is a limit cone. This is local on `X`, and `𝒪_{E,X} = C(-, 𝒪_E)` is the
limit of the `C(-, 𝒪_E/ϖⁿ)`. -/
theorem isLimit_cokernelEndPowTowerCone_of_isLocallyFree {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))
    (hM : IsLocallyFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) M)
    (ϖ : integers ℓ E.1) (hϖ : IsLocalRing.maximalIdeal (integers ℓ E.1) = Ideal.span {ϖ}) :
    Nonempty (IsLimit (cokernelEndPowTowerCone (padicIntegersSmul ϖ M))) := by
  sorry

/-- **Lattices of lisse `E`-modules on connected normal schemes** (blueprint
`lemma-global-lattice-normal-scheme`). Let `X` be a connected Noetherian scheme whose local rings
are integrally closed domains (e.g. a nonempty connected normal scheme of finite type over a
field) and `E/ℚ_ℓ` finite. Every lisse (locally free) `E_X`-module `L` contains a lisse
`𝒪_{E,X}`-submodule `M` with `M[1/ℓ] = L`: there is a monomorphism `ι : M ⟶ L` of
`𝒪_{E,X}`-modules with adjoint `E_X ⊗_{𝒪_{E,X}} M ≅ L`. For every uniformiser `ϖ` of `𝒪_E`, the
reductions `Mₙ = M/ϖⁿM` are finite locally constant étale sheaves (`Mₙ ≅ ν^* Gₙ` with `Gₙ` finite
locally constant on the small étale site), and `M ≅ lim Mₙ`. -/
theorem exists_lisse_integral_lattice_of_isIntegrallyClosed_stalk {X : Scheme.{u}}
    [IsNoetherian X] [ConnectedSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X))
    (hL : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E.1) X) L) :
    ∃ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))
      (ι : M ⟶ (Mod.comap (padicIntegersToPadicSubfield X ℓ E)).obj L),
      IsLocallyFree (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) M ∧ Mono ι ∧
        IsIso (((Mod.extendRestrictAdjunction (padicIntegersToPadicSubfield X ℓ E)).homEquiv
          M L).symm ι) ∧
        ∀ ϖ : integers ℓ E.1, IsLocalRing.maximalIdeal (integers ℓ E.1) = Ideal.span {ϖ} →
          (∀ n : ℕ, ∃ G : Sheaf X.smallEtaleTopology Ab.{u + 1}, IsFiniteLocallyConstantSheaf G ∧
            Nonempty ((ν^*(X)[Ab.{u + 1}]).obj G ≅
              ((cokernelEndPowTower (padicIntegersSmul ϖ M)).obj (op n)).X)) ∧
          Nonempty (IsLimit (cokernelEndPowTowerCone (padicIntegersSmul ϖ M))) := by
  obtain ⟨M, ι, hM, hι, hι'⟩ :=
    exists_mono_isLocallyFree_padicIntegers_of_isIntegrallyClosed_stalk hX L hL
  exact ⟨M, ι, hM, hι, hι', fun ϖ hϖ ↦
    ⟨exists_isFiniteLocallyConstantSheaf_iso_of_isLocallyFree M hM ϖ hϖ,
      isLimit_cokernelEndPowTowerCone_of_isLocallyFree M hM ϖ hϖ⟩⟩

end AlgebraicGeometry.ProEtale
