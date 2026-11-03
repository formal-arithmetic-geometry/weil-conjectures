/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-! # Realization of a finite closed support

Source: latest blueprint, `sec-deligne-laumon-a1/sk-p-dl-a1-perverse/`
`sk-p-dl-a1-perverse.proof.md`, the finite-boundary localization argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCurve

/-- A coefficient module vanishing off finitely many closed points comes from their
zero-dimensional reduced closed subscheme.
Source: latest blueprint, right exactness and finite-boundary localization
(blueprint: lem-per-finite-closed-support).

Proof: take the reduced induced closed subscheme of the closed complement. Its
closed embedding identifies its points with that complement. Thus it is finite,
and each of its singletons is closed. A finite T1 space is discrete, hence has
Krull dimension at most zero, including the empty case. The abelian supported-unit
isomorphism applies to the vanishing open restriction. The coefficient pullback
comparison transfers that vanishing to the underlying abelian sheaf, and the
module supported-unit comparison lifts the resulting isomorphism back to actual
coefficient modules. Its target is the direct image of the closed restriction. -/
theorem finiteClosedSupport_realization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [IsNoetherian X]
    (G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (U : X.Opens) (hfin : ((U : Set X)ᶜ).Finite)
    (hclosed : ∀ x ∈ (U : Set X)ᶜ, IsClosed ({x} : Set X))
    (hzero : IsZero ((CondensedRing.upperStar Λ U.ι).obj G)) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (_ : IsClosedImmersion i),
      topologicalKrullDim Z ≤ 0 ∧
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z),
        Nonempty (G ≅ (CondensedRing.lowerStar Λ i).obj M) := by
  let J := Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
  let Z := J.subscheme
  let i : Z ⟶ X := J.subschemeι
  have hi : Set.range i = (U : Set X)ᶜ := Scheme.IdealSheafData.range_subschemeι _
  have hfinite : Finite Z := by
    have : Finite ((U : Set X)ᶜ : Set X) := hfin
    exact Finite.of_injective (fun z : Z ↦
      (⟨i z, hi ▸ Set.mem_range_self z⟩ : ((U : Set X)ᶜ : Set X)))
      (fun _ _ h ↦ i.isClosedEmbedding.injective (congrArg Subtype.val h))
  have hT1 : T1Space Z := ⟨fun z ↦ by
    have hc := (hclosed (i z) (hi ▸ Set.mem_range_self z)).preimage i.continuous
    convert hc using 1
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact i.isClosedEmbedding.injective.eq_iff.symm⟩
  have : DiscreteTopology Z := inferInstance
  have hij : Set.range U.ι = (Set.range i)ᶜ := by simp [hi]
  have hab : IsZero ((ProEtale.upperStar Ab.{u + 1} U.ι).obj G.X) :=
    ((Mod.forget _).map_isZero hzero).of_iso
      ((profinitePointModuleForgetPullbackIso Λ U.ι).app G).symm
  have hunit := CondensedRing.moduleUnitOfAbelian Λ i G
    ((ProEtale.abelian_closed_support i U.ι hij).2 G.X hab)
  exact ⟨Z, i, inferInstance, topologicalKrullDim_zero_of_discreteTopology Z,
    (CondensedRing.upperStar Λ i).obj G,
    ⟨asIso ((CondensedRing.upperStarLowerStarAdjunction Λ i).unit.app G)⟩⟩

end AlgebraicGeometry.ProEtale.CondensedCurve
