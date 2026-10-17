/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import WeilConjectures.TateTwist.ProEtale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def

/-! Geometric and shift components of the bounded-constructibility argument. -/

@[expose] public section

universe u u'

open CategoryTheory MonoidalCategory MonoidalClosed
open MonObj Limits ZeroObject
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

private lemma finitelyPresented_of_regular_iso
    {Y : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R}
    (e : M ≅ Mod.regular R) : Mod.IsFinitelyPresented R M := by
  refine ⟨1, 0, 0, ⟨?_⟩⟩
  exact e ≪≫ (biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular R)).symm ≪≫
    (cokernelZeroIsoTarget (X := Mod.finiteFree R 0)).symm

/-- The zero Tate twist is the regular module, hence constructible.

Source: the zero clause of `tateTwistNat`. Use the identity stratum and identity cover.
Each inverse image preserves the tensor unit, and the regular module has the presentation
with one generator and no relations.
(blueprint: lem-poincare-zero-twist-constructible) -/
lemma zeroTwist_constructible : IsConstructibleModuleObject
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) (tateTwist X ℓ 0) := by
  let R := condensedRingObj (Profinite.padicAlgClRingObj ℓ) X
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  refine ⟨S, fun a ↦ ?_⟩
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  let F := upperStar Ab.{u + 1} (S.immersion a)
  let G := upperStar Ab.{u + 1} (𝟙 X)
  let : F.Braided := {}
  let : G.Braided := {}
  exact finitelyPresented_of_regular_iso _
    ((G.mapMod (F.obj R)).mapIso F.mapModUnitIso.symm ≪≫ G.mapModUnitIso.symm)

end AlgebraicGeometry.ProEtale
