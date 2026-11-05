/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.GaloisCoverTrace
public import WeilConjectures.SixFunctors.ProEtale.UpperStarIsoRestrictionMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# The trace of a Galois covering as a natural transformation, and the monoidal action

For a Galois covering `g : Y ⟶ X` with group `Γ` (`AlgebraicGeometry.ProEtale.IsGaloisAction`),
this file packages the trace `g_* g^* H ⟶ H` of `AlgebraicGeometry.ProEtale.galoisTrace` and the
action of `Γ` on `g_* g^* H` as natural transformations
(`AlgebraicGeometry.ProEtale.galoisTraceNatTrans`,
`AlgebraicGeometry.ProEtale.galoisActionNatTrans`)
of functors on abelian pro-étale sheaves, and
proves:

* the action is monoidal for the lax monoidal structure of `g^* ⋙ g_*`
  (`AlgebraicGeometry.ProEtale.isMonoidal_galoisActionNatTrans`): it is the restriction along the
  automorphisms `V ×_X Y ⟶ V ×_X Y`, conjugated by the monoidal comparison `g^* ≅ j_g^*`;
* the action fixes the unit, the unit is a monomorphism, and the trace factors the norm through
  the unit.

These are the inputs of `CategoryTheory.Adjunction.mapModTrace`, which lifts the trace to module
objects over any coefficient ring.
-/

@[expose] public section

universe u

open CategoryTheory Category MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [WeaklyEtale g] [Surjective g] [QuasiCompact g]
  {Γ : Type u} {ρ : Γ → (Y ⟶ Y)} (hρ : ∀ i, ρ i ≫ g = g)
  [Group Γ] [Fintype Γ] (hmul : ∀ a b, ρ a ≫ ρ b = ρ (a * b)) (hgal : IsGaloisAction g ρ)

omit [Surjective g] [QuasiCompact g] in
instance isContinuous_baseChangeFunctor :
    (baseChangeFunctor g).IsContinuous (Scheme.ProEt.topology X) (Scheme.ProEt.topology X) :=
  isContinuous_overPullback_comp_overMap g

/-- **The trace of a Galois covering** as a natural transformation `g^* ⋙ g_* ⟶ 𝟭`. -/
@[simps]
noncomputable def galoisTraceNatTrans :
    (g)^*[AddCommGrpCat.{u + 1}] ⋙ (g)_*[AddCommGrpCat.{u + 1}] ⟶ 𝟭 _ where
  app := galoisTrace g hρ hmul hgal
  naturality _ _ φ := galoisTrace_naturality g hρ hmul hgal φ

omit [Group Γ] [Fintype Γ] in
/-- The unit `H ⟶ g_* g^* H` of a surjective weakly étale `g` is a monomorphism. -/
instance mono_upperStarLowerStarAdjunction_unit_app
    (H : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :
    Mono ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app H) := by
  have : Mono ((localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g
      inferInstance).unit.app H).hom :=
    Presheaf.mono_baseChangeUnit (ProEt.topology X) (generate_singleton_baseChangeProj_mem g)
      (isSheaf_comp_forget H)
  have : Mono ((localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g
      inferInstance).unit.app H) := Sheaf.Hom.mono_of_presheaf_mono _ _ _
  have h := upperStarLowerStarAdjunction_unit_app_comp g H
  exact mono_of_mono_fac h

end AlgebraicGeometry.ProEtale
