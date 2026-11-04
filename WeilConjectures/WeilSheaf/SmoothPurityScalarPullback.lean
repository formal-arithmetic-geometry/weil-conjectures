/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.CondensedModelWeil
public import WeilConjectures.TateTwist.TateModuleTrivialization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal

/-! # Coefficient-parametric pullback comparisons for Tate descent -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (g : U ⟶ X)

/-- The coefficient extension unit, with the coefficient object left abstract. -/
noncomputable def purityPullbackUnit
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (g)^*[Ab.{u + 1}].obj M.X ⟶ ((g)^*⟦Λ⟧.obj M).X :=
  CondensedRing.upperStarUnitHom Λ g M

/-- Extension of an isomorphism of modules over the pulled-back coefficient ring. -/
noncomputable def purityExtendPullbackIso
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (e : ((g)^*[Ab.{u + 1}].mapMod _).obj M ≅
      ((g)^*[Ab.{u + 1}].mapMod _).obj N) :
    (g)^*⟦Λ⟧.obj M ≅ (g)^*⟦Λ⟧.obj N :=
  (Mod.extendScalars (condensedPullbackHom Λ g)).mapIso e

variable {K : Type u} [Field K] [WeaklyEtale g] (f : U ⟶ Spec (.of K))
  (l : ℕ) [Fact l.Prime] {ζ : ℕ → K}
  (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ n)) (hζ' : ∀ n, ζ (n + 1) ^ l = ζ n)

/-- The Tate-module trivialization transported through coefficient extension. -/
noncomputable def purityTateModuleTrivialization :
    (g)^*⟦Profinite.continuousMapRingObj ℤ_[l]⟧.obj (tateModule X l) ≅
      (g)^*⟦Profinite.continuousMapRingObj ℤ_[l]⟧.obj (𝟙_ _) :=
  purityExtendPullbackIso (Profinite.continuousMapRingObj ℤ_[l]) g _ _
    (upperStarMapModTateModuleIsoUnit g f l hζ hζ' ≪≫ (g)^*[Ab.{u + 1}].mapModUnitIso)

end AlgebraicGeometry.ProEtale
