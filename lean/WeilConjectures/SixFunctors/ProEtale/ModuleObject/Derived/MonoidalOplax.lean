/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalIso

/-!
# The oplax monoidal structure of the derived pullback of module objects

Part of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`, split off so that
each file compiles within the time limit: the oplax monoidal structure
`leftDerivedUpperStarOplaxMonoidal` of `Lf^*`.
-/


set_option Elab.async false

@[expose] public section

open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option synthInstance.maxHeartbeats 400000 in
-- the K-flat derivability structure on complexes of module objects is found by instance search
set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The oplax monoidal structure on `Lf^*` whose comonoidal structure is the comparison `m`
(`CategoryTheory.Functor.OplaxMonoidal.ofLaxSquare'`): its coherences are checked on K-flat
complexes, whose pullbacks are K-flat. -/
@[instance_reducible]
noncomputable def leftDerivedUpperStarOplaxMonoidal : L((f)^*⟦Λ⟧).OplaxMonoidal :=
  haveI := DerivedCategory.isIso_ε_Qh
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  Functor.OplaxMonoidal.ofLaxSquare' (Q₁ := DerivedCategory.Qh) (Q₂ := DerivedCategory.Qh)
    (F := (f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)) (leftDerivedUpperStarTensor Λ f)
    (fun a ↦ (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app a)
    (fun _ _ g ↦ (f)^*⟦Λ⟧.leftDerivedFunctorCounit.naturality g)
    (leftDerivedUpperStarTensor_laxSquare Λ f) (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
    (exists_kFlat_iso_Qh_obj Λ)
    (fun a ha ↦ (f)^*⟦Λ⟧.isIso_leftDerivedFunctorCounit_app_of_kFlat' a ha)
    (fun x b hb ↦ by
      obtain ⟨B, rfl⟩ := b.quotient_obj_surjective
      exact isIso_μNatTrans_Qh_app_app_of_kFlat x _ (kFlat_upperStar_mapHomotopyCategory_obj Λ f
        ((HomotopyCategory.kFlat_quotient_obj_iff B).1 hb)))

end AlgebraicGeometry.ProEtale.CondensedRing
