/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
/-!
# Underlying abelian sheaf of the small-model module inverse image

## References

* Stacks Project, Modules on Sites, Tags 03D2 and 03D3.
-/
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
/-- Forgetting the action on the model-site module pullback gives model-site abelian inverse
image (Stacks, Tags 03D2 and 03D3). -/
theorem proEtaleModelModuleInverseImage_underlying {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    let A := (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
    let B := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
    let A' := ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj A
    let B' := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj B
    Nonempty (SheafOfModules.pullback.{u + 1} (proEtaleModelRingUnit f R) ⋙
      SheafOfModules.toSheaf B' ≅
      SheafOfModules.toSheaf A' ⋙
        Functor.sheafPullbackConstruction.sheafPullback (proEtaleModelBaseChange f)
          AddCommGrpCat.{u + 1} (proEtaleModelTopology Y) (proEtaleModelTopology X)) := by
  let : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsEquivalence
  let : Limits.PreservesFiniteLimits (proEtaleModelBaseChange f) := by
    change Limits.PreservesFiniteLimits
      ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt) ⋙ proEtaleBaseChange f ⋙ AsSmall.up)
    infer_instance
  let : RepresentablyFlat (proEtaleModelBaseChange f) := flat_of_preservesFiniteLimits _
  obtain ⟨p, hp⟩ := proEtaleModelRingPresentation f R
  obtain ⟨e, _⟩ := SheafOfModules.inverseImage_underlying_of_ring_presentation
    (proEtaleModelRingUnit f R) p (by ext U r; exact hp U r)
  exact ⟨e⟩
end AlgebraicGeometry.Scheme
