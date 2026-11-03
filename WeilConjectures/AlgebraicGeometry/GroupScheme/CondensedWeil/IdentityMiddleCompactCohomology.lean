/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FieldSmoothDuality.CondensedFieldSmoothDuality
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage

/-! # The identity middle image on native compact cohomology

Source: sk-cor-wft-curve-upper, specialization to the identity open immersion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.CondensedWeil

/-- The carrier of the ordinary identity middle extension is the original module.
Source: sk-cor-wft-curve-upper, the clause j_*F = F for j = id.
(blueprint: lem-a1-identity-middle-compact-cohomology). -/
def identityMiddleCarrierIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (C₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]
    (F : NativeL2.WeilModule D l C₀) :
    (NativeL2.middleWeilImage D l (𝟙 C₀) F).carrier ≅ F.carrier := by
  unfold NativeL2.middleWeilImage
  change (lowerStar (Profinite.padicAlgClRingObj l)
    (NativeL2.geometricMap D (𝟙 C₀))).obj F.carrier ≅ F.carrier
  have h : NativeL2.geometricMap D (𝟙 C₀) = 𝟙 (D.geometricFiber C₀).left := by
    exact congrArg (fun f => f.left)
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map_id C₀)
  exact (lowerStarCongr (Profinite.padicAlgClRingObj l) h ≪≫
    lowerStarId (Profinite.padicAlgClRingObj l) (D.geometricFiber C₀).left).app F.carrier

end WeilConjectures.CondensedWeil
