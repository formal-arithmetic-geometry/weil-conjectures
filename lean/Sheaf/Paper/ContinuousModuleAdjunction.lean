/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module

public import Sheaf.Paper.IntegralModelOpenClosedBasic
import all Sheaf.AlgebraicGeometry.ProEtaleOperations

/-!
# The continuous-coefficient module adjunction

Source: Stacks Project, Tags 03D2 and 03D6
(blueprint: lem-weil-pbc-continuous-module-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false in
private def directImageComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (latticeCoefficientSheaf Y T) ≅ latticeCoefficientSheaf X T)
    (hc : c.hom = continuousCoefficientInverseImageMap f T) :
    Scheme.proEtaleRingModuleDirectImage f (latticeCoefficientSheaf Y T)
      (latticeCoefficientSheaf X T) c ≅ continuousModuleDirectImage f T := by
  dsimp only [Scheme.proEtaleRingModuleDirectImage, Scheme.proEtaleRingDirectImageMap]
  rw [hc]
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    exact PresheafOfModules.isoMk (fun V ↦ Iso.refl _) (by intros; rfl)
  · intro M N a
    ext V x
    rfl

/-- Scalar extension along the specified coefficient isomorphism followed by ordinary
inverse image is left adjoint to the concrete continuous-coefficient direct image.
Source: Stacks Project, Tags 03D2 and 03D6
(blueprint: lem-weil-pbc-continuous-module-adjunction).
Proof: compose the constructed module inverse-image adjunction with extension/restriction
of scalars. The resulting right adjoint has the same section groups and maps as the
continuous direct image. Its scalar action first applies the ring adjunction unit and
then c; this is exactly the action of the two composed functors defining the continuous
direct image. The sectionwise identity is therefore a natural linear isomorphism.
Transport the adjunction along it. -/
theorem continuousModule_adjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (latticeCoefficientSheaf Y T) ≅ latticeCoefficientSheaf X T)
    (hc : c.hom = continuousCoefficientInverseImageMap f T) :
    Nonempty (Scheme.proEtaleRingModulePullback f (latticeCoefficientSheaf Y T)
      (latticeCoefficientSheaf X T) c ⊣ continuousModuleDirectImage f T) := by
  exact ⟨(Scheme.proEtaleRingModulePullbackAdjunction f (latticeCoefficientSheaf Y T)
    (latticeCoefficientSheaf X T) c).ofNatIsoRight (directImageComparison f T c hc)⟩

end AlgebraicGeometry.ProEtale
