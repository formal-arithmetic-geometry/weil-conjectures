/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.TorsionControlledCompletionHomLiftExists
import WeilConjectures.AlgebraicGeometry.CoherentMapTorsionCompletionExt
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Lifting maps between torsion-controlled coherent arrows

## References

* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 05EK](https://stacks.math.columbia.edu/tag/05EK)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Completion and the arrow to H jointly determine a coherent comparison map.
There is no claim that completion alone is fully faithful.
-/
theorem torsionControlled_completion_hom_lift
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H F F' : CoherentModules X) (a : F ⟶ H) (a' : F' ⟶ H)
    (ha : (∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a.hom))))
    (ha' : (∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a'.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a'.hom))))
    (θ : (completion X J).obj F ⟶ (completion X J).obj F')
    (hθ : θ ≫ (completion X J).map a' = (completion X J).map a) :
    ∃! g : F ⟶ F', g ≫ a' = a ∧ (completion X J).map g = θ := by
  obtain ⟨g, hg⟩ := torsionControlled_completion_hom_lift_exists J H F F' a a' ha ha' θ hθ
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  obtain ⟨s, hs, hk, hc⟩ := ha'
  symm
  apply coherentMap_torsion_completion_ext J F F' H a' ⟨s, hs, hk⟩ g g'
  · exact hg.1.trans hg'.1.symm
  · exact hg.2.trans hg'.2.symm

end AlgebraicGeometry
