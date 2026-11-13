/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentMapTorsionCompletionExtZero
import WeilConjectures.AlgebraicGeometry.TorsionControlledCompletionHomLiftCompletion

/-!
# Existence of lifts of completion homomorphisms

For maps `a : F ⟶ H` and `a' : F' ⟶ H` of coherent modules on a Noetherian scheme whose
kernels and cokernels are killed by a power of `J`, every map of completions over the
completion of `H` lifts to a map `F ⟶ F'` over `H`.

## References

* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 05EK](https://stacks.math.columbia.edu/tag/05EK)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Existence part of the torsion-controlled completion homomorphism lifting theorem: if the
kernels and cokernels of `a` and `a'` are killed by a power of `J`, a map of completions `θ`
over the completion of `H` lifts to `g : F ⟶ F'` with `g ≫ a' = a`. -/
theorem torsionControlled_completion_hom_lift_exists
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
    ∃ g : F ⟶ F', g ≫ a' = a ∧ (completion X J).map g = θ := by
  obtain ⟨s, hs, hk, hc⟩ := ha
  obtain ⟨n, hn⟩ := coherentMap_torsion_completion_ext_zero J F' H a'
    (by obtain ⟨s, hs, hk, hc⟩ := ha'; exact ⟨s, hs, hk⟩)
  exact ⟨torsionControlledCompletionHomLift J a a' ha' θ hθ n hn,
    torsionControlled_completion_hom_lift_constructed J a a' ha' θ hθ n hn⟩

end AlgebraicGeometry
