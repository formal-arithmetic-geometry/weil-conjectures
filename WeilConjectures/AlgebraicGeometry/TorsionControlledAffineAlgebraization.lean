/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.TorsionControlledAffineCandidate
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesIsoInvariant
import WeilConjectures.AlgebraicGeometry.CoherentOfFormalQuotientsAndTorsionKernel

/-! # The affine part of torsion-controlled algebraization

## References

* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 0ALK](https://stacks.math.columbia.edu/tag/0ALK)
* [Stacks Project, Tag 05EU](https://stacks.math.columbia.edu/tag/05EU)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Algebraization on a single affine scheme. Descent to a nonaffine scheme is not
part of this assertion. -/
theorem torsionControlled_affine_algebraization
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (htorsion : ∃ t : ℕ, 1 ≤ t ∧ ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (kernel (δ.hom.app (op e)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (cokernel (δ.hom.app (op e))))) :
    ∃ (F : CoherentModules X) (a : F ⟶ H) (β : N ≅ (completion X J).obj F),
      δ = β.hom ≫ (completion X J).map a ∧
      (∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (kernel a.hom)) ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (cokernel a.hom))) := by
  obtain ⟨F, hqc, a, β, hδ, s, hs, hk, hc⟩ :=
    torsionControlled_affine_candidate J H N δ htorsion
  have : F.IsQuasicoherent := hqc
  have hquot : RingedSpace.IsCoherent X.toRingedSpace
      (((formalCompletionFunctor J).obj F).obj (op (s - 1))) :=
    (coherentFormalModules_of_iso X J β N.property).1 (s - 1)
  have hF := coherent_of_formalQuotients_and_torsionKernel J F H a s hs hquot hk
  let Fc : CoherentModules X := ⟨F, hF⟩
  let ac : Fc ⟶ H := ObjectProperty.homMk a
  let βc : N ≅ (completion X J).obj Fc :=
    (IsCoherentFormalModule J).isoMk β
  refine ⟨Fc, ac, βc, ?_, s, hs, hk, hc⟩
  apply (ObjectProperty.ι (IsCoherentFormalModule J)).map_injective
  exact hδ

end AlgebraicGeometry
