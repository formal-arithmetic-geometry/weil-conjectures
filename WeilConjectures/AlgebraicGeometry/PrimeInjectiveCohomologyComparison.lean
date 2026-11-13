/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.BaseChange.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.KilledSheafModuleLift
import WeilConjectures.AlgebraicGeometry.ModuleAcyclicCohomologyComparison

/-!
# Cohomology comparison from prime-module injective acyclicity

## References

* Stacks Project, Tag 095T, <https://stacks.math.columbia.edu/tag/095T>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- Degree-zero comparison and acyclicity of restricted injectives imply comparison
for abelian sheaves killed by a prime (Stacks, Tag 095T). -/
theorem Etale.bijective_cohomologyMap_of_prime_injective_acyclic
    {X Y : Scheme.{u}} (i : Y ⟶ X) (r : ℕ) [Fact r.Prime]
    (hzero : ∀ G : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))),
      IsIso (globalSectionsUpperStarMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) i G))
    (hacyclic : ∀ (J : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Injective J]
        (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
          AddCommGrpCat.{u + 1})).obj
            ((i)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))].obj J)) q))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : r • 𝟙 G = 0)
    (q : ℕ) : Function.Bijective (Etale.cohomologyMap i G q) := by
  obtain ⟨M, ⟨e⟩⟩ := exists_module_sheaf_of_nsmul_id_eq_zero X r G hG
  have hM := Etale.bijective_cohomologyMap_of_module_acyclic i r hzero hacyclic M q
  let eX := (Sheaf.functorH X.smallEtaleTopology q).mapIso e
  let eY := (Sheaf.functorH Y.smallEtaleTopology q).mapIso
    (((i)^*[AddCommGrpCat.{u + 1}]).mapIso e)
  have hX : Function.Bijective (Sheaf.H.map e.hom q) :=
    (ConcreteCategory.bijective_of_isIso eX.hom)
  have hY : Function.Bijective
      (Sheaf.H.map (((i)^*[AddCommGrpCat.{u + 1}]).map e.hom) q) :=
    (ConcreteCategory.bijective_of_isIso eY.hom)
  refine ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨x', rfl⟩ := hX.2 x
    obtain ⟨y', rfl⟩ := hX.2 y
    apply congrArg (Sheaf.H.map e.hom q)
    apply hM.1
    apply hY.1
    simpa only [← Etale.cohomologyMap_map] using hxy
  · intro y
    obtain ⟨y', rfl⟩ := hY.2 y
    obtain ⟨x', hx'⟩ := hM.2 y'
    refine ⟨Sheaf.H.map e.hom q x', ?_⟩
    rw [Etale.cohomologyMap_map, hx']

end AlgebraicGeometry
