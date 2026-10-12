/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Algebra.Homology.DoubleComplexVerticalTowerMaps
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Sheaf.Algebra.Homology.FirstQuadrantTotalShortExact
import Sheaf.Algebra.Homology.DoubleComplexVerticalQuotientComparison
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
/-! # Top endpoint comparison for the smart vertical tower

Source: Stacks Project, tag 012X, finite-diagonal totalization and the smart
truncation cokernel comparison.
-/

@[expose] public section
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)]
variable (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
/-- Finite/top-endpoint cone comparison, isolating this endpoint case of the
vertical tower comparison.
Source: the columnwise smart truncation and bounded-below totalization argument in Stacks 012X.
(blueprint: lem-sp-double-complex-vertical-tower-comparison-top)
Proof: form the actual cokernel short complex of the columnwise cutoff inclusion.
The inclusion is degreewise mono. Finite-diagonal totalization and extension preserve
short exactness. The tower map to top is this totalized inclusion by verticalTowerMap_ι.
Mathlib's descShortComplex is a quasi-isomorphism from its cone to the totalized cokernel.
Compose its homology isomorphism with that of the canonical quotient-to-lower map. -/
theorem verticalTower_interval_homology_iso_top
    (a : ℤ) (n : ℤ) :
    Nonempty ((CochainComplex.mappingCone
      ((verticalTower K).map (homOfLE (show (a : EInt) ≤ ⊤ by simp)))).homology n ≅
      ((total (((ComplexShape.embeddingUpNat.extendFunctor C ⋙
        (ComplexShape.embeddingUpIntGE a).truncGEFunctor C ⋙
        ComplexShape.embeddingUpNat.restrictionFunctor C).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K) (ComplexShape.up ℕ)).extend
            ComplexShape.embeddingUpNat).homology n) := by
  let S := verticalQuotientShortComplex K a
  have hm : Mono S.f := by
    apply HomologicalComplex.mono_of_mono_f
    intro p
    apply HomologicalComplex.mono_of_mono_f
    intro q
    change Mono ((HomologicalComplex.ιTruncLE
      ((K.X p).extend ComplexShape.embeddingUpNat)
      (ComplexShape.embeddingUpIntLE (a - 1))).f (ComplexShape.embeddingUpNat.f q))
    infer_instance
  have he : Epi S.g := by
    change Epi (cokernel.π (verticalCutoffBicomplexι K a))
    infer_instance
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_cokernel (verticalCutoffBicomplexι K a) }
  let T := totalExtendShortComplex S
  have hT : T.ShortExact := totalExtendShortComplex_shortExact S hS
  have hc : QuasiIso (CochainComplex.mappingCone.descShortComplex T) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hT
  have hq := verticalQuotientToLower_total_quasiIso K a
  let q := HomologicalComplex.extendMap
    (total.map (verticalQuotientToLower K a) (ComplexShape.up ℕ))
    ComplexShape.embeddingUpNat
  have hf : (verticalTower K).map (homOfLE (show (a : EInt) ≤ ⊤ by simp)) = T.f := by
    have h := verticalTowerMap_ι K (show (a : EInt) ≤ ⊤ by simp)
    change verticalTowerMap K (show (a : EInt) ≤ ⊤ by simp) ≫ 𝟙 _ = T.f at h
    change verticalTowerMap K (show (a : EInt) ≤ ⊤ by simp) = T.f
    simpa only [Category.comp_id] using h
  rw [hf]
  exact ⟨isoOfQuasiIsoAt
    (CochainComplex.mappingCone.descShortComplex T) n ≪≫
    isoOfQuasiIsoAt q n⟩
end HomologicalComplex₂
