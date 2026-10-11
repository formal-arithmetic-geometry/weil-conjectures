/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion

/-!
# The open–closed short exact sequence on the pro-étale site

Let `i : Z ⟶ X` be a closed immersion whose complementary open immersion `j : U ⟶ X` is
quasi-compact. For a pro-étale sheaf of modules `F` on `X`, the sequence
`0 ⟶ j_! j^* F ⟶ F ⟶ i_* i^* F ⟶ 0` given by the counit of `j_! ⊣ j^*` and the unit of
`i^* ⊣ i_*` is short exact (`AlgebraicGeometry.ProEtale.shortExact_openClosedShortComplex`).
This is the pro-étale analogue of `AlgebraicGeometry.Etale.shortExact_openClosedShortComplex`;
it is checked after restriction to `Z` and to `U`, which jointly detect the vanishing of sheaves
(`AlgebraicGeometry.ProEtale.isZero_of_isZero_upperStar_of_isCompl`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R : Type (u + 1)) [Ring R] {Z U X : Scheme.{u}}
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]

/-- The short complex `j_! j^* F ⟶ F ⟶ i_* i^* F` of pro-étale sheaves of modules attached to a
closed immersion `i` and an open immersion `j` with disjoint ranges. -/
@[simps]
noncomputable def openClosedShortComplex
    (hij : Disjoint (Set.range i.base) (Set.range j.base))
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) :
    ShortComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) where
  X₁ := (j)_!open[ModuleCat.{u + 1} R].obj
    ((ProEtale.openImmersionRestriction (ModuleCat.{u + 1} R) j).obj F)
  X₂ := F
  X₃ := (i)_*[ModuleCat.{u + 1} R].obj ((i)^*[ModuleCat.{u + 1} R].obj F)
  f := (ProEtale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) j).counit.app F
  g := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app F
  zero := by
    rw [← (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit_naturality,
      (ProEtale.isZero_upperStar_openImmersionLowerShriek _ j i
        (Set.disjoint_iff_inter_eq_empty.1 hij.symm) _).eq_of_src
          ((i)^*[ModuleCat.{u + 1} R].map _) 0,
      Functor.map_zero, Limits.comp_zero]

variable [QuasiCompact j]

omit [IsOpenImmersion j] in
/-- The pullbacks to a closed immersion and to its quasi-compact open complement jointly detect
exactness of short complexes of pro-étale sheaves of modules. -/
lemma exact_of_exact_map_upperStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (S : ShortComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)))
    (hi : (S.map (i)^*[ModuleCat.{u + 1} R]).Exact)
    (hj : (S.map (j)^*[ModuleCat.{u + 1} R]).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology] at hi hj ⊢
  exact isZero_of_isZero_upperStar_of_isCompl i j hij _
    (hi.of_iso (S.mapHomologyIso _).symm) (hj.of_iso (S.mapHomologyIso _).symm)

/-- The open–closed sequence `0 ⟶ j_! j^* F ⟶ F ⟶ i_* i^* F ⟶ 0` on the pro-étale site is short
exact, for a closed immersion `i` with quasi-compact open complement `j`. -/
theorem shortExact_openClosedShortComplex
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) :
    (openClosedShortComplex R i j hij.disjoint F).ShortExact := by
  have hX₁ : IsZero ((i)^*[ModuleCat.{u + 1} R].obj ((j)_!open[ModuleCat.{u + 1} R].obj
      ((ProEtale.openImmersionRestriction (ModuleCat.{u + 1} R) j).obj F))) :=
    ProEtale.isZero_upperStar_openImmersionLowerShriek _ j i
      (Set.disjoint_iff_inter_eq_empty.1 hij.disjoint.symm) _
  have hX₃ : IsZero ((j)^*[ModuleCat.{u + 1} R].obj
      ((i)_*[ModuleCat.{u + 1} R].obj ((i)^*[ModuleCat.{u + 1} R].obj F))) :=
    isZero_upperStar_lowerStar_of_disjoint _ i j hij.disjoint _
  have hf : IsIso ((j)^*[ModuleCat.{u + 1} R].map
      ((ProEtale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) j).counit.app F)) := by
    rw [NatIso.isIso_map_iff (ProEtale.upperStarIsoOpenImmersionRestriction _ j)]
    infer_instance
  have hg : IsIso ((i)^*[ModuleCat.{u + 1} R].map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app F)) := by
    have h := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).left_triangle_components F
    have : IsIso ((i)^*[ModuleCat.{u + 1} R].map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app F) ≫
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).counit.app
          ((i)^*[ModuleCat.{u + 1} R].obj F)) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).counit.app _)
  have hmono : Mono
      ((ProEtale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) j).counit.app F) := by
    refine Preadditive.mono_of_isZero_kernel _
      (isZero_of_isZero_upperStar_of_isCompl i j hij _ ?_ ?_)
    · exact (hX₁.of_mono (kernel.ι ((i)^*[ModuleCat.{u + 1} R].map
        ((ProEtale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) j).counit.app
          F)))).of_iso (PreservesKernel.iso _ _)
    · exact (isZero_kernel_of_mono ((j)^*[ModuleCat.{u + 1} R].map
        ((ProEtale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) j).counit.app
          F))).of_iso (PreservesKernel.iso _ _)
  have hepi : Epi ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app F) := by
    refine Preadditive.epi_of_isZero_cokernel _
      (isZero_of_isZero_upperStar_of_isCompl i j hij _ ?_ ?_)
    · exact (isZero_cokernel_of_epi ((i)^*[ModuleCat.{u + 1} R].map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app F))).of_iso
          (PreservesCokernel.iso _ _)
    · exact (hX₃.of_epi (cokernel.π ((j)^*[ModuleCat.{u + 1} R].map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app F)))).of_iso
          (PreservesCokernel.iso _ _)
  refine { exact := exact_of_exact_map_upperStar_of_isCompl R i j hij _ ?_ ?_
           mono_f := hmono
           epi_g := hepi }
  · rw [ShortComplex.exact_iff_mono _ (hX₁.eq_of_src _ _)]
    exact inferInstanceAs (Mono ((i)^*[ModuleCat.{u + 1} R].map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app F)))
  · rw [ShortComplex.exact_iff_epi _ (hX₃.eq_of_tgt _ _)]
    exact inferInstanceAs (Epi ((j)^*[ModuleCat.{u + 1} R].map
      ((ProEtale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) j).counit.app F)))

end AlgebraicGeometry.ProEtale
