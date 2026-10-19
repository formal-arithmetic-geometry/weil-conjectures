/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.LiftToFinset

/-!
# Higher direct images commute with filtered colimits and direct sums

Source: Weil conjectures blueprint, snapshot main-20261015,
sec-proetale-coefficients/sk-cor-pe-bounded-continuity/
sk-lem-proper-heart-continuity-direct-image.md
(blueprint: det-proper-heart-continuity-direct-image).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

private theorem ringDerivedDirectImage_additive {X Y : Scheme.{u}} (p : X ⟶ Y)
    (A : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}) :
    (Scheme.ProEt.ringDerivedDirectImage p A).Additive := by
  -- The localization restricted to K-injectives is full and essentially surjective.
  let C := SheafOfModules.{u + 1} A
  let F := Scheme.ProEt.ringModuleDirectImage p A
  let h := Scheme.ProEt.ringModuleDirectImage_hasKInjectiveResolutions A
  let R := Scheme.ProEt.ringDerivedDirectImage p A
  let K := HomotopyCategory.KInjectives.Qh (C := C)
  have : K.EssSurj := by
    constructor
    intro Z
    obtain ⟨L, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := DerivedCategory.Qh) Z
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨I, s, hI, hs⟩ := h L
    have := hI
    have := hs
    have : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map s)) := by
      exact Localization.inverts DerivedCategory.Qh
        (HomotopyCategory.quasiIso C (.up ℤ))
        ((HomotopyCategory.quotient C (.up ℤ)).map s)
        (by simpa [HomotopyCategory.quotient_map_mem_quasiIso_iff])
    exact ⟨HomotopyCategory.KInjectives.mk I,
      ⟨(asIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (.up ℤ)).map s))).symm ≪≫ e⟩⟩
  -- On this subcategory the derived unit identifies R with an additive functor.
  let α := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h
  have : IsIso (Functor.whiskerLeft (HomotopyCategory.KInjectives.ι (C := C)) α) := by
    exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun I ↦ by
      obtain ⟨I, hI, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective I
      exact F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h I)
  have : (HomotopyCategory.KInjectives.ι (C := C) ⋙
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).Additive := by
    dsimp [HomotopyCategory.KInjectives.ι]
    infer_instance
  have : (K ⋙ R).Additive :=
    Functor.additive_of_iso
      (asIso (Functor.whiskerLeft (HomotopyCategory.KInjectives.ι (C := C)) α) ≪≫
        (Functor.associator _ _ _).symm)
  have : K.Additive := by
    dsimp [K, HomotopyCategory.KInjectives.Qh, HomotopyCategory.KInjectives.ι]
    infer_instance
  exact Functor.additive_of_full_essSurj_comp K R

/-- For a quasi-compact, quasi-separated morphism, every integer-degree higher direct
image on pro-étale module sheaves preserves filtered colimits and direct sums. The target
is the category of modules over the direct-image ring sheaf `p_*A`. The input is placed
in degree zero before localization, right derivation and degree-`q` cohomology.

Source: Weil conjectures blueprint, snapshot main-20261015,
sec-proetale-coefficients/sk-cor-pe-bounded-continuity/
sk-lem-proper-heart-continuity-direct-image.md and its unit's Complement;
Stacks Project, derived.tex, Tags 015A, 05TH and 013P for the finite-sum calculation
(blueprint: det-proper-heart-continuity-direct-image).

Proof for stage 3:
1. For a filtered diagram `M`, put `K_i = M_i[0]`, with common lower bound zero.
   Module-sheaf colimits agree with underlying abelian-sheaf colimits by
   lem-weil-pbc-module-sheaves-colimits-forgetful, so the termwise colimit is
   `(colim M)[0]`. Apply det-pe-bounded-continuity-direct-image at bound zero.
   Its comparison on each leg is higher direct image of the colimit inclusion.
   Thus it is the canonical `colimit.post` displayed here, in `p_*A`-modules.
2. For a finite family choose bounded-below termwise injective K-injective resolutions
   of the degree-zero inputs as in lem-sc-bounded-below-injective-resolution, on the
   small site model. For arbitrary rings one may use the already published
   `Scheme.ProEt.ringModuleDirectImage_hasKInjectiveResolutions`: boundedness of the
   chosen resolutions is unnecessary in this finite-sum calculation. Finite sums are
   K-injective: component null-homotopies assemble into a finite tuple. Cohomology
   of the block-diagonal differential is the finite sum of the cohomologies, so the
   summed resolution is a quasi-isomorphism, also for the empty family. The sectionwise
   pushforward of det-pe-topos-functoriality-inverse-image preserves finite biproducts.
   Computing the derived functor on these resolutions gives finite-sum preservation.
   Naturality of the derived unit identifies the maps with higher direct images of
   summand inclusions, compatibly with inclusion of one finite subsum in another.
3. The poset of finite subsets of a small set `J`, including the empty subset, is
   small and filtered, with union as an upper bound. The colimit of its finite subsums
   is the whole sum: cocones are exactly families of maps from the individual summands.
   Apply this universal-property description in both module-sheaf categories, whose
   colimits exist by lem-weil-pbc-module-sheaves-colimits-forgetful.
4. Apply Step 1 to the finite-subsum diagram and combine Steps 2 and 3. On each original
   summand the resulting isomorphism is higher direct image of its coproduct inclusion,
   so it is the canonical coproduct comparison. This includes the empty family. -/
theorem properHeartContinuityDirectImage {X Y : Scheme.{u}} (p : X ⟶ Y)
    [QuasiCompact p] [QuasiSeparated p]
    (A : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}) :
    ∀ (q : ℤ),
      (∀ {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
        (M : I ⥤ SheafOfModules.{u + 1} A),
        IsIso (colimit.post M
          (CochainComplex.singleFunctor (SheafOfModules.{u + 1} A) 0 ⋙
            DerivedCategory.Q ⋙ Scheme.ProEt.ringHigherDirectImage p A q))) ∧
      ∀ (J : Type (u + 1)),
        PreservesColimitsOfShape (Discrete J)
          (CochainComplex.singleFunctor (SheafOfModules.{u + 1} A) 0 ⋙
            DerivedCategory.Q ⋙ Scheme.ProEt.ringHigherDirectImage p A q) := by
  intro q
  have hfiltered {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
      (M : I ⥤ SheafOfModules.{u + 1} A) :
      IsIso (colimit.post M
        (CochainComplex.singleFunctor (SheafOfModules.{u + 1} A) 0 ⋙
          DerivedCategory.Q ⋙ Scheme.ProEt.ringHigherDirectImage p A q)) := by
    let D : I ⥤ CochainComplex (SheafOfModules.{u + 1} A) ℤ :=
      M ⋙ CochainComplex.singleFunctor (SheafOfModules.{u + 1} A) 0
    have hD : ∀ i : I, ∀ n : ℤ, n < 0 → IsZero ((D.obj i).X n) := by
      intro i n hn
      have hne : n ≠ 0 := by omega
      exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) _ _ _ hne
    have : IsIso (colimit.post D
        (DerivedCategory.Q ⋙ Scheme.ProEt.ringHigherDirectImage p A q)) :=
      AlgebraicGeometry.Scheme.ProEt.boundedContinuityDirectImage p A D 0 hD q
    have hsingleP : PreservesColimitsOfShape I
        (CochainComplex.singleFunctor (SheafOfModules.{u + 1} A) 0) := by
      change PreservesColimitsOfShape I
        (HomologicalComplex.single (SheafOfModules.{u + 1} A) (ComplexShape.up ℤ) 0)
      infer_instance
    let := hsingleP
    have hsingle : IsIso (colimit.post M
        (CochainComplex.singleFunctor (SheafOfModules.{u + 1} A) 0)) := by
      infer_instance
    rw [← colimit.post_post]
    infer_instance
  constructor
  · exact hfiltered
  · intro J
    let F := CochainComplex.singleFunctor (SheafOfModules.{u + 1} A) 0 ⋙
      DerivedCategory.Q ⋙ Scheme.ProEt.ringHigherDirectImage p A q
    have : (Scheme.ProEt.ringDerivedDirectImage p A).Additive :=
      ringDerivedDirectImage_additive p A
    have : F.Additive := by dsimp [F, Scheme.ProEt.ringHigherDirectImage]; infer_instance
    have : PreservesColimitsOfShape (Finset (Discrete J)) F := by
      constructor
      intro M
      have := hfiltered M
      exact preservesColimit_of_isIso_post F M
    exact preservesColimitsOfShape_discrete_of_preservesColimitsOfShape_finset J F

end AlgebraicGeometry.ProEtale
