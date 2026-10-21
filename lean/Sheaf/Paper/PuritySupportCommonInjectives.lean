/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# A common injective model for etale/pro-etale comparison with support

Source: Stacks Project, proetale.tex, Tags 099V (2) and 09B1 (2)
(blueprint: lem-pur-support-comparison-common-injectives).

We use ordinary fixed-ring module sheaves, the presentation of constant-ring module
sheaves used by `Scheme.proEtaleSiteComparisonModules`. In this presentation direct
image is restriction itself, so the evaluation and support comparisons are equalities.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]

/-- A sheaf viewed as a bounded-below complex concentrated in degree zero.
Source: Stacks Project, Tag 099V (1), viewed as the special case of (2)
(blueprint: lem-pur-support-comparison-common-injectives). -/
noncomputable def supportComparisonSource
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    CochainComplex.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  ⟨(CochainComplex.singleFunctor _ 0).obj F, ⟨0, inferInstance⟩⟩

/-- The ordinary comparison unit followed by the direct image of the resolution map.
Source: Stacks Project, Tags 099V (2), 09B1 (2); the augmentation specified in the node
(blueprint: lem-pur-support-comparison-common-injectives). -/
noncomputable def supportComparisonAugmentation
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (J : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (h : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj
      (supportComparisonSource T A F) ⟶ J) :
    (supportComparisonSource T A F).obj ⟶
      ((comparisonLowerStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj J).obj :=
  (NatTrans.mapHomologicalComplex (T.proEtaleSiteComparisonModules A).unit (.up ℤ)).app
      (supportComparisonSource T A F).obj ≫
    ((comparisonLowerStar (ModuleCat.{u + 1} A) T).mapHomologicalComplex (.up ℤ)).map h.hom

/-- The derived direct image of the localized resolution map, with the canonical
factorization identifying localization of termwise inverse image with derived inverse image.
Source: Stacks Project, Tags 099V (2), 09B1 (2), and derived.tex Tag 05TI (2)
(blueprint: lem-pur-support-comparison-common-injectives). -/
noncomputable def supportComparisonDerivedResolutionMap
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (J : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (h : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj
      (supportComparisonSource T A F) ⟶ J) :=
  (comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctorPlus.map
    ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlusFactorsh.hom.app
        ((HomotopyCategory.Plus.quotient _).obj (supportComparisonSource T A F)) ≫
      DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient _).map h))

/-- Every resolution on the pro-etale site gives the specified common injective model,
including its derived-unit normalization and literal evaluation and support kernels.
Source: Stacks Project, proetale.tex, Tags 099V (2), 09B1 (2)
(blueprint: lem-pur-support-comparison-common-injectives).

Proof:
1. In the common larger universe, the module-sheaf categories are Grothendieck abelian
(`lem-weil-pbc-ring-sheaves-grothendieck`), hence have enough injectives
(`lem-sp-grothendieck-enough-injectives`). Apply bounded-below injective resolution
existence (`lem-sc-bounded-below-injective-resolution-existence`) to the termwise inverse
image of the degree-zero complex. This gives the first conjunct; fix any such resolution.
2. The comparison inverse image is additive and exact (`lem-sf-comparison-pullback-exact`).
The right adjoint therefore preserves injectives (`lem-sp-right-adjoint-preserves-injectives`).
Termwise direct image preserves the lower bound and the displayed augmentation is the
ordinary unit followed by direct image of the resolution map.
3. The canonical comparison alpha is invertible on the bounded-below injective complex
(`lem-weil-pbc-right-derived-plus-injective`), as is the derived image of the localized
quasi-isomorphism h. Thus theta = alpha followed by the inverse of R(Qh) is an isomorphism.
The normalization equation of `lem-pur-comparison-unit-injective-model` says exactly that
Qa followed by theta is the derived unit. The equation theta followed by R(Qh) = alpha
below characterizes this same canonical theta, rather than an arbitrary isomorphism.
4. The derived unit is invertible by `thm-weil-pbc-site-comparison`, so Qa is invertible
and a is a quasi-isomorphism. Together with step 2 this gives the etale injective resolution.
5. Direct image is restriction along `Scheme.toProEt T`, identity on schemes and arrows.
Consequently evaluation gives identical complexes, restriction arrows and differentials.
Apply this to the terminal object and the open complement of any closed immersion:
`def-pur-support-cohomology` takes the kernel of that very restriction map. These kernels,
their differentials and their kernel inclusions are literally identical. No constructibility,
local freeness or finite generation of F enters any step. -/
theorem supportComparisonCommonInjectives
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (∃ (J : CochainComplex.Plus
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
      (h : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj
        (supportComparisonSource T A F) ⟶ J),
      QuasiIso h.hom ∧ ∀ n : ℤ, Injective (J.obj.X n)) ∧
    ∀ (J : CochainComplex.Plus
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
      (h : (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj
        (supportComparisonSource T A F) ⟶ J),
      QuasiIso h.hom → (∀ n : ℤ, Injective (J.obj.X n)) →
      (∀ n : ℤ, Injective
        (((comparisonLowerStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj J).obj.X n)) ∧
      QuasiIso (supportComparisonAugmentation T A F J h) ∧
      (∃ θ : DerivedCategory.Plus.Q.obj
          ((comparisonLowerStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj J) ≅
        (comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctorPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus.obj
            (DerivedCategory.Plus.Q.obj (supportComparisonSource T A F))),
        θ.hom ≫ supportComparisonDerivedResolutionMap T A F J h =
          (comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient _).obj J) ∧
        DerivedCategory.Plus.Q.map
            (ObjectProperty.homMk (supportComparisonAugmentation T A F J h)) ≫ θ.hom =
          (derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} A) T).unit.app
            (DerivedCategory.Plus.Q.obj (supportComparisonSource T A F))) ∧
      (∀ W : T.Etale,
        (((sheafSections T.smallEtaleTopology
            (ModuleCat.{u + 1} A)).obj (op W)).mapHomologicalComplex (.up ℤ)).obj
            ((comparisonLowerStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj J).obj =
          (((sheafSections (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).obj
            (op ((Scheme.toProEt T).obj W))).mapHomologicalComplex (.up ℤ)).obj J.obj) ∧
      (∀ (W₁ W₂ : T.Etale) (f : W₁ ⟶ W₂) (n : ℤ),
        ((((comparisonLowerStar
              (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj J).obj.X n).obj.map
          f.op) =
          (J.obj.X n).obj.map ((Scheme.toProEt T).map f).op) ∧
      (∀ (C : Scheme.{u}) (i : C ⟶ T) [IsClosedImmersion i],
        ((Sheaf.supportedSectionsFunctor T.smallEtaleTopology (ModuleCat.{u + 1} A)
            (Etale.supportRestrictionArrow i)).mapHomologicalComplex (.up ℤ)).obj
            ((comparisonLowerStar (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj J).obj =
          ((supportSections i A).mapHomologicalComplex (.up ℤ)).obj J.obj) ∧
      (∀ (C : Scheme.{u}) (i : C ⟶ T) [IsClosedImmersion i] (n : ℤ),
        kernel.ι
            ((((comparisonLowerStar
              (ModuleCat.{u + 1} A) T).mapCochainComplexPlus.obj J).obj.X n).obj.map
               (Etale.supportRestrictionArrow i).op) =
          kernel.ι ((J.obj.X n).obj.map (supportRestrictionArrow i).op)) := by
  let E := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)
  let P := Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)
  let L := comparisonUpperStar (ModuleCat.{u + 1} A) T
  let R := comparisonLowerStar (ModuleCat.{u + 1} A) T
  let M := supportComparisonSource T A F
  refine ⟨?_, ?_⟩
  · let K := L.mapCochainComplexPlus.obj M
    obtain ⟨n, hn⟩ := K.property
    have : K.obj.IsStrictlyGE n := hn
    obtain ⟨J, _, h, hh⟩ := CochainComplex.Plus.exists_quasiIso_injective K n
    refine ⟨(InjectiveObject.ι P).mapCochainComplexPlus.obj J, h, hh, ?_⟩
    intro n
    exact (J.obj.X n).property
  · intro J h hh hJ
    have : QuasiIso h.hom := hh
    let : ∀ n : ℤ, Injective (J.obj.X n) := hJ
    have : R.PreservesInjectiveObjects :=
      Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits
        (comparisonAdjunction (ModuleCat.{u + 1} A) T)
    have hinj : ∀ n : ℤ, Injective
        ((R.mapCochainComplexPlus.obj J).obj.X n) := fun n ↦ R.injective_obj_of_injective (hJ n)
    let K := (HomotopyCategory.Plus.quotient E).obj M
    let qh := (HomotopyCategory.Plus.quotient P).map h
    have hqh : IsIso (DerivedCategory.Plus.Qh.map qh) := by
      apply Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso P)
      exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hh
    let b := supportComparisonDerivedResolutionMap T A F J h
    have hb : IsIso b := by
      dsimp [b, supportComparisonDerivedResolutionMap]
      infer_instance
    let α := R.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient P).obj J)
    have hα : IsIso α := by
      dsimp [α]
      infer_instance
    let θ := asIso α ≪≫ (asIso b).symm
    have hθ : θ.hom ≫ b = α := by simp [θ]
    set_option backward.isDefEq.respectTransparency false in
    have hfac :
        DerivedCategory.Plus.Q.map
            (ObjectProperty.homMk (supportComparisonAugmentation T A F J h)) ≫ α =
          (derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} A) T).unit.app
            (DerivedCategory.Plus.Q.obj M) ≫ b := by
      have hunit := (comparisonAdjunction (ModuleCat.{u + 1} A) T).derivedPlus_unit_app_fac K
      have hnat := R.rightDerivedFunctorPlusUnit.naturality qh
      change DerivedCategory.Plus.Qh.map (R.mapHomotopyCategoryPlus.map qh) ≫ α =
        R.rightDerivedFunctorPlusUnit.app (L.mapHomotopyCategoryPlus.obj K) ≫
          R.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map qh) at hnat
      change _ = (comparisonAdjunction (ModuleCat.{u + 1} A) T).derivedAdjunctionPlus.unit.app _ ≫ b
      rw [(comparisonAdjunction (ModuleCat.{u + 1} A) T).derivedAdjunctionPlus_eq_derivedPlus]
      dsimp only [b, supportComparisonDerivedResolutionMap]
      rw [Functor.map_comp, ← Category.assoc, hunit, Category.assoc, ← hnat,
        ← Category.assoc, ← Functor.map_comp]
      change DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient E).map
            (ObjectProperty.homMk (supportComparisonAugmentation T A F J h))) ≫ α = _
      apply congrArg (fun f ↦ DerivedCategory.Plus.Qh.map f ≫ α)
      apply (HomotopyCategory.Plus.ι E).map_injective
      rw [Functor.map_comp, Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app]
      change (HomotopyCategory.quotient E (.up ℤ)).map
          (supportComparisonAugmentation T A F J h) =
        ((comparisonAdjunction (ModuleCat.{u + 1} A) T).mapHomotopyCategory (.up ℤ)).unit.app
          ((HomotopyCategory.quotient E (.up ℤ)).obj M.obj) ≫
        (R.mapHomotopyCategory (.up ℤ)).map
          ((HomotopyCategory.quotient P (.up ℤ)).map h.hom)
      rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
      dsimp [supportComparisonAugmentation]
      rw [Functor.map_comp]
      rfl
    have hnorm :
        DerivedCategory.Plus.Q.map
            (ObjectProperty.homMk (supportComparisonAugmentation T A F J h)) ≫ θ.hom =
          (derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} A) T).unit.app
            (DerivedCategory.Plus.Q.obj M) := by
      apply (cancel_mono b).1
      simpa only [Category.assoc, hθ] using hfac
    have hqa : IsIso (DerivedCategory.Plus.Q.map
        (ObjectProperty.homMk (supportComparisonAugmentation T A F J h))) := by
      have := isIso_compactSupportComparisonUnit T A
      have hcomp : IsIso (DerivedCategory.Plus.Q.map
          (ObjectProperty.homMk (supportComparisonAugmentation T A F J h)) ≫ θ.hom) := by
        rw [hnorm]
        infer_instance
      exact IsIso.of_isIso_comp_right _ θ.hom
    have ha : QuasiIso (supportComparisonAugmentation T A F J h) := by
      apply (DerivedCategory.isIso_Q_map_iff_quasiIso E _).1
      exact (DerivedCategory.Plus.ι (C := E)).map_isIso
        (DerivedCategory.Plus.Q.map
          (ObjectProperty.homMk (supportComparisonAugmentation T A F J h)))
    refine ⟨hinj, ha, ⟨θ, hθ, hnorm⟩, ?_, ?_, ?_, ?_⟩
    · intro W
      rfl
    · intro W₁ W₂ f n
      rfl
    · intro C i hi
      rfl
    · intro C i hi n
      rfl

end AlgebraicGeometry.ProEtale
