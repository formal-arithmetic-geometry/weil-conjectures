/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import Sheaf.Paper.ProEtaleConstantModulePullbackEncoding
import WeilConjectures.ConstructibleSheaf.OpenCover
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Constructible interval descent on a finite open cover

Source: blueprint main-20261015, thm-pur-general-admissibility.proof.md, Step 4;
Stacks Project, etale-cohomology.tex, Tags 095E and 095F
(blueprint: lem-pur-finite-open-interval-descent).
-/

@[expose] public section
set_option autoImplicit false
universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

private theorem fixed_constructible_open_descent
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X]
    {J : Type v} [Finite J] (U : J → X.Opens)
    (hcover : ∀ x : X, ∃ t : J, x ∈ U t)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))
    (hF : ∀ t, ProEtale.IsConstructible A
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) (U t).ι).obj F)) :
    ProEtale.IsConstructible A F := by
  let D := ModuleCat.{u + 1} A
  let R := (DerivedCategory.singleFunctor _ 0).obj F
  have hR : DerivedCategory.TStructure.t.plus
      ((ProEtale.comparisonLowerStar D X).rightDerivedFunctor.obj R) := by
    have := Functor.isGE_rightDerivedFunctor_obj_singleFunctor
      (ProEtale.comparisonLowerStar D X) F
    exact ⟨0, inferInstance⟩
  have hloc : ∀ t, ∃ N, Nonempty
      ((ProEtale.upperStar D (U t).ι).mapDerivedCategory.obj R ≅
        (ProEtale.comparisonUpperStar D (U t).toScheme).mapDerivedCategory.obj N) := by
    intro t
    obtain ⟨G, _, ⟨e⟩⟩ :=
      ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A (hF t)
    refine ⟨(DerivedCategory.singleFunctor _ 0).obj G, ⟨?_⟩⟩
    exact ((ProEtale.upperStar D (U t).ι).mapDerivedCategorySingleFunctor 0).app F ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso e.symm ≪≫
      (((ProEtale.comparisonUpperStar D (U t).toScheme).mapDerivedCategorySingleFunctor 0).app
        G).symm
  have := ProEtale.isIso_derivedComparisonAdjunction_counit_app_of_openCover
    D U hcover R hR hloc
  let M := (ProEtale.comparisonLowerStar D X).rightDerivedFunctor.obj R
  let G := (DerivedCategory.homologyFunctor _ 0).obj M
  let e : (ProEtale.comparisonUpperStar D X).obj G ≅ F :=
    ((ProEtale.comparisonUpperStar D X).mapDerivedCategoryHomologyFunctorIso 0).app M ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapIso
        (asIso ((ProEtale.derivedComparisonAdjunction D X).counit.app R)) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F
  have hG : IsConstructibleSheaf G := by
    apply IsConstructibleSheaf.of_iSup_eq_top U
      (eq_top_iff.mpr (fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr (hcover x)))
    intro t
    obtain ⟨G', hG', ⟨e'⟩⟩ :=
      ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A (hF t)
    have := hG'
    exact IsConstructibleSheaf.of_iso
      ((ProEtale.comparisonUpperStar D (U t).toScheme).preimageIso
        (e' ≪≫ (ProEtale.upperStar D (U t).ι).mapIso e.symm ≪≫
          ((ProEtale.comparisonUpperStarCompUpperStarIso D (U t).ι).app G)))
  have := hG
  exact ProEtale.isConstructible_of_iso e
    (ProEtale.isConstructible_comparisonUpperStar_obj G)

private theorem intrinsic_constructible_of_iso
    {X : Scheme.{u}} (A : Type u) [CommRing A] [Finite A]
    {F G : proEtaleRingModules X (proEtaleConstantRing X A)} (e : F ≅ G)
    (hF : IsConstructibleProEtaleModuleSheaf X A F) :
    IsConstructibleProEtaleModuleSheaf X A G := by
  apply (proEtaleModuleRestriction_constructible_iff X A G).mpr
  exact ProEtale.isConstructible_of_iso
    ((proEtaleModuleRestriction X A).mapIso e)
    ((proEtaleModuleRestriction_constructible_iff X A F).mp hF)

private theorem intrinsic_sheaf_open_descent
    (A : Type u) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X]
    {J : Type v} [Finite J] (U : J → X.Opens)
    (hcover : ∀ x : X, ∃ t : J, x ∈ U t)
    (F : proEtaleRingModules X (proEtaleConstantRing X A)) :
    ((∀ t, IsConstructibleProEtaleModuleSheaf (U t).toScheme A
        ((proEtaleConstantRingPullback A (U t).ι).obj F)) →
      IsConstructibleProEtaleModuleSheaf X A F) ∧
    ((∀ t, IsZero ((proEtaleConstantRingPullback A (U t).ι).obj F)) → IsZero F) := by
  let E := proEtaleModuleRestriction X A
  let := proEtaleModuleRestriction_isEquivalence X A
  have : E.Additive := by
    constructor
    intro M N f g
    ext V x
    rfl
  have e (t : J) :
      (proEtaleModuleRestriction (U t).toScheme A).obj
          ((proEtaleConstantRingPullback A (U t).ι).obj F) ≅
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (U t).ι).obj
          (E.obj F) :=
    (proEtaleModuleRestriction_pullback (U t).ι A F).some
  constructor
  · intro hF
    apply (proEtaleModuleRestriction_constructible_iff X A F).mpr
    apply fixed_constructible_open_descent (ULift.{u + 1, u} A) X U hcover
    intro t
    exact ProEtale.isConstructible_of_iso (e t)
      ((proEtaleModuleRestriction_constructible_iff (U t).toScheme A _).mp (hF t))
  · intro hF
    have hEF : IsZero (E.obj F) :=
      ProEtale.isZero_of_forall_isZero_upperStar_obj
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U hcover _ (fun t ↦ by
          let := proEtaleModuleRestriction_isEquivalence (U t).toScheme A
          have : (proEtaleModuleRestriction (U t).toScheme A).Additive := by
            constructor
            intro M N f g
            ext V x
            rfl
          exact ((proEtaleModuleRestriction (U t).toScheme A).map_isZero (hF t)).of_iso
            (e t).symm)
    apply (IsZero.iff_id_eq_zero _).mpr
    apply E.map_injective
    exact hEF.eq_of_src _ _

/-- Constructible cohomological bounds descend on a finite open cover, without any
boundedness, etale-origin or Tor assumption on the ambient complex. The second clause
allows different bounded constructible intervals on different cover members. The last
clause records the empty-scheme convention as a categorical zero object.
Source: blueprint main-20261015, thm-pur-general-admissibility, Step 4; Stacks Project,
etale-cohomology.tex, Tags 095E/095F
(blueprint: lem-pur-finite-open-interval-descent).

Proof:
1. Finite type over the field makes X Noetherian and quasi-separated, by
lem-weil-pbc-finite-type-over-noetherian and lem-weil-pbc-locally-noetherian-quasi-separated.
Use lem-weil-pbc-affine-opens-basis and quasi-compactness to refine to a finite affine
cover subordinate to the given cover; no separatedness or affine intersections are needed.
2. By lem-weil-proetale-weakly-etale-localization and
lem-sfb-proetale-object-inverse-image-restriction, pullback to an open is site restriction.
By lem-pur-site-restriction-module-adjunction-exact it is exact, so termwise restriction
computes derived restriction on arbitrary complexes and commutes with every cohomology
sheaf (def-weil-derived-cohomology-sheaves).
3. The open cover is a pro-etale cover: on every affine open choose a finite affine
refinement. Outside [r,s] all restricted cohomology sheaves vanish. Apply covering-family
vanishing in lem-cbc-proetale-stalk-conservative, without geometric-stalk conservativity.
4. Local constancy with finite stalks is preserved by any scheme pullback. Indeed choose
trivializing members (def-weil-proetale-locally-constant-sheaf), discard empty ones, and
use lem-pur-proetale-inverse-image-stalk, lem-pe-constant-left-module-inverse-image and
lem-weil-proetale-constant-sheaf-stalk to see the constant models are finite. Base change
of their covers (lem-exc-proetale-pullback-locally-constant) and
lem-weil-pbc-proetale-finite-model-stalks prove the assertion.
5. Intersect each chart's finite constructible locally closed partition with the finite
affine refinement. Noetherianity makes these strata constructible. Inverse images compose
by lem-weil-pbc-site-morphism-composition and lem-pe-constant-left-module-inverse-image,
so step 4 preserves the required local constancy and finite stalks on these strata.
6. Apply lem-weil-pbc-etale-stratification-local-gluing-core to get a finite global
immersed stratification factoring through chart strata. Pull back along these actual
factorizations and use step 4. This proves constructibility of each cohomology sheaf.
7. Step 3 gives vanishing outside the finite interval; steps 5--6 give constructibility
inside it, and zero sheaves are constructible. This is exactly
 def-weil-finite-torsion-constructibility and def-weil-constructible-intervals.
8. For bounded constructible restrictions and a nonempty finite index set choose local
intervals, take their minimum lower and maximum upper endpoints, and apply steps 1--7.
For the empty scheme the empty family covers the final pro-etale object. Cover detection
makes every module sheaf zero and every derived morphism invertible, hence F is zero.
Its cohomology vanishes in every degree and the empty partition is constructible. This
also handles the empty cover and every displayed interval. -/
theorem purityFiniteOpenIntervalDescent
    (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
    (J : Type v) [Finite J] (U : J → X.Opens)
    (hcover : ∀ x : X, ∃ t : J, x ∈ U t)
    (F : proEtaleDerivedCategory X P.Ring) :
    (∀ r s : ℤ, r ≤ s →
      (∀ t : J, constructibleInterval P.coefficients.l P.extension P.level P.level_pos
        (U t).toScheme r s
        ((proEtaleConstantRingDerivedPullback P.Ring (U t).ι).obj F)) →
      constructibleInterval P.coefficients.l P.extension P.level P.level_pos X r s F) ∧
    ((∀ t : J, intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos (U t).toScheme
        ((proEtaleConstantRingDerivedPullback P.Ring (U t).ι).obj F)) →
      intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        P.level P.level_pos X F) ∧
    (IsEmpty X → IsZero F) := by
  classical
  let : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of P.field.k))
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of P.field.k))
  let : IsNoetherian X := {}
  let H (i : ℤ) := (DerivedCategory.homologyFunctor
    (proEtaleRingModules X (proEtaleConstantRing X P.Ring)) i).obj F
  let Ht (t : J) (i : ℤ) := (DerivedCategory.homologyFunctor
    (proEtaleRingModules (U t).toScheme (proEtaleConstantRing (U t).toScheme P.Ring)) i).obj
      ((proEtaleConstantRingDerivedPullback P.Ring (U t).ι).obj F)
  have e (t : J) (i : ℤ) :
      (proEtaleConstantRingPullback P.Ring (U t).ι).obj (H i) ≅ Ht t i :=
    ((proEtaleConstantRingPullback P.Ring (U t).ι).mapDerivedCategoryHomologyFunctorIso i).app F
  have hz (i : ℤ) (h : ∀ t, IsZero (Ht t i)) : IsZero (H i) :=
    (intrinsic_sheaf_open_descent P.Ring X U hcover (H i)).2
      (fun t ↦ (h t).of_iso (e t i))
  have hc (i : ℤ) (h : ∀ t, IsConstructibleProEtaleModuleSheaf (U t).toScheme
      P.Ring (Ht t i)) : IsConstructibleProEtaleModuleSheaf X P.Ring (H i) :=
    (intrinsic_sheaf_open_descent P.Ring X U hcover (H i)).1
      (fun t ↦ intrinsic_constructible_of_iso P.Ring (e t i).symm (h t))
  refine ⟨?_, ?_, ?_⟩
  · intro r s _ hF
    have hs : proEtaleCohomologicalSupport F ⊆ Set.Icc r s := by
      intro i hi
      by_contra hout
      apply hi
      exact hz i (fun t ↦ by
        by_contra hti
        exact hout ((hF t).2 hti))
    exact ⟨⟨(Set.finite_Icc r s).subset hs, fun i ↦ hc i (fun t ↦ (hF t).1.2 i)⟩, hs⟩
  · intro hF
    have hf : Set.Finite (⋃ t, {i : ℤ | ¬ IsZero (Ht t i)}) :=
      Set.finite_iUnion (fun t ↦ (hF t).1)
    refine ⟨hf.subset ?_, fun i ↦ hc i (fun t ↦ (hF t).2 i)⟩
    intro i hi
    by_contra hout
    apply hi
    exact hz i (fun t ↦ by
      by_contra hti
      exact hout (Set.mem_iUnion.mpr ⟨t, hti⟩))
  · intro hX
    let := hX
    apply DerivedCategory.isZero_of_forall_isZero_homology
    intro i
    exact (intrinsic_sheaf_open_descent P.Ring X
      (fun t : Fin 0 ↦ Fin.elim0 t) (fun x ↦ isEmptyElim x) (H i)).2
        (fun t ↦ Fin.elim0 t)

end WeilConjectures
