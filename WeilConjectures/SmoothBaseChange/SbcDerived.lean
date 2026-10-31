/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClassicalDerivedDefinitions
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ClassicalDefinition
public import WeilConjectures.AlgebraicGeometry.SbcExchangeCompatibility
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.AlgebraicGeometry.BoundedDerivedSmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.BoundedAllowableTorsionSmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange

import WeilConjectures.AlgebraicGeometry.ClassicalDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.BoundedBelowProEtaleComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheaves

/-!
# Smooth base change for classical torsion complexes

Source: literature/blueprint/latest/blueprint/sec-smooth-base-change/
`sk-thm-sbc-derived/_section.md` (blueprint: sk-thm-sbc-derived).

The main declarations state the classical derived assertion and its sheaf consequence.
The complementary clauses reuse the publicly imported declarations
`Etale.isIso_derivedBaseChangeMap_of_boundedConstructible_of_smooth`,
`Etale.isIso_abelianDerivedBaseChangeArrow_of_bounded_allowable_torsion`, and
`Etale.boundedBelow_derived_smooth_baseChange`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

private theorem classicalModule_transport (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ]
    {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (e : F ≅ G) (hF : IsClassicalModuleFor X Λ F) : IsClassicalModuleFor X Λ G := by
  intro I _ _ P
  have hmap := continuityMap_natural P e.hom.hom
  have : IsIso (continuityMap P F.obj) := hF P
  have : IsIso (Functor.whiskerLeft P.diagram.op e.hom.hom) := by
    change IsIso (Functor.isoWhiskerLeft P.diagram.op
      ((sheafToPresheaf _ _).mapIso e)).hom
    infer_instance
  apply (isIso_comp_left_iff
    (colimMap (Functor.whiskerLeft P.diagram.op e.hom.hom)) _).mp
  rw [hmap]
  infer_instance

private theorem classicalComplex_transport (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ]
    {K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (e : K ≅ L) (hK : IsClassicalComplexFor X Λ K) : IsClassicalComplexFor X Λ L := by
  intro q
  exact classicalModule_transport X Λ
    ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q).mapIso
      ((ShrinkHoms.equivalence _).inverse.mapIso e)) (hK q)

/-- Smooth base change for bounded-below classical pro-étale complexes with discrete
coefficients killed by an integer invertible on the base.

Source: literature/blueprint/latest/blueprint/sec-smooth-base-change/
`sk-thm-sbc-derived/_section.md` (blueprint: sk-thm-sbc-derived).

Proof:
1. The additive order of a coefficient divides n in ℤ. Mapping this divisibility to
   the base section ring shows that this order is a unit, including when n = 0 or n < 0.
   Apply the arbitrary-ring bounded-below étale smooth base-change theorem.
2. The invertible comparison unit and classical derived equivalence give an étale
   origin L = Rν_* K and its invertible counit ν^* L → K.
3. Base-change permanence makes f' qcqs. The existing arbitrary-coefficient theorem
   `comparison_derivedBaseChangeMap` identifies the étale and pro-étale exchanges under
   the canonical source and target comparison isomorphisms. Its statement applies to
   the coefficient universe here, unlike the ULift-only packaged discrete site clause
   of `sbcExchangeCompatibility`. Conjugation and naturality at the counit make the
   specified pro-étale exchange at K invertible.
4. Its source is isomorphic to ν^* of the bounded-below étale source, so it is classical
   by the classical derived equivalence. Continuity-map naturality makes classicality
   invariant under isomorphisms. Exact inverse image and right-derived Plus compatibility
   identify the ambient source with the stated bounded-below source.
5. Transport classicality through the invertible exchange and the analogous target
   compatibility maps. Since the classical subcategory is full, it contains the inverse.
6. For the sheaf consequence, the classical sheaf equivalence writes F as ν^* M.
   Exact inverse image commutes with the degree-zero single functor, so F[0] is classical.
   Apply the result and then the homology functor in every integer degree.
7. The complement remains the three publicly imported existing derived theorems, with
   their coefficient and boundedness conventions.
-/
theorem smoothBaseChangeDerived
    (Λ : Type (u + 1)) [CommRing Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback u' f' f g)
    [Smooth g] [QuasiCompact f] [QuasiSeparated f]
    (n : ℤ) (hnΛ : ∀ a : Λ, n • a = 0)
    (hnY : IsUnit (n : Γ(Y, ⊤)))
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hK : ClassicalPlus X Λ K) :
    ClassicalPlus Y' Λ
        ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.obj
          ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj K)) ∧
      ClassicalPlus Y' Λ
        ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f').rightDerivedFunctorPlus.obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) u').mapDerivedCategoryPlus.obj K)) ∧
      IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
        sq.toCommSq).app (DerivedCategory.Plus.ι.obj K)) := by
  have hu (Z : Scheme.{u}) := (boundedBelowComparison Z Λ).1
  have he (Z : Scheme.{u}) := classicalDerivedEquivalence Z Λ
    (fun L ↦ by let := hu Z; infer_instance)
  have hε := (he X).2.1 K hK
  let L := (comparisonLowerStar (ModuleCat.{u + 1} Λ) X).rightDerivedFunctorPlus.obj K
  let eK : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj L.obj ≅
      K.obj :=
    ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlusCompatibility.app
      L).symm ≪≫ DerivedCategory.Plus.ι.mapIso
        (asIso ((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus.counit.app K))
  have : QuasiCompact f' := MorphismProperty.of_isPullback
    (P := @QuasiCompact) sq inferInstance
  have : QuasiSeparated f' := MorphismProperty.of_isPullback
    (P := @QuasiSeparated) sq inferInstance
  have htor (a : Λ) : IsUnit (addOrderOf a : Γ(Y, ⊤)) := by
    have hd : (addOrderOf a : ℤ) ∣ n := addOrderOf_dvd_iff_zsmul_eq_zero.mpr (hnΛ a)
    exact isUnit_of_dvd_unit (by simpa using map_dvd (Int.castRingHom Γ(Y, ⊤)) hd) hnY
  have hBC : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L) := by
    have := Etale.isIso_baseChange_of_smooth_of_ring_order_invertible Λ sq htor
    infer_instance
  let α := ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq
  have hα : IsIso (α.app K.obj) := by
    rw [← NatTrans.isIso_app_iff_of_iso α eK]
    have heq := comparison_derivedBaseChangeMap Λ sq L
    have hmap : IsIso ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map
          ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L))) := inferInstance
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (Arrow.isoMk ((baseChangeSourceComparisonIso f g Λ).app L)
        ((baseChangeTargetComparisonIso u' f' Λ).app L) heq.symm)).1 hmap
  let S := ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus ⋙
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus).obj L
  let eS := (baseChangeSourceComparisonIso f g Λ).app L ≪≫
    ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor ⋙
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor).mapIso eK
  let eleft :=
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).app _ ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategory.mapIso
        ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlusCompatibility.app
          K).symm ≪≫
      ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusCompatibility.app
        ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj K)).symm
  have hsource : ClassicalPlus Y' Λ
      ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj K)) := by
    apply classicalComplex_transport Y' Λ (eS ≪≫ eleft)
    exact classicalComplex_transport Y' Λ
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategoryPlusCompatibility.app
        S) ((he Y').1 S)
  let eright :=
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f').rightDerivedFunctor.mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) u').app K.obj ≪≫
        ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) u').mapDerivedCategoryPlusCompatibility.app
          K).symm) ≪≫
      ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f').rightDerivedFunctorPlusCompatibility.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) u').mapDerivedCategoryPlus.obj K)).symm
  refine ⟨hsource, ?_, hα⟩
  exact classicalComplex_transport Y' Λ (eleft.symm ≪≫ asIso (α.app K.obj) ≪≫ eright)
    hsource

/-- Degreewise consequence for a classical module sheaf.
Source: literature/blueprint/latest/blueprint/sec-smooth-base-change/
`sk-thm-sbc-derived/_section.md` (blueprint: sk-thm-sbc-derived).

Proof: The classical sheaf equivalence gives an étale sheaf M with ν^* M ≅ F.
Exact inverse image commutes with the degree-zero single functor. The classical
image clause of the derived equivalence therefore makes F[0] classical. Apply
the derived exchange theorem and then the homology functor, which preserves
isomorphisms in every integer degree.
-/
theorem smoothBaseChangeDerived_sheaf
    (Λ : Type (u + 1)) [CommRing Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback u' f' f g)
    [Smooth g] [QuasiCompact f] [QuasiSeparated f]
    (n : ℤ) (hnΛ : ∀ a : Λ, n • a = 0)
    (hnY : IsUnit (n : Γ(Y, ⊤)))
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hF : IsClassicalModuleFor X Λ F) (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y') (ModuleCat.{u + 1} Λ)) q).map
      ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := by
  obtain ⟨E, hE, hEq, _, _⟩ := (AlgebraicGeometry.proEtaleClassicalSheaves X).2.2 Λ
  let : E.IsEquivalence := hEq
  let P : ObjectProperty (Sheaf (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} Λ)) := IsClassicalModuleFor X Λ
  let M := E.asEquivalence.inverse.obj ⟨F, hF⟩
  let eF : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj M ≅ F :=
    (eqToIso (congrArg (fun T ↦ T.obj M) hE)).symm ≪≫
      P.ι.mapIso (E.asEquivalence.counitIso.app ⟨F, hF⟩)
  let e := ((comparisonUpperStar
    (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlusSingleFunctor 0).app M ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso eF
  have hu := (boundedBelowComparison X Λ).1
  have hc := (classicalDerivedEquivalence X Λ
    (fun L ↦ by let := hu; infer_instance)).1
      ((DerivedCategory.Plus.singleFunctor _ 0).obj M)
  have hsingle : ClassicalPlus X Λ ((DerivedCategory.Plus.singleFunctor _ 0).obj F) :=
    classicalComplex_transport X Λ (DerivedCategory.Plus.ι.mapIso e) hc
  have := (smoothBaseChangeDerived Λ sq n hnΛ hnY
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F) hsingle).2.2
  infer_instance

end AlgebraicGeometry.ProEtale
