/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction
public import Sheaf.AlgebraicGeometry.ExceptionalBaseChangeCartesianOpenInjectiveAcyclic
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful

/-!
# Finite-CD proper/open interchange on the small pro-etale site

Source: `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-prop-sf-existence/prop-exc-base-change-proper.proof.md`, Step 3;
Stacks Project, `derived.tex`, Tag 07K7
(blueprint: lem-exc-proetale-finite-cd-proper-open-interchange).

The all-sheaf finite cohomological-dimension bound makes the canonical proper/open
comparison invertible on ordinary unbounded derived categories.  Its component is
computed on K-injective complexes with injective terms by the degreewise sheaf
comparison followed by the direct image of a K-injective resolution.  The two
normalization equations below state the restriction and open-adjunction forms of
that component, including the unit that identifies the open restriction with the
identity.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

open SheafOfModules in
/-- Under an all-sheaf finite cohomological-dimension bound, proper direct image
commutes with extension by zero on an arbitrary open in the ordinary unbounded
small pro-etale derived categories.  The displayed comparison is the canonical map
whose representative is the degreewise proper/open sheaf comparison followed by the
termwise direct image of a K-injective resolution.

Source: blueprint `lem-exc-proetale-finite-cd-proper-open-interchange`
(blueprint: lem-exc-proetale-finite-cd-proper-open-interchange), retained repaired
proof Step 3; Stacks Project, `derived.tex`, Tag 07K7.

Proof:
1. Use the small-site Grothendieck module categories and the functorial
   K-injective resolutions from `prop-pur-kinjective-resolutions-exist`.  Represent
   `M` by a K-injective complex `J` with injective terms, choose a K-injective
   resolution `a : k_! J ⟶ I`, and use exactness of `k_!` to compute `k_! M`.
   The ordinary unbounded operations compute `Rr_* M` by `r_* J` and `Rp_* k_! M`
   by `p_* I`.
2. For every degree `s`, the Cartesian proper/open injective-acyclicity theorem
   `lem-exc-proetale-cartesian-open-injective-acyclic` gives
   `R^q p_* (k_! J^s) = 0` for `q > 0`.  Each `I^s` is also `p_*`-acyclic by
   `lem-weil-pbc-derived-functor-injective-vanishing`; no claim that `k_!` preserves
   injectives is made.
3. Apply `lem-kun-finite-cd-acyclic-complex` to `p_*`.  Its finite-CD hypothesis is
   exactly `hcd`, and its comparison identifies the termwise map `p_* a` with the
   ordinary right derived map.  Applying the specified natural sheaf comparison
   `lem-exc-proetale-proper-open-sheaf-comparison` degreewise gives the map whose
   localization is the displayed comparison.
4. A morphism of inputs is represented by a chain map between K-injective
   representatives, unique up to homotopy, by
   `lem-weil-pbc-kinjective-hom-derived`.  The corresponding comparison of the
   resolutions is unique up to homotopy; additive direct image preserves homotopies.
   Naturality of the sheaf comparison therefore proves independence of all choices
   and naturality in `M`.
5. The derived restriction comparison in
   `lem-exc-proetale-derived-open-restriction`, together with the open unit, identifies
   the restriction of the displayed map with the termwise map `r_* (k^* a)`.  The
   inverse of this map is the specified `proEtaleOpenRestrictionLambdaInverse`, so
   the first normalization equation is the unit form of this identification.
6. Under the derived adjunction `prop-exc-open-adjoint`, the adjunct of the displayed
   comparison is the inverse restriction from step 5.  The inverse adjunction
   formula is the open counit after applying `i_!`; this is the second normalization
   equation.  No quasi-compactness of `i`, boundedness, completion, constructibility,
   or etale-origin condition is used.
-/
theorem proEtaleFiniteCDProperOpenInterchange
    (A : Type u) [CommRing A] [Finite A]
    {V T W : Scheme.{u}} (p : V ⟶ T) (i : W ⟶ T)
    [IsProper p] [IsOpenImmersion i]
    (d : ℕ)
    (hcd : ∀ (F : proEtaleRingModules V (proEtaleConstantRing V A))
      (q : ℕ), d < q →
        IsZero ((DerivedCategory.homologyFunctor
          (proEtaleRingModules T (proEtaleConstantRing T A)) (q : ℤ)).obj
          ((proEtaleConstantDerivedDirectImage p A).obj
            ((DerivedCategory.singleFunctor
              (proEtaleRingModules V (proEtaleConstantRing V A)) 0).obj F)))) :
    IsIso (sfProperOpenDerivedComparison A (pullback.snd p i) (pullback.fst p i)
      i p (IsPullback.of_hasPullback p i).flip) ∧
      IsIso (proEtaleOpenRestrictionLambdaInverse p i A) ∧
      ∀ M : proEtaleDerivedCategory (pullback p i) A,
        (exceptionalOpenAdjunction i A).unit.app
            ((proEtaleConstantDerivedDirectImage (pullback.snd p i) A).obj M) ≫
          (sfIntrinsicDerivedPullback A i).map
            ((sfProperOpenDerivedComparison A (pullback.snd p i) (pullback.fst p i)
              i p (IsPullback.of_hasPullback p i).flip).app M) =
          (proEtaleOpenRestrictionLambdaInverse p i A).app M ∧
        (sfProperOpenDerivedComparison A (pullback.snd p i) (pullback.fst p i)
          i p (IsPullback.of_hasPullback p i).flip).app M =
          (sfIntrinsicDerivedOpen A i).map
              ((proEtaleOpenRestrictionLambdaInverse p i A).app M) ≫
            (exceptionalOpenAdjunction i A).counit.app
              ((sfIntrinsicDerivedOpen A (pullback.fst p i) ⋙
                proEtaleConstantDerivedDirectImage p A).obj M) := by
  have hLambda := (proEtaleDerivedOpenRestriction p i A).2.2
  refine ⟨?_, hLambda, ?_⟩
  · classical
    let C := proEtaleRingModules (pullback p i)
      (proEtaleConstantRing (pullback p i) A)
    let B := proEtaleRingModules V (proEtaleConstantRing V A)
    let D := proEtaleRingModules T (proEtaleConstantRing T A)
    let F := proEtaleConstantModuleDirectImage p A
    have : PreservesFiniteLimits F :=
      (proEtaleConstantModuleDirectImage_additive_leftExact p A).2
    let k := sfIntrinsicExtensionByZero (pullback.fst p i) A
    let r := proEtaleConstantModuleDirectImage (pullback.snd p i) A
    let j := sfIntrinsicExtensionByZero i A
    let t := sfIntrinsicPullback A i
    have hjFull : j.Full := by
      dsimp [j, sfIntrinsicExtensionByZero]
      infer_instance
    have hjFaithful : j.Faithful := by
      dsimp [j, sfIntrinsicExtensionByZero]
      infer_instance
    have hunit : IsIso (sfIntrinsicOpenAdjunction A i).unit := inferInstance
    -- Transport the invertible sheaf open unit to the derived adjunction.
    let eunit : j.mapDerivedCategory ⋙ t.mapDerivedCategory ≅ 𝟭 _ :=
      (Functor.mapDerivedCategoryCompIso j t).symm ≪≫
        Functor.mapDerivedCategoryNatIso (asIso (sfIntrinsicOpenAdjunction A i).unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso _
    let ff := (exceptionalOpenAdjunction i A).fullyFaithfulLOfCompIsoId eunit
    have := ff.full
    have := ff.faithful
    have hGroth (X : Scheme.{u}) : IsGrothendieckAbelian.{u + 1}
        (proEtaleRingModules X (proEtaleConstantRing X A)) :=
      (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
        (ProEt.topology X) (proEtaleConstantRing X A)).1
    have := hGroth V
    have := hGroth (pullback p i)
    have hd (N : B) (q : ℕ) (hq : d < q) : IsZero ((F.rightDerived q).obj N) :=
      F.isZero_rightDerived_of_isZero_homology N q (hcd N q hq)
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro M
    let K : CochainComplex C ℤ := DerivedCategory.Q.objPreimage M
    let J := (CochainComplex.kInjectiveResolutionFunctor.{u + 1} C).obj K
    have : IsIso (DerivedCategory.Q.map
        ((CochainComplex.toKInjectiveResolution.{u + 1} C).app K)) :=
      Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso C _) _
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} C K).2
    have eM : M ≅ DerivedCategory.Q.obj J :=
      (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
        asIso (DerivedCategory.Q.map
          ((CochainComplex.toKInjectiveResolution.{u + 1} C).app K))
    have hkJ (n : ℤ) : F.rightAcyclic ((k.mapHomologicalComplex (.up ℤ)).obj J |>.X n) := by
      intro q
      apply F.isZero_rightDerived_of_isZero_homology
      exact isZero_higherDirectImage_cartesianOpen_injective A p i ⟨d, hcd⟩
        (J.X n) (q + 1) (Nat.zero_lt_succ q)
    -- Acyclic terms make the derived comparison invertible on k!J.
    have hcomp := F.isIso_rightDerivedFunctorUnit_app_of_rightAcyclic d hd
      ((k.mapHomologicalComplex (.up ℤ)).obj J) hkJ
    have hγ := sfProperOpenSheafComparison_isIso A p i
    let γ := asIso (sfProperOpenSheafComparison A (pullback.snd p i)
      (pullback.fst p i) i p (IsPullback.of_hasPullback p i).flip)
    let LJ := (k.mapHomologicalComplex (.up ℤ)).obj J
    let RJ := (r.mapHomologicalComplex (.up ℤ)).obj J
    let eF : F.rightDerivedFunctor.obj (DerivedCategory.Q.obj LJ) ≅
        DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj LJ) :=
      F.rightDerivedFunctor.mapIso ((DerivedCategory.quotientCompQhIso B).app LJ).symm ≪≫
        (asIso (F.rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient B (.up ℤ)).obj LJ))).symm ≪≫
        (DerivedCategory.quotientCompQhIso D).app _
    let esheaf : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj LJ) ≅
        (sfIntrinsicDerivedOpen A i).obj (DerivedCategory.Q.obj RJ) :=
      DerivedCategory.Q.mapIso
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (k ⋙ F)) (.up ℤ)).app J ≪≫
            (NatIso.mapHomologicalComplex γ (.up ℤ)).symm.app J ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (r ⋙ j)) (.up ℤ)).symm.app J) ≪≫
        (j.mapDerivedCategoryFactors.app RJ).symm
    let eY : (proEtaleConstantDerivedDirectImage p A).obj
        ((sfIntrinsicDerivedOpen A (pullback.fst p i)).obj M) ≅
        (sfIntrinsicDerivedOpen A i).obj (DerivedCategory.Q.obj RJ) :=
      F.rightDerivedFunctor.mapIso
          (k.mapDerivedCategory.mapIso eM ≪≫ k.mapDerivedCategoryFactors.app J) ≪≫
        eF ≪≫ esheaf
    -- On the essential image of the fully faithful open extension, the counit is invertible.
    have hc := (exceptionalOpenAdjunction i A).isIso_counit_app_of_iso eY
    have hLambdaM : IsIso ((proEtaleOpenRestrictionLambdaInverse p i A).app M) := by
      have := hLambda
      infer_instance
    change IsIso ((sfIntrinsicDerivedOpen A i).map
      ((proEtaleOpenRestrictionLambdaInverse p i A).app M) ≫
        (exceptionalOpenAdjunction i A).counit.app _)
    infer_instance
  · intro M
    have hΓ :
        (sfProperOpenDerivedComparison A (pullback.snd p i) (pullback.fst p i)
          i p (IsPullback.of_hasPullback p i).flip).app M =
        ((exceptionalOpenAdjunction i A).homEquiv _ _).symm
          ((proEtaleOpenRestrictionLambdaInverse p i A).app M) := by
      rfl
    constructor
    · rw [hΓ]
      exact ((exceptionalOpenAdjunction i A).homEquiv _ _).apply_symm_apply _
    · rfl

end AlgebraicGeometry.Scheme
