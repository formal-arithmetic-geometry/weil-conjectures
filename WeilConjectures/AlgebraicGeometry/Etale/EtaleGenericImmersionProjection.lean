/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.AlgebraicGeometry.Open.OpenClosedRecollement
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.Derived.DerivedExtensionZeroBaseChangeUnderivedCompatibility
import WeilConjectures.SixFunctors.OpenClosed.Stalk
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenProjectionExchange
import WeilConjectures.AlgebraicGeometry.Derived.DerivedPullbackCompositionMonoidal
import WeilConjectures.AlgebraicGeometry.Etale.EtaleStalkTensorScalar
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-! # Projection formula for an immersion extension by zero

Source: Stacks Project, Tags 0E8I, 0GL1, 03S6 and 0A45
(blueprint: lem-sf-etale-generic-immersion-projection).

The comparison is the open projection inverse followed by the closed direct-image
projection map, with symmetries and the pullback-composition comparison. The theorem
includes its isomorphism property, naturality in both complexes, and the Cartesian
base-change equation using the composite of open base change and closed finite exchange.
-/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The functor `Rs_! = j_! Ri_*` for the chosen closed-then-open factorization.
Source: Stacks Project, Tags 0E8I and 0A45
(blueprint: lem-sf-etale-generic-immersion-projection). -/
noncomputable abbrev immersionLowerShriek
    (A : Type (u + 1)) [CommRing A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] :
    DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  R((i)_*[ModuleCat.{u + 1} A]) ⋙ D((j)_!open[ModuleCat.{u + 1} A])

/-- The canonical projection arrow `C ⊗ᴸ Rs_! P ⟶ Rs_! (s^* C ⊗ᴸ P)`.
Source: Stacks Project, Tags 0E8I and 0GL1
(blueprint: lem-sf-etale-generic-immersion-projection).

First interchange the tensor factors and use the inverse open projection isomorphism.
Inside `j_!`, apply the closed direct-image projection map. Inside `Ri_*`, interchange
factors and identify `Li^* Lj^* C` with `L(i ≫ j)^* C` by the inverse composition map.
Every factor is an existing canonical map; no choice of a projection arrow is made. -/
noncomputable def immersionProjectionMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (C : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (P : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj C).obj
        ((immersionLowerShriek A i j).obj P) ⟶
      (immersionLowerShriek A i j).obj
        (((derivedTensor (ModuleCat.{u + 1} A) S).obj
          ((L((i ≫ j)^*[ModuleCat.{u + 1} A])).obj C)).obj P) :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app C).app
      ((immersionLowerShriek A i j).obj P) ≫
    ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} A) j).inv.app
      ((R((i)_*[ModuleCat.{u + 1} A])).obj P)).app C ≫
    (D((j)_!open[ModuleCat.{u + 1} A])).map
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) i).app P).app
          ((L((j)^*[ModuleCat.{u + 1} A])).obj C) ≫
        (R((i)_*[ModuleCat.{u + 1} A])).map
          ((((derivedTensorSymmetry (ModuleCat.{u + 1} A) S).hom.app P).app
              ((L((i)^*[ModuleCat.{u + 1} A])).obj
                ((L((j)^*[ModuleCat.{u + 1} A])).obj C)) ≫
            ((derivedTensor (ModuleCat.{u + 1} A) S).map
              ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i j).inv.app C)).app P)))

/-- The canonical extension-by-zero base-change arrow `b_P : g_X^* Rs_! P ⟶ Rs'_! g_S^* P`.
Source: Stacks Project, Tag 03S6; finite exchange and open extension by zero
(blueprint: lem-sf-etale-generic-immersion-projection).

This is the inverse open base-change isomorphism, followed inside `j'_!` by the
closed finite exchange map. Its invertibility is included in `immersionProjectionFormula`. -/
noncomputable def immersionLowerShriekBaseChangeMap
    (A : Type (u + 1)) [CommRing A]
    {S U X S' U' X' : Scheme.{u}}
    {i : S ⟶ U} {j : U ⟶ X} {i' : S' ⟶ U'} {j' : U' ⟶ X'}
    {gS : S' ⟶ S} {gU : U' ⟶ U} {gX : X' ⟶ X}
    [IsClosedImmersion i] [IsOpenImmersion j]
    [IsClosedImmersion i'] [IsOpenImmersion j']
    (hi : IsPullback gS i' i gU) (hj : IsPullback gU j' j gX)
    (P : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (L((gX)^*[ModuleCat.{u + 1} A])).obj ((immersionLowerShriek A i j).obj P) ⟶
      (immersionLowerShriek A i' j').obj ((L((gS)^*[ModuleCat.{u + 1} A])).obj P) :=
  (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A) hj).inv.app
      ((R((i)_*[ModuleCat.{u + 1} A])).obj P) ≫
    (D((j')_!open[ModuleCat.{u + 1} A])).map
      ((derivedBaseChangeMap (ModuleCat.{u + 1} A) hi.toCommSq).app P)

/-- The canonical target tensor identification for immersion projection base change:
`g_S^*(s^* C ⊗ᴸ P) ⟶ s'^* g_X^* C ⊗ᴸ g_S^* P`.
Source: Stacks Project, Tags 03S6 and 0GL1
(blueprint: lem-sf-etale-generic-immersion-projection).

Use the pullback tensor comparison and then the inverse square comparison for the
composite immersion. This fixes the identifications in the base-change equation. -/
noncomputable def immersionProjectionBaseChangeTensorMap
    (A : Type (u + 1)) [CommRing A]
    {S U X S' U' X' : Scheme.{u}}
    {i : S ⟶ U} {j : U ⟶ X} {i' : S' ⟶ U'} {j' : U' ⟶ X'}
    {gS : S' ⟶ S} {gU : U' ⟶ U} {gX : X' ⟶ X}
    (hi : IsPullback gS i' i gU) (hj : IsPullback gU j' j gX)
    (C : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (P : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (L((gS)^*[ModuleCat.{u + 1} A])).obj
        (((derivedTensor (ModuleCat.{u + 1} A) S).obj
          ((L((i ≫ j)^*[ModuleCat.{u + 1} A])).obj C)).obj P) ⟶
      ((derivedTensor (ModuleCat.{u + 1} A) S').obj
        ((L((i' ≫ j')^*[ModuleCat.{u + 1} A])).obj
          ((L((gX)^*[ModuleCat.{u + 1} A])).obj C))).obj
            ((L((gS)^*[ModuleCat.{u + 1} A])).obj P) :=
  ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) gS).app
      ((L((i ≫ j)^*[ModuleCat.{u + 1} A])).obj C)).app P ≫
    ((derivedTensor (ModuleCat.{u + 1} A) S').map
      ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (hi.toCommSq.vert_comp hj.toCommSq)).inv.app C)).app
          ((L((gS)^*[ModuleCat.{u + 1} A])).obj P)

/-- The immersion projection formula is an isomorphism, natural in both complexes and
compatible with every Cartesian base change, using the specified canonical comparisons.
Source: Stacks Project, Tags 0E8I, 0GL1, 03S6 and 0A45
(blueprint: lem-sf-etale-generic-immersion-projection).

Proof plan:
1. Closed immersions are finite, so their direct images are exact, as are inverse images
and open extension by zero. Choose K-flat resolutions (`lem-pc-kflat-resolution`) and
compute derived tensors on them (`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`).
2. The closed projection map is an isomorphism on geometric stalks: a closed finite fibre
is empty or a singleton. Use the finite stalk formula, the closed-pushforward stalk
identification, the inverse-image germ isomorphism and the stalk tensor identification
(`lemma-weil-pbc-finite-stalk-formula`, `lemma-openclosed-stalk-lowerstar`,
`lem-weil-pbc-inverse-image-stalk-germ`, `lem-pod-etale-stalk-tensor-scalar`). Geometric-stalk
conservativity then gives the sheaf isomorphism, and K-flat totalization gives its derived form.
3. Compose with the inverse open projection (`lem-pur-etale-open-derived-tensor`), symmetry
and pullback composition (`lem-kun-inverse-image-monoidal`,
`lem-kun-derived-pullback-composition-monoidal`). This is precisely the defined map.
All these comparisons are natural, giving the displayed equation for arbitrary input maps.
4. Finite exchange (`lemma-weil-pbc-finite-exchange`) identifies the closed stalk
calculation with its Cartesian pullback. Inverse-image germ and monoidal composition
compatibility identify the tensor maps, so stalk conservativity gives the closed equation.
5. Apply `lem-asd-open-projection-exchange` with `E = Ri_* P` and `N = C`.
By `lem-cbc-derived-extension-zero-base-change-underived-compatibility` its open comparison
is the inverse open mate used in `immersionLowerShriekBaseChangeMap`. Compose with step 4
and the monoidal composition comparisons to obtain the final displayed equation. Finite
exchange and open base change also make `b_P` invertible. -/
theorem immersionProjectionFormula
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] :
    (∀ (C : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (P : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))),
      IsIso (immersionProjectionMap A i j C P)) ∧
    (∀ (C C' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (P P' : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (f : C ⟶ C') (h : P ⟶ P'),
      derivedTensorHom (ModuleCat.{u + 1} A) f ((immersionLowerShriek A i j).map h) ≫
          immersionProjectionMap A i j C' P' =
        immersionProjectionMap A i j C P ≫ (immersionLowerShriek A i j).map
          (derivedTensorHom (ModuleCat.{u + 1} A)
            ((L((i ≫ j)^*[ModuleCat.{u + 1} A])).map f) h)) ∧
    (∀ {S' U' X' : Scheme.{u}} {i' : S' ⟶ U'} {j' : U' ⟶ X'}
      {gS : S' ⟶ S} {gU : U' ⟶ U} {gX : X' ⟶ X}
      [IsClosedImmersion i'] [IsOpenImmersion j']
      (hi : IsPullback gS i' i gU) (hj : IsPullback gU j' j gX)
      (C : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (P : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))),
      IsIso (immersionLowerShriekBaseChangeMap A hi hj P) ∧
      (L((gX)^*[ModuleCat.{u + 1} A])).map (immersionProjectionMap A i j C P) ≫
          immersionLowerShriekBaseChangeMap A hi hj
            (((derivedTensor (ModuleCat.{u + 1} A) S).obj
              ((L((i ≫ j)^*[ModuleCat.{u + 1} A])).obj C)).obj P) ≫
          (immersionLowerShriek A i' j').map
            (immersionProjectionBaseChangeTensorMap A hi hj C P) =
        ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) gX).app C).app
            ((immersionLowerShriek A i j).obj P) ≫
          ((derivedTensor (ModuleCat.{u + 1} A) X').obj
            ((L((gX)^*[ModuleCat.{u + 1} A])).obj C)).map
              (immersionLowerShriekBaseChangeMap A hi hj P) ≫
          immersionProjectionMap A i' j'
            ((L((gX)^*[ModuleCat.{u + 1} A])).obj C)
            ((L((gS)^*[ModuleCat.{u + 1} A])).obj P)) := by
  sorry

end AlgebraicGeometry.Etale
