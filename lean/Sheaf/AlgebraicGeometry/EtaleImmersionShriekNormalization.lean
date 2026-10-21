/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
public import WeilConjectures.SixFunctors.Finite.Exact
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor

/-! # Specified open and closed normalizations of ordinary etale compact support

Source: Stacks Project, Tags 0F7I, 0F51, 04FX and 03S5
(blueprint: lem-sf-etale-immersion-shriek-normalization).

The normalizations use the existing canonical compactification comparison, only on D+,
followed by the identity and exact-functor identifications in the ambient unbounded category.
The termwise exact functors themselves act on every unbounded complex.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The specified open normalization for any supplied compactification: compare with `(j,id)`,
then remove the derived identity direct image. Its components are ambient isomorphisms on D+.
Source: Stacks Project, Tag 0F7I, comparison with the trivial open compactification
(blueprint: lem-sf-etale-immersion-shriek-normalization). -/
noncomputable def etaleOpenCompactSupportNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W T : Scheme.{u}} (j : W ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (d : Compactification j) :
    DerivedCategory.Plus.ι ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ≅
      DerivedCategory.Plus.ι ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory :=
  rightDerivedLowerShriekOfCompactificationPlusιIso A d
      (Compactification.ofIsOpenImmersion j) ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      (Functor.isoWhiskerLeft
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
          (rightDerivedLowerStarIdIso A T) ≪≫
        Functor.rightUnitor _)

/-- The specified closed normalization: compare with `(id,c)`, remove the identity extension,
and apply the canonical exact-direct-image comparison. No unbounded compactification
independence is used.
Source: Stacks Project, Tags 0F7I, 0F51 and 04FX
(blueprint: lem-sf-etale-immersion-shriek-normalization). -/
noncomputable def etaleClosedCompactSupportNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (c : Z ⟶ T) [IsClosedImmersion c]
    (d : Compactification c) :
    DerivedCategory.Plus.ι ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ≅
      DerivedCategory.Plus.ι ⋙ (lowerStar (ModuleCat.{u + 1} A) c).mapDerivedCategory :=
  rightDerivedLowerShriekOfCompactificationPlusιIso A d (Compactification.ofIsProper c) ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      (Functor.isoWhiskerRight
          (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) Z)
          (rightDerivedLowerStar (ModuleCat.{u + 1} A) c) ≪≫
        Functor.leftUnitor _ ≪≫
        rightDerivedFunctorLowerStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) c)

/-- Closed direct image is exact; the two termwise descents preserve every cohomological lower
bound and commute naturally with every cohomology functor. The specified ambient normalizations
above are compatible with all canonical changes of compactification on bounded-below inputs.
Naturality in those inputs is encoded by their types as natural isomorphisms.

Source: Stacks Project, Tags 0F7I, 0F51, 04FX, 03S5 and 015F
(blueprint: lem-sf-etale-immersion-shriek-normalization).

Proof plan:
1. A closed immersion is finite (lem-weil-pbc-closed-immersion-finite); apply
   lemma-weil-pbc-finite-direct-image-exact. Alternatively transfer exactness from abelian
   sheaves using lem-weil-pbc-module-direct-image-left-exact and the faithful exact forgetful
   functor of lem-weil-pbc-module-sheaves-colimits-forgetful.
2. Extension by zero is exact by lem-weil-pbc-extension-by-zero-exact. The degreewise functors
   descend on all unbounded complexes by lem-weil-pbc-exact-functor-derived-factorization;
   these are the existing mapDerivedCategory functors with mapDerivedCategoryFactors.
3. Apply lem-weil-pbc-exact-functor-bounded-below to obtain the natural cohomology comparisons.
   Additivity sends zero to zero, preserving each lower bound m, including negative m.
4. The identity direct image and identity extension are canonically the identity on sheaves
   (def-weil-pbc-direct-image, def-weil-pbc-extension-by-zero, def-weil-pbc-sheafification).
   Descend these identifications by lem-weil-pbc-localization-universal-property and use
   lem-weil-pbc-exact-functor-derived-functor for the derived identity direct image.
5. The trivial compactifications are (j,id) and (id,c); c is proper by
   lem-weil-pbc-closed-immersion-proper. Their candidates of def-amb-etale-compact-support
   normalize by the identity identifications and the exact-direct-image comparison.
6. Compose these with lem-amb-etale-compact-comparisons to get precisely the two definitions
   above. All components are isomorphisms in the ambient category, evaluated only on D+.
7. Naturality follows by composition of natural isomorphisms. For a second compactification,
   apply the cocycle law of lem-amb-etale-compact-comparisons to d, d' and the trivial one;
   associativity gives each displayed compatibility equation. No comparison on a general
   unbounded input is asserted. -/
theorem etaleImmersionShriekNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W Z T : Scheme.{u}} [IsNoetherian W] [IsNoetherian Z] [IsNoetherian T]
    (j : W ⟶ T) [IsOpenImmersion j] (c : Z ⟶ T) [IsClosedImmersion c]
    (dj : Compactification j) (dc : Compactification c) :
    (PreservesFiniteLimits (lowerStar (ModuleCat.{u + 1} A) c) ∧
      PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) c)) ∧
    (∀ (m : ℤ) (H : DerivedCategoryModule A W), H.IsGE m →
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj H).IsGE m) ∧
    (∀ (m : ℤ) (L : DerivedCategoryModule A Z), L.IsGE m →
      ((lowerStar (ModuleCat.{u + 1} A) c).mapDerivedCategory.obj L).IsGE m) ∧
    (∀ q : ℤ, Nonempty
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
          DerivedCategory.homologyFunctor _ q ≅
        DerivedCategory.homologyFunctor _ q ⋙
          openImmersionLowerShriek (ModuleCat.{u + 1} A) j)) ∧
    (∀ q : ℤ, Nonempty
      ((lowerStar (ModuleCat.{u + 1} A) c).mapDerivedCategory ⋙
          DerivedCategory.homologyFunctor _ q ≅
        DerivedCategory.homologyFunctor _ q ⋙ lowerStar (ModuleCat.{u + 1} A) c)) ∧
    (∀ dj' : Compactification j,
      rightDerivedLowerShriekOfCompactificationPlusιIso A dj dj' ≪≫
          etaleOpenCompactSupportNormalization A j dj' =
        etaleOpenCompactSupportNormalization A j dj) ∧
    (∀ dc' : Compactification c,
      rightDerivedLowerShriekOfCompactificationPlusιIso A dc dc' ≪≫
          etaleClosedCompactSupportNormalization A c dc' =
        etaleClosedCompactSupportNormalization A c dc) := by
  sorry

end AlgebraicGeometry.Etale
