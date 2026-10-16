/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Detecting derived comparisons off a finite boundary

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-boundary-comparison.md`
(blueprint: lem-fin-finite-boundary-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A comparison is invertible if its open restriction and proper direct image are
invertible and the complementary closed subscheme is finite over the base.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-boundary-comparison.md`
(blueprint: lem-fin-finite-boundary-comparison).

Proof plan:
1. Forget module coefficients to abelian sheaves using
   `lem-weil-pbc-module-abelian-derived-direct-image-comparison` and
   `prop-weil-pbc-inverse-image-modules-exact`. Exact forgetting commutes with cohomology
   and reflects isomorphisms, hence so does its derived functor by
   `lem-weil-pbc-derived-plus-iso-on-cohomology`.
2. Take a distinguished cone triangle of the forgotten comparison. Exact inverse image
   and derived direct image are triangulated (`prop-weil-pbc-inverse-image-exact`,
   `lem-sf-exact-functor-derived-triangulated`,
   `lem-weil-pbc-derived-direct-image-triangulated`). The long exact cohomology sequence
   (`lem-sf-derived-homology-long-exact`) and the cohomology criterion show that the cone M
   has zero open restriction and zero derived direct image.
3. The closed immersion is finite (`lem-weil-pbc-closed-immersion-finite`), so its direct
   image is exact (`lemma-weil-pbc-finite-direct-image-exact`). Every cohomology sheaf of M
   is supported on Z, by `lemma-openclosed-stalk-upperstar`. Closed-image recovery and
   full faithfulness (`lem-kun-04ca`) identify its adjunction unit with an isomorphism.
   Exactness and the cohomology criterion therefore give M ≅ i_*i^*M.
4. Put N = i^*M. Derived pushforward composition
   (`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`), computed on bounded below
   K-injectives (`def-weil-pbc-direct-image`), gives R(bi)_*N = 0. Finite exactness gives
   (bi)_*H^n(N) = 0 for every n.
5. By `lemma-weil-pbc-finite-stalk-formula`, each stalk of H^n(N) is a retract of a zero
   finite product, hence zero. Geometric-stalk conservativity
   (`lemma-weil-pbc-geometric-stalk-conservative`) gives H^n(N) = 0, including empty fibres.
6. The cohomology criterion gives N = 0, then M = 0. The original cone triangle and its
   cohomology sequence make the forgotten comparison invertible. Reflection in step 1
   makes c invertible. Properness is retained although this argument does not need it. -/
theorem isIso_of_finite_boundary
    (Λ : Type (u + 1)) [CommRing Λ] {Y S G Z : Scheme.{u}}
    (b : Y ⟶ S) [IsProper b]
    (a : G ⟶ Y) [IsOpenImmersion a] (i : Z ⟶ Y) [IsClosedImmersion i]
    (hcomplement : Set.range i.base = (Set.range a.base)ᶜ) [IsFinite (i ≫ b)]
    {K L : _root_.DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (c : K ⟶ L)
    (hopen : IsIso ((upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlus.map c))
    (hpush : IsIso ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) b).map c)) :
    IsIso c := by
  sorry

end AlgebraicGeometry.Etale
