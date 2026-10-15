/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.Paper.InverseImageStalkGerm
import Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Abelian.RightDerived
import Sheaf.AlgebraicGeometry.StrictBaseClosedPointLocalizations
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Local acyclicity and the closed-fibre restriction of the derived unit

Source: Stacks Project, Tag 0GJU, lemma-beta-is-isomorphism, specialized to `G[0]`
(blueprint: lem-weil-pbc-local-acyclicity-closed-fibre-unit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- For a locally acyclic morphism relative to an abelian étale sheaf, the derived
unit for any geometric fibre over the strict local base becomes an isomorphism
on the closed geometric fibre. No properness or torsion assumption is needed.
Source: Stacks Project, Tag 0GJU, lemma-beta-is-isomorphism, specialized to `G[0]`
(blueprint: lem-weil-pbc-local-acyclicity-closed-fibre-unit).

Proof:
1. The geometric-fibre projection `h` is affine: over an affine `Spec B` of `X'`,
   its inverse image is `Spec (B ⊗[A] Ω')`. Thus `h` is quasi-compact and quasi-separated
   (lem-weil-pbc-fibre-product-affine-spectra, pqf-def-affine-morphism,
   lem-weil-pbc-affine-morphism-permanence).
2. At a geometric point of the closed fibre, the strict-base closed-point localization
   identifications identify the strict-local fibre of `h` with the variety of vanishing
   cycles of `f`. The maps to `X` agree, so inverse-image composition identifies coefficients
   (lem-weil-pbc-strict-base-closed-point-localizations,
   lem-weil-pbc-inverse-image-composition).
3. Exact inverse image and exact geometric stalks identify the degree-q target stalk with
   the higher-direct-image stalk of `h`. The unrestricted strict-henselization stalk formula
   computes this as cohomology of that variety. Both source and target have zero negative
   cohomology, using a nonnegative injective resolution of the degree-zero sheaf
   (prop-weil-pbc-geometric-stalks-exact, lem-weil-pbc-inverse-image-stalk-germ,
   lem-weil-pbc-unrestricted-strict-henselization-stalk,
   lem-weil-pbc-left-exact-injective-resolution-degree-zero).
4. The derived-unit formula identifies its degree-zero map with the ordinary unit.
   A germ represented on a pointed étale neighbourhood is sent to its pullback section
   and then restricted to the strict-local fibre. The inverse germ isomorphism followed
   by restriction gives the same section, precisely `localAcyclicityAlpha`
   (prop-weil-pbc-derived-inverse-image-adjunction,
   lem-weil-pbc-strictly-henselian-sections-stalk,
   lem-weil-pbc-inverse-image-stalk-germ, lem-weil-pbc-inverse-image-composition).
5. Local acyclicity makes this degree-zero map an isomorphism and kills positive
   cohomology of the variety of vanishing cycles, also for empty fibres
   (def-weil-pbc-local-acyclicity-abelian-sheaf).
6. Geometric stalks are conservative, so all cohomology-sheaf maps are isomorphisms.
   The bounded-below cohomology criterion makes the original map an isomorphism
   (lemma-weil-pbc-geometric-stalk-conservative, lem-weil-pbc-derived-plus-iso-on-cohomology).
-/
theorem isIso_closedFibre_derivedUnit_of_isLocallyAcyclicRelative
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : IsLocallyAcyclicRelative f G)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s) :
    IsIso
      ((Functor.mapDerivedCategoryPlus
        (upperStar AddCommGrpCat.{u + 1}
          (pullback.fst (pullback.snd f (Scheme.strictHenselizationStructuralMap s))
            (Spec.map (CommRingCat.ofHom
              (Scheme.strictHenselizationPointEvaluation s)))))).map
        ((Adjunction.derivedPlus
          (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
            (pullback.fst (pullback.snd f (Scheme.strictHenselizationStructuralMap s)) t))).unit.app
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{u + 1}
              (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj G)))) := by
  sorry

end AlgebraicGeometry.Etale
