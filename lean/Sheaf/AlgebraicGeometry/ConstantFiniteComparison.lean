/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.AlgebraicGeometry.FiniteConstructibleDirectImage
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical

/-!
# Constant coefficients under a finite comparison

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`lem-finrepair-constant-finite-comparison.md`
(blueprint: lem-finrepair-constant-finite-comparison).

Higher direct images are the cohomology sheaves of the total right derived direct image
of a constant sheaf placed in degree zero. The comparison is the derived adjunction unit,
followed by constant-coefficient pullback and the derived composition isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Constructibility descends through a finite surjective comparison which is an
isomorphism off a reduced closed subscheme finite over the base; the canonical comparison
is an isomorphism in degrees at least two.

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`lem-finrepair-constant-finite-comparison.md`
(blueprint: lem-finrepair-constant-finite-comparison).

Proof:
1. Put A = constant M on X, B = nu_* constant M on Y. The adjunction unit A to B is
   stalkwise the diagonal into the finite nonempty geometric fibre, hence injective
   (lemma-constructible-pullback-constant, lem-weil-pbc-constant-sheaf-geometric-stalk,
   lemma-weil-pbc-finite-stalk-formula, prop-weil-pbc-geometric-stalks-exact,
   lemma-weil-pbc-geometric-stalk-conservative). Let Q be its cokernel.
2. The constant sheaves are finite locally constant, hence constructible. Finite
   pushforward preserves constructibility (lem-fin-finite-morphism), and constructible
   sheaves form a Serre subcategory (thm-constructible-serre), so Q is constructible.
3. Over U the unit is invertible, so exact inverse image gives Q restricted to U zero
   (prop-weil-pbc-inverse-image-exact). The open-closed exact sequence identifies Q with
   i_* G for G = i^* Q (lem-weil-pbc-open-closed-short-exact); G is constructible
   (prop-constructible-pullback).
4. Closed-immersion exactness and the composition spectral sequence identify R^q f_* Q
   with R^q (i f)_* G (lem-fin-closed-immersion,
   lem-weil-pbc-grothendieck-spectral-sequence). Since i f is finite, f_* Q is
   constructible and all its positive derived images vanish (lem-fin-finite-morphism).
5. Finite pushforward is exact by its finite-product geometric-stalk formula, and
   preserves injectives. An injective resolution on Y therefore identifies R f_* B with
   R (nu f)_* constant M, including the specified unit/composition comparison
   (lem-weil-pbc-module-sheaves-enough-injectives,
   lem-weil-pbc-direct-image-preserves-injectives).
6. Apply the derived long exact sequence to 0 to A to B to Q to 0
   (lem-weil-pbc-derived-functor-long-exact). In degrees at least two its adjacent
   Q terms vanish, so the displayed comparison is invertible.
7. In degree zero f_* A is the kernel of v_* M to f_* Q; in degree one R^1 f_* A
   is an extension of R^1 v_* M by the cokernel of that map. Serre closure proves
   constructibility in these degrees; the comparison proves it in every higher degree.
-/
theorem constructible_constant_of_finite_comparison
    (k : Type u) [Field k] (X S Y Z : Scheme.{u})
    [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (f : X ⟶ S) [IsProper f]
    (hf : f ≫ (S ↘ Spec (.of k)) = (X ↘ Spec (.of k)))
    (ν : Y ⟶ X) [IsFinite ν] [Surjective ν]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsReduced Z] [IsFinite (i ≫ f)]
    (U : X.Opens) (hU : ∀ x : X, x ∈ U ↔ x ∉ Set.range i)
    (hν : IsIso (pullback.snd ν U.ι))
    (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : IsSmoothBaseChangeCoefficients N Λ S)
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (hv : ∀ q : ℕ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((lowerStar (ModuleCat.{u + 1} Λ) (ν ≫ f)).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor
            (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
              ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))))) :
    (∀ q : ℕ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
              ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))))) ∧
    ∀ q : ℕ, 2 ≤ q → IsIso
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)).map
          ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.map
            ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) ν).unit.app
              ((_root_.DerivedCategory.singleFunctor
                (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
                  ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ≫
              (lowerStar (ModuleCat.{u + 1} Λ) ν).rightDerivedFunctor.map
                (((upperStar (ModuleCat.{u + 1} Λ) ν).mapDerivedCategorySingleFunctor 0).hom.app
                  ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ≫
                  (_root_.DerivedCategory.singleFunctor
                    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).map
                      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) ν).hom.app M))) ≫
            (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) ν f).hom.app
              ((_root_.DerivedCategory.singleFunctor
                (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
                  ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  sorry

end AlgebraicGeometry.Etale
