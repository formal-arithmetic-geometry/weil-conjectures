/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import WeilConjectures.ConstructibleSheaf.Defs
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Sheaf.CategoryTheory.TruncationHypercohomology
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.Filtration
import Sheaf.CategoryTheory.TruncationCouple
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Closed-support amplitude

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
sk-prop-a1-kummer/lem-exc-closed-amplitude.md,
node lem-exc-closed-amplitude, order 1911
(blueprint: lem-exc-closed-amplitude).
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The closed exceptional inverse image sends [a,b] into [a,b+c+1], with the
same assertion for constructible cohomology under the extra direct-image finiteness
hypothesis. Ri^! is the right adjoint of the actual closed derived direct image,
whose existence is lem-exc-closed-ambient, not an assumed exceptional functor.
Source: blueprint smooth-purity, sk-prop-a1-kummer, node order 1911
(blueprint: lem-exc-closed-amplitude).

Proof (the eight steps of the node):
1. Exact inverse image (prop-weil-pbc-inverse-image-modules-exact) commutes with
   cohomology (lem-weil-pbc-exact-functor-complex-cohomology), so j^* K is in [a,b].
2. Pull back the finite constructible stratification and its etale trivializing
   covers (def-weil-pbc-etale-constructible-sheaf,
   lemma-constructible-pullback-stratification, lem-pur-scheme-constructible-preimage,
   lem-weil-pbc-etale-covering-base-change, lemma-constructible-pullback-constant).
   The finite constant module values stay the same. Both i^* and j^* therefore
   preserve the recorded global notion of constructibility.
3. Module sheaves are Grothendieck abelian and have enough injectives
   (lem-weil-pbc-module-sheaves-grothendieck-abelian,
   lem-weil-pbc-module-sheaves-enough-injectives); j_* is additive left exact
   (lem-weil-pbc-module-direct-image-left-exact). A bounded below injective
   representative is K-injective (lem-weil-pbc-dplus-injective-representative).
   Apply thm-sp-truncation-e2: E2^(p,q) = R^p j_* H^q(j^* K) converges to H^(p+q)(L),
   L = Rj_* j^* K, with a finite exhaustive separated filtration. Entries vanish
   outside 0 ≤ p ≤ c, a ≤ q ≤ b, and zero entries stay zero on later pages. Outside
   [a,b+c] all graded terms vanish, hence the abutment vanishes.
4. Under the extra hypothesis E2 is constructible. Kernels, cokernels and extensions
   of constructible sheaves are constructible (thm-constructible-serre). Images are
   kernels of cokernels. Induction through the pages and the finite abutment
   filtration makes every H^n(L) constructible.
5. A closed immersion is finite (lem-weil-pbc-closed-immersion-finite), so i_* is
   exact on abelian sheaves (lemma-weil-pbc-finite-direct-image-exact). Faithful exact
   forgetting (lem-weil-pbc-module-sheaves-colimits-forgetful) and its compatibility
   with direct image (lem-weil-pbc-module-direct-image-left-exact) reflect exactness
   to module sheaves. The counit i^* i_* ≅ Id
   (prop-openclosed-lowerstar-fully-faithful) extends termwise to derived categories.
6. For F = i_* Ri^! K the distinguished triangle F → K → L → F[1]
   (lem-exc-closed-support-triangle, using lem-exc-closed-ambient) gives
   H^(n-1)(L) → H^n(F) → H^n(K) (lem-sf-derived-homology-long-exact).
   The outside terms vanish for n < a and n > b+c+1, using c ≥ 0. Hence F has
   cohomology in [a,b+c+1].
7. Exact i_* commutes with cohomology
   (lem-weil-pbc-exact-functor-complex-cohomology). Its left inverse i^* from step 5
   detects the zeroes, proving the asserted bound for Ri^! K on Z.
8. Put u_n : H^n(K) → H^n(L). The same long exact sequence gives
   0 → coker(u_(n-1)) → H^n(F) → ker(u_n) → 0. By thm-constructible-serre, H^n(F)
   is constructible. Exact i^*, its cohomology comparison and the counit identify
   H^n(Ri^! K) with i^* H^n(F), constructible by step 2. This proves the second
   assertion with exactly the same interval and the same constructibility notion. -/
theorem closedImmersion_rightAdjoint_amplitude
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (a b c : ℤ) (hc : 0 ≤ c)
    (hcd : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ), c < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj M)))) :
    (∀ K : DerivedCategoryModule A T,
      _root_.DerivedCategory.homologyConcentratedIn a b K →
      _root_.DerivedCategory.homologyConcentratedIn a (b + c + 1)
        ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K)) ∧
    ((∀ (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ),
      Scheme.IsConstructibleEtaleModuleSheaf F →
      Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) →
      ∀ K : DerivedCategoryModule A T,
        _root_.DerivedCategory.homologyConcentratedIn a b K →
        (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
          ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) →
        _root_.DerivedCategory.homologyConcentratedIn a (b + c + 1)
          ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K) ∧
        ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
          ((_root_.DerivedCategory.homologyFunctor _ q).obj
            ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K))) := sorry

end AlgebraicGeometry.Etale
