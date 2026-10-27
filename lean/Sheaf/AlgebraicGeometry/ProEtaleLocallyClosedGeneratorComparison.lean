/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
public import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules

import Sheaf.AlgebraicGeometry.OpenClosedRecollement
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Paper.ProEtaleLisseOrigin
import Sheaf.AlgebraicGeometry.ProEtaleComparisonStalk
import Sheaf.CategoryTheory.ConstantRingModuleSheaves
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Mathlib.Topology.NoetherianSpace
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Comparison of locally closed generators on the etale and pro-etale sites

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-sf-flat-model,
proof, paragraph 1 and the first paragraph of the complement
(blueprint: lem-sfb-proetale-locally-closed-generator-comparison).

We use the fixed-module-valued presentations for direct image and extension by zero.
For local constancy and module stalks we apply the existing canonical intrinsic
realization over the constant ring sheaf. The right-derived comparison is the specified
right-derived-functor unit at the degree-zero complex, hence is a morphism in the
unbounded derived category, rather than a comparison of cohomology groups alone.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Exact closed direct image, preservation of finite projective local systems, and the
natural comparison for extension along the closure of a locally closed stratum.
Here `a.image` is the scheme-theoretic closure, and `j` is its open factor: the equation
`hj` identifies it uniquely with `a.toImage` by the monomorphism `a.imageι`.

The right-derived unit has source `Qh(C(g_*)((j_!M)[0]))`, canonically identified with
`(g_*j_!M)[0]`; its target is `Rg_*((j_!M)[0])`. Thus its invertibility asserts the
particular canonical comparison, on each site. The final functor isomorphism includes
naturality for every module sheaf, without a local-constancy hypothesis.

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-sf-flat-model,
proof, paragraph 1 and complement, first paragraph; Stacks Tags 09BM, 015F, 099Y,
0GLZ, 0993 and 09AF
(blueprint: lem-sfb-proetale-locally-closed-generator-comparison).

Proof:
1. A finite affine Noetherian cover makes the underlying space of X Noetherian
   (lem-sc-affine-noetherian-underlying-space, lem-kun-finite-union-noetherian).
   Every subset is quasi-compact (lem-sfb-noetherian-space-compact-subsets), so the
   open complement of the closed immersion g = a.imageι is retrocompact.
2. Apply lem-cbc-open-closed-recollement on the etale site and
   lem-weil-pbc-proetale-ringed-open-closed on the pro-etale site. Identify the
   inverse-image constant coefficient rings by lem-pe-constant-left-module-inverse-image.
   This gives exactness of the specified direct images on both sites.
3. Apply lem-weil-pbc-exact-functor-derived-factorization and
   lem-weil-pbc-exact-functor-derived-functor to each exact g_* and (j_!M)[0].
   Termwise direct image identifies the source with (g_*j_!M)[0], so the canonical
   right-derived unit at this complex is invertible, with no condition on M.
4. Finite generation over the finite ring makes every stalk of L finite as a set.
   The forward direction of lem-sf-proetale-locally-constant-origin makes its
   comparison pullback locally constant. Express this in the intrinsic constant-ring
   presentation by the canonical associated-module-sheaf realization.
5. The linear stalk isomorphism of lem-cbc-proetale-comparison-stalk transports finite
   generation and projectivity. Projective modules are flat
   (lem-weil-pbc-projective-module-flat). The intrinsic module stalk is the same
   pointed-neighbourhood colimit with scalars restricted along the constant germ.
6. Identify the fixed-module and constant-ring extension-by-zero conventions using
   lem-cbc-constant-ring-module-sheaves, lem-weil-proetale-weakly-etale-localization,
   lem-pur-site-restriction-module-adjunction-exact, the extension-by-zero adjunction,
   and lem-weil-pbc-conjugate-iso-unit-equation (uniqueness with its unit equation).
7. A closed immersion is affine, hence quasi-compact and quasi-separated
   (def-weil-closed-immersion, lem-weil-pbc-affine-morphism-permanence).
8. Apply prop-weil-pbc-comparison-direct-image to g and N[0], with N = j_!M.
   By exactness of g_* and lem-sf-comparison-pullback-exact, both sides are single
   complexes. Taking H^0 gives the natural sheaf comparison for closed direct image.
9. Compose it with the image under pro-etale g_* of the open comparison
   lem-cbc-proetale-extension-zero-comparison. Both maps are natural, so the result
   is a natural isomorphism. Empty strata and the zero ring give zero sheaves and
   the same invertible comparisons. No separatedness hypothesis on X is used. -/
theorem proEtale_locallyClosed_generator_comparison
    (X : Scheme.{u}) [IsNoetherian X] (Λ : Type u) [CommRing Λ] [Finite Λ]
    {S : Scheme.{u}} (a : S ⟶ X) [IsImmersion a]
    (j : S ⟶ a.image) [IsOpenImmersion j] (_hj : j ≫ a.imageι = a) :
    PreservesFiniteLimits (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))
      a.imageι) ∧
    PreservesFiniteColimits (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))
      a.imageι) ∧
    PreservesFiniteLimits (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))
      a.imageι) ∧
    PreservesFiniteColimits (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))
      a.imageι) ∧
    (∀ M : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)),
      IsIso ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))
        a.imageι).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj ((CochainComplex.singleFunctor _ 0).obj
            ((Etale.openImmersionLowerShriek
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) j).obj M))))) ∧
    (∀ M : Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)),
      IsIso ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))
        a.imageι).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj ((CochainComplex.singleFunctor _ 0).obj
            ((ProEtale.openImmersionLowerShriek
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) j).obj M))))) ∧
    (∀ L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)),
      Scheme.IsLocallyConstantSheaf L →
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        Module.Finite (ULift.{u + 1, u} Λ)
          (pointedEtaleStalk (A := ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) L s) ∧
        Module.Projective (ULift.{u + 1, u} Λ)
          (pointedEtaleStalk (A := ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) L s)) →
      Scheme.IsLocallyConstantProEtaleModuleSheafOfUniverses S Λ
        ((ProEtale.finiteCoefficientIntrinsicComparison S Λ).obj L) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        Module.Finite (ULift.{u + 1, u} Λ)
          ((Scheme.finiteCoefficientModuleStalkFunctor s Λ).obj
            ((ProEtale.finiteCoefficientIntrinsicComparison S Λ).obj L)) ∧
        Module.Projective (ULift.{u + 1, u} Λ)
          ((Scheme.finiteCoefficientModuleStalkFunctor s Λ).obj
            ((ProEtale.finiteCoefficientIntrinsicComparison S Λ).obj L)) ∧
        Module.Flat (ULift.{u + 1, u} Λ)
          ((Scheme.finiteCoefficientModuleStalkFunctor s Λ).obj
            ((ProEtale.finiteCoefficientIntrinsicComparison S Λ).obj L))) ∧
    Nonempty
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) j ⋙
          Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) a.imageι ⋙
          ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) X ≅
        ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) S ⋙
          ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) j ⋙
          ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) a.imageι) := by
  sorry

end AlgebraicGeometry
