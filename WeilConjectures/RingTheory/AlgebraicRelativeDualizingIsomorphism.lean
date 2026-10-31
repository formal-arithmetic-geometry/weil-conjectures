/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.RingTheory.RingPseudoCoherent
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
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
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
public import WeilConjectures.AlgebraicGeometry.AffineRelativeDualizingComparison
import WeilConjectures.Algebra.Homology.ProjectiveHomEvaluationModel
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.FiniteFreeResolution
import WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Single
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import WeilConjectures.Algebra.Homology.SemidualizingRHomConservative
import WeilConjectures.TraceFormula.AlgebraicShriekRelativePerfect
import WeilConjectures.TraceFormula.PolynomialDiagonalRhomReduction

/-! # Unnormalized uniqueness of algebraic relative dualizing objects

Source: Stacks Project, Duality for Schemes, Tag 0E2D, using Definition 0E2C,
in the Noetherian case (blueprint: lem-trf-algebraic-relative-dualizing-isomorphism).

The diagonal, first pullback and derived Hom are the shared affine-comparison
constructions. Scalar extension uses K-flat resolutions; the native derived closed
structure uses K-injective resolutions for Hom. The Tor interval is over R.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Any two algebraic relative dualizing objects are isomorphic, with no normalization
by a chosen diagonal generator.
Source: Stacks Project, dualizing.tex, Tag 0E2D and Definition 0E2C; More on Algebra,
Definition 0DHS (blueprint: lem-trf-algebraic-relative-dualizing-isomorphism).

Proof:
1. The two assumptions on each object are precisely R-perfectness (Definition 0DHS).
   Testing the Tor interval on R bounds its cohomology. The Noetherian pseudo-coherence
   criterion (lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion) makes each
   cohomology module finite. Thus both objects belong to the bounded finite derived category.
2. Choose a finite polynomial presentation P = R[x_1,...,x_n] onto A. Put
   C = RHom_P(A,P)[n], with its coinduced A-action. By
   lem-trf-algebraic-shriek-relative-perfect, C has bounded finite cohomology and the
   scalar-action map A to RHom_A(C,C) is an isomorphism.
3. For T = M,N, lem-trf-polynomial-diagonal-rhom-reduction and restriction along p1
   turn the assumed diagonal isomorphism into g_T : A isomorphic to RHom_A(C,T).
   Multiplication composed with p1 is the identity, so the restricted target is A.
   This is restriction of scalars along p1, not an underived restriction along B to A.
4. Use lem-pod-projective-hom-evaluation-model on a bounded-above projective model of C.
   Let f_T : C to T be the tensor-Hom adjunct of g_T. The scalar-action map is adjunct
   to the identity of C. Naturality gives RHom_A(C,f_T) composed with that scalar map
   equal to g_T, so RHom_A(C,f_T) is an isomorphism.
5. By lem-trf-semidualizing-rhom-conservative, f_M and f_N are isomorphisms.
   Their composite f_M inverse followed by f_N gives M isomorphic to N. The choices
   of g_T are arbitrary, and no compatibility with chosen generators is asserted.
-/
theorem algebraic_relativeDualizing_isomorphic
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A]
    (hflat : RingHom.Flat (algebraMap R A)) [Algebra.FinitePresentation R A]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [HasDerivedCategory.{u} (ModuleCat.{u} (A ⊗[R] A))]
    (M N : DerivedCategory (ModuleCat.{u} A))
    (hM : DerivedCategory.IsPseudoCoherent M)
    (hN : DerivedCategory.IsPseudoCoherent N)
    (hMTor : ∃ a b : ℤ, a ≤ b ∧ ∀ (Q : ModuleCat.{u} R) (i : ℤ),
      i < a ∨ b < i → IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
          (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj M) ⊗
            DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj Q))))
    (hNTor : ∃ a b : ℤ, a ≤ b ∧ ∀ (Q : ModuleCat.{u} R) (i : ℤ),
      i < a ∨ b < i → IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
          (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) ⊗
            DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj Q))))
    (hMHom : Nonempty
      (relativeDualizingModuleHom R A M ≅ relativeDualizingModuleDiagonal R A))
    (hNHom : Nonempty
      (relativeDualizingModuleHom R A N ≅ relativeDualizingModuleDiagonal R A)) :
    Nonempty (M ≅ N) := by
  sorry

end AlgebraicGeometry
