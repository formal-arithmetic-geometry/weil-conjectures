/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.AlgebraicShriekCalculus
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.Algebra.Module.Projective
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.AlgebraicGeometry.AffineProjectiveComplexDerivedHom
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.FiniteFreeResolution
import WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import Mathlib.Algebra.Homology.Single
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Extend

/-! # Bounded coherent algebraic upper shriek

Source: Stacks Project, dualizing.tex, Tag 0BZK, lemma-shriek-boundedness (1)(2)
(blueprint: lem-trf-upper-shriek-bounded-coherent).

## Main statements

* `AlgebraicGeometry.AlgebraicShriekCalculus.shriek_bounded_finite_homology`:
  a perfect polynomial presentation makes upper shriek preserve bounded finite cohomology.
* `AlgebraicGeometry.AlgebraicShriekCalculus.shriek_unit_bounded_finite_homology`:
  the same assertion for the degree-zero regular module.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicShriekCalculus

/-- A finite-type map of Noetherian rings, perfect over a polynomial presentation,
sends bounded finite cohomology to bounded finite cohomology under algebraic upper shriek.
The module in the perfectness hypothesis is the regular A-module restricted along p;
it therefore has precisely the prescribed polynomial action.
Source: Stacks Project, dualizing.tex, Tag 0BZK, lemma-shriek-boundedness (1)(2)
(blueprint: lem-trf-upper-shriek-bounded-coherent).

Proof:
1. The chosen polynomial presentation P = R[x_1,...,x_n] is Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian. By def-pc-perfect-ring-complex,
   represent A[0] over P by a bounded complex E of finite projective modules in [u,v].
   The polynomial model in lem-trf-algebraic-shriek-calculus computes the restriction
   of upper shriek of K by RHom_P(A, K tensor_R^L P)[n]. No flatness of R to A is used.
2. By lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion and
   def-pc-ring-pseudo-coherent-complex, K has a bounded-above finite-free model F.
   Its terms are flat since tensoring with finite free modules is a finite direct sum.
   Lem-pc-module-bounded-flat-kflat makes F K-flat. By lem-pur-derived-change-of-rings,
   L = F tensor_R P computes derived extension and has finite-free P-terms.
3. The monomial basis of def-weil-pbc-mv-polynomial-ring makes P free, hence R-flat:
   tensoring is a direct sum of copies, whose exactness is coordinatewise.
   Lem-weil-pbc-flat-tensor-exact identifies H^j(L) with H^j(F) tensor_R P.
   Thus its cohomology is supported in some interval [a,b].
4. Truncate L below a: use zero below a, coker(d^{a-1}) in degree a, and L^j above a.
   The projection is a quasi-isomorphism by its degreewise cohomology calculation.
   The truncated complex G is bounded in [a,b] and its terms are finite over P,
   including degree a since a quotient of a finite module is finite.
5. Lem-sc-affine-projective-complex-derived-hom represents RHom_P(A,L) by Hom(E,G).
   Its terms are finite sums of Hom_P(E^i,G^{i+t}). By def-weil-pbc-projective-module,
   each E^i is a summand of a finite free module, so these Hom modules are retracts
   of finite sums of G^{i+t}, hence finite. They vanish unless a-v <= t <= b-u.
6. By lem-weil-pbc-noetherian-submodule-finite, kernels of differentials are finite;
   their quotient cohomology modules are finite as well. The polynomial model shifts
   the support interval to [a-v-n,b-u-n]. Exact restriction of scalars identifies
   these P-cohomology modules with the restricted A-cohomology modules. Their finite
   P-generators also generate over A by applying p to coefficients.
7. For the particular case in the companion statement, take K = R[0], whose only
   cohomology is the cyclic module R in degree zero, including when R is the zero ring. -/
theorem shriek_bounded_finite_homology
    (S : AlgebraicGeometry.AlgebraicShriekCalculus.{u})
    {R A : CommRingCat.{u}} [IsNoetherianRing R] [IsNoetherianRing A]
    (φ : R →+* A) (hφ : RingHom.FiniteType φ)
    (n : ℕ) (p : MvPolynomial (Fin n) R →+* A)
    (_hp : Function.Surjective p)
    (_hc : p.comp (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) = φ)
    (_hperfect : DerivedCategory.IsPerfectRingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) R)) 0).obj
        ((ModuleCat.restrictScalars p).obj (ModuleCat.of A A))))
    (K : AlgebraicGeometry.algebraicShriekD R)
    (_hbounded : ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b)
    (_hfinite : ∀ i : ℤ,
      Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) :
    (∃ a b : ℤ, ((S.shriek φ hφ).obj K).IsGE a ∧ ((S.shriek φ hφ).obj K).IsLE b) ∧
      ∀ i : ℤ, Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ((S.shriek φ hφ).obj K)) := by
  sorry

/-- In particular, algebraic upper shriek of R[0] has bounded finite A-cohomology.
Source: Stacks Project, dualizing.tex, Tag 0BZK, lemma-shriek-boundedness (1)(2)
(blueprint: lem-trf-upper-shriek-bounded-coherent).

Proof: Apply the preceding bounded-coherence argument (steps 1--6 of this node)
to K = R[0]. This is step 7 of the node: cohomology vanishes outside degree zero,
and degree-zero cohomology is R, generated by 1. This also covers the zero ring. -/
theorem shriek_unit_bounded_finite_homology
    (S : AlgebraicGeometry.AlgebraicShriekCalculus.{u})
    {R A : CommRingCat.{u}} [IsNoetherianRing R] [IsNoetherianRing A]
    (φ : R →+* A) (hφ : RingHom.FiniteType φ)
    (n : ℕ) (p : MvPolynomial (Fin n) R →+* A)
    (_hp : Function.Surjective p)
    (_hc : p.comp (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) = φ)
    (_hperfect : DerivedCategory.IsPerfectRingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) R)) 0).obj
        ((ModuleCat.restrictScalars p).obj (ModuleCat.of A A)))) :
    (∃ a b : ℤ,
      ((S.shriek φ hφ).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))).IsGE a ∧
      ((S.shriek φ hφ).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))).IsLE b) ∧
      ∀ i : ℤ, Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          ((S.shriek φ hφ).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) := by
  sorry

end AlgebraicGeometry.AlgebraicShriekCalculus
