/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Paper.QcqsOpenClosedTree
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.AlgebraicGeometry.CondensedLocalizationExactCohomology
import Sheaf.Paper.CoefficientComplexRationalization
import Mathlib.Algebra.Category.Grp.AB
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Supported three-term scalar local-model cohomology

Source: blueprint latest, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md (2), first paragraph, agent affine heart-bound
obligation (blueprint: lem-sfb-supported-three-term-scalar-cd).

The exact full-generality coefficient estimate is WANTED. Hemo--Richarz--Scholbach,
Section 8, condition (8.1), is motivation; its finite-field colimit topology does not
replace the all-continuous norm topology on the algebraic closure here.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The homology of three finite constant scalar local models, extended along the
specified support chain, has ordinary module-derived sections vanishing above `d+2`
on affine pro-etale objects over an affine base with uniform affine etale torsion
cohomological dimension at most `d`. Differentials are arbitrary actual module maps.
No finite local model or completeness is assumed for their images or homology.

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md (2), first paragraph,
agent supported affine heart-bound obligation. HRS Section 8 (8.1) is motivation only;
the exact coefficient estimate in this generality remains WANTED.
(blueprint: lem-sfb-supported-three-term-scalar-cd)

Proof plan, following the node's seven steps:
1. Put Z=ker(c), B=im(b), C=im(c), N=Z/B. The relation b followed by c is zero
   gives 0 -> Z -> L0 -> C -> 0 and 0 -> B -> Z -> N -> 0. Each open factor of J
   is exact (def-sfb-module-open-lower-shriek). Each closed factor is exact using
   its quasi-compact open complement (lem-weil-pbc-proetale-ringed-open-closed),
   transported by def-weil-pbc-internal-abelian-sheaf-module-equivalence and
   def-sfb-module-lower-star. Exact module pullback to U follows from
   lem-sfb-condensed-localization-exact-cohomology. Thus F=v*J preserves both sequences.
2. For any map f between finite scalar local models, the finite discrete A case
   of lem-sfb-supported-image-torsion-reductions-cd bounds R Gamma(U,F(im f)[0]) by d,
   using exactly the assumed bound on all affine etale V over the original X.
3. For OE (including Z_l), lem-sfb-supported-image-derived-completeness gives
   derived completeness of the actual supported image. Its derived quotient
   reductions are bounded by d by lem-sfb-supported-image-torsion-reductions-cd.
   Apply lem-sfb-complete-reduction-rgamma-upper-bound: derived sections commute
   with the derived inverse limit and the bound becomes d+1. No image of a reduced
   matrix or classicality identification is used.
4. By lem-sfb-supported-rational-image-integral-approximation rational image section
   complexes are termwise filtered colimits of scalar localizations of finite sums
   of integral image section complexes over the same X. Exact localization
   (lem-weil-coefficient-complex-rationalization) and exact filtered colimits
   (lem-weil-pbc-filtered-colimit-abelian-groups-exact) preserve the bound d+1.
5. The bound is uniform over all finite subfields E, all chains and all U over X.
   Apply lem-sfb-supported-continuous-omega-image-comparison to obtain the bound
   d+1 for all continuous norm-topological Omega coefficients. There is no
   degree-zero finite-field descent assertion. Use f=b,c,id to bound FB,FC,FL0.
6. The internal module equivalence preserves sections. Small-site K-injective
   existence (prop-pur-kinjective-resolutions-exist) and enough injectives
   (lem-sp-grothendieck-enough-injectives) allow the universal right-derived delta
   functor for module evaluation (lem-weil-pbc-right-derived-universal-delta-functor).
   Bounded-below injective resolutions are K-injective
   (lem-weil-pbc-bounded-below-injectives-kinjective), so its long exact sequences
   compute exactly these ordinary module-derived section groups.
7. If q>d+2, the segment H^(q-1)(FC) -> H^q(FZ) -> H^q(FL0) has zero outer
   groups, since q-1>d+1 and q>d+1. Then H^q(FZ) -> H^q(FN) -> H^(q+1)(FB)
   also has zero outer groups. Hence H^q(FN)=0. The empty chain, empty schemes,
   zero objects and zero coefficient ring obey the same argument.
-/
theorem supported_three_term_scalar_cohomology_vanishes
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    (X : Scheme.{u}) [IsAffine X] (d : ℕ)
    (hcd : ∀ (V : Scheme.{u}) (v : V ⟶ X) [IsAffine V] [Etale v],
      V.HasTorsionEtaleCohomologicalDimensionLE d)
    {S : Scheme.{u}} (tree : QcqsOpenClosedTree X) (p : tree.Path S)
    (L : ShortComplex
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)))
    (hL₁ : HasFiniteConstantLocalModel Λ S L.X₁)
    (hL₂ : HasFiniteConstantLocalModel Λ S L.X₂)
    (hL₃ : HasFiniteConstantLocalModel Λ S L.X₃)
    (U : X.ProEt) [IsAffine U.left] (q : ℤ) (hq : (d : ℤ) + 2 < q) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
      ((condensedModuleSections Λ U.left).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.upperStar Λ U.hom).obj
            ((p.extension Λ).obj L.homology))))) := by
  sorry

end AlgebraicGeometry.ProEtale
