/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.CategoryTheory.KInjectiveComputes
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import Sheaf.CategoryTheory.SiteTruncationDerivedLimit
import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups
import WeilConjectures.CategoryTheory.Triangulated.MilnorBoundaryFactorization
import WeilConjectures.CategoryTheory.Triangulated.MilnorProjectionFactorization

/-! # Unbounded cohomology on an acyclic basis of a ringed site

Source: Stacks Project, Cohomology on Sites, Tag 0BKZ,
`lemma-cohomology-over-U-trivial`, including its truncation-limit construction
(blueprint: lem-sfb-ringed-site-acyclic-basis-cohomology).

The edge is specified by the quotient of cycles, as a natural transformation with values
in presheaves of modules. Thus its components are linear and its restriction squares are
semilinear over the actual restriction of the ring. K-injective models are quantified,
not chosen by an unspecified existence assertion. No boundedness is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSiteAcyclicBasis

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J RingCat.{max c v r})

/-- Sectionwise cohomology as a presheaf of modules, retaining all restriction maps.
Source: Stacks 0BKZ (blueprint: lem-sfb-ringed-site-acyclic-basis-cohomology). -/
abbrev sectionCohomology (q : ℤ) :=
  (SheafOfModules.forget.{max c v r} R).mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.homologyFunctor _ (.up ℤ) q

/-- Sections of the cohomology sheaf, without sheafifying again.
Source: Stacks 0BKZ (blueprint: lem-sfb-ringed-site-acyclic-basis-cohomology). -/
abbrev cohomologySections (q : ℤ) :=
  HomologicalComplex.homologyFunctor (ringedSiteModules.{max c v r} R) (.up ℤ) q ⋙
    SheafOfModules.forget.{max c v r} R

/-- The canonical kernel comparison for cycles. Kernels of module sheaves are sectionwise.
Source: Stacks 0BKZ (blueprint: lem-sfb-ringed-site-acyclic-basis-cohomology). -/
def sectionCyclesIso (I : CochainComplex (ringedSiteModules.{max c v r} R) ℤ) (q : ℤ) :
    (SheafOfModules.forget.{max c v r} R).obj (I.cycles q) ≅
      (((SheafOfModules.forget.{max c v r} R).mapHomologicalComplex (.up ℤ)).obj I).cycles q :=
  ((((SheafOfModules.forget.{max c v r} R).mapHomologicalComplex
    (.up ℤ)).obj I).sc q).isoCyclesOfIsLimit
    (KernelFork.mapIsLimit _ (I.sc q).cyclesIsKernel (SheafOfModules.forget.{max c v r} R))

variable [HasDerivedCategory.{w} (ringedSiteModules.{max c v r} R)]

/-- The hypothesis of 0BKZ, using every K-injective resolution of each H^q(K)[0].
Source: Stacks 0BKZ (blueprint: lem-sfb-ringed-site-acyclic-basis-cohomology). -/
def IsAcyclicOn (B : Set C) (K : DerivedCategory (ringedSiteModules.{max c v r} R)) : Prop :=
  ∀ (U : C), U ∈ B → ∀ (p q : ℤ), 0 < p →
    ∀ (I : CochainComplex (ringedSiteModules.{max c v r} R) ℤ)
      (ι : (CochainComplex.singleFunctor (ringedSiteModules.{max c v r} R) 0).obj
        ((DerivedCategory.homologyFunctor _ q).obj K) ⟶ I),
      I.IsKInjective → QuasiIso ι →
        IsZero ((((SheafOfModules.evaluation.{max c v r} R (op U)).mapHomologicalComplex
          (.up ℤ)).obj I).homology p)

/-- Transport the cycles-normalized edge on a K-injective model to the given derived object.
Source: Stacks 0BKZ (blueprint: lem-sfb-ringed-site-acyclic-basis-cohomology). -/
def modelEdge (α : ∀ q : ℤ, sectionCohomology.{c, v, r} R q ⟶ cohomologySections.{c, v, r} R q)
    (K : DerivedCategory (ringedSiteModules.{max c v r} R))
    (I : CochainComplex (ringedSiteModules.{max c v r} R) ℤ)
    (e : DerivedCategory.Q.obj I ≅ K) (q : ℤ) :
    (sectionCohomology.{c, v, r} R q).obj I ⟶
      (SheafOfModules.forget.{max c v r} R).obj ((DerivedCategory.homologyFunctor _ q).obj K) :=
  (α q).app I ≫ (SheafOfModules.forget.{max c v r} R).map
    (((DerivedCategory.homologyFunctorFactors _ q).app I).inv ≫
      (DerivedCategory.homologyFunctor _ q).map e.hom)

/-- Canonical, linear, natural and restriction-compatible unbounded acyclic-basis edges.
Source: Stacks 0BKZ, including the truncation-limit proof, and its use in 071Q
(blueprint: lem-sfb-ringed-site-acyclic-basis-cohomology).

Proof plan:
1. Evaluation is additive and left exact. The recorded ringed-site resolution theorem
   supplies functorial K-injective models with injective terms; evaluation preserves
   homotopies. The K-injective Hom bijection descends this computation to D(R).
2. Set K_n = truncGE(-n) K. Apply thm-sp-truncation-e2 to its bounded-below model.
   Acyclicity kills every positive column, and the finite filtration identifies the
   abutment with sections of H^q(K_n). Its edge sends a cycle to its homology class,
   exactly the equation with sectionCyclesIso below.
3. Apply lem-kun-site-truncation-derived-limit with d=0 and the covering subset B.
   Apply lem-kun-site-rgamma-derived-limit to its specified Roos triangle.
4. The Milnor projection and boundary factorizations identify the projection-induced
   map to the inverse limit as surjective with kernel R^1 lim in the preceding degree.
5. For n >= max(0,1-q), both cohomology towers are constant. The Roos difference map
   is surjective: solve forwards using inverse tail transitions and backwards through
   the finite initial segment. Its kernel is identified by any tail coordinate.
6. Compose the bounded-below edge with H^q(RGamma(c_n)). The transition identities
   show independence of n and identify the composite with the cycles-normalized map.
7. Kernels, quotients, evaluation and truncation are functorial on module complexes
   and on restrictions. This gives α as a natural transformation of presheaves of
   modules, hence linearity and both required naturalities, also for derived morphisms
   by the K-injective Hom bijection. The displayed model equation includes every
   canonical lower truncation projection, so records the eventually constant edge.
8. For M[0], cycles and cohomology are M in degree zero and their quotient is the
   identity. The last equation retains this normalization before taking any resolution;
   its naturality square with M[0] -> I gives the derived degree-zero normalization.
-/
theorem exists_acyclicBasisCohomology
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (B : Set C)
    (_hB : ∀ U : C, ∃ S : Presieve U, Sieve.generate S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f → V ∈ B) :
    ∃! α : ∀ q : ℤ, sectionCohomology.{c, v, r} R q ⟶ cohomologySections.{c, v, r} R q,
      (∀ (I : CochainComplex (ringedSiteModules.{max c v r} R) ℤ) (q : ℤ),
        (sectionCyclesIso.{c, v, r} R I q).hom ≫
            (((SheafOfModules.forget.{max c v r} R).mapHomologicalComplex
              (.up ℤ)).obj I).homologyπ q ≫
              (α q).app I = (SheafOfModules.forget.{max c v r} R).map (I.homologyπ q)) ∧
      (∀ (K : DerivedCategory (ringedSiteModules.{max c v r} R)), IsAcyclicOn.{c, v, r, w} R B K →
        ∀ (I : CochainComplex (ringedSiteModules.{max c v r} R) ℤ), I.IsKInjective →
          ∀ (e : DerivedCategory.Q.obj I ≅ K) (q : ℤ) (U : C), U ∈ B →
            IsIso ((modelEdge.{c, v, r, w} R α K I e q).app (op U))) ∧
      (∀ (K L : DerivedCategory (ringedSiteModules.{max c v r} R)) (a : K ⟶ L)
        (I T : CochainComplex (ringedSiteModules.{max c v r} R) ℤ)
        (eI : DerivedCategory.Q.obj I ≅ K) (eT : DerivedCategory.Q.obj T ≅ L)
        (f : I ⟶ T), DerivedCategory.Q.map f ≫ eT.hom = eI.hom ≫ a →
          ∀ q : ℤ, (sectionCohomology.{c, v, r} R q).map f ≫ modelEdge.{c, v, r, w} R α L T eT q =
            modelEdge.{c, v, r, w} R α K I eI q ≫
              (SheafOfModules.forget.{max c v r} R).map
                ((DerivedCategory.homologyFunctor _ q).map a)) ∧
      (∀ (K : DerivedCategory (ringedSiteModules.{max c v r} R)),
        IsAcyclicOn.{c, v, r, w} R B K →
        ∀ (I : CochainComplex (ringedSiteModules.{max c v r} R) ℤ), I.IsKInjective →
        ∀ (eI : DerivedCategory.Q.obj I ≅ K) (n : ℕ) (q : ℤ), 1 - q ≤ (n : ℤ) →
        ∀ (T : CochainComplex (ringedSiteModules.{max c v r} R) ℤ), T.IsKInjective →
        ∀ (eT : DerivedCategory.Q.obj T ≅
            (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K)
          (f : I ⟶ T),
          DerivedCategory.Q.map f ≫ eT.hom =
            eI.hom ≫ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K →
        ∀ (U : C), U ∈ B →
          IsIso (((sectionCohomology.{c, v, r} R q).map f).app (op U)) ∧
          modelEdge.{c, v, r, w} R α K I eI q ≫
              (SheafOfModules.forget.{max c v r} R).map
                ((DerivedCategory.homologyFunctor _ q).map
                  ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)) =
            (sectionCohomology.{c, v, r} R q).map f ≫
              modelEdge.{c, v, r, w} R α
                ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K) T eT q) ∧
      (∀ (M : ringedSiteModules.{max c v r} R),
        (SheafOfModules.forget.{max c v r} R).map
            (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 M).inv ≫
          (sectionCyclesIso.{c, v, r} R ((CochainComplex.singleFunctor _ 0).obj M) 0).hom ≫
          (((SheafOfModules.forget.{max c v r} R).mapHomologicalComplex (.up ℤ)).obj
            ((CochainComplex.singleFunctor _ 0).obj M)).homologyπ 0 ≫
          (α 0).app ((CochainComplex.singleFunctor _ 0).obj M) ≫
          (SheafOfModules.forget.{max c v r} R).map
            (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 M).hom =
          𝟙 ((SheafOfModules.forget.{max c v r} R).obj M)) := by
  sorry

end CategoryTheory.RingedSiteAcyclicBasis
