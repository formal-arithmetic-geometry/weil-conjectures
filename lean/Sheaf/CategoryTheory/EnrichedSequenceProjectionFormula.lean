/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.CategoryTheory.SequencePushforwardLimitProjections
public import Sheaf.CategoryTheory.CoefficientSequenceSectionsLimit
public import Sheaf.CategoryTheory.ClosedAdjunctionEnrichedIsomorphism
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.CategoryTheory.SystemEvaluationTopos
public import Sheaf.CategoryTheory.SystemRingedSequenceSite
public import Sheaf.CategoryTheory.SystemLevelLeftExtension
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.CategoryTheory.ClosedScalarHomComparison
public import Sheaf.Paper.CoefficientHomZeroClass
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Finite projections of the enriched sequence adjunction

Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 07A4, 08J9, 08JA and 0D6E;
agent uncurrying of the enriched finite projection, returned calculus step 14
(blueprint: lem-coef-enriched-sequence-projection-formula).

Index n denotes positive level n+1. We use the sequence-site realization of systems
and the recorded equivalence with strict semilinear systems to retain total-limit
projections and the strict derived-sections comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open WeilConjectures.SemilinearSections
namespace SheafOfModules.EnrichedSequenceProjection

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- Global sections as maps from the recorded rank-one module.
Source: Stacks 08JA (blueprint: lem-coef-enriched-sequence-projection-formula). -/
abbrev homSections (A : Sheaf J CommRingCat.{max c v r}) :
    sequenceCoefficientModules A ⥤ AddCommGrpCat.{max c v r} :=
  preadditiveCoyoneda.obj (op (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)))

/-- The comparison of the two ordinary sections presentations is fixed on every section.
Source: Stacks 01FT, 08JA
(blueprint: lem-coef-enriched-sequence-projection-formula).
Proof: a limit element is a compatible family of sections. The unit-Hom equivalence
sends a map out of the rank-one module to its value on one. These inverse operations
preserve addition and commute with module maps. Equality of all section evaluations
makes the isomorphism unique. This also applies to the empty site. -/
theorem ordinarySectionsIso_exists (A : Sheaf J CommRingCat.{max c v r}) :
    ∃! ξ : sequenceCoefficientSections A ≅ homSections.{c, v, r} J A,
      ∀ (M : sequenceCoefficientModules A) (x : (sequenceCoefficientSections A).obj M)
        (U : Cᵒᵖ),
        (M.unitHomEquiv ((ξ.hom.app M) x)).val U =
          (lim.π U).app ((toSheaf (derivedChangeRingIndependentCoefficients J A) ⋙
            sheafToPresheaf J AddCommGrpCat.{max c v r}).obj M) x := by
  sorry

/-- The identity-on-sections comparison, determined uniquely by its section formula.
Source: Stacks 01FT, 08JA
(blueprint: lem-coef-enriched-sequence-projection-formula). -/
def ordinarySectionsIso (A : Sheaf J CommRingCat.{max c v r}) :=
  (ordinarySectionsIso_exists.{c, v, r} J A).exists.choose

/-- The canonical K-injective computation of the recorded zeroth hypercohomology.
Source: Stacks 070I, 08JA
(blueprint: lem-coef-enriched-sequence-projection-formula). -/
def sectionsResolutionIso (A : Sheaf J CommRingCat.{max c v r})
    (I : CochainComplex (sequenceCoefficientModules A) ℤ) (hI : I.IsKInjective) :
    (ringedSiteZerothHypercohomologyOfUniverses.{c, v, r} J A).obj
        (DerivedCategory.Q.obj I) ≅
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).obj
        (DerivedCategory.Q.obj (((homSections.{c, v, r} J A).mapHomologicalComplex
          (.up ℤ)).obj I)) :=
  letI : IsGrothendieckAbelian.{max c v r} (sequenceCoefficientModules A) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J A).1
  letI : I.IsKInjective := hI
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).mapIso
    ((homSections.{c, v, r} J A).rightDerivedFunctorObjQIso I)

/-- The sections presentation transport on H0, fixed by its computation on resolutions.
Source: Stacks 070I, 08JA
(blueprint: lem-coef-enriched-sequence-projection-formula).
Proof: on each K-injective complex both derived sections presentations are computed by
ordinary sections. Apply ordinarySectionsIso termwise and conjugate by the two derived
units. Naturality on the K-injective homotopy category descends along its equivalence
with the derived category. The same equivalence proves uniqueness. No evaluation of a
varying-coefficient K-injective system is used. -/
theorem sectionsH0Comparison_exists (A : Sheaf J CommRingCat.{max c v r})
    (p : SequenceSectionsDerivedPair (sequenceCoefficientSections A)) :
    ∃! ξ : p.functor ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0 ≅
        ringedSiteZerothHypercohomologyOfUniverses.{c, v, r} J A,
      ∀ (I : CochainComplex (sequenceCoefficientModules A) ℤ) (hI : I.IsKInjective),
        (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map (p.unit.app I) ≫
            ξ.hom.app (DerivedCategory.Q.obj I) =
          (DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map
            (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
              (ordinarySectionsIso.{c, v, r} J A) (.up ℤ)).hom.app I)) ≫
            (sectionsResolutionIso.{c, v, r} J A I hI).inv := by
  sorry

/-- The unique resolution-normalized transport to the hypercohomology used by 08JA.
Source: Stacks 08JA (blueprint: lem-coef-enriched-sequence-projection-formula). -/
def sectionsH0Comparison (A : Sheaf J CommRingCat.{max c v r})
    (p : SequenceSectionsDerivedPair (sequenceCoefficientSections A)) :=
  (sectionsH0Comparison_exists.{c, v, r} J A p).exists.choose

/-- The recorded exact equivalence from sequence-site modules to strict systems, derived.
Source: Stacks 05RU, 0941 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
abbrev toStrict : DS.{c, v, max c v r} J B τ ⥤
    DerivedCategory (StrictRingSystem (rings.{c, v, max c v r} J B τ)) :=
  letI : (sequenceToStrictSystemFunctor (rings.{c, v, max c v r} J B τ)).IsEquivalence :=
    inferInstanceAs
      (strictSystemSequenceEquivalence (rings.{c, v, max c v r} J B τ)).inverse.IsEquivalence
  (sequenceToStrictSystemFunctor (rings.{c, v, max c v r} J B τ)).mapDerivedCategory

/-- Identity on vertical sections specifies the comparison between the two existing
ordinary evaluations. Source: Zheng Construction 4.1; Stacks 0941
(blueprint: lem-coef-enriched-sequence-projection-formula).
Proof: the ring sheaves agree on every vertical slice. Both module pushforwards
retain the original sections and maps, so identity on sections is a natural module
isomorphism. Its section formula determines every component and hence uniqueness. -/
theorem ordinaryEvaluationIso_exists (n : ℕ) :
    ∃! ξ : sequenceToStrictSystemFunctor (rings.{c, v, max c v r} J B τ) ⋙
        systemEvaluation (rings.{c, v, max c v r} J B τ) n ≅
          SemilinearSections.evaluation.{c, v, max c v r} J B τ n,
      ∀ (M : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ),
        HEq (fun x ↦ ((ξ.hom.app M).val.app U) x)
          (id : M.val.obj (op (n, U.unop)) → M.val.obj (op (n, U.unop))) := by
  sorry

/-- The unique identity-on-sections evaluation comparison.
Source: Stacks 0941 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
def ordinaryEvaluationIso (n : ℕ) :=
  (ordinaryEvaluationIso_exists.{c, v, r} J B τ n).exists.choose

/-- Evaluation agrees under the actual sequence-site equivalence, using the exact-functor
localization compositor and the specified identity-on-sections comparison.
Source: Stacks 0941 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
def toStrictEvaluation (n : ℕ) :
    toStrict.{c, v, r} J B τ ⋙
        derivedSystemEvaluation (rings.{c, v, max c v r} J B τ) n ≅
      e.{c, v, max c v r} J B τ n :=
  letI : (sequenceToStrictSystemFunctor (rings.{c, v, max c v r} J B τ)).IsEquivalence :=
    inferInstanceAs
      (strictSystemSequenceEquivalence (rings.{c, v, max c v r} J B τ)).inverse.IsEquivalence
  letI := SemilinearSections.evaluationAdditive.{c, v, max c v r} J B τ n
  letI := SemilinearSections.evaluationLimits.{c, v, max c v r} J B τ n
  letI := SemilinearSections.evaluationColimits.{c, v, max c v r} J B τ n
  (Functor.mapDerivedCategoryCompIso
    (sequenceToStrictSystemFunctor (rings.{c, v, max c v r} J B τ))
    (systemEvaluation (rings.{c, v, max c v r} J B τ) n)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (ordinaryEvaluationIso.{c, v, r} J B τ n)

/-- The total derived direct image in the sequence-site realization, computed through
strict systems by the dependency's universal derived pair.
Source: Stacks 0941, 0D6E (blueprint: lem-coef-enriched-sequence-projection-formula). -/
abbrev limitPushforward (A : Sheaf J CommRingCat.{max c v r})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ rings.{c, v, max c v r} J B τ)
    (s : SequenceSectionsComparisons (rings.{c, v, max c v r} J B τ) A α)
    (p : SequenceSectionsDerivedPair (sequenceProjectionDirectImage s)) :=
  toStrict.{c, v, r} J B τ ⋙ p.functor

/-- Actual finite projection, transported by the identity-on-sections comparisons.
Source: Stacks 0941, 0D6E (blueprint: lem-coef-enriched-sequence-projection-formula). -/
def projection (A : Sheaf J CommRingCat.{max c v r})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ rings.{c, v, max c v r} J B τ)
    (s : SequenceSectionsComparisons (rings.{c, v, max c v r} J B τ) A α)
    (p : SequenceSectionsDerivedPair (sequenceProjectionDirectImage s))
    (π : ∀ n : ℕ, p.functor ⟶ s.restriction.functor.mapDerivedCategory ⋙
      ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
        (op n)).mapDerivedCategory) (n : ℕ) :
    limitPushforward.{c, v, r} J B τ A α s p ⟶
      e.{c, v, max c v r} J B τ n ⋙ resD (α.app (op n)) :=
  Functor.whiskerLeft (toStrict.{c, v, r} J B τ) (π n) ≫
    Functor.whiskerLeft (toStrict.{c, v, r} J B τ)
      (sequenceRestrictionDerivedEvaluation s.restriction n).hom ≫
    Functor.whiskerRight (toStrictEvaluation.{c, v, r} J B τ n).hom
      (resD (α.app (op n)))

variable (A : Sheaf J CommRingCat.{max c v r})
  (d : Data.{c, v, r} J B τ) (a : SemilinearSections.Closed.{c, v, r} J A)
  (R : D.{c, v, max c v r} J A ⥤ DS.{c, v, max c v r} J B τ)
  (L : DS.{c, v, max c v r} J B τ ⥤ D.{c, v, max c v r} J A)
  (adj : R ⊣ L) (μ : a.tensor ⋙ R ≅ (R.prod R) ⋙ d.closed.tensor)
  (α : (Functor.const ℕᵒᵖ).obj A ⟶ rings.{c, v, max c v r} J B τ)
  (σ : ∀ n : ℕ, ScalarData.{c, v, max c v r} (α.app (op n)))
  (ρ : ∀ n : ℕ, R ⋙ e.{c, v, max c v r} J B τ n ≅ (σ n).T)

/-- Evaluation of the actual system tensor-pullback comparison, transported along rho.
Its representative model in the theorem below fixes this very map, before choosing nu.
Source: Stacks 07A4, its total-complex comparison on flat-term K-flat representatives
(blueprint: lem-coef-enriched-sequence-projection-formula). -/
def evaluatedTensorComparison (n : ℕ) :
    a.tensor ⋙ (σ n).T ≅ ((σ n).T.prod (σ n).T) ⋙ (d.levelClosed n).tensor :=
  Functor.isoWhiskerLeft a.tensor (ρ n).symm ≪≫
    Functor.isoWhiskerRight μ (e.{c, v, max c v r} J B τ n) ≪≫
    Functor.isoWhiskerLeft (R.prod R) (d.tensorEvaluation n) ≪≫
    Functor.isoWhiskerRight (NatIso.prod (ρ n) (ρ n)) (d.levelClosed n).tensor

/-- V is the recorded derived internal Hom over A.
Source: Stacks 08J9 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
abbrev sourceHom (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ) :=
  (internalHom.{c, v, r} J A).obj (op P, L.obj N)

/-- J is the recorded derived internal Hom on the ringed sequence site.
Source: Stacks 08J9 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
abbrev systemHom (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ) :=
  (internalHom.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ)).obj (op (R.obj P), N)

/-- The finite internal Hom, with scalar extension only in its first input.
Source: Stacks 07A6, 08J9 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
abbrev levelHom (P : D.{c, v, max c v r} J A)
    (N : DS.{c, v, max c v r} J B τ) (n : ℕ) :=
  (internalHom.{c, v, r} J (B n)).obj
    (op ((σ n).T.obj P), (e.{c, v, max c v r} J B τ n).obj N)

/-- The evaluation-defined b, with no arbitrary comparison map.
Source: Stacks 07A6, 08J9 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
def comparison (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ) :=
  ClosedAdjunctionComparison.comparison a.tensor d.closed.tensor
    (internalHom.{c, v, r} J A)
    (internalHom.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ))
    a.transpose d.closed.transpose R L (fun X Y ↦ (μ.app (X, Y)).symm) adj P N

/-- Delta is the unit followed by L(b), as in the closed-adjunction dependency.
Source: Stacks 07A6, 08J9 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
def delta (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ) :=
  ClosedAdjunctionComparison.adjointComparison a.tensor d.closed.tensor
    (internalHom.{c, v, r} J A)
    (internalHom.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ))
    a.transpose d.closed.transpose R L (fun X Y ↦ (μ.app (X, Y)).symm) adj P N

/-- The cartesian first-input Hom comparison followed by the scalar-extension identification.
Source: Stacks 08J9; Zheng Construction 4.1
(blueprint: lem-coef-enriched-sequence-projection-formula). -/
def homIdentification (P : D.{c, v, max c v r} J A)
    (N : DS.{c, v, max c v r} J B τ)
    (hP : Normalized.{c, v, max c v r} J B τ d.scalar (R.obj P)) (n : ℕ) :
    (e.{c, v, max c v r} J B τ n).obj (systemHom.{c, v, r} J B τ A R P N) ≅
      levelHom.{c, v, r} J B τ A α σ P N n :=
  (d.homEvaluation (R.obj P) hP n).app N ≪≫
    (internalHom.{c, v, r} J (B n)).mapIso
      (Iso.prod ((ρ n).app P).symm.op (Iso.refl _))

/-- Component of the system counit, with its source identified with scalar extension.
Source: Stacks 07A6, 0941 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
def counitLevel (N : DS.{c, v, max c v r} J B τ) (n : ℕ) :
    (σ n).T.obj (L.obj N) ⟶ (e.{c, v, max c v r} J B τ n).obj N :=
  (ρ n).inv.app (L.obj N) ≫
    (e.{c, v, max c v r} J B τ n).map (adj.counit.app N)

/-- Reduced evaluation followed by the actual counit component. The inverse tensor
comparison is precisely the displayed canonical tensor reassociation in the node.
Source: Stacks 07A4, 07A6, 08J9
(blueprint: lem-coef-enriched-sequence-projection-formula). -/
def reducedEvaluation
    (ν : ∀ n : ℕ, a.tensor ⋙ (σ n).T ≅ ((σ n).T.prod (σ n).T) ⋙ (d.levelClosed n).tensor)
    (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ) (n : ℕ) :=
  (ν n).inv.app (sourceHom.{c, v, r} J B τ A L P N, P) ≫
    (σ n).T.map (a.evaluation P (L.obj N)) ≫
      counitLevel.{c, v, r} J B τ A R L adj α σ ρ N n

/-- The scalar internal-Hom adjunction after H_A(P,pi_n), using its existing five
normalized scalar and closed Hom bijections. This is the internal scalar-extension map,
not an integral Hom/tensor base-change isomorphism.
Source: Stacks 07A6, 08J9 (blueprint: lem-coef-enriched-sequence-projection-formula). -/
def internalScalarMap
    (π : ∀ n : ℕ, L ⟶ e.{c, v, max c v r} J B τ n ⋙ resD (α.app (op n)))
    (ν : ∀ n : ℕ, a.tensor ⋙ (σ n).T ≅ ((σ n).T.prod (σ n).T) ⋙ (d.levelClosed n).tensor)
    (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ) (n : ℕ) :=
  (internalHom.{c, v, r} J A).map (Prod.mkHom (𝟙 (op P)) ((π n).app N)) ≫
    (ClosedScalarHom.component a (d.levelClosed n) (σ n).adjunction (ν n) P
      ((e.{c, v, max c v r} J B τ n).obj N)).inv

/-- Finite projection of delta, with the specified cartesian-Hom identification.
Source: Stacks 07A6, 08J9, 0941
(blueprint: lem-coef-enriched-sequence-projection-formula). -/
def finiteProjection
    (π : ∀ n : ℕ, L ⟶ e.{c, v, max c v r} J B τ n ⋙ resD (α.app (op n)))
    (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ)
    (hP : Normalized.{c, v, max c v r} J B τ d.scalar (R.obj P)) (n : ℕ) :=
  delta.{c, v, r} J B τ A d a R L adj μ P N ≫
    (π n).app (systemHom.{c, v, r} J B τ A R P N) ≫
    (resD (α.app (op n))).map
      (homIdentification.{c, v, r} J B τ A d R α σ ρ P N hP n).hom

/-- The finite scalar-extension adjunct of a projected morphism, then its closed transpose.
Source: Stacks 07A6 and 08J9
(blueprint: lem-coef-enriched-sequence-projection-formula). -/
def uncurried
    (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ) (n : ℕ)
    (q : sourceHom.{c, v, r} J B τ A L P N ⟶
      (resD (α.app (op n))).obj (levelHom.{c, v, r} J B τ A α σ P N n)) :=
  ((d.levelClosed n).transpose _ ((σ n).T.obj P)
    ((e.{c, v, max c v r} J B τ n).obj N)).symm
      (((σ n).adjunction.homEquiv _ _).symm q)

/-- The global map RΓ(delta), transported to the total limit and projected at n,
then identified with finite derived sections of the evaluated internal Hom.
Source: Stacks 0D6E, 08JA
(blueprint: lem-coef-enriched-sequence-projection-formula). -/
def globalProjection
    (s : SequenceSectionsComparisons (rings.{c, v, max c v r} J B τ) A α)
    (p : SequenceSectionsDerivedPair (sequenceProjectionDirectImage s))
    (hL : L ≅ limitPushforward.{c, v, r} J B τ A α s p)
    (rl : SequenceSectionsDerivedPair
      (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{max c v r}) ⥤ AddCommGrpCat.{max c v r}))
    (πL : ∀ n : ℕ, rl.functor ⟶
      ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{max c v r}).obj
        (op n)).mapDerivedCategory)
    (κ : p.functor ⋙ (s.finite A).functor ≅ s.global ⋙ rl.functor)
    (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ)
    (hP : Normalized.{c, v, max c v r} J B τ d.scalar (R.obj P)) (n : ℕ) :=
  (s.finite A).functor.map (delta.{c, v, r} J B τ A d a R L adj μ P N) ≫
    (s.finite A).functor.map (hL.hom.app (systemHom.{c, v, r} J B τ A R P N)) ≫
    κ.hom.app ((toStrict.{c, v, r} J B τ).obj
      (systemHom.{c, v, r} J B τ A R P N)) ≫
    (πL n).app (s.global.obj ((toStrict.{c, v, r} J B τ).obj
      (systemHom.{c, v, r} J B τ A R P N))) ≫
    (s.finiteEvaluation n).hom.app ((toStrict.{c, v, r} J B τ).obj
      (systemHom.{c, v, r} J B τ A R P N)) ≫
    (s.finite (B n)).functor.map
      ((toStrictEvaluation.{c, v, r} J B τ n).hom.app
        (systemHom.{c, v, r} J B τ A R P N) ≫
        (homIdentification.{c, v, r} J B τ A d R α σ ρ P N hP n).hom)

/-- The finite projection of the evaluation-defined enriched adjunction is uniquely
characterized by reduced evaluation, equals the internal scalar-extension adjunction
following H_A(P,pi_n), and has the same description after the specified strict-system
sections/limit comparison. Its degree-zero Hom action is h sent to e_n after scalar
extension of h.

The derived pair p, its complex-normalized projections piP, and hL present the actual
right derived sequence projection. The unit equation normalizes the transported
adjunction and rho. The representative model for evaluatedTensorComparison fixes
actual evaluations of mu by the ordinary pure-tensor formula, the total summand maps,
and the K-flat localization square; the tensor equation then fixes nu to these maps.
These are presentations of the specified operations, not flatness,
perfectness, boundedness, or a normalization assumption on the Hom system.

Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 07A4, 08J9, 08JA and 0D6E;
agent uncurrying of the enriched finite projection, returned calculus step 14
(blueprint: lem-coef-enriched-sequence-projection-formula).

Proof plan, following the node's six steps:
1. Naturality of the actual total-limit projection at b and the unit normalization give
   pi_n(delta) = Res(b_n) eta_n, by lem-coef-sequence-pushforward-limit-projections and
   lem-coef-sequence-projection-derived-adjunction. This is an equality of derived maps.
2. Uncurry b using lem-coef-closed-adjunction-enriched-isomorphism. Apply the tensor
   evaluation and cartesian first-input Hom evaluation of lem-coef-semilinear-derived-sections.
   The tensor-pullback comparison of lem-weil-pbc-ringed-topoi-derived-tensor-pullback
   is fixed after evaluation by hMuModel: its ordinary pure tensors and total summands
   give the canonical 07A4 comparison on K-flat representatives. The compatibility
   equation identifies this actual evaluated comparison with nu. Thus the resulting
   map is precisely reducedEvaluation; no faithfulness of evaluation is used.
3. Scalar transposition (lem-pur-sheaf-ring-derived-coefficient-adjunction), followed by
   closed transposition (lem-sf-ringed-derived-closed-symmetric-monoidal), is a bijection.
   Step 1 therefore identifies the finite projection as the unique map with this uncurry.
4. Uncurry the inverse scalar internal-Hom comparison of lem-sfb-dc-hom-scalar-adjunction
   after H_A(P,pi_n). Naturality of evaluation and the counit normalization give the same
   reduced evaluation. Step 3 proves the equivalent internal formula without extending
   the second Hom input.
5. Use lem-coef-sequence-sections-limit-comparison for the strict right derived pair p.
   Its normalized composition comparison and finite comparisons are natural. Its nth
   projection is sections of piP followed by inverse scalar restriction comparison.
   Transport through toStrictEvaluation and hL, then apply sections to step 4. This is
   the asserted global mapping-complex formula on arbitrary Hom systems.
6. Take degree zero using coefficientHomZeroEquiv of def-coef-hom-zero-cycle-class,
   uniquely fixed by naturality and its representative normalization: a degree-zero Hom
   cocycle for a chain map g represents Q(g), with the inverse resolution augmentation.
   Naturality makes H_A(P,pi_n) postcomposition with pi_n. The normalized scalar adjunction
   sends that composite to scalar(h) followed by the evaluated system counit, giving the
   final displayed Hom equation for H0 of globalProjection itself. The uniquely
   resolution-normalized sectionsH0Comparison transports the limit-based sections to
   the hypercohomology used by 08JA at both endpoints. No evaluated K-injective system
   is assumed K-injective. -/
theorem enrichedSequenceProjectionFormula
    (s : SequenceSectionsComparisons (rings.{c, v, max c v r} J B τ) A α)
    (_hs : s.Normalized)
    (p : SequenceSectionsDerivedPair (sequenceProjectionDirectImage s))
    (πP : ∀ n : ℕ, p.functor ⟶ s.restriction.functor.mapDerivedCategory ⋙
      ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
        (op n)).mapDerivedCategory)
    (_hπP : ∀ (X : CochainComplex (StrictRingSystem (rings.{c, v, max c v r} J B τ)) ℤ)
      (n : ℕ),
      p.unit.app X ≫ (πP n).app (DerivedCategory.Q.obj X) ≫
          ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
            (op n)).mapDerivedCategory.map
            (s.restriction.functor.mapDerivedCategoryFactors.hom.app X) ≫
          ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
            (op n)).mapDerivedCategoryFactors.hom.app
            ((s.restriction.functor.mapHomologicalComplex (.up ℤ)).obj X) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
          ((s.restriction.functor.mapHomologicalComplex (.up ℤ)).obj X)))
    (hL : L ≅ limitPushforward.{c, v, r} J B τ A α s p)
    (π : ∀ n : ℕ, L ⟶ e.{c, v, max c v r} J B τ n ⋙ resD (α.app (op n)))
    (_hπ : ∀ n : ℕ, π n = hL.hom ≫ projection.{c, v, r} J B τ A α s p πP n)
    (_hunit : ∀ (X : D.{c, v, max c v r} J A) (n : ℕ),
      adj.unit.app X ≫ (π n).app (R.obj X) ≫
        (resD (α.app (op n))).map ((ρ n).hom.app X) = (σ n).adjunction.unit.app X)
    (aModels : Models.{c, v, r} J A a)
    (_hμModel : ∀ n : ℕ, ScalarTensorComparisonModel.{c, v, r} J A (B n)
      (α.app (op n)) (σ n) a (d.levelClosed n) aModels (d.levelTensorModels n)
      (evaluatedTensorComparison.{c, v, r} J B τ A d a R μ α σ ρ n))
    (ν : ∀ n : ℕ, a.tensor ⋙ (σ n).T ≅ ((σ n).T.prod (σ n).T) ⋙ (d.levelClosed n).tensor)
    (_hμ : ∀ (X Y : D.{c, v, max c v r} J A) (n : ℕ),
      (e.{c, v, max c v r} J B τ n).map (μ.hom.app (X, Y)) ≫
          (d.tensorEvaluation n).hom.app (R.obj X, R.obj Y) ≫
          (d.levelClosed n).tensor.map (Prod.mkHom ((ρ n).hom.app X) ((ρ n).hom.app Y)) =
        (ρ n).hom.app (a.tensor.obj (X, Y)) ≫ (ν n).hom.app (X, Y)) :
    ∃ (rl : SequenceSectionsDerivedPair
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{max c v r}) ⥤ AddCommGrpCat.{max c v r}))
      (πL : ∀ n : ℕ, rl.functor ⟶
        ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{max c v r}).obj
          (op n)).mapDerivedCategory)
      (κ : p.functor ⋙ (s.finite A).functor ≅ s.global ⋙ rl.functor),
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{max c v r}) ℤ) (n : ℕ),
        rl.unit.app X ≫ (πL n).app (DerivedCategory.Q.obj X) ≫
          ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{max c v r}).obj
            (op n)).mapDerivedCategoryFactors.hom.app X =
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X)) ∧
      (∀ X : CochainComplex (StrictRingSystem (rings.{c, v, max c v r} J B τ)) ℤ,
        (s.finite A).unit.app
            (((sequenceProjectionDirectImage s).mapHomologicalComplex (.up ℤ)).obj X) ≫
          (s.finite A).functor.map (p.unit.app X) ≫ κ.hom.app (DerivedCategory.Q.obj X) =
        DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (sequenceSectionsLimitOrdinary s) (.up ℤ)).hom.app X) ≫
          rl.unit.app (((s.restriction.functor ⋙ sequenceTowerSections A).mapHomologicalComplex
            (.up ℤ)).obj X) ≫
          rl.functor.map (s.tower.unit.app
            ((s.restriction.functor.mapHomologicalComplex (.up ℤ)).obj X)) ≫
          rl.functor.map (s.tower.functor.map
            (s.restriction.functor.mapDerivedCategoryFactors.inv.app X))) ∧
      ∀ (P : D.{c, v, max c v r} J A) (N : DS.{c, v, max c v r} J B τ)
        (hP : Normalized.{c, v, max c v r} J B τ d.scalar (R.obj P))
        (_hN : Normalized.{c, v, max c v r} J B τ d.scalar N) (n : ℕ),
        (uncurried.{c, v, r} J B τ A d L α σ P N n
            (finiteProjection.{c, v, r} J B τ A d a R L adj μ α σ ρ π P N hP n) =
          reducedEvaluation.{c, v, r} J B τ A d a R L adj α σ ρ ν P N n) ∧
        (∀ q : sourceHom.{c, v, r} J B τ A L P N ⟶
            (resD (α.app (op n))).obj (levelHom.{c, v, r} J B τ A α σ P N n),
          uncurried.{c, v, r} J B τ A d L α σ P N n q =
              reducedEvaluation.{c, v, r} J B τ A d a R L adj α σ ρ ν P N n →
            q = finiteProjection.{c, v, r} J B τ A d a R L adj μ α σ ρ π P N hP n) ∧
        (finiteProjection.{c, v, r} J B τ A d a R L adj μ α σ ρ π P N hP n =
          internalScalarMap.{c, v, r} J B τ A d a L α σ π ν P N n) ∧
        (globalProjection.{c, v, r} J B τ A d a R L adj μ α σ ρ s p hL rl πL κ P N hP n =
          (s.finite A).functor.map
              (internalScalarMap.{c, v, r} J B τ A d a L α σ π ν P N n) ≫
            (s.scalar (α.app (op n))).inv.app (levelHom.{c, v, r} J B τ A α σ P N n)) ∧
        (∀ h : P ⟶ L.obj N,
          coefficientHomZeroEquiv.{r, c, v} J (B n)
            ((σ n).T.obj P) ((e.{c, v, max c v r} J B τ n).obj N)
            (((DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0).map
                (globalProjection.{c, v, r} J B τ A d a R L adj μ α σ ρ
                  s p hL rl πL κ P N hP n) ≫
              (sectionsH0Comparison.{c, v, r} J (B n) (s.finite (B n))).hom.app
                (levelHom.{c, v, r} J B τ A α σ P N n))
              ((sectionsH0Comparison.{c, v, r} J A (s.finite A)).inv.app
                (sourceHom.{c, v, r} J B τ A L P N)
                ((coefficientHomZeroEquiv.{r, c, v} J A P (L.obj N)).symm h))) =
            (σ n).T.map h ≫ counitLevel.{c, v, r} J B τ A R L adj α σ ρ N n) := by
  sorry

end SheafOfModules.EnrichedSequenceProjection

