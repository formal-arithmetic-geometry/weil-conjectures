/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.StrictRoosComparison
public import Sheaf.CategoryTheory.StrictRoosModel
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction
import Sheaf.SixFunctors.ResolvingDerivedAdjunction
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.SequencePushforwardLimitProjections
import Sheaf.CategoryTheory.SystemRingedSequenceSite

/-!
# The actual completion unit on a strict quotient cone

Source: blueprint main-20261015, trace formula, rational Frobenius integral model,
proof (2)--(3); Stacks 07A6, 09T5, 0D6E, 0941 and 08TC. This is the normalization
refinement of those constructions, not a verbatim assertion of a Stacks tag.
(blueprint: lem-trf-completion-unit-strict-quotient-model).

The auxiliary structures package canonical constructions and their normalization
conditions. They introduce no alternative tensor, limit, or derived category.
The theorem asserts their existence together with the whole-morphism unit formula.
Index n denotes the positive exponent n+1. Site and coefficient universes are independent.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures
namespace CompletionUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Exact restriction of a system complex to its completed-coefficient tower.
Source: Stacks 0941 (blueprint: lem-trf-completion-unit-strict-quotient-model). -/
abbrev tower := (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)

/-- The ordinary sequence direct image: restriction of rings followed by inverse limit.
Source: Stacks 07A6, 0941 (blueprint: lem-trf-completion-unit-strict-quotient-model). -/
abbrev ordinaryLimit := coefficientSequenceRestriction l E W ⋙
  (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)

/-- The quotient-system tensor functor with its ordinary adjunction and actual tensor
unit. The evaluation isomorphisms identify its components with the recorded scalar
extension, and `transition` fixes the strict quotient maps, including all levels.
`unit_tensor` fixes the adjunction itself on sections, rather than only its functors.
Source: Stacks 03EK, 07A6, 0941 and item proof step 2
(blueprint: lem-trf-completion-unit-strict-quotient-model). -/
structure OrdinaryModel where
  tensor : scalarReductionSource l E W ⥤ coefficientSequenceModules l E W
  [additive : tensor.Additive]
  evaluation : ∀ n : ℕ, tensor ⋙ coefficientSequenceEvaluation l E W n ≅
    scalarReductionExtension l E W n
  transition : ∀ (M : scalarReductionSource l E W) {m n : ℕ} (h : n ≤ m),
    (coefficientSequenceTransition l E W h).app (tensor.obj M) ≫
        (normalizedDVRModuleRes l E W h).map ((evaluation n).hom.app M) =
      (evaluation m).hom.app M ≫ (coefficientOrdinaryQuotient l E W h).app M
  adjunction : tensor ⊣ ordinaryLimit l E W
  unit_tensor : ∀ (M : scalarReductionSource l E W) (n : ℕ) (V : W.ProEtᵒᵖ)
    (x : M.val.obj V),
    ((adjunction.unit.app M ≫
        limit.π ((coefficientSequenceRestriction l E W).obj (tensor.obj M)) (op n) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
          (tensor.obj M) ≫
        (scalarReductionRestriction l E W n).map ((evaluation n).hom.app M)).val.app V) x =
      unrestrictedIntegralTensorSection l E W n M V 1 x
  limitComparison : (ordinaryLimit l E W).mapHomologicalComplex (.up ℤ) ≅
    tower l E W ⋙ roosLimitFunctor
  limitComparison_projection : ∀ (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (n : ℕ) (p : ℤ),
    ((limitComparison.hom.app I) ≫
        limit.π ((tower l E W).obj I).asFunctor (op n)).f p =
      limit.π ((coefficientSequenceRestriction l E W).obj (I.X p)) (op n)

attribute [instance] OrdinaryModel.additive

/-- The strict quotient system of a complex is the termwise ordinary tensor functor.
Source: Stacks 06YY, 0941 (blueprint: lem-trf-completion-unit-strict-quotient-model). -/
abbrev OrdinaryModel.quotient (M : OrdinaryModel l E W) :=
  M.tensor.mapHomologicalComplex (.up ℤ)

/-- The ordinary-adjunction transpose, in the canonical termwise-limit coordinates.
Source: Stacks 07A6 and item proof step 2
(blueprint: lem-trf-completion-unit-strict-quotient-model). -/
def OrdinaryModel.transpose (M : OrdinaryModel l E W)
    {Q : CochainComplex (scalarReductionSource l E W) ℤ}
    {I : CochainComplex (coefficientSequenceModules l E W) ℤ}
    (a : (M.quotient l E W).obj Q ⟶ I) :
    Q ⟶ limit ((tower l E W).obj I).asFunctor :=
  (M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I a ≫
    M.limitComparison.hom.app I

/-- The strict quotient augmentation to the ordinary limit; its level maps are z tensor 1.
Source: Stacks 07A6, 0941 and item proof steps 2, 5
(blueprint: lem-trf-completion-unit-strict-quotient-model). -/
def OrdinaryModel.augmentation (M : OrdinaryModel l E W)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    Q ⟶ limit ((tower l E W).obj ((M.quotient l E W).obj Q)).asFunctor :=
  M.transpose l E W (𝟙 _)

/-- Canonical derived comparisons for the actual ordinary quotient adjunction.
The limit unit is pinned on every K-injective tower by the existing right-derived
functor comparison. The Roos isomorphism is normalized on the ordinary inclusion.
The system unit is the composition comparison for exact restriction and projection.
Finally `hom_normalization` derives the ordinary Hom correspondence on chain maps.
These conditions specify comparisons, rather than postulating arbitrary isomorphisms.
Source: Stacks 09T5, 0D6E, 0941 and item proof steps 3--4, 6
(blueprint: lem-trf-completion-unit-strict-quotient-model). -/
structure DerivedModel (S : CoefficientDerivedSystemCalculus l E W)
    (M : OrdinaryModel l E W) where
  towerLimitComparison :
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ) ≅ roosLimitFunctor
  towerLimitComparison_projection :
    ∀ (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ) (p : ℤ),
      (towerLimitComparison.hom.app Z ≫ limit.π Z.asFunctor (op n)).f p =
        limit.π (Z.X p) (op n)
  limitUnit : roosLimitFunctor ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W
  limitUnit_normalization :
    ∀ (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective],
      limitUnit.app J ≫
          ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
            scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom =
        DerivedCategory.Q.map (towerLimitComparison.inv.app J)
  roos : roosF ⋙ DerivedCategory.Q ≅
    DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W
  roos_normalization : ∀ Z,
    DerivedCategory.Q.map (roosι Z) ≫ roos.hom.app Z = limitUnit.app Z
  systemUnit : (ordinaryLimit l E W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ coefficientSequenceLimit l E W
  system_isIso : ∀ (I : CochainComplex (coefficientSequenceModules l E W) ℤ),
    I.IsKInjective → IsIso (systemUnit.app I)
  systemUnit_composition : ∀ I,
    systemUnit.app I = DerivedCategory.Q.map (M.limitComparison.hom.app I) ≫
      limitUnit.app ((tower l E W).obj I) ≫
      (coefficientConstantTowerLimit l E W).map
        ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app I)
  reductionComparison : DerivedCategory.Q ⋙ S.reduction ⟶
    M.quotient l E W ⋙ DerivedCategory.Q
  reduction_isLeftDerived : S.reduction.IsLeftDerivedFunctor reductionComparison
    (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ))
  reduction_isIso : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ),
    Q.IsKFlatIndependentCoefficients → (∀ p : ℤ, (Q.X p).IsFlatOnSite) →
      IsIso (reductionComparison.app Q)
  reduction_evaluation : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : Q.IsKFlatIndependentCoefficients) (_hflat : ∀ p : ℤ, (Q.X p).IsFlatOnSite) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E W n).map (reductionComparison.app Q) ≫
        (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
          ((M.quotient l E W).obj Q) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q) =
      (S.reductionEvaluation n).hom.app (DerivedCategory.Q.obj Q) ≫
        (coefficientFiniteReductionModel l E W Q hQ n).hom
  hom_normalization : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (a : (M.quotient l E W).obj Q ⟶ I),
    S.adjunction.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
        (reductionComparison.app Q ≫ DerivedCategory.Q.map a) =
      DerivedCategory.Q.map ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I a) ≫
        systemUnit.app I

/-- The strict cone augmentation is the ordinary-limit lift followed by the existing
zero-shifted-coordinate Roos inclusion. Thus this is a real chain map by construction.
Source: Stacks 08TC, 0941 and item proof step 5
(blueprint: lem-trf-completion-unit-strict-quotient-model). -/
def OrdinaryModel.coneAugmentation (M : OrdinaryModel l E W)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    Q ⟶ roosF.obj ((tower l E W).obj ((M.quotient l E W).obj Q)) :=
  M.augmentation l E W Q ≫ roosι _

/-- The normalized Roos comparison to the simultaneous reduction/limit object.
Both transports are the recorded localization comparison for exact restriction and
the universal left-derived comparison on the specified K-flat complex.
Source: Stacks 09T5, 0941 and item proof steps 3, 6
(blueprint: lem-trf-completion-unit-strict-quotient-model). -/
def DerivedModel.completionComparison
    {S : CoefficientDerivedSystemCalculus l E W} {M : OrdinaryModel l E W}
    (D : DerivedModel l E W S M) (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : Q.IsKFlatIndependentCoefficients) (hflat : ∀ p : ℤ, (Q.X p).IsFlatOnSite) :
    DerivedCategory.Q.obj (roosF.obj ((tower l E W).obj ((M.quotient l E W).obj Q))) ≅
      (coefficientSequenceLimit l E W).obj (S.reduction.obj (DerivedCategory.Q.obj Q)) :=
  D.roos.app _ ≪≫
    (coefficientConstantTowerLimit l E W).mapIso
      ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app
        ((M.quotient l E W).obj Q)).symm ≪≫
    (coefficientSequenceLimit l E W).mapIso
      (@asIso _ _ _ _ (D.reductionComparison.app Q) (D.reduction_isIso Q hQ hflat)).symm

/-- The actual completion unit, including its two-resolution composition normalization.
The existential packages choose only the canonical tensor/derived constructions fixed
by their universal properties and displayed normalizations. They add no hypothesis on N.
Every resolution in the last clause is universally quantified.

Source: blueprint main-20261015, rational Frobenius integral model, proof (2)--(3),
normalization refinement; Stacks 07A6, 09T5, 0D6E, 0941, 08TC.
(blueprint: lem-trf-completion-unit-strict-quotient-model).

Proof plan (the seven steps of the node):
1. Work in the fixed small module universe. Use det-pe-products-exact and
   prop-pur-kinjective-resolutions-exist on the sequence and constant-ring tower sites.
   Restriction is exact; it is not assumed to preserve K-injective complexes.
2. The ordinary tensor/limit adjunction sends a to the compatible family a_n(r_n z).
   Balancing gives its inverse b tensor z mapped to b times the nth limit projection.
   This constructs OrdinaryModel, its unit_tensor and the termwise-limit comparison.
3. Derive that adjunction with the flat-term K-flat representative on the left and a
   K-injective resolution on the right. The resolving-adjunction normalization says
   that the transpose of the resolved identity computes the actual unit, as a whole
   derived morphism; this supplies reductionComparison and hom_normalization.
4. Factor the sequence projection as ring restriction followed by constant-ring
   projection. The normalized derived direct-image composition theorem identifies its
   unit with systemUnit_composition. For arbitrary I and J as below, lim(j) is a
   quasi-isomorphism and represents this comparison. The constant sequence-site
   equivalence identifies J with a K-injective tower with injective degree terms.
5. The quotient transition sends r_(n+1) to r_n. Hence (1-s)gamma=0 and
   d(0,gamma z)=(0,gamma dz), so coneAugmentation has precisely zero shifted coordinate.
   Both H(j U(a))v and iota_J (lim j)b have coordinates (0,(j_n a_n r_n z)_n).
6. Apply lem-weil-strict-roos-comparison to j U(a). Its normalization gives the
   comparison as H(j U(a)) followed by the inverse inclusion and the derived limit
   identification. Cancel that inclusion in step 5 and substitute step 4 to get the
   displayed unit equality. No argument from level projections alone is used.
7. Every allowed I, a, J, j was arbitrary, so the formula is resolution-independent.
   The naturality of the actual adjunction unit gives the last equation for every
   derived morphism h. Quantifying over every representative isomorphism q also gives
   independence of the chosen K-flat representative. No bound or completeness enters. -/
theorem completionUnitStrictQuotientModel
    [∀ x : W, Invertible (l : W.residueField x)] :
    ∃ (S : CoefficientDerivedSystemCalculus l E W)
      (_coherence : CoefficientDerivedSystemCoherence l E W S)
      (M : OrdinaryModel l E W) (D : DerivedModel l E W S M),
      (∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
        (hQ : Q.IsKFlatIndependentCoefficients) (hflat : ∀ p : ℤ, (Q.X p).IsFlatOnSite),
        (∀ (p : ℤ) (n : ℕ) (V : W.ProEtᵒᵖ) (x : (Q.X p).val.obj V),
          (((M.augmentation l E W Q ≫
              limit.π ((tower l E W).obj ((M.quotient l E W).obj Q)).asFunctor
                (op n)).f p ≫
              (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
                (((M.quotient l E W).obj Q).X p) ≫
              (scalarReductionRestriction l E W n).map
                ((M.evaluation n).hom.app (Q.X p))).val.app V) x =
            unrestrictedIntegralTensorSection l E W n (Q.X p) V 1 x) ∧
        (∀ p : ℤ,
          (M.coneAugmentation l E W Q).f (p + 1) ≫
              (roosχ ((tower l E W).obj ((M.quotient l E W).obj Q)) p).hom =
            biprod.lift 0
              ((Pi.lift (fun n : ℕ ↦ M.augmentation l E W Q ≫
                limit.π ((tower l E W).obj ((M.quotient l E W).obj Q)).asFunctor
                  (op n))).f (p + 1))) ∧
        (∀ (N : DerivedCategory (scalarReductionSource l E W))
          (q : DerivedCategory.Q.obj Q ≅ N),
          S.adjunction.unit.app N = q.inv ≫
            DerivedCategory.Q.map (M.coneAugmentation l E W Q) ≫
            (D.completionComparison l E W Q hQ hflat).hom ≫
            (coefficientSequenceLimit l E W).map (S.reduction.map q.hom)) ∧
        (∀ (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
          (a : (M.quotient l E W).obj Q ⟶ I) [QuasiIso a] [I.IsKInjective]
          (_hI : ∀ p : ℤ, Injective (I.X p))
          (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
          (j : (tower l E W).obj I ⟶ J) [QuasiIso j] [J.IsKInjective]
          (_hJ : ∀ p : ℤ, Injective (J.X p)),
          ∃ (eI : DerivedCategory.Q.obj (limit ((tower l E W).obj I).asFunctor) ≅
              (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj I))
            (eJ : DerivedCategory.Q.obj (limit J.asFunctor) ≅
              (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj I))
            (eCone : DerivedCategory.Q.obj (limit J.asFunctor) ≅
              DerivedCategory.Q.obj (roosF.obj J)),
            eCone.hom = DerivedCategory.Q.map (roosι J) ∧
            eI.hom = DerivedCategory.Q.map (M.limitComparison.inv.app I) ≫
              D.systemUnit.app I ∧
            eJ.hom = D.limitUnit.app J ≫
              (coefficientConstantTowerLimit l E W).map (inv (DerivedCategory.Q.map j)) ≫
              (coefficientConstantTowerLimit l E W).map
                ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app I) ∧
            QuasiIso (lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j)) ∧
            QuasiIso (roosι J) ∧
            DerivedCategory.Q.map
                (lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j)) ≫
                eJ.hom = eI.hom ∧
            M.transpose l E W a = M.augmentation l E W Q ≫
              lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
                ((tower l E W).map a)) ∧
            (M.transpose l E W a ≫
                lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j)) ≫
                roosι J =
              M.coneAugmentation l E W Q ≫ roosF.map ((tower l E W).map a ≫ j) ∧
            (D.completionComparison l E W Q hQ hflat).hom ≫
                (coefficientSequenceLimit l E W).map (D.reductionComparison.app Q) ≫
                (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map a) =
              DerivedCategory.Q.map (roosF.map ((tower l E W).map a ≫ j)) ≫
                eCone.inv ≫ eJ.hom ∧
            (∀ (N : DerivedCategory (scalarReductionSource l E W))
              (q : DerivedCategory.Q.obj Q ≅ N),
              S.adjunction.unit.app N = q.inv ≫
                DerivedCategory.Q.map (M.transpose l E W a ≫
                  lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map j)) ≫
                eJ.hom ≫
                (coefficientSequenceLimit l E W).map (inv (DerivedCategory.Q.map a)) ≫
                (coefficientSequenceLimit l E W).map
                  (@asIso _ _ _ _ (D.reductionComparison.app Q)
                    (D.reduction_isIso Q hQ hflat)).inv ≫
                (coefficientSequenceLimit l E W).map (S.reduction.map q.hom)))) ∧
      (∀ (N N' : DerivedCategory (scalarReductionSource l E W)) (h : N ⟶ N'),
        h ≫ S.adjunction.unit.app N' = S.adjunction.unit.app N ≫
          (coefficientSequenceLimit l E W).map (S.reduction.map h)) := by
  sorry

end CompletionUnit
end WeilConjectures
