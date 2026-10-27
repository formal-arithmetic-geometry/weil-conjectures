/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.AlgebraicGeometry.ClosedSupportExceptionalComparison
public import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import Sheaf.Paper.SupportedHomPullback
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import Sheaf.CategoryTheory.DerivedCategory.GoodTruncationNormalization
public import Sheaf.AlgebraicGeometry.SupportLongExact
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.CategoryTheory.RingedSiteModules

/-!
# Counit-normalized supported classes and evaluation

Source: main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
lem-pur-gysin-structure.proof.md, paragraphs 1--2
(blueprint: lem-pur-supported-class-evaluation-comparison).

All coefficient categories are ordinary module sheaves. The small pro-etale site has
object universe u+1 and morphism universe u. The relative exceptional Hom map is used
only with an explicit bounded-below etale antecedent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The supported-Hom comparison, fixed by its value on every injective cocycle.
The published theorem supplies normalized identifications, which determine the map
uniquely; no choice of an unnormalized Hom isomorphism is made.
Source: Milne, Section 9, and the source's supported-Hom identification
(blueprint: lem-pur-supported-class-evaluation-comparison). -/
def supportedEvaluationChi (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (proEtaleSupportHomPair P i).Identification :=
  Classical.choose (Classical.choose_spec (supportedHom_pullback P)) i

/-- Evaluation of a derived map on the canonical constant section 1, after the canonical
single-cohomology identification. Source: source paragraph 2, evaluation at one
(blueprint: lem-pur-supported-class-evaluation-comparison). -/
def supportedEvaluation (P : WeilConjectures.PurityFiniteSetting.{u}) (Z : Scheme.{u})
    (C : DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
      (ModuleCat.{u + 1} P.Coefficient)))
    (m : (DerivedCategory.singleFunctor _ 0).obj (P.constant Z) ⟶ C) :
    ((DerivedCategory.homologyFunctor _ 0).obj C).obj.obj (op (Scheme.ProEt.mk (𝟙 Z))) :=
  ((constantSheafAdj (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} P.Coefficient)
    (Scheme.ProEt.isTerminalMkId Z)).homEquiv _ _
      ((comparisonUpperStarConstantSheafIso P.Coefficient Z).inv.app
          (ModuleCat.of P.Coefficient P.Coefficient) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app (P.constant Z) ≫
        (DerivedCategory.homologyFunctor _ 0).map m)) 1

/-- The sheaf map associated to a global section. Under the constant-sheaf adjunction its
value on each object is a times the restricted section, including locally constant a.
Source: source paragraph 2, inverse evaluation formula
(blueprint: lem-pur-supported-class-evaluation-comparison). -/
def supportedEvaluationSectionMap (P : WeilConjectures.PurityFiniteSetting.{u})
    (Z : Scheme.{u}) (M : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} P.Coefficient))
    (v : M.obj.obj (op (Scheme.ProEt.mk (𝟙 Z)))) : P.constant Z ⟶ M :=
  (comparisonUpperStarConstantSheafIso P.Coefficient Z).hom.app
      (ModuleCat.of P.Coefficient P.Coefficient) ≫
    ((constantSheafAdj (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} P.Coefficient)
      (Scheme.ProEt.isTerminalMkId Z)).homEquiv _ _).symm
        (ModuleCat.ofHom (LinearMap.toSpanSingleton P.Coefficient _ v))

/-- The shift identification i_*A[-2][2] = i_*A[0], using the canonical exact single
comparison, not a free isomorphism. Source: proof step 5 of the source comparison
(blueprint: lem-pur-supported-class-evaluation-comparison). -/
def supportedEvaluationShiftSource (P : WeilConjectures.PurityFiniteSetting.{u})
    [Finite P.Coefficient]
    {Z X V : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j)) :
    ((supportClosedDerivedPlus P.Coefficient i j hPair).obj
      ((DerivedCategory.Plus.singleFunctor _ 2).obj (P.constant Z))).obj⟦(2 : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)) :=
  letI := preservesFiniteColimits_lowerStar_of_isCompl (R := P.Coefficient) i j hPair
  (shiftFunctor _ (2 : ℤ)).mapIso
      (((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategorySingleFunctor
        2).app (P.constant Z)) ≪≫
    ((DerivedCategory.singleFunctors _).shiftIso 2 0 2 (by decide)).app
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z))

/-- The support adjunction selected with its prescribed injective-model counit. The
localization theorem specifies that counit on all injective models, hence determines
this adjunction uniquely. Source: support-localization triangle, counit normalization
(blueprint: lem-pur-supported-class-evaluation-comparison). -/
def supportedEvaluationAdjunction (P : WeilConjectures.PurityFiniteSetting.{u})
    [Finite P.Coefficient]
    {Z X V : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j)) :
    supportClosedDerivedPlus P.Coefficient i j hPair ⊣
      (finiteClosedUpperShriek P.Coefficient i j).rightDerivedFunctorPlus :=
  Classical.choose (supportLocalizationTriangle P.Coefficient i j hPair)

/-- The complete formula for eta: supported Hom, unshift, support adjunction, shift,
and postcomposition with phi[2]. The single in degree 2 is A[-2].
Source: source paragraph 2 and the node's proof step 5
(blueprint: lem-pur-supported-class-evaluation-comparison). -/
def supportedEvaluationEta (P : WeilConjectures.PurityFiniteSetting.{u})
    [Finite P.Coefficient]
    {Z X V : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j))
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (B : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} P.Coefficient)))
    (phi : ((finiteClosedUpperShriek P.Coefficient i j).rightDerivedFunctorPlus.obj K).obj ≅ B)
    (b : supportHypercohomology i P.Coefficient 2 K) :
    (DerivedCategory.singleFunctor _ 0).obj (P.constant Z) ⟶ B⟦(2 : ℤ)⟧ :=
  (((DerivedCategory.singleFunctors _).shiftIso 2 0 2 (by decide)).app
      (P.constant Z)).inv ≫
    (DerivedCategory.Plus.ι.map
      ((supportedEvaluationAdjunction P i j hPair).homEquiv _ K
        (DerivedCategory.Plus.ι.preimage
          ((Functor.FullyFaithful.ofFullyFaithful (shiftFunctor _ (2 : ℤ))).homEquiv.symm
            ((supportedEvaluationShiftSource P i j hPair).hom ≫
              (supportedEvaluationChi P i).chi K 2 b)))))⟦(2 : ℤ)⟧' ≫ phi.hom⟦(2 : ℤ)⟧'

/-- Full statement in fixed-scalar coordinates. The local instances follow from the
finite-type structure maps and the positive finite coefficient level. The sole geometric
map in the exceptional functor uses exactly Compactification.ofIsProper i = (id_Z,i).
Source: source paragraphs 1--2, with all normalization and boundary clauses
(blueprint: lem-pur-supported-class-evaluation-comparison). -/
def supportedClassEvaluationComparisonProperty
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z X V : Scheme.{u}}
    (aZ : Z ⟶ Spec (.of P.field.k)) (aX : X ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : V ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j)) : Prop :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite (ULift.{u + 1} P.Ring) := Finite.of_equiv P.Ring Equiv.ulift.symm
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
    P.Coefficient (Compactification.ofIsProper i)
  let R := (finiteClosedUpperShriek P.Coefficient i j).rightDerivedFunctorPlus
  let S := supportClosedDerivedPlus P.Coefficient i j hPair
  let F := sfFiniteExceptionalAt P.Coefficient (Compactification.ofIsProper i)
  let adj := supportedEvaluationAdjunction P i j hPair
  let q := closedSupportCompactIso P.Coefficient i j hPair
  let A0 := (DerivedCategory.singleFunctor
    (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} P.Coefficient)) 0).obj (P.constant Z)
  ∀ K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)),
    Nonempty ((R.obj K).obj⟦(2 : ℤ)⟧ ≅ A0) →
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) Z
      ((R.obj K).obj⟦(2 : ℤ)⟧) →
    ∃ (hB : _root_.DerivedCategory.TStructure.t.plus (F.obj K.obj))
      (WB : Scheme.FixedEtaleOriginWitness Z P.Coefficient ⟨F.obj K.obj, hB⟩)
      (phi : (R.obj K).obj ≅ F.obj K.obj),
      DerivedCategory.Plus.ι.map (S.map (DerivedCategory.Plus.ι.preimage
        (X := R.obj K) (Y := ⟨F.obj K.obj, hB⟩) phi.hom)) ≫
        (q.inv.app ⟨F.obj K.obj, hB⟩ ≫
          (specifiedExceptionalHomEquiv P.Coefficient (Compactification.ofIsProper i)
            _ WB K).symm (𝟙 _)) = DerivedCategory.Plus.ι.map (adj.counit.app K) ∧
      (∀ (T : DerivedCategory.Plus
          (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} P.Coefficient)))
        (W : Scheme.FixedEtaleOriginWitness Z P.Coefficient T) (f : T.obj ⟶ (R.obj K).obj),
        specifiedExceptionalHomEquiv P.Coefficient (Compactification.ofIsProper i) T W K
          (q.hom.app T ≫ DerivedCategory.Plus.ι.map
            ((adj.homEquiv T K).symm (DerivedCategory.Plus.ι.preimage f))) = f ≫ phi.hom) ∧
      Nonempty (F.obj K.obj⟦(2 : ℤ)⟧ ≅ A0) ∧
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) Z
        (F.obj K.obj⟦(2 : ℤ)⟧) ∧
      ∃ hC : ∀ r : ℤ, r ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ r).obj
          (F.obj K.obj⟦(2 : ℤ)⟧)),
        Nonempty ((DerivedCategory.homologyFunctor _ 0).obj (F.obj K.obj⟦(2 : ℤ)⟧) ≅
          P.constant Z) ∧
        ∃ (eta : supportHypercohomology i P.Coefficient 2 K ≃+
            (A0 ⟶ F.obj K.obj⟦(2 : ℤ)⟧))
          (ev : (A0 ⟶ F.obj K.obj⟦(2 : ℤ)⟧) ≃+
            ((DerivedCategory.homologyFunctor _ 0).obj (F.obj K.obj⟦(2 : ℤ)⟧)).obj.obj
              (op (Scheme.ProEt.mk (𝟙 Z)))),
          (∀ b, eta b = supportedEvaluationEta P i j hPair K (F.obj K.obj) phi b) ∧
          (∀ m, ev m = supportedEvaluation P Z (F.obj K.obj⟦(2 : ℤ)⟧) m) ∧
          (∀ v, ev.symm v =
            (DerivedCategory.singleFunctor _ 0).map (supportedEvaluationSectionMap P Z _ v) ≫
              (DerivedCategory.goodTruncationNormalization _ hC).inv) ∧
          (∀ (delta : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology X)
              (ModuleCat.{u + 1} P.Coefficient) (supportRestrictionArrow i) ⊤)
            (alpha : (Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology X)
              (ModuleCat.{u + 1} P.Coefficient) (Scheme.ProEt.mk i.openComplement.ι) 1).obj K),
            ev (eta ((delta 1).app ⟨K, trivial⟩ alpha)) =
              (eta.trans ev) ((delta 1).app ⟨K, trivial⟩ alpha) ∧
            (eta.trans ev).symm (ev (eta ((delta 1).app ⟨K, trivial⟩ alpha))) =
              (delta 1).app ⟨K, trivial⟩ alpha)

/-- The counit-normalized comparison, supported-Hom formula, and evaluation at one.
Source: main-20261015, lem-pur-gysin-structure.proof.md, paragraphs 1--2
(blueprint: lem-pur-supported-class-evaluation-comparison).

Proof:
1. A closed immersion is proper; its identity-open compactification has a finite
 dimension bound (zero for empty Z), by lem-kun-dimension-finite-type. Apply
 thm-sf-ambient-adjoint-class and lem-pur-support-localization-triangle on D+.
2. B0 is A[-2] by hypothesis and has etale origin by comparison-pullback exactness.
 B has its specified etale antecedent, bounded below by the finite-amplitude bound.
3. Transpose epsilon0 to define phi, and transpose epsilon in the support adjunction
 to define its inverse. Naturality and injectivity at B0 and B prove the inverse
 identities, counit normalization, uniqueness and agreement on every allowed test.
4. Shift phi by 2. Cohomology and tensor preserve isomorphisms, so concentration,
 the constant rank-one sheaf and finite-Tor constructibility pass from C0 to C.
5. Apply lem-pur-supported-hom at degree 2, unshift using the exact single comparison,
 apply the support adjunction, shift, then postcompose with phi[2]. Every factor is
 bijective. The normalized cocycle interface fixes chi, rather than an arbitrary iso.
 The comparison on all origin tests in step 3 includes A[-2].
6. lem-pur-good-truncation-exact-normalization identifies maps with H0 sheaf maps.
 The constant-sheaf adjunction evaluates a module map at 1. Its inverse sends v to
 a times its restriction on each object. It is a module-sheaf map since restriction
 commutes with multiplication. Compose with inverse normalized good truncation.
7. Both maps are bijective, so the section associated to the boundary delta(alpha)
 has unique inverse delta(alpha), including alpha=0. This applies to the canonical
 boundary of thm-pur-with-support-exactness and uses no adjunction on other inputs. -/
theorem supportedClassEvaluationComparison
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z X V : Scheme.{u}}
    (aZ : Z ⟶ Spec (.of P.field.k)) (aX : X ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    (i : Z ⟶ X) [IsClosedImmersion i] (_hi : i ≫ aX = aZ)
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j)) :
    supportedClassEvaluationComparisonProperty P aZ aX i j hPair := by
  sorry

end AlgebraicGeometry.ProEtale
