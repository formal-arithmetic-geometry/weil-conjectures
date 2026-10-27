/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.CompletedOpenStrictMateIdentification
public import Sheaf.Paper.SfImmersionCompletedPullbackComparison
public import Sheaf.SixFunctors.OpenFactorPullModel
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.SixFunctors.IntegralOpenReductionComparison
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison
public import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.Paper.ExactProductFunctorStrictLimit
import Sheaf.Paper.AdicPullbackPresentationTransport
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.AlgebraicGeometry.OpenImmersionSquare
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.IntegralReductionTowerCanonical
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Paper.PbcQbarCompletedPullback
import Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars
import Sheaf.Paper.CompletedOpenExchangeTransport
import Sheaf.Paper.IntegralUniformCoefficient
import Sheaf.Paper.CompletedRingStrictFiniteExchange
import Sheaf.Algebra.Homology.RingedOpenFlatResolution
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.StrictRoosComparison

/-! # Restriction of the completed open exchange in strict Roos coordinates

Source: Stacks Project, proetale.tex, Tags 099N (2),(5) and 09BN;
sites-cohomology.tex, Tag 0D6D; blueprint main-20261015, sk-prop-sf-pf-coherence,
base-change paragraph (blueprint: lem-sf-open-exchange-roos-restriction).

The integral datum is the existing uniformizer datum. Its completed-ring presentation
is transported to integral coefficients by the projection-normalized `transport`.
The strict exchange and completed exchange are the published maps, including their
endpoint comparisons. No equality is tested by separate derived evaluations.
The signed coordinates below are `(y,x)`, the order of `strictRoosCoordinates`;
in these coordinates the augmentation is `(0,gamma)`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u uA vA uB vB
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.OpenExchangeRoos

/-- The actual termwise action on strict complexes, before derived localization.
Source: Stacks 099N(5) (blueprint: lem-sf-open-exchange-roos-restriction). -/
abbrev towerComplex {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] :=
  ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)

/-- The comparison has the canonical product map on both signed summands.
Thus its data are fixed before passage to derived categories.
Source: Stacks 08TC and 09BP (blueprint: lem-sf-open-exchange-roos-restriction). -/
structure SignedComparison {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasCountableProducts A] {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasCountableProducts B] (F : A ⥤ B) [F.Additive]
    (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) where
  iso : (F.mapHomologicalComplex (.up ℤ)).obj (strictRoosComplex M) ≅
    strictRoosComplex ((towerComplex F).obj M)
  coordinates : ∀ p : ℤ,
    iso.hom.f (p + 1) ≫ (strictRoosCoordinates ((towerComplex F).obj M) p).hom =
      F.map (strictRoosCoordinates M p).hom ≫ biprodComparison F _ _ ≫
        biprod.map
          ((piComparison (F.mapHomologicalComplex (.up ℤ))
            (fun n : ℕ ↦ M.asFunctor.obj (op n))).f p)
          ((piComparison (F.mapHomologicalComplex (.up ℤ))
            (fun n : ℕ ↦ M.asFunctor.obj (op n))).f (p + 1))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The singleton generating tuple for the existing uniformizer ideal.
Source: Stacks 099N (blueprint: lem-sf-open-exchange-roos-restriction). -/
def generators : Fin 1 → PbcIntegralRing l E := fun _ ↦ pbcUniformizer l E

/-- The tuple generates precisely the recorded ideal; no alternative ideal is used.
Source: the coefficient DVR in Stacks 099N
(blueprint: lem-sf-open-exchange-roos-restriction).
Proof: Fin 1 is nonempty, so the range of the constant tuple is the singleton
uniformizer. The ideal field of pbcIntegralDatum is the span of that singleton. -/
theorem generators_span : Ideal.span (Set.range (generators l E)) =
    (pbcIntegralDatum l E).ideal := by
  sorry

/-- Roos completeness in the coefficient presentation of the completed-open comparison.
This is only the recorded predicate composed with the recorded coefficient transport.
Source: Stacks 099N and Bhatt--Scholze 3.5.2
(blueprint: lem-sf-open-exchange-roos-restriction). -/
abbrev complete (W : Scheme.{u}) : ObjectProperty ((pbcIntegralDatum l E).derived W) :=
  fun K ↦ IntegralOnSlice.IsComplete l E W none
    ((ImmersionCompletedPullback.transport l E W).obj K)

/-- The section-normalized open unit, on the ordinary derived category.
Source: Stacks 09BN (blueprint: lem-sf-open-exchange-roos-restriction). -/
def openUnit {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  @asIso _ _ _ _ (cbcDerivedOpenAdjunction (pbcIntegralDatum l E) j).unit
    (cbcOpenUnit_isIso (pbcIntegralDatum l E) j)

/-- The completed square has the ordinary square's normalization on the actual units.
The source is the full subcategory of Roos-complete objects, with no boundedness or
constructibility condition. Source: Stacks 099N and 0D6D
(blueprint: lem-sf-open-exchange-roos-restriction). -/
abbrev Square {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (h : X' ⟶ X) :=
  (complete l E X).ι ⋙ (pbcIntegralDatum l E).completedPull h ⋙
      (pbcIntegralDatum l E).pull j' ≅
    (complete l E X).ι ⋙ (pbcIntegralDatum l E).pull j ⋙
      (pbcIntegralDatum l E).completedPull a

/-- Its unit equation uses the ordinary compositor and the recorded quotient unit.
Source: Stacks 099N(2),(5), 0D6D
(blueprint: lem-sf-open-exchange-roos-restriction). -/
def SquareUnit {U' U X' X : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {h : X' ⟶ X} (sq : OpenImmersionSquare a j' j h)
    (c : Square l E a j' j h) : Prop :=
  ∀ H : (complete l E X).FullSubcategory,
    ((pbcIntegralDatum l E).pull j').map
        ((pbcIntegralDatum l E).ordinaryToCompleted h H.obj) ≫ c.hom.app H =
      (cbcSquarePull (pbcIntegralDatum l E) a j' j h sq.w).hom.app H.obj ≫
        (pbcIntegralDatum l E).ordinaryToCompleted a
          (((pbcIntegralDatum l E).pull j).obj H.obj)

/-- Simultaneous restriction of the finite open-unit transpose, in strict towers.
Source: Stacks 09BN, 0D6D; finite scalar compatibility in the node's proof Step 4
(blueprint: lem-sf-open-exchange-roos-restriction).
Proof: transpose the inverse exchange under the normalized open adjunction.
The transpose is pullback of the source open unit followed by the inverse square
compositor. Invert this equation. The units are isomorphisms and their inverse
identifies the restricted extension with the original strict system. Scalar
compatibility and naturality give this equation for every quotient transition
before localization. Exact localization preserves that same equation. -/
theorem finite_restriction {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (h : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : OpenImmersionSquare a j' j h)
    (M : ProEtale.StrictTower.Derived (PbcIntegralRing l E) U) :
    (ProEtale.StrictTower.G (PbcIntegralRing l E) j').map
        ((ProEtale.StrictTower.beta (PbcIntegralRing l E) a j' j h sq.w
          (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)).hom.app
            M) =
      (ProEtale.StrictTower.squareG (PbcIntegralRing l E) a j' j h sq.w).hom.app
          ((ProEtale.StrictTower.J (PbcIntegralRing l E) j).obj M) ≫
        (ProEtale.StrictTower.G (PbcIntegralRing l E) a).map
          ((@asIso _ _ _ _ (ProEtale.StrictTower.jAdj (PbcIntegralRing l E) j).unit
            (ProEtale.StrictTower.jAdj_unit_isIso (PbcIntegralRing l E) j)).inv.app M) ≫
        (ProEtale.StrictTower.jAdj (PbcIntegralRing l E) j').unit.app
          ((ProEtale.StrictTower.G (PbcIntegralRing l E) a).obj M) := by
  sorry

/-- Restricting the extension/product comparison gives the identity on each projection.
The open unit is written explicitly, so the equality holds before identification.
Source: Stacks 09BN and 09BP; proof Step 6
(blueprint: lem-sf-open-exchange-roos-restriction).
Proof: project the two canonical product comparisons to n. Their defining
projection equations give pullback of the n-th projection. Naturality of the
open unit makes this the n-th projection followed by that unit. These equations
identify the entire product map by the product universal property. -/
theorem product_restriction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : ℕ → ProEtale.StrictTower.Modules (PbcIntegralRing l E) U) (n : ℕ) :
    (ProEtale.StrictTower.moduleJAdj (PbcIntegralRing l E) j).unit.app (∏ᶜ M) ≫
        (ProEtale.StrictTower.modulePullback (PbcIntegralRing l E) j).map
          (piComparison (ProEtale.StrictTower.moduleJ (PbcIntegralRing l E) j) M) ≫
        piComparison (ProEtale.StrictTower.modulePullback (PbcIntegralRing l E) j)
          (fun i ↦ (ProEtale.StrictTower.moduleJ (PbcIntegralRing l E) j).obj (M i)) ≫
        Pi.π (fun i ↦ (ProEtale.StrictTower.modulePullback (PbcIntegralRing l E) j).obj
          ((ProEtale.StrictTower.moduleJ (PbcIntegralRing l E) j).obj (M i))) n =
      Pi.π M n ≫ (ProEtale.StrictTower.moduleJAdj (PbcIntegralRing l E) j).unit.app
        (M n) := by
  sorry

/-- Both signed summands of the restricted extension/Roos comparison are the same
identity in open-unit coordinates. The formula also fixes every augmentation.
Source: Stacks 08TC, 09BP; proof Step 6
(blueprint: lem-sf-open-exchange-roos-restriction).
Proof: build the extension and restriction comparisons from their canonical
product maps on both signed coordinates. Exactness and product preservation make
them invertible. Product_restriction identifies their composite on each projection.
The signed cone coordinates therefore identify the composite with the Roos map
of the termwise open unit, on both summands. Equality of these chain maps includes
the augmentation (0,gamma) for every strict cone gamma. -/
theorem roos_restriction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j]
    (M : CochainComplex (ProEtale.StrictTower.Towers (PbcIntegralRing l E) U) ℤ) :
    ∃ (e : SignedComparison (ProEtale.StrictTower.moduleJ (PbcIntegralRing l E) j) M)
      (r : SignedComparison (ProEtale.StrictTower.modulePullback (PbcIntegralRing l E) j)
        ((towerComplex (ProEtale.StrictTower.moduleJ (PbcIntegralRing l E) j)).obj M)),
      (((ProEtale.StrictTower.moduleJAdj (PbcIntegralRing l E) j).mapHomologicalComplex
        (.up ℤ)).unit.app (strictRoosComplex M)) ≫
          ((ProEtale.StrictTower.modulePullback (PbcIntegralRing l E) j).mapHomologicalComplex
            (.up ℤ)).map e.iso.hom ≫ r.iso.hom =
        integralOperationsRoosMap
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            ((((ProEtale.StrictTower.moduleJAdj (PbcIntegralRing l E) j).whiskerRight
              ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).unit.app M)) := by
  sorry

/-- The ordinary derived open adjunction used by the constant-coefficient limit model.
It is the existing module adjunction descended termwise, with its canonical right-derived
comparison. Source: Stacks 09BN (blueprint: lem-sf-open-exchange-roos-restriction). -/
def constantOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  Adjunction.ofNatIsoRight
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (ProEtale.StrictTower.moduleJAdj (PbcIntegralRing l E) j))
    (Functor.rightDerivedFunctorIsoMapDerivedCategory
      (ProEtale.StrictTower.modulePullback (PbcIntegralRing l E) j))

/-- The restricted derived-limit comparison is identity under the actual open units.
The restriction/Rlim arrow is its canonical constant-diagram mate, so this equation
also identifies the augmentation-normalized comparison of exactProductFunctorStrictLimit.
Source: Stacks 09BN, 09BP, 099N; proof Steps 2 and 6
(blueprint: lem-sf-open-exchange-roos-restriction).
Proof: the canonical product comparison has the projection equations of
product_restriction. Its signed Roos map has that same comparison on each summand,
by roos_restriction. The comparison to total right-derived inverse limit preserves
those maps and all strict augmentations. This proves the displayed equation in the
ordinary unbounded derived category; no separate reduction-evaluation test is used. -/
theorem limit_restriction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] (M : ProEtale.StrictTower.Derived (PbcIntegralRing l E) U) :
    (constantOpenAdjunction l E j).unit.app
        ((completedRlim U (exchangeConstantRing U (PbcIntegralRing l E))).obj M) ≫
      (ProEtale.StrictTower.modulePullback (PbcIntegralRing l E) j).mapDerivedCategory.map
        ((cbcRealizationOpenLimit (pbcIntegralDatum l E) j).hom.app M) ≫
      (cbcRealizationLimitMap
        (ProEtale.StrictTower.modulePullback (PbcIntegralRing l E) j)).app
          ((ProEtale.StrictTower.J (PbcIntegralRing l E) j).obj M) =
    (completedRlim U (exchangeConstantRing U (PbcIntegralRing l E))).map
      ((ProEtale.StrictTower.jAdj (PbcIntegralRing l E) j).unit.app M) := by
  sorry

/-- Quasi-compactness of an open into a finite-type scheme over the fixed field.
It is supplied as a consequence, rather than imposed on the theorem's inputs.
Source: Stacks 01T1 and 01K5; proof Step 1
(blueprint: lem-sf-open-exchange-roos-restriction).
Proof: a field is Noetherian, and a scheme of finite type over its spectrum is
Noetherian. Every open subset of a Noetherian space is quasi-compact, hence the
open immersion is quasi-compact. The empty open is included. -/
theorem finiteOpenQC (F : FiniteFieldDatum.{u})
    (U X : Over (Spec (.of F.k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] : QuasiCompact j.left := by
  sorry

/-- Clause-by-clause assertion on the fixed completed coefficient presentation.
The square is uniquely determined by its actual unit equation. Its exchange is the
specified one, transported to the fixed strict endpoints rather than chosen anew.
Source: Stacks 099N, 09BN and 0D6D
(blueprint: lem-sf-open-exchange-roos-restriction). -/
def Assertion {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (h : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] [qc : QuasiCompact j]
    (sq : OpenImmersionSquare a j' j h) : Prop :=
    ∃! c : Square l E a j' j h,
      SquareUnit l E sq c ∧
      ∀ (K : (pbcIntegralDatum l E).derived U), complete l E U K →
        ∃ (hI : cbcCompleteProperty (pbcIntegralDatum l E) U 1 (generators l E)
            (generators_span l E) K)
          (hJ : complete l E X
            ((cbcDerivedOpenShriek (pbcIntegralDatum l E) j inferInstance).obj K)),
          complete l E X' (((pbcIntegralDatum l E).completedPull h).obj
            ((cbcDerivedOpenShriek (pbcIntegralDatum l E) j inferInstance).obj K)) ∧
          complete l E X'
            ((cbcDerivedOpenShriek (pbcIntegralDatum l E) j' inferInstance).obj
              (((pbcIntegralDatum l E).completedPull a).obj K)) ∧
          IsIso ((cbcDatumCompletedExchange (pbcIntegralDatum l E) sq 1 (generators l E)
            (generators_span l E)).app ⟨K, hI⟩) ∧
          (cbcRealizationRes (pbcIntegralDatum l E) X').mapDerivedCategory.map
              ((cbcDatumCompletedExchange (pbcIntegralDatum l E) sq 1 (generators l E)
                (generators_span l E)).app ⟨K, hI⟩) ≫
                (cbcOpenMateCompletedB (pbcIntegralDatum l E)
                  (j' := j') (v := a) K).hom =
            (cbcOpenMateCompletedA (pbcIntegralDatum l E)
                (j := j) (g := h) K).hom ≫
              (completedRlim X'
                (exchangeConstantRing X' (PbcIntegralRing l E))).map
                  (cbcOpenMateBeta (pbcIntegralDatum l E) sq K).hom ≫
              (@cbcRealizationOpenLimit _ _ (pbcIntegralDatum l E) U' X' j'
                inferInstance (cbcOpenMateQC sq)).inv.app
                  ((ProEtale.StrictTower.G (PbcIntegralRing l E) a).obj
                    ((cbcOpenMateM (pbcIntegralDatum l E) (U := U)).obj K)) ∧
          ((pbcIntegralDatum l E).pull j').map
              ((cbcDatumCompletedExchange (pbcIntegralDatum l E) sq 1 (generators l E)
                (generators_span l E)).app ⟨K, hI⟩) ≫
                (openUnit l E j').inv.app
                  (((pbcIntegralDatum l E).completedPull a).obj K) =
            c.hom.app
                ⟨(cbcDerivedOpenShriek (pbcIntegralDatum l E) j inferInstance).obj K, hJ⟩ ≫
              ((pbcIntegralDatum l E).completedPull a).map
                ((openUnit l E j).inv.app K)

/-- The specified completed exchange is the ordered strict derived limit of its finite
open exchanges. Its restriction is the finite-composition comparison, and that
comparison preserves the actual ordinary-to-completed pullback units.
Source: Stacks 099N (2),(5), 09BN and 0D6D; blueprint main-20261015,
sk-prop-sf-pf-coherence, open-factor proof Steps 10--11
(blueprint: lem-sf-open-exchange-roos-restriction).

Proof, following the nine steps of the DAG node:
1. Finite type over the algebraic closure of the finite field gives Noetherian and
qcqs schemes and quasi-compact opens. The coefficient datum is the recorded DVR
with its uniformizer ideal. The quotient-augmentation completeness bridge identifies
Roos completeness with intrinsic completeness and the actual invertible unit.
2. Exact countable products and the exact ringed-slice adjunction give the normalized
restriction and extension/Rlim comparisons; only these functors need preserve products.
3. On a flat-term K-flat representative the canonical open scalar map identifies
the entire reduction tower of j!K with JQ(K), including the quotient transitions.
4. Apply finite_restriction to the simultaneous finite open-unit exchange. Its
scalar comparison is the one of finite-open-exchange-scalars. The square compositor
is finite pullback composition. The open units leave sections unchanged.
5. CompletedOpenStrictMateIdentification identifies the specified completed exchange,
in its fixed endpoints, with Rlim(b) followed by inverse lambda. Its completeness
assertions and the bridge of Step 1 give precisely the complete endpoints below.
6. Product_restriction and roos_restriction compute restricted lambda: identity on
every projection and both signed summands. This also fixes strict augmentations.
7. Naturality of the normalized restriction/Rlim comparison moves restriction
past Rlim(b). Substituting Steps 4 and 6 gives the displayed restriction equation
in the actual completed derived category, without evaluation faithfulness.
8. On a good representative the two restricted strict augmentations send the same
local tensor to its reduction, and commute with all quotient transitions. The
projection-normalized coefficient and universal-counit transports preserve this formula.
9. The Roos augmentations have equal first coordinates and zero second coordinates
(in the source's coordinate order). Functorial strict Rlim gives SquareUnit. Its
completion universal property determines the square uniquely. Apply it to j!K and
its normalized open unit to give exactly the displayed Theta. -/
theorem openExchangeRoosRestriction (F : FiniteFieldDatum.{u}) (_hl : l ≠ F.p)
    (U' U X' X : Over (Spec (.of F.k)))
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (h : X' ⟶ X)
    [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
    (sq : OpenImmersionSquare a.left j'.left j.left h.left) :
    Assertion l E a.left j'.left j.left h.left
      (qc := finiteOpenQC F U X j) sq := by
  sorry

end WeilConjectures.OpenExchangeRoos
