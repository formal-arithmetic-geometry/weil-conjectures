/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.ConstantCoefficientObjectsConstructible
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.SixFunctors.RationalVerdier
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import WeilConjectures.Algebra.Homology.HomTensorTotal
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.CompactSupportReductionTower
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.FiniteCoefficientTensorCtf
import Sheaf.Algebra.Homology.DerivedTensor
import Sheaf.Paper.FiniteTorAmplitude
import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.IntegralConstructibleInternalHom
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.Paper.IntegralResidueTor
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Paper.NormalizedDVRTower
import Sheaf.Paper.PbcRationalTransport
import Sheaf.SixFunctors.CoefIntegralFiniteExtension
import Sheaf.SixFunctors.IntegralVerdier
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
import Sheaf.SixFunctors.CoefDualFormulaScalarTranspose
import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Paper.FiniteFreeCoefficientExtension

/-! # Identification of rational internal Hom and exceptional inverse image

Source: Weil blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
lem-coef-rational-operations (blueprint: lem-coef-rational-operations).

The comparison records below are conclusions, never hypotheses of the theorem.
They retain the completed integral evaluation and the actual adjunction maps.
The exceptional functors come from the recorded coefficient-compatible system;
its finite terms are the etale-origin construction, with no ambient pro-etale adjoint.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct

namespace WeilConjectures.RationalOperations

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u})

/-- The recorded internal Hom on the whole constructible category, once its closure
assertion is supplied. This only changes the domain presentation, not the operation.
Source: blueprint internal-Hom clause (blueprint: lem-coef-rational-operations). -/
def homPair (h : ∀ K M : sfRationalConstructibleCategory l E X,
    constructibleRationalHomPairs l E X (op K, M)) :
    (sfRationalConstructibleCategory l E X)ᵒᵖ × sfRationalConstructibleCategory l E X ⥤
      (constructibleRationalHomPairs l E X).FullSubcategory :=
  (constructibleRationalHomPairs l E X).lift (𝟭 _) (fun P ↦ h P.1.unop P.2)

/-- Tensor with a fixed first input, using exactly the coefficient-passage tensor.
Source: blueprint tensor clause (blueprint: lem-coef-rational-operations). -/
def tensorLeft [∀ x : X, Invertible (l : X.residueField x)]
    (K : sfRationalConstructibleCategory l E X) :
    sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E X :=
  (((Functor.const _).obj K).prod' (𝟭 _)) ⋙ rationalDerivedTensor l E X

/-- Internal Hom from a fixed first input; every arrow is the recorded rational Hom map.
Source: blueprint internal-Hom clause (blueprint: lem-coef-rational-operations). -/
def homRight (h : ∀ K M : sfRationalConstructibleCategory l E X,
    constructibleRationalHomPairs l E X (op K, M))
    (K : sfRationalConstructibleCategory l E X) :
    sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E X :=
  (((Functor.const _).obj (op K)).prod' (𝟭 _)) ⋙
    homPair l E X h ⋙ rationalDerivedInternalHom l E X

/-- The same internal Hom with its second input fixed to the dualizing object.
Source: blueprint first displayed formula (blueprint: lem-coef-rational-operations). -/
def homDual (h : ∀ K M : sfRationalConstructibleCategory l E X,
    constructibleRationalHomPairs l E X (op K, M))
    (ω : sfRationalConstructibleCategory l E X) :
    (sfRationalConstructibleCategory l E X)ᵒᵖ ⥤ sfRationalConstructibleCategory l E X :=
  ((𝟭 _).prod' ((Functor.const _).obj ω)) ⋙
    homPair l E X h ⋙ rationalDerivedInternalHom l E X

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]

/-- Identification with the closed internal Hom, including the normalized evaluation.
The integral evaluation is ordinary evaluation preceded by the inverse of the actual
completion map. Its quotient-map and zero-coordinate normalization are retained in A.
Source: blueprint paragraphs 1--6 (blueprint: lem-coef-rational-operations). -/
structure HomIdentification (w : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (A : RationalVerdier.Datum D l hl X E w) where
  permitted : ∀ K M : sfRationalConstructibleCategory l E X,
    constructibleRationalHomPairs l E X (op K, M)
  adjunction (K : sfRationalConstructibleCategory l E X) :
    @tensorLeft l _ E _ _ _ X (RationalVerdier.units D l hl X) K ⊣
      homRight l E X permitted K
  integral_evaluation (K M : sfIntegralConstructibleCategory l E X) :
    HEq ((adjunction ((sfRationalConstructibleLocalization l E X).obj K)).counit.app
      ((sfRationalConstructibleLocalization l E X).obj M))
      ((sfRationalConstructibleLocalization l E X).map
        (ObjectProperty.homMk
          (X := (@constructibleIntegralTensor l _ E _ _ _ X
            (RationalVerdier.units D l hl X)).obj
              (K, (constructibleIntegralHom l E X).obj
                (integralPairOfRationalHomPair l E X
                  ⟨(op ((sfRationalConstructibleLocalization l E X).obj K),
                    (sfRationalConstructibleLocalization l E X).obj M), permitted _ _⟩)))
          (Y := M)
          ((@asIso _ _ _ _ (A.completion.map.app
            (K.obj, ((integralDerivedInternalHom l E X).obj (op K.obj, M.obj))))
            (A.completion.invertible K
              ((constructibleIntegralHom l E X).obj
                (integralPairOfRationalHomPair l E X
                  ⟨(op ((sfRationalConstructibleLocalization l E X).obj K),
                    (sfRationalConstructibleLocalization l E X).obj M), permitted _ _⟩)))).inv ≫
            (A.ordinary.adjunction K.obj).counit.app M.obj)))
  duality : A.dual ≅ homDual l E X permitted
    ((sfRationalConstructibleLocalization l E X).obj w.omega)
  evaluation (K : sfRationalConstructibleCategory l E X) :
    (RationalVerdier.tensor D l hl X E).map
        (Prod.mkHom (𝟙 K) (duality.hom.app (op K))) ≫
      (adjunction K).counit.app ((sfRationalConstructibleLocalization l E X).obj w.omega) =
        A.evaluation K

/-- The constant coefficient object is the completed regular module in degree zero,
then its image in the raw rational category. Its data are explicit.
Source: blueprint omega = Ra! E (blueprint: lem-coef-rational-operations). -/
def coefficientUnit : sfRationalConstructibleCategory l E X :=
  (sfRationalConstructibleLocalization l E X).obj
    ⟨integralConstantCoefficientObject l E X,
      (integralConstantCoefficient_constructible l E X D hl).2.1⟩


section Exceptional
open ConstructibleExceptionalCoefficients

variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f) (S : System l Ω D hl (f := f))
  (F : FieldStage.{u} l)

/-- The dual formula uses the already recorded pullback, with its residue-field units
inherited from the finite-field base. Both dualities are the rationalized integral ones.
Source: blueprint second displayed formula (blueprint: lem-coef-rational-operations). -/
abbrev dualFormula
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl F.carrier)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl F.carrier)
    (A : RationalVerdier.Datum D l hl X F.carrier wX)
    (B : RationalVerdier.Datum D l hl Y F.carrier wY) :=
  B.dual.rightOp ⋙
    (@rationalDerivedPullback l _ F.carrier _ _ _ X Y f
      (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).op ⋙ A.dual

/-- Exceptional comparison with its transported adjunction for the actual compact-support
functor. The two equations fix the unit and counit, rather than asserting only isomorphic
objects or unrelated adjunctions. The given system already fixes finite coefficient
origins, scalar comparisons, and rationalization of the integral adjunction.
Source: blueprint paragraph 7 (blueprint: lem-coef-rational-operations). -/
structure ExceptionalIdentification
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl F.carrier)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl F.carrier)
    (A : RationalVerdier.Datum D l hl X F.carrier wX)
    (B : RationalVerdier.Datum D l hl Y F.carrier wY) where
  comparison : (S.ring.operation c (.rational F)).G ≅ dualFormula l X D hl (f := f) F wX wY A B
  adjunction : sfCompactSupportFiniteFunctor l D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier ⊣
      dualFormula l X D hl (f := f) F wX wY A B
  unit (K : sfRationalConstructibleCategory l F.carrier X) :
    adjunction.unit.app K =
      (S.ring.operation c (.rational F)).adjunction.unit.app K ≫
        (S.ring.operation c (.rational F)).G.map ((S.ring.rationalLeft c F).hom.app K) ≫
        comparison.hom.app ((sfCompactSupportFiniteFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier).obj K)
  counit (M : sfRationalConstructibleCategory l F.carrier Y) :
    adjunction.counit.app M =
      (sfCompactSupportFiniteFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier).map
          (comparison.inv.app M) ≫
        (S.ring.rationalLeft c F).inv.app ((S.ring.operation c (.rational F)).G.obj M) ≫
          (S.ring.operation c (.rational F)).adjunction.counit.app M

/-- The identification data for one finite coefficient field. Every field is an asserted
conclusion. In particular no closure, duality, or exceptional adjunction is assumed.
Source: blueprint all identification clauses (blueprint: lem-coef-rational-operations). -/
structure Identification where
  wX : IntegralFiniteExtension.DualizingDatum l X D hl F.carrier
  wY : IntegralFiniteExtension.DualizingDatum l Y D hl F.carrier
  DX : RationalVerdier.Datum D l hl X F.carrier wX
  DY : RationalVerdier.Datum D l hl Y F.carrier wY
  homX : HomIdentification l F.carrier X D hl wX DX
  homY : HomIdentification l F.carrier Y D hl wY DY
  exceptional : ExceptionalIdentification l X D hl Ω c S F wX wY DX DY


variable (G : FieldStage.{u} l) (ι : F.carrier →ₐ[Padic l] G.carrier)
  (I : Identification l X D hl Ω c S F) (J : Identification l X D hl Ω c S G)

/-- The scalar comparison for the dual formula is the specified duality comparison,
followed contravariantly by the inverse pullback and target-duality comparisons.
Source: blueprint finite-extension paragraph (blueprint: lem-coef-rational-operations). -/
def dualScalar
    (eX : RationalVerdier.Extension D l hl X F.carrier G.carrier ι I.wX J.wX I.DX J.DX)
    (eY : RationalVerdier.Extension D l hl Y F.carrier G.carrier ι I.wY J.wY I.DY J.DY)
    (M : sfRationalConstructibleCategory l F.carrier Y) :
    (RationalVerdier.scalar l X F.carrier G.carrier ι).obj
        ((dualFormula l X D hl (f := f) F I.wX I.wY I.DX I.DY).obj M) ⟶
      (dualFormula l X D hl (f := f) G J.wX J.wY J.DX J.DY).obj
        ((RationalVerdier.scalar l Y F.carrier G.carrier ι).obj M) :=
  eX.comparison.hom.app (op
      ((@rationalDerivedPullback l _ F.carrier _ _ _ X Y f
        (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj
          (I.DY.dual.obj (op M)))) ≫
    J.DX.dual.map
      (((@rationalDerivedPullback l _ G.carrier _ _ _ X Y f
          (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).map
            (eY.comparison.inv.app (op M)) ≫
        (@rationalPullbackScalarComparison l _ F.carrier _ _ _ G.carrier _ _ _ ι X Y f
          (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).inv.app
            (I.DY.dual.obj (op M))).op)

/-- Finite scalar extension identifies the actual exceptional comparison with the
mate comparison of compact support. Together with ExceptionalIdentification.unit and
.counit and the system's Comparison.unit and .counit, this is compatibility of the
same units and counits on both sides, not just invertibility of scalar-extension maps.
Source: blueprint last paragraph (blueprint: lem-coef-rational-operations). -/
structure ScalarCompatibility where
  dualX : RationalVerdier.Extension D l hl X F.carrier G.carrier ι I.wX J.wX I.DX J.DX
  dualY : RationalVerdier.Extension D l hl Y F.carrier G.carrier ι I.wY J.wY I.DY J.DY
  normalizedX : RationalVerdier.ExtensionProperties D l hl X F.carrier G.carrier ι
    I.wX J.wX I.DX J.DX dualX
  normalizedY : RationalVerdier.ExtensionProperties D l hl Y F.carrier G.carrier ι
    I.wY J.wY I.DY J.DY dualY
  exceptional (M : sfRationalConstructibleCategory l F.carrier Y) :
    (RationalVerdier.scalar l X F.carrier G.carrier ι).map
        (I.exceptional.comparison.hom.app M) ≫
      dualScalar l X D hl Ω c S F G ι I J dualX dualY M =
    (S.fields.rationalComparison c F G ι).b.hom.app M ≫
      J.exceptional.comparison.hom.app
        ((RationalVerdier.scalar l Y F.carrier G.carrier ι).obj M)

end Exceptional

section HomScalars
variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)
  (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
  (wL : IntegralFiniteExtension.DualizingDatum l X D hl L)
  (A : RationalVerdier.Datum D l hl X E wE) (B : RationalVerdier.Datum D l hl X L wL)
  (hE : HomIdentification l E X D hl wE A) (hL : HomIdentification l L X D hl wL B)

/-- Evaluation commutes with the recorded finite scalar comparison of internal Hom.
Both tensor and Hom comparisons are the canonical rationalizations of the completed
integral comparisons. This equation also fixes the adjunction unit by transposition.
Source: blueprint evaluation and finite-extension clauses
(blueprint: lem-coef-rational-operations). -/
def HomScalarCompatibility : Prop :=
  ∀ K M : sfRationalConstructibleCategory l E X,
    (RationalVerdier.tensor D l hl X L).map
        (Prod.mkHom (𝟙 ((RationalVerdier.scalar l X E L ι).obj K))
          (rationalHomScalarComparison l E L ι X
            ⟨(op K, M), hE.permitted K M⟩).hom) ≫
      (hL.adjunction ((RationalVerdier.scalar l X E L ι).obj K)).counit.app
        ((RationalVerdier.scalar l X E L ι).obj M) =
    (@rationalTensorScalarComparison l _ E _ _ _ L _ _ _ ι X
      (RationalVerdier.units D l hl X)).inv.app
        (K, (homRight l E X hE.permitted K).obj M) ≫
      (RationalVerdier.scalar l X E L ι).map ((hE.adjunction K).counit.app M)

end HomScalars

section Dualizing
open ConstructibleExceptionalCoefficients
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The structure morphism commutes with the base structure in the canonical Spec
presentation. This is only the Spec identity law, not an extra hypothesis.
Source: blueprint structure morphism (blueprint: lem-coef-rational-operations). -/
instance structureIsOverSpec :
    (X ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) where
  comp_over := by
    rw [specOverSpec_over]
    simp

/-- The existing exceptional system at the structure morphism, with its canonical
base structure and no new coefficient operation.
Source: blueprint structure morphism (blueprint: lem-coef-rational-operations). -/
abbrev structureSystem := System l Ω D hl (f := X ↘ Spec (.of D.k))

/-- The dualizing object is the value of the same exceptional coefficient system on
E at the structure morphism. Its coefficient object is the actual completed regular
module, localized; no arbitrary point object is allowed.
Source: blueprint omega = Ra! E (blueprint: lem-coef-rational-operations). -/
def DualizingIdentification
    (S : structureSystem l X D hl Ω)
    (F : FieldStage.{u} l)
    (w : IntegralFiniteExtension.DualizingDatum l X D hl F.carrier) : Prop :=
  Nonempty ((sfRationalConstructibleLocalization l F.carrier X).obj w.omega ≅
    (S.ring.operation (integralDualizingCompactification D X) (.rational F)).G.obj
      (coefficientUnit l F.carrier (Spec (.of D.k)) D hl))

end Dualizing
end WeilConjectures.RationalOperations

namespace WeilConjectures.RationalOperations
open ConstructibleExceptionalCoefficients

/-- The complete identification assertion, simultaneously for every finite scalar
extension (including the identity). All closure and comparison data are conclusions.
The same exceptional systems serve every coefficient field, so their unit/counit
and rationalization equations remain the specified coherent ones.
Source: blueprint all clauses (blueprint: lem-coef-rational-operations). -/
def Conclusion
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X Y : Scheme.{u}) [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f) : Prop :=
  ∃ (S : System l Ω D hl (f := f))
    (Sa : structureSystem l X D hl Ω),
    ∀ (F G : FieldStage.{u} l) (ι : F.carrier →ₐ[Padic l] G.carrier),
      ∃ (I : Identification l X D hl Ω c S F) (J : Identification l X D hl Ω c S G),
        Nonempty (ScalarCompatibility l X D hl Ω c S F G ι I J) ∧
        HomScalarCompatibility l F.carrier X D hl G.carrier ι
          I.wX J.wX I.DX J.DX I.homX J.homX ∧
        HomScalarCompatibility l F.carrier Y D hl G.carrier ι
          I.wY J.wY I.DY J.DY I.homY J.homY ∧
        DualizingIdentification l X D hl Ω Sa F I.wX ∧
        DualizingIdentification l X D hl Ω Sa G J.wX

end WeilConjectures.RationalOperations

namespace WeilConjectures

/-- Rational internal Hom and exceptional inverse image are exactly the coefficient-passage
operations, using completed integral tensor, with evaluation and adjunction data preserved
by rationalization and finite scalar extension.
Source: Weil blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
lem-coef-rational-operations (blueprint: lem-coef-rational-operations).

Proof (the full DAG plan, with its coefficient and representative normalizations):

1. Use the inherited global datum $k=\overline{\mathbf F}_q$, $\ell\ne\operatorname{char}k$, a
finite $E/\mathbf Q_\ell$, and separated finite-type $k$-schemes. Put $R=\mathcal O_E$,
$\pi=\varpi_E$, $A_n=R/\pi^n$, and $\mathscr R_W=\widehat{\mathcal O}_{E,W}$ on the small
pro-etale site of $W$. In this proof an ambient integral tensor or internal Hom is over $\mathscr
R_W$, not over the discrete constant sheaf $R_W$. Write $\mathcal C_R(W)=D^b_c(W,R)$ for the full
derived-complete subcategory with constructible finite reductions and one uniform cohomological
interval. Fix the small site skeletons and coefficient universes of the pro-etale site and size
conventions, so the resolution and tower lemmas apply. All inverse limits below use strict towers
and their functorial derived-limit realization. These are the coefficient categories and
operations appearing in the statement.
Uses: def-weil-finite-field-fiber, def-weil-completed-integral-coefficients,
def-weil-derived-complete-integral-detailed, def-weil-derived-pullback-tensor-hom,
def-weil-pbc-proetale-site, def-weil-size-convention.

2. For $P,K\in\mathcal C_R(X)$ let $N=P\otimes^L_{\mathscr R_X}K$. Choose K-flat resolutions with
flat terms. Their tensor is K-flat: tensor an acyclic complex first with one resolution and then
with the other, obtaining an acyclic complex twice by the definition of K-flatness. The K-flat
change-of-rings lemma makes their reductions K-flat with flat terms as well; the strict
completed-tensor construction descends independently of these choices by integral-operations
well-definedness. Reassociation of their ordinary tensor complexes, $(p\otimes k)\otimes
a\mapsto(p\otimes1)\otimes(k\otimes a)$, identifies $N\otimes^L_{\mathscr R_X}(A_n)_X$ with
$P_n\otimes^L_{A_n}K_n$. For $m\le n$, further reduction is $P_m\otimes^L_{A_m}K_m$; all
transition cocycles hold already on these tensor representatives. Thus this is a normalized DVR
tower. The residue-Tor lemma supplies uniform finite Tor intervals $[a,b]$, $[c,d]$ for the
inputs, and finite tensor preservation supplies constructibility and interval $[a+c,b+d]$. Taking
the degree-zero test module $(A_n)_X$ in the definition of Tor amplitude shows that this same
interval contains the cohomological support of every tensor reduction: tensor with the
coefficient unit is identified with the original complex by $x\otimes a\mapsto ax$, inverse
$x\mapsto x\otimes1$. Normalized effectivity identifies the reductions of its derived limit with
these objects and makes the limit complete. Hence
$C(N):=R\lim_n\operatorname{Res}_n(P_n\otimes^L_{A_n}K_n)$ belongs to $\mathcal C_R(X)$. By the
definition of integral operations this is precisely $P\widehat\otimes_R^LK$. No assertion of
local perfection on the site is used.
Uses: lem-pc-kflat-resolution, def-coef-normalized-dvr-tower, lem-coef-integral-residue-tor,
lem-sf-tensor-ctf, lem-coef-normalized-dvr-effectivity,
def-weil-derived-complete-integral-detailed, def-weil-derived-pullback-tensor-hom,
def-pc-kflat-complex, lem-pur-kflat-change-of-rings, lem-pur-integral-operations-well-defined,
def-weil-proetale-tor-amplitude.

3. Use the strict K-flat tensor representative $Q$ of $N$ from Step 2. Its quotient maps $Q\to
Q\otimes_{\mathscr R_X}(A_n)_X$ commute strictly with the transitions. Since countable products
are exact, the strict-tower limit is represented by the product mapping fiber of $1-s$. The
quotient maps define a chain map $\eta_N:Q\to\operatorname{Cone}(1-s)[-1]$ with zero homotopy
component. This is the canonical completion unit, natural in the strict representatives, not an
arbitrary triangulated lift. Write $L_n=N\otimes^L_{\mathscr R_X}(A_n)_X$. Normalized effectivity
applied to the tower of Step 2 identifies the adjoint of the projection
$C(N)\to\operatorname{Res}_nL_n$ with an isomorphism $e_n:C(N)\otimes^L_{\mathscr R_X}(A_n)_X\to
L_n$. The composite projection with $\eta_N$ is the reduction unit of $N$. By naturality and the
triangle identity for derived extension/restriction, its adjoint is the identity on $L_n$; thus
$e_n\circ(\eta_N\otimes^L(A_n)_X)=1_{L_n}$. Therefore $\eta_N$ is an isomorphism modulo every
$\pi^n$.
Uses: lem-weil-proetale-countable-products-exact,
lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-coef-normalized-dvr-effectivity,
lem-weil-derived-scalar-extension-restriction-adjunction.

4. Let $C=\operatorname{Cone}(\eta_N)$. The coefficient ring $R$ is a DVR, hence a Noetherian
domain. Flatness of $\mathscr R_X$ over the constant $R$-sheaf and its quotient identification
imply that $\pi:\mathscr R_X\to\mathscr R_X$ is injective with cokernel $(A_1)_X$. Indeed
multiplication by $\pi$ is injective on locally constant $R$-sections, and tensoring this
injection with the flat completed sheaf preserves it. Consequently $F=[\mathscr
R_X\xrightarrow{\pi}\mathscr R_X]$ in degrees $[-1,0]$ resolves $(A_1)_X$. It is K-flat:
tensoring any acyclic complex with $F$ gives a shifted multiplication cone, acyclic by the long
exact cohomology sequence. Tensor with this two-term free complex commutes with mapping cones by
the signed total-complex formula. Step 3 therefore gives $C\otimes^L_{\mathscr R_X}(A_1)_X=0$.
But tensoring $C$ with $F$ also identifies this object with the cone of $\pi:C\to C$. Its
vanishing and the long exact sequence show that $\pi$ induces isomorphisms on all cohomology
objects, hence is invertible in the derived category.
Uses: lem-weil-l-adic-extension-integers-dvr, lem-weil-pbc-constant-completion-equivalence,
def-pc-kflat-complex, def-pc-tensor-complex-sheaves, def-weil-abstract-derived-category,
lem-sf-derived-homology-long-exact.

5. For complete $M$, use its global Roos triangle from [def-weil-derived-complete], with terms
$B=\prod_n\operatorname{Res}_n M_n$. For every $j\in\mathbf Z$ and
$h:C[j]\to\operatorname{Res}_nM_n$, scalar linearity gives $h\circ\pi_{C[j]}^n=\pi_{M_n}^n\circ
h=0$, because $M_n$ is a complex of $(A_n)_X$-modules. The first factor is invertible by Step 4,
so $h=0$. The categorical product property gives
$\operatorname{Hom}(C[j],B)=\prod_n\operatorname{Hom}(C[j],\operatorname{Res}_nM_n)=0$ for every
$j$. Apply Hom-into-triangle exactness to the rotated Roos triangle $B[-1]\to M\to B$: its outer
Hom groups vanish, since $\operatorname{Hom}(C[j],B[-1])=\operatorname{Hom}(C[j+1],B)=0$. Hence
$\operatorname{Hom}(C[j],M)=0$ for all $j$. Finally Hom-out-of-triangle exactness on
$N\xrightarrow{\eta_N}C(N)\to C\to N[1]$ and its rotations gives the natural $R$-linear bijection
$$\operatorname{Hom}(C(N),M)\xrightarrow{\;\circ\eta_N\;}\operatorname{Hom}(N,M),$$ because the
adjacent terms are $\operatorname{Hom}(C,M)=\operatorname{Hom}(C[-1],M)=0$. This proves the
completion adjunction needed here using the global completeness definition itself.
Uses: def-weil-derived-complete, lem-weil-pbc-hom-into-triangle-exact,
lem-weil-pbc-hom-out-of-triangle-exact.

6. The ambient tensor-Hom adjunction needed here is for an arbitrary ringed site. Choose K-flat
representatives $Q_P,Q_K$ with flat terms and a K-injective representative $I_M$. The internal
Hom complex $\mathcal Hom^\bullet(Q_K,I_M)$ is K-injective. The functorial total-complex currying
isomorphism gives $$\mathcal Hom^\bullet(Q_P,\mathcal Hom^\bullet(Q_K,I_M))\cong\mathcal
Hom^\bullet(\operatorname{Tot}(Q_P\otimes Q_K),I_M).$$ These represent the corresponding derived
internal Homs: the definition computes internal Hom into a K-injective resolution, and the cited
quasi-isomorphism invariance permits the K-flat replacements. Taking degree-zero derived global
sections and using the global-sections/Hom identification yields
$$\operatorname{Hom}(P\otimes^L_{\mathscr R_X}K,M)\cong\operatorname{Hom}(P,R\mathcal
Hom_{\mathscr R_X}(K,M)).$$ The currying formula sends a map $h$ to $p\mapsto(k\mapsto h(p\otimes
k))$, where, for $p\in Q_P^i$, the tensor differential is $d(p\otimes k)=dp\otimes
k+(-1)^ip\otimes dk$ and the differential of a homogeneous Hom map $h$ of degree $t$ is
$dh=d_Mh-(-1)^thd$. Substitution in these two formulas verifies that currying commutes with the
differential, with no additional sign in the displayed currying formula. Its inverse evaluates.
This describes the evaluation and the naturality of the adjunction, rather than invoking a
tensor-Hom theorem for scheme structure sheaves.
Uses: lem-pc-kflat-resolution, prop-pur-kinjective-resolutions-exist,
lem-pur-hom-kflat-into-kinjective, lem-sc-derived-hom-tensor-total, lem-pur-rhom-well-defined,
lem-pur-rhom-global-sections, def-weil-derived-pullback-tensor-hom.

7. For $P,K,M\in\mathcal C_R(X)$, integral internal Hom is in $\mathcal C_R(X)$ by the
integral-Hom preservation statement. Combine Steps 2-6, using fullness of this subcategory, to
obtain the natural $R$-linear bijection $$\Phi_R:\operatorname{Hom}_{\mathcal
C_R}(P\widehat\otimes_R^LK,M)\cong\operatorname{Hom}_{\mathcal C_R}(P,R\mathcal Hom_R(K,M)).$$
Its left-to-right map is first precomposition with the canonical completion unit, then currying.
The counit is the unique map $R\mathcal Hom_R(K,M)\widehat\otimes_R^LK\to M$ whose precomposition
with that unit is ambient evaluation. The unit is $\Phi_R(1_{P\widehat\otimes_R^LK}):P\to
R\mathcal Hom_R(K,P\widehat\otimes_R^LK)$; the counit is $\Phi_R^{-1}(1_{R\mathcal Hom_R(K,M)})$.
Naturality of $\Phi_R$ makes the two triangle identities the assertion that currying and
uncurrying are inverse. Thus completion has not silently changed the tensor adjunction or its
evaluation.
Uses: cor-coef-integral-internal-hom, def-weil-derived-complete-integral-detailed.

8. The raw scalar localization has exactly the same objects and Hom groups
$\operatorname{Hom}_{\mathcal C_R}(U,V)\otimes_RE$. Tensoring $\Phi_R$ with $E$ therefore gives
$$\operatorname{Hom}_{D^b_c(X,E)}(P\otimes_E^LK,M)\cong\operatorname{Hom}_{D^b_c(X,E)}(P,R\mathcal
Hom_E(K,M)).$$ Every map is a finite sum of integral maps times scalars; the displayed bijection
sends $h\otimes a$ to $\Phi_R(h)\otimes a$. Its naturality for fractions follows from
$R$-linearity: the two sides of each integral naturality identity are multiplied by the same
product of the denominators' inverses. In two-variable operations $u\otimes a$ and $v\otimes b$
act by the integral operation on $(u,v)$ times $ab$ (precomposition in the contravariant
variable). Thus these are exactly the coefficient-passage functors, on maps as well as objects.
The evaluation, unit, counit and their identities are the integral ones tensored with $1$, as
follows by applying this Hom bijection to identities. No new objects from a Karoubi envelope are
involved.
Uses: def-weil-rationalization-karoubi, def-weil-derived-pullback-tensor-hom,
prop-weil-pbc-rational-transport.

9. Integral Verdier duality is $D_{X,R}K=R\mathcal Hom_R(K,\omega_{X,R})$ and the rational
duality functor is its localization, with $\omega_{X,E}$ the image of $\omega_{X,R}$. Specialize
Step 8 to that second argument. It gives the asserted equality $D_{X,E}K=R\mathcal
Hom_E(K,\omega_{X,E})$, with evaluation the rationalized integral evaluation. The double-dual map
is the same one as in rational Verdier duality, since both are obtained by transposing that
evaluation; the cited integral and rational duality statements identify these actual maps.
Uses: thm-coef-integral-verdier, thm-coef-rational-verdier.

10. For separated finite-type $f:X\to Y$, put $A_R=Rf_{!,R}$ and
$G_R(M)=R\lim_n\operatorname{Res}_n Rf_n^!M_n$. The integral exceptional-adjoint theorem supplies
the adjunction $A_R\dashv G_R$ on the stated bounded constructible categories, its actual unit
$\eta_R$, counit $\varepsilon_R$, and the canonical isomorphism $G_R\cong
D_{X,R}f^*_{\mathrm{comp}}D_{Y,R}$ identifying those data. The compact-support functor is
$R$-linear by its coefficient-level construction and strict derived limit. The displayed formula
for $G_R$ also makes it $R$-linear: internal duality acts by linear precomposition (Steps 6 and
9), completed pullback is linear on the coefficient representatives of Step 1, and the formula
contains two dualities. For $h:A_RK\to M$, its adjoint is $G_R(h)\circ\eta_{R,K}$, so the adjoint
of $ah$ is $G_R(ah)\circ\eta_{R,K}=a(G_R(h)\circ\eta_{R,K})$. This proves the required linearity
of the actual adjunction bijection. Apply scalar transport to the functors and natural
transformations, and explicitly tensor the integral Hom bijection with $E$. This gives $A_E\dashv
G_E$, with units $\eta_R\otimes1$ and counits $\varepsilon_R\otimes1$; the triangle equations
remain equations after tensoring with $1$. The transport statement alone is not being used as a
theorem asserting that every adjunction survives an unspecified localization.
Uses: prop-coef-integral-exceptional-adjoint, prop-weil-pbc-rational-transport,
def-weil-rationalization-karoubi.

11. The left adjoint $A_E$ of Step 10 is the rational compact-support functor: its integral
representative and strict finite-reduction tower are exactly the ones in the definition of
rational compact support. Likewise $G_E$ is the rationalized finite-stage exceptional inverse
image specified in the exceptional-inverse-image definition. Localizing the integral formula,
using the already identified pullback and duality functors, gives $Rf_E^!M\cong
D_{X,E}f^*D_{Y,E}M$. If either operation is instead characterized by the adjunction, its
comparison is forced by the counit: the unique map between right adjoints whose transpose is the
other counit is inverse to the reverse comparison, since both composites transpose to the
original counit. This proves preservation of the units and counits too. For $f=a_X$, the integral
theorem identifies $G_R(R)$ with $\omega_{X,R}$, so rationalizing gives
$Ra_{X,E}^!E=\omega_{X,E}$.
Uses: def-weil-integral-rational-qbar-compact-support, def-weil-exceptional-inverse-image,
def-weil-derived-pullback-tensor-hom, prop-coef-integral-exceptional-adjoint,
thm-coef-rational-verdier.

12. We now check finite extension, including the adjunction maps. Let $E\subset L$, $S=\mathcal
O_L$, $v=\varpi_L$, ramification index $e$, and $r=[L:E]$. At level $n$ use
$B_n=S/\pi^nS=S/v^{en}$, finite free over $A_n$; these are the specified cofinal $S$-levels.
Write $T_W$ for integral completed extension. Finite-free completed-scalar comparison identifies
it, by its canonical completion map, with ordinary derived extension $-\otimes^L_{\mathscr
R_W}\mathscr S_W$, where $\mathscr S_W$ is finite free of rank $r$ over $\mathscr R_W$. This
comparison is between the actual strict-tower functors, not just unrelated objects with
isomorphic reductions. The integral dualizing, internal-Hom and duality comparisons
$u,v_{K,M},\beta$ preserve evaluation and biduality; pullback and tensor also have the stated
scalar comparisons. In particular internal-Hom evaluation has the scalar rule $(h\otimes
s,k\otimes t)\mapsto h(k)\otimes st$.
Uses: lem-coef-finite-free-extension, lem-weil-finite-free-completed-scalar-comparison,
lem-coef-integral-finite-extension, lem-pur-integral-operations-scalar-extension.

13. Fix one compactification $f=pj$ at all coefficient levels. The compact-support
reduction-tower functor gives a lift to the derived category of strict towers, whose evaluations
and quotient transitions are exactly the stated finite compact-support functors; use this lift
when applying derived inverse limit below. At $A_n\to B_n$, extension by zero commutes with
finite direct sums and restriction of scalars because it is an exact additive left adjoint
computed degreewise. The $Rp_*$ finite-free comparison is the one in the finite-free-extension
statement, and composing gives $T_{Y,n}Rf_{!,A_n}\cong Rf_{!,B_n}T_{X,n}$. These maps are
compatible with the quotient transitions: restriction of scalars commutes with $Rf_!$, and the
cited finite-free comparisons commute with reductions. Choose an $R$-basis of $S$, giving a
compatible basis of every $B_n$. On the underlying $A_n$-complexes the comparison is the
finite-sum map $(Rf_{!,A_n}K_n)^{\oplus r}\to Rf_{!,A_n}(K_n^{\oplus r})$. A basis change acts by
the same matrix on both sides, so the map is independent of the basis. Finite sums commute with
termwise products and $1-s$ and hence with the strict-tower cone computing $R\lim$; exact
countable products justify this model on pro-etale modules. Taking these actual tower maps and
the cofinal levels of Step 12 yields $$\alpha:T_Y A_R\xrightarrow{\sim}A_S T_X.$$ Its underlying
map in any basis is finite-sum distributivity. All its inverses and compositions are therefore
compatible with the chosen reduction maps, not just identifiable after reduction.
Uses: lem-cbc-proetale-extension-zero, lem-coef-finite-free-extension,
lem-sf-compact-support-restriction-of-scalars, def-weil-integral-rational-qbar-compact-support,
lem-weil-proetale-countable-products-exact, lem-weil-pbc-ringed-strict-tower-homotopy-limit,
lem-weil-finite-free-completed-scalar-comparison,
lem-weil-compact-support-reduction-tower-functor.

14. Let $U_W$ be restriction from $\mathscr S_W$ to $\mathscr R_W$; it leaves underlying abelian
sheaves unchanged and is exact. The balanced maps $h\mapsto[k\mapsto h(1\otimes k)]$ and
$g\mapsto[s\otimes k\mapsto s g(k)]$ give $T_W\dashv U_W$ on module sheaves. Finite freeness
makes $T_W$ exact as well. Thus the partial-derived-adjunction lemma applies with
everywhere-defined derived functors: their quasi-isomorphism diagrams are already constant up to
the invertible images of the quasi-isomorphisms. It gives the same adjunction on ambient derived
categories. It restricts to the constructible categories. Indeed $T_W$ preserves them by the
integral finite-extension statement. For $N\in\mathcal C_S(W)$, choose an $S$-K-flat resolution;
it is also $R$-K-flat: for an acyclic $R$-complex $Q$, first tensor with the finite free
$\mathscr S_W$, then with the $S$-K-flat resolution. Both operations preserve the required
acyclicity. Tensoring this representative gives $$(U_WN)\otimes^L_{\mathscr
R_W}(A_n)_W=\operatorname{Res}_{A_n\to B_n}(N\otimes^L_{\mathscr S_W}(B_n)_W).$$ Restriction
preserves finite-level constructibility (finite modules remain finite, and the same local
constant presentations apply) and the given uniform cohomological interval. It also commutes with
products and cones on the underlying sheaves. Completeness therefore follows from the complete
$S$-tower on the cofinal $en$ levels of Step 12. Hence $U_WN\in\mathcal C_R(W)$.
Uses: def-pc-sheaf-restrict-scalars, lem-weil-finite-free-completed-scalar-comparison,
lem-pc-pre-derived-adjoint-functors-general, lem-coef-integral-finite-extension,
lem-coef-finite-free-extension, def-weil-derived-complete-integral-detailed,
lem-weil-pbc-ringed-strict-tower-homotopy-limit, def-pc-kflat-complex, lem-pc-kflat-resolution.

15. Apply Steps 10 and 14 over both rings. For $N\in\mathcal C_S(Y)$ the following natural
bijections, in this order, determine an isomorphism $\rho:U_XG_SN\cong G_RU_YN$:
$$\begin{aligned} \operatorname{Hom}_R(K,U_XG_SN)&\cong\operatorname{Hom}_S(T_XK,G_SN)\\
&\cong\operatorname{Hom}_S(A_ST_XK,N)\\ &\cong\operatorname{Hom}_S(T_YA_RK,N)\\
&\cong\operatorname{Hom}_R(A_RK,U_YN)\\ &\cong\operatorname{Hom}_R(K,G_RU_YN). \end{aligned}$$
The middle map is precomposition with $\alpha_K$. Taking identities on the two representing
objects gives inverse comparison maps: their composites are identities because the displayed
bijections are inverse and natural. In particular this uses only the constructible exceptional
adjunction, not an unbounded ambient pro-etale exceptional adjoint.
Uses: prop-coef-integral-exceptional-adjoint.

16. Define $b_M:T_XG_RM\to G_ST_YM$ as the transpose under $A_S\dashv G_S$ of
$$A_ST_XG_RM\xrightarrow{\alpha_{G_RM}^{-1}}T_YA_RG_RM\xrightarrow{T_Y\varepsilon_{R,M}}T_YM.$$
This map is invertible. To check it, choose the basis of Step 13. Then $U_YT_YM=M^{\oplus r}$,
and $\rho$ of Step 15 identifies the underlying target with $G_R(M^{\oplus r})$. A right adjoint
preserves finite products; here they are finite biproducts. The $i$-th component of $\rho U_Xb_M$
is $G_R$ applied to the $i$-th coefficient projection, composed with the map transposed from the
corresponding component of $T_Y\varepsilon_R$. By the scalar rule for the extension/restriction
adjunction and the finite-sum description of $\alpha$, this is projection onto the $i$-th copy of
$G_RM$, followed by $G_R\varepsilon_R\circ\eta_RG_R=1$. The off-diagonal components are zero.
Thus the underlying matrix of $b_M$ is the identity on $(G_RM)^{\oplus r}$. Restriction detects
an isomorphism, since it leaves the cohomology sheaves of its cone unchanged. This proves
invertibility without inferring equality of maps from equality of their finite reductions.
Uses: lem-weil-pbc-right-adjoint-preserves-limits, prop-coef-integral-exceptional-adjoint,
def-pc-sheaf-restrict-scalars.

17. Apply the mate counit identity [lem-amb-mate-unit-counit] and unit identity
[lem-pur-mate-unit-compatibility] to $L_1=A_R$, $R_1=G_R$, $L_2=A_S$, $R_2=G_S$, $G=T_X$,
$H=T_Y$, and the square $\alpha^{-1}$. Step 16 defined $b$ by exactly this transpose. Hence
$$\varepsilon_{S,T_YM}\circ A_S(b_M)\circ\alpha_{G_RM}=T_Y(\varepsilon_{R,M}),$$ $$b_{A_RK}\circ
T_X(\eta_{R,K})=G_S(\alpha_K^{-1})\circ\eta_{S,T_XK}.$$ These are the required counit and unit
identities for the actual integral adjunctions. The only rearrangement is precomposition of the
counit equation with the isomorphism $\alpha_{G_RM}$.
Uses: lem-amb-mate-unit-counit, lem-pur-mate-unit-compatibility.

18. The integral adjunction uses the coherent finite exceptional realization specified in
[prop-coef-integral-exceptional-adjoint]. Apply [lem-coef-finite-scalar-mate-realization] with
the fixed compactification of Step 13 and the cofinal $S$-levels $en$ of Step 12. Its source and
target comparisons are precisely those used in Steps 12-14. It identifies the total limit of the
finite transposes with the map whose transpose is $T_Y\varepsilon_R\circ\alpha^{-1}$. That map is
$b$ by Step 16 and injectivity of the adjunction bijection. Thus the coefficient-passage
exceptional comparison is $b$, with the equations of Step 17. No equality of integral maps is
inferred solely from equality of their finite reductions.
Uses: prop-coef-integral-exceptional-adjoint, lem-coef-finite-scalar-mate-realization.

19. Write $c_Z:T_Xf_R^*Z\xrightarrow{\sim}f_S^*T_YZ$ and
$\beta^W_Z:T_WD_{W,R}Z\xrightarrow{\sim}D_{W,S}T_WZ$ for the pullback and duality comparisons of
Step 12. With the canonical formula identifications $\kappa_R:G_R\cong D_{X,R}f_R^*D_{Y,R}$ and
$\kappa_S:G_S\cong D_{X,S}f_S^*D_{Y,S}$, their composite is $$b'_M=\kappa_{S,T_YM}^{-1}\circ
D_{X,S}\bigl(c_{D_{Y,R}M}^{-1}\circ
f_S^*((\beta^Y_M)^{-1})\bigr)\circ\beta^X_{f_R^*D_{Y,R}M}\circ T_X(\kappa_{R,M}).$$ The arrow
inside $D_{X,S}$ runs from $f_S^*D_{Y,S}T_YM$ to $T_Xf_R^*D_{Y,R}M$, as contravariance requires.
By [lem-coef-dual-formula-scalar-transpose], the $A_S\dashv G_S$ transpose of this map is
$T_Y\varepsilon_R\circ\alpha^{-1}$. It equals the defining transpose of $b$ in Step 16, so
$b'=b$. Consequently the formula comparison preserves the same units and counits as the
coefficient-passage comparison; the evaluation comparisons remain those fixed in Step 12.
Uses: lem-coef-dual-formula-scalar-transpose.

20. Finally rationalize the finite-extension comparisons. By the definition of $-\otimes_E L$,
its integral representative is exactly $T$, and each component of $\alpha,b,u,v,\beta$ is sent to
that component tensored with $1$. Composition in raw scalar localization is bilinear, so both
equations of Step 17 and the evaluation identities remain the same equations after localization.
Coherence for $E\subset L\subset L'$ follows at compact support from multiplication $(k\otimes
s)\otimes t\mapsto k\otimes st$ on the finite free tower maps; taking mates gives the same
equality for $b$ because their transposes are the same composite counit. For internal Hom and
duality, identity and associator coherence are those of the integral comparisons. The rational
duality theorem gives the corresponding evaluation and biduality comparisons as well. This proves
every scalar-extension compatibility claimed in the item within the specified rationalized
constructible categories.
Uses: def-weil-rationalization-karoubi, prop-weil-pbc-rational-transport,
lem-coef-integral-finite-extension, lem-pur-integral-operations-scalar-extension,
thm-coef-rational-verdier.
-/
theorem coef_rational_operations
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X Y : Scheme.{u}) [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f) :
    RationalOperations.Conclusion D l hl Ω X Y f c := by
  sorry

end WeilConjectures
