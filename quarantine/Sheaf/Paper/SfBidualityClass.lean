/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.SixFunctors.IntegralDualizing
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.Topology.KrullDimension
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.DualityPairing
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.Paper.WeilVerdierPreservationStrata
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.IntegralResidueTor
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.FiniteFieldFiber
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.FiniteTorAmplitude

import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.SfDerivedComplete
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.FiniteStageVerdierBiduality
import Sheaf.SixFunctors.FiniteDualitySiteComparison
import Sheaf.SixFunctors.IntegralVerdier
import Sheaf.SixFunctors.RationalOperations
import Sheaf.SixFunctors.RationalVerdier
/-! # Verdier biduality on the four coefficient stages

Source: Weil blueprint, main-20261015, sec-six-functors/sk-thm-sf-package,
node thm-sf-biduality-class, and sk-prop-sf-biduality-general
(blueprint: thm-sf-biduality-class).

The integral dualizing object is characterized by its coherent exceptional reduction
system and its derived limit. Rational and algebraically closed duality are specified
by natural descent comparisons, including the evaluation transpose. Thus the field
clauses use the actual raw localization and common-stage categories, without an
idempotent completion or an unspecified double-dual isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u v a b c e
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace WeilConjectures

/-- Compatibility with the evaluation-defined double-dual arrow under a natural
comparison of contravariant functors. The two comparison factors are forced by
contravariance; this fixes the transported arrow, not merely its source and target.
Source: blueprint thm-sf-biduality-class, coefficient descent
(blueprint: thm-sf-biduality-class). -/
def SfClassEvaluationCompatible
    {C : Type a} [Category.{b} C] {B : Type c} [Category.{e} B]
    (F : C ⥤ B) (D : Cᵒᵖ ⥤ C) (H : Bᵒᵖ ⥤ B)
    (δ : 𝟭 C ⟶ D.rightOp ⋙ D) (ε : 𝟭 B ⟶ H.rightOp ⋙ H)
    (r : D ⋙ F ≅ F.op ⋙ H) : Prop :=
  ∀ K : C,
    F.map (δ.app K) ≫ r.hom.app (op (D.obj (op K))) ≫
      H.map (r.inv.app (op K)).op = ε.app (F.obj K)

/-- An exact contravariant anti-equivalence together with its natural biduality
isomorphism. The specific evaluation normalization is imposed by the stage clauses.
Source: blueprint thm-sf-biduality-class, first conclusion
(blueprint: thm-sf-biduality-class). -/
structure SfClassDuality (C : Type a) [Category.{b} C]
    [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] where
  /-- The contravariant dual functor. -/
  dual : Cᵒᵖ ⥤ C
  /-- Exact anti-equivalence, using the actual distinguished triangles. -/
  exact : ∃ s : dual.CommShift ℤ, ∀ T : Triangle Cᵒᵖ,
    T ∈ distTriang Cᵒᵖ →
      Triangle.mk (dual.map T.mor₁) (dual.map T.mor₂)
        (dual.map T.mor₃ ≫ (s.commShiftIso (1 : ℤ)).hom.app T.obj₁) ∈
          distTriang C
  /-- The specified contravariant functor is an equivalence. -/
  equivalence : dual.IsEquivalence
  /-- The evaluation-defined natural double-dual isomorphism. -/
  bidual : 𝟭 C ≅ dual.rightOp ⋙ dual

/-- Exact restricted duality and its specified evaluation transpose in an ambient
triangulated category. This packages both assertions of the present node, rather than
replacing the evaluation arrow by an arbitrary isomorphism.
Source: blueprint thm-sf-biduality-class, finite-stage conclusion
(blueprint: thm-sf-biduality-class). -/
structure SfClassAmbientDuality
    (C : Type a) [Category.{b} C] [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) (H : Cᵒᵖ ⥤ C)
    (ev : ∀ K : C, K ⟶ H.obj (op (H.obj (op K)))) where
  /-- Preservation of the indicated full subcategory. -/
  preserves : ∀ K : C, P K → P (H.obj (op K))
  /-- The equivalence is the restriction of H, naturally on objects and maps. -/
  restriction : ∃ e : P.FullSubcategoryᵒᵖ ≌ P.FullSubcategory,
    Nonempty (e.functor ⋙ P.ι ≅ P.ι.op ⋙ H)
  /-- Exactness for the inherited distinguished triangles. -/
  exact : ∃ s : H.CommShift ℤ, ∀ T : Triangle Cᵒᵖ,
    P T.obj₁.unop → P T.obj₂.unop → P T.obj₃.unop →
      T ∈ distTriang Cᵒᵖ →
        Triangle.mk (H.map T.mor₁) (H.map T.mor₂)
          (H.map T.mor₃ ≫ (s.commShiftIso (1 : ℤ)).hom.app T.obj₁) ∈
            distTriang C
  /-- Naturality of the specified evaluation transpose on the ambient category. -/
  naturality : ∀ (K L : C) (f : K ⟶ L),
    f ≫ ev L = ev K ≫ (H.rightOp ⋙ H).map f
  /-- The evaluation transpose is invertible on precisely the asserted domain. -/
  invertible : ∀ K : C, P K → IsIso (ev K)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]

/-- The existing etale internal Hom into the finite dualizing object.
Source: blueprint thm-sf-biduality-class, finite etale dual
(blueprint: thm-sf-biduality-class). -/
abbrev sfClassEtaleDual (n : ℕ) :=
  (Etale.derivedHom (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) X).flip.obj
    (finiteDualizingEtaleTerm l E D X n)

/-- Finite etale duality, including the natural evaluation transpose and signed bounds.
Source: blueprint thm-sf-biduality-class, finite-stage assertion
(blueprint: thm-sf-biduality-class). -/
def SfClassFiniteEtale (n : ℕ) : Prop :=
  (∃ h : Etale.AmbientDualityPairing
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) X (finiteDualizingEtaleTerm l E D X n),
    Nonempty (SfClassAmbientDuality _
      (finiteTorConstructibleEtale l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X)
      (sfClassEtaleDual D l E X n)
      (Etale.AmbientDualityPairing.bidualityMap
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) X h))) ∧
  ∀ (d : ℕ), topologicalKrullDim X ≤ (d : WithBot ℕ∞) →
    (∀ (K : Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) X) (a b : ℤ),
      a ≤ b →
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X K →
      Etale.DerivedCategory.hasTorAmplitudeIn (finiteDualizingCoeff l E n) X a b K →
      Etale.DerivedCategory.hasTorAmplitudeIn (finiteDualizingCoeff l E n) X
        (-b - 2 * (d : ℤ)) (-a) ((sfClassEtaleDual D l E X n).obj (op K))) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn (finiteDualizingCoeff l E n) X
      (-(2 * (d : ℤ))) 0 (finiteDualizingEtaleTerm l E D X n)

/-- The recorded internal Hom in the constant positive-level coefficient sheaf.
Index n means exponent n+1, covering every positive finite coefficient level.
Source: blueprint thm-sf-biduality-class, definition of D
(blueprint: thm-sf-biduality-class). -/
abbrev sfClassFiniteHom (n : ℕ) :=
  Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u}
    (ProEt.topology X)
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))))

/-- Internal Hom into the existing exceptional inverse image of the coefficient unit.
Source: blueprint thm-sf-biduality-class, finite-stage dual
(blueprint: thm-sf-biduality-class). -/
abbrev sfClassFiniteDual (n : ℕ) :=
  (sfClassFiniteHom l E X n).flip.obj (integralDualizingFiniteTerm l E D X n)

/-- Finite-stage duality with its actual evaluation transpose and the signed Tor bound.
The full subcategory is the existing finite-Tor constructible category.
Source: blueprint thm-sf-biduality-class, finite and dualizing-object clauses
(blueprint: thm-sf-biduality-class). -/
def SfClassFinite (n : ℕ) : Prop :=
  ∃ M : RingedSiteDualityModel.{u + 1, u, u}
      (ProEt.topology X)
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))),
    Nonempty (SfClassAmbientDuality _
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X)
      (sfClassFiniteDual D l E X n)
      (ringedSiteBidual M.closed M.symmetric (integralDualizingFiniteTerm l E D X n))) ∧
      ∀ (d : ℕ), topologicalKrullDim X ≤ (d : WithBot ℕ∞) →
        (∀ (K : normalizedDVRDerived l E X n) (a b : ℤ),
          intrinsicFiniteTorsionConstructible l E (n + 1)
              (Nat.succ_le_succ (Nat.zero_le n)) X K →
          HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1)) K a b →
          HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
            ((sfClassFiniteDual D l E X n).obj (op K)) (-b - 2 * (d : ℤ)) (-a)) ∧
        HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
          (integralDualizingFiniteTerm l E D X n) (-(2 * (d : ℤ))) 0

/-- The recorded internal Hom over the completed integral coefficient sheaf.
Source: blueprint thm-sf-biduality-class, integral-stage dual
(blueprint: thm-sf-biduality-class). -/
abbrev sfClassIntegralHom :=
  Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u}
    (ProEt.topology X) (completedIntegralCommRingSheafUnrestricted l E X))

/-- Integral duality on the whole specified category, retaining the coherent normalized
exceptional tower that defines omega. The model fixes the actual evaluation map.
Source: blueprint thm-sf-biduality-class, integral-stage assertions
(blueprint: thm-sf-biduality-class). -/
structure SfClassIntegral where
  /-- The integral dualizing object in the specified constructible category. -/
  omega : sfIntegralConstructibleCategory l E X
  /-- Its actual coherent normalized reduction system. -/
  tower : NormalizedDVRTower l E X D hl
  /-- Its finite terms are the canonical finite dualizing objects. -/
  finiteIso : ∀ n : ℕ, tower.M n ≅ integralDualizingFiniteTerm l E D X n
  /-- The identifications retain the canonical exceptional quotient transitions. -/
  transition : ∀ {m n : ℕ} (h : n ≤ m),
    tower.tau h ≫ (normalizedDVRRes l E X h).map (finiteIso n).hom =
      (finiteIso m).hom ≫
        (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
          (integralDualizingFiniteComparison l E D X hl h)
  /-- The object is the derived inverse limit of that strict coherent tower. -/
  limitIso : omega.obj ≅ (integralDualizingLimit l E X).obj tower.tower
  /-- Its reductions are the counit maps of the derived limit. -/
  limitPresentation : IntegralDualizingLimitPresentation l E D hl X tower omega.obj
  /-- The normalized closed model supplies the ordinary derived evaluation. -/
  model : RingedSiteDualityModel.{u + 1, u, u}
    (ProEt.topology X) (completedIntegralCommRingSheafUnrestricted l E X)
  /-- Duality on all bounded constructible integral objects. -/
  duality : SfClassDuality (sfIntegralConstructibleCategory l E X)
  /-- Its ambient functor is exactly the recorded RHom into omega. -/
  comparison : duality.dual ⋙ (sfIntegralConstructible l E X).ι ≅
    (sfIntegralConstructible l E X).ι.op ⋙ (sfClassIntegralHom l E X).flip.obj omega.obj
  /-- The natural biduality isomorphism is the actual evaluation transpose. -/
  evaluation : ∀ K : sfIntegralConstructibleCategory l E X,
    (sfIntegralConstructible l E X).ι.map (duality.bidual.hom.app K) ≫
        comparison.hom.app (op (duality.dual.obj (op K))) ≫
        ((sfClassIntegralHom l E X).flip.obj omega.obj).map
          (comparison.inv.app (op K)).op =
      ringedSiteBidual model.closed model.symmetric omega.obj K.obj
  /-- The uniform finite-Tor subcategory equals the whole integral category. -/
  whole : finiteTorConstructibleIntegral l E X = sfIntegralConstructible l E X
  /-- Every uniform input Tor interval gives the indicated uniform output interval. -/
  tor : ∀ (d : ℕ), topologicalKrullDim X ≤ (d : WithBot ℕ∞) →
    ∀ (K : sfIntegralConstructibleCategory l E X) (a b : ℤ), a ≤ b →
      (∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension l E X n).obj K.obj) a b) →
      ∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension l E X n).obj
          (duality.dual.obj (op K)).obj) (-b - 2 * (d : ℤ)) (-a)
  /-- The integral dualizing object has the same uniform finite-level interval. -/
  omegaTor : ∀ (d : ℕ), topologicalKrullDim X ≤ (d : WithBot ℕ∞) →
    ∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension l E X n).obj omega.obj) (-(2 * (d : ℤ))) 0

/-- The rational dual is obtained from any integral representative by localization.
The natural comparison controls all maps, and its double-dual equation identifies
rational evaluation with localized integral evaluation. Its dualizing object is the
localization of I.omega. No new objects or idempotent completion occur.
Source: blueprint thm-sf-biduality-class, rational-stage assertion
(blueprint: thm-sf-biduality-class). -/
structure SfClassRational (I : SfClassIntegral D l hl E X) where
  /-- Exact duality on the entire raw rationalized category. -/
  duality : SfClassDuality (sfRationalConstructibleCategory l E X)
  /-- Canonical descent of the integral dual through raw localization. -/
  comparison : I.duality.dual ⋙ sfRationalConstructibleLocalization l E X ≅
    (sfRationalConstructibleLocalization l E X).op ⋙ duality.dual
  /-- Evaluation, and consequently its transpose, are the localized integral maps. -/
  evaluation : SfClassEvaluationCompatible (sfRationalConstructibleLocalization l E X)
    I.duality.dual duality.dual I.duality.bidual.hom duality.bidual.hom comparison

/-- All integral and rational assertions at a finite coefficient field, kept together
so the common-stage comparison can refer to their actual functors and evaluation maps.
Source: blueprint thm-sf-biduality-class, integral and rational assembly
(blueprint: thm-sf-biduality-class). -/
structure SfClassIntegralRational where
  /-- Integral internal-Hom duality. -/
  integral : SfClassIntegral D l hl E X
  /-- Its raw rational localization. -/
  rational : SfClassRational D l hl E X integral

/-- Exact duality on algebraically closed coefficients, with natural finite-field
comparisons that identify the actual evaluation-defined double-dual maps. Every pair
and every common-stage representative is covered by these natural comparisons.
Source: blueprint thm-sf-biduality-class, algebraically closed coefficient assertion
(blueprint: thm-sf-biduality-class). -/
def SfClassAlgebraicallyClosed (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] : Prop :=
  ∃ (S : ∀ F : AlgebraicallyClosedCoefficients.Index l Ω,
        SfClassIntegralRational D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) X)
    (B : SfClassDuality (generalAlgebraicallyClosedConstructibleCategory l Ω X)),
    ∀ F : AlgebraicallyClosedCoefficients.Index l Ω,
      ∃ r : (S F).rational.duality.dual ⋙
            GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) F ≅
          (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := Ω) (Y := X) F).op ⋙ B.dual,
        SfClassEvaluationCompatible
          (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) F)
          (S F).rational.duality.dual B.dual
          (S F).rational.duality.bidual.hom B.bidual.hom r

/-- Verdier biduality for all four coefficient stages, with signed dimension bounds.
Finite levels are n+1. The natural-number dimension bound includes the empty scheme
with d=0, and gives the sharp bound d=dim X whenever X is nonempty. Field categories
are the full specified categories, as in finiteTorFieldCoefficientCategory.

Source: blueprint main-20261015, thm-sf-biduality-class, order 2500
(blueprint: thm-sf-biduality-class).

Proof:
1. Apply thm-fix-general-biduality at every positive finite level. The etale bound
   lem-weil-verdier-preservation-strata and lem-weil-finite-duality-site-comparison,
   including evaluation compatibility, give the pro-etale result. The two Tor
   comparison clauses of lem-sf-comparison-tor-amplitude preserve the endpoints.
2. For integral K, lem-coef-integral-residue-tor gives a single finite Tor interval
   from its bounded residue reduction. Thus the whole integral category is finite-Tor.
   thm-coef-integral-verdier gives internal-Hom duality, the uniform output bounds,
   and invertibility of the actual evaluation transpose, compatibly with all reductions.
3. Apply the finite bound to the coefficient unit, whose Tor interval is [0,0].
   Evaluation at 1 identifies Hom(A,I) with I, so its dual is omega and has interval
   [-2d,0]. prop-coef-integral-dualizing supplies the normalized exceptional tower,
   its derived limit and the same uniform bound at the integral stage.
4. thm-coef-rational-verdier descends the integral functor and evaluation through raw
   scalar localization. lem-coef-rational-operations identifies this with internal
   Hom into Ra^!E. Naturality computes the dual from any integral representative.
5. thm-coef-qbar-verdier descends over common finite extensions. Each object and map
   has such a representative; evaluation and biduality are represented there too.
   The inverse is represented by the inverse finite-stage biduality map. Both
   composites are identities already there; scalar comparisons preserve them.
   def-weil-finite-tor-amplitude identifies both field finite-Tor categories with
   the entire specified constructible categories. No ambient pro-etale adjoint is used.
-/
theorem sf_biduality_class
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))] :
    (∀ (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E],
      (∀ n : ℕ, SfClassFiniteEtale D l E X n ∧ SfClassFinite D l E X n) ∧
        Nonempty (SfClassIntegralRational D l hl E X)) ∧
    ∀ (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω],
      SfClassAlgebraicallyClosed D l hl X Ω := by
  sorry

end WeilConjectures
