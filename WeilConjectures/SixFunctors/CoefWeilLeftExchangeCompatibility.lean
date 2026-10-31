/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefVerdierWeilData

/-! # Normalized compact-support Frobenius exchanges and coefficient squares

Source: blueprint `cor-coef-verdier-weil-equivariance`, proof paragraphs 1 and 3
(blueprint: lem-coef-weil-left-exchange-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v i a b c d a' b' c' d'
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.CoefVerdierWeil
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)

/-- Normalized exchange families and their coefficient laws on cached types.
Source: blueprint coefficient squares
(blueprint: lem-coef-weil-left-exchange-compatibility). -/
structure CompatibleLeftExchanges {I : Type i} [Preorder I]
    (F : I → Type a) (G : Type b)
    (finiteNorm : (∀ i, F i) → Prop) (commonNorm : G → Prop)
    (scalarLaw : ∀ i j, i ≤ j → F i → F j → Prop)
    (stageLaw : ∀ i, F i → G → Prop) where
  finite (i : I) : F i
  common : G
  finiteNormalized : finiteNorm finite
  commonNormalized : commonNorm common
  scalar (i j : I) (h : i ≤ j) : scalarLaw i j h (finite i) (finite j)
  stage (i : I) : stageLaw i (finite i) common

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
  [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
  [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
  [QuasiCompact f₀.left]

section LeftExchangeData
variable (c₀ : Compactification f₀.left)
  (A : FiberExceptional D l hl Ω X₀ f₀
    (FrobeniusExchange.geometricCompactification D f₀ c₀))
  {BX : FiberDuality D l hl Ω X₀} {BY : FiberDuality D l hl Ω Y₀}
  (WX : Coefficients D l hl Ω X₀ BX) (WY : Coefficients D l hl Ω Y₀ BY)

local notation "F" => (fiberLeft D l hl Ω X₀ f₀
  (FrobeniusExchange.geometricCompactification D f₀ c₀) A)
local notation "P" => (fun E : Index l Ω ↦
  sfWeilFrobeniusPullback D l hl X₀ (Coefficient l Ω E))
local notation "Q" => (fun E : Index l Ω ↦
  sfWeilFrobeniusPullback D l hl Y₀ (Coefficient l Ω E))
local notation "PX" => sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω
local notation "QY" => sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω
local notation "α" => (fiberLeftScalar D l hl Ω X₀ f₀
  (FrobeniusExchange.geometricCompactification D f₀ c₀) A)

/-- The finite scalar equation, on all underlying objects.
Source: blueprint coefficient squares
(blueprint: lem-coef-weil-left-exchange-compatibility). -/
def scalarLeftExchangeLaw (E L : Index l Ω) (h : E ≤ L)
    (x : finiteLeftExchangeType D l hl Ω X₀ f₀ c₀ A E)
    (y : finiteLeftExchangeType D l hl Ω X₀ f₀ c₀ A L) : Prop :=
  ∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
      (D.geometricFiber X₀).left,
    (scalarFrobenius D l hl Ω Y₀ E L h).hom.app ((F E).obj K) ≫
      (transition l Ω (D.geometricFiber Y₀).left E L h).map (x.hom.app K) ≫
      (α E L h).hom.app ((P E).obj K) =
    (Q L).map ((α E L h).hom.app K) ≫
      y.hom.app ((transition l Ω (D.geometricFiber X₀).left E L h).obj K) ≫
      (F L).map ((scalarFrobenius D l hl Ω X₀ E L h).hom.app K)

/-- The finite-to-common equation, on all underlying objects.
Source: blueprint coefficient squares
(blueprint: lem-coef-weil-left-exchange-compatibility). -/
def stageLeftExchangeLaw (E : Index l Ω)
    (x : finiteLeftExchangeType D l hl Ω X₀ f₀ c₀ A E)
    (y : commonLeftExchangeType D l hl Ω X₀ f₀ c₀ A) : Prop :=
  ∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
      (D.geometricFiber X₀).left,
    (WY.stageFrobenius E).hom.app ((F E).obj K) ≫ (fiberInclusion D l Ω Y₀ E).map (x.hom.app K) ≫
      ((fiberLeftComparison D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A) E).hom.app ((P E).obj K) =
    (QY).map (((fiberLeftComparison D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀) A) E).hom.app K) ≫
      y.hom.app ((fiberInclusion D l Ω X₀ E).obj K) ≫
      (fiberCommonLeft D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A).map
          ((WX.stageFrobenius E).hom.app K)

/-- Only the compact-support exchanges, with their normalization and coefficient
squares. No exceptional right exchange, mate, unit, or counit is included.
Source: blueprint proof paragraphs 1 and 3
(blueprint: lem-coef-weil-left-exchange-compatibility). -/
abbrev LeftExchanges :=
  CompatibleLeftExchanges
    (finiteLeftExchangeType D l hl Ω X₀ f₀ c₀ A)
    (commonLeftExchangeType D l hl Ω X₀ f₀ c₀ A)
    (finiteLeftExchangeLaw D l hl Ω X₀ f₀ c₀ A)
    (commonLeftExchangeLaw D l hl Ω X₀ f₀ c₀ A)
    (scalarLeftExchangeLaw D l hl Ω X₀ f₀ c₀ A)
    (stageLeftExchangeLaw D l hl Ω X₀ f₀ c₀ A WX WY)

end LeftExchangeData

/-- One can choose the underlying relative exceptional data with normalized Frobenius exchanges
whose finite scalar and stage-inclusion squares commute on every underlying object.
The target duality is chosen with a normalized Weil duality structure: the duality
interface pins the signed symmetry only on literal K-flat pairs, so the one-scheme
normalization holds for the normalized construction, not for every duality.

Source: blueprint `cor-coef-verdier-weil-equivariance`, proof paragraphs 1 and 3
(blueprint: lem-coef-weil-left-exchange-compatibility).

Proof: construct the relative data and its duality formula by the normalized
coefficient construction of thm-coef-qbar-verdier and rational exceptional duality,
with the natural signed symmetry at every finite field of BY. The one-scheme
argument of lem-coef-weil-normalized-duality (inverse-Frobenius equivalence, the
structure-morphism mate on the coefficient unit, the evaluation-normalized
internal-Hom pullback comparison and the injective tensor-Hom transpose) applies to
this BY and gives WY with its dualizing normalization.
Keep the rational realizations induced from this same coherent integral system,
so their coefficient comparisons are the prescribed ones. For this chosen system A,
at a finite field conjugate the specified rational Frobenius exchange by
A.system.ring.rationalLeft. Inverse Frobenius and exchange pasting make this
transformation invertible. Its conjugation back is literally frobeniusRational.
The scalar comparison square is the normalized compact-support coefficient square:
compute both routes before total inverse limit, where scalar tensor and inverse
image commute and proper adjunction mates and open extension commute with those
maps. Rationalization preserves that equality. Conjugate it by the same finite
realization maps to obtain the displayed scalar equation for every rational object.

At common coefficients, represent each object by its finite-stage object and use
A.leftComparison to descend the finite exchanges. Every arrow and equality has a
representative at a larger finite field. The scalar equation proves independence
of enlargement, hence naturality; it also descends the finite inverse. This is the
canonical commonStageExchange, since both have its prescribed finite components.
The defining component calculation gives commonNormalized. Finally WX and WY have
stage comparisons fixed componentwise to sfWeilStagePullbackIdentification. Insert
these identities in the same finite-component calculation to obtain stage. No
Weil structure on an input object and no right-adjoint exchange is needed. -/
theorem coef_weil_left_exchange_compatibility
    (c₀ : Compactification f₀.left) (BX : FiberDuality D l hl Ω X₀)
    (hIX : Nonempty (FiberInternalHom D l hl Ω X₀ BX))
    (hωX : FiberDualizing D l hl Ω X₀ BX) :
    ∃ (BY : FiberDuality D l hl Ω Y₀)
      (A : FiberExceptional D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀)),
      Nonempty (FiberInternalHom D l hl Ω Y₀ BY) ∧
      FiberDualizing D l hl Ω Y₀ BY ∧
      Nonempty (FiberExceptionalFormula D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) BX BY A) ∧
      (∃ WY : Coefficients D l hl Ω Y₀ BY, DualizingNormalization D l hl Ω Y₀ BY WY) ∧
      ∀ (WX : Coefficients D l hl Ω X₀ BX) (WY : Coefficients D l hl Ω Y₀ BY),
        Nonempty (LeftExchanges D l hl Ω X₀ f₀ c₀ A WX WY) := by sorry

end WeilConjectures.CoefVerdierWeil
