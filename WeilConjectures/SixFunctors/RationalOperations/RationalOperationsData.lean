/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.ConstantCoefficientObjectsConstructible
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SixFunctors.Rational.RationalVerdier

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

end WeilConjectures.RationalOperations
