/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.Paper.CompletedConstantRightUnit
public import Sheaf.Paper.ConstantWeilStageCompatibility
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.EtaleWeilFundamentalRepresentation
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.Paper.LisseCompletedSystemData
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Constant-line tensor and scalar Weil rescaling

Source: the first sentence of the constant-twist weight proof in the current blueprint,
sec-purity-real-sheaves/sk-r-real-linear/lem-wf-constant-twist-weight.proof.md
(blueprint: lem-wf-constant-twist-coefficient-comparison).

All tensor products below are the recorded completed PBC tensor. The normalization
retains coefficient multiplication before completion, rather than choosing a tensor iso.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor
namespace WeilConjectures
attribute [local irreducible] wfRationalTensor wfConstructibleInclusion
  wfRationalTensorPullback wfWeilStructure
  ScalarLocalization.category ScalarLocalization.preadditive
  ScalarLocalization.linear ScalarLocalization.linearOriginal

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]
  (S : FdCoefficientComparisonSystem.{u} c.l c.Qbar)

/-- View a PBC Weil object in the ambient tensor category, retaining its Weil map.
Source: item proof, step 6 (blueprint: lem-wf-constant-twist-coefficient-comparison). -/
def constantTwistAmbientPair (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (K : WeilD D c X₀ E) : IsoAlgebra (wfAmbientFrobenius D c X₀ E) :=
  IsoAlgebra.mk (wfWeilCarrier D c X₀ E K) (wfWeilStructure D c X₀ E K)

/-- The finite-stage comparison, including the prescribed completed right-unit map.
Source: item proof, steps 4--7
(blueprint: lem-wf-constant-twist-coefficient-comparison).
Proof: the ordinary tensor/pullback unit equation survives completion by naturality
of the Koszul unit. Multiplication by b on the second factor becomes multiplication
by b on the target. Thus the completed right unitor intertwines the tensor Frobenius
with b theta. Its inverse satisfies the inverse square. The forgetful functor is
faithful, so the underlying-map normalization determines the Weil isomorphism uniquely. -/
theorem constantTwistFiniteEta_existsUnique
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) (b : E.valˣ)
    (K : sfWeilComplex D c.l c.different X₀ (pbcFiniteField.{u} c.l c.Qbar E)) :
    ∃! e : pbcFiniteConstantWeilTensor D c X₀ S E b
          ((constantTwistFiniteComparison D c X₀ S E).obj K) ≅
        constantTwistAmbientPair D c X₀ E
          ((constantTwistFiniteComparison D c X₀ S E).obj
            (sfFiniteConstantTwist D c X₀ E b K)),
      HEq e.hom.hom.f (constantTwistRationalRightUnit D c X₀ S E K.carrier).hom := by
  sorry

/-- The unique finite-stage Weil isomorphism with underlying completed right unitor.
Source: item proof, step 7 (blueprint: lem-wf-constant-twist-coefficient-comparison). -/
def constantTwistFiniteEta (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (b : E.valˣ)
    (K : sfWeilComplex D c.l c.different X₀ (pbcFiniteField.{u} c.l c.Qbar E)) :=
  (constantTwistFiniteEta_existsUnique D c X₀ S E b K).exists.choose

attribute [local irreducible] constantTwistOrdinaryRightUnit constantTwistIntegralUnit
  constantTwistCompletedRightUnit constantTwistRationalRightUnit constantTwistFiniteEta


/-- The explicit finite PBC line is the common J-image in the statement.
Source: item first displayed definition
(blueprint: lem-wf-constant-twist-coefficient-comparison).
Proof: evaluate J's normalized finite-stage comparison on the twisted constant pair.
Its source is the common-stage image and its target is precisely the defined PBC
line. This is the prescribed comparison, so no independent coefficient model enters. -/
theorem constantTwistLine_commonImage
    (J : ConstantTwistWeilComparison D c X₀ S)
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) (b : E.valˣ) :
    Nonempty (J.common.functor.obj (sfWeilStageObject D c.l c.different X₀ c.Qbar E
        (sfFiniteConstantTwist D c X₀ E b
          (constantWeilRationalComplex c.l (pbcFiniteField.{u} c.l c.Qbar E)
            D c.different X₀))) ≅ pbcConstantWeilLine D c X₀ S E b) := by
  sorry

/-- Eta is natural on all rational Weil arrows, including arrows with denominators.
Source: item proof, steps 4--7
(blueprint: lem-wf-constant-twist-coefficient-comparison).
Proof: ordinary right multiplication and the completion unit are natural. Localizing
preserves their naturality squares. The twists keep the underlying arrows unchanged,
so these are precisely the displayed squares on the completed tensor carriers. -/
theorem constantTwistFiniteEta_natural
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) (b : E.valˣ)
    (K L : sfWeilComplex D c.l c.different X₀ (pbcFiniteField.{u} c.l c.Qbar E))
    (f : K ⟶ L) :
    (wfTensor D c X₀ E).map
        (X := (wfWeilCarrier D c X₀ E
          ((constantTwistFiniteComparison D c X₀ S E).obj K),
          wfWeilCarrier D c X₀ E (pbcFiniteConstantWeilLine D c X₀ S E b)))
        (Y := (wfWeilCarrier D c X₀ E
          ((constantTwistFiniteComparison D c X₀ S E).obj L),
          wfWeilCarrier D c X₀ E (pbcFiniteConstantWeilLine D c X₀ S E b)))
        (Prod.mkHom ((constantTwistAmbientInclusion D c X₀ E).map
          (((S.coefficients (D.geometricFiber X₀).left).stage E).rational.functor.map
            f.hom.f)) (𝟙 _)) ≫
      (constantTwistFiniteEta D c X₀ S E b L).hom.hom.f =
    (constantTwistFiniteEta D c X₀ S E b K).hom.hom.f ≫
      (constantTwistAmbientInclusion D c X₀ E).map
        (((S.coefficients (D.geometricFiber X₀).left).stage E).rational.functor.map
          f.hom.f) := by
  sorry

/-- Rescaled constant-object scalar comparison, with the original normalized alpha.
Source: item proof, step 3 (blueprint: lem-wf-constant-twist-coefficient-comparison).
Proof: the original alpha commutes with theta. Coefficient extension carries b to its
image, so the two Weil-square routes acquire the same scalar. Compose the fixed-pair
coefficient comparison with J(alpha). The underlying arrow is prescribed and the
forgetful functor is faithful, proving uniqueness. -/
theorem constantTwistLineScalar_existsUnique
    {E L : Padic.FiniteCoefficientFields c.l c.Qbar} (h : E ≤ L) (b : E.valˣ) :
    ∃! a : (weilScalarExtension D c X₀ h).obj
          (pbcFiniteConstantWeilLine D c X₀ S E b) ≅
        pbcFiniteConstantWeilLine D c X₀ S L
          (Units.map (IntermediateField.inclusion h).toMonoidHom b),
      HEq a.hom.hom.f
        (((constantTwistFiniteScalar D c X₀ S h).hom.app
          (sfFiniteConstantTwist D c X₀ E b
            (constantWeilRationalComplex c.l (pbcFiniteField.{u} c.l c.Qbar E)
              D c.different X₀))).hom.f ≫
          ((S.coefficients (D.geometricFiber X₀).left).stage L).rational.functor.map
            (constantWeilStageScalar D c X₀ h).hom.hom.f) := by
  sorry

/-- The canonical scalar identification of constant lines, fixed by coefficient multiplication.
Source: item proof, step 3 (blueprint: lem-wf-constant-twist-coefficient-comparison). -/
def constantTwistLineScalar
    {E L : Padic.FiniteCoefficientFields c.l c.Qbar} (h : E ≤ L) (b : E.valˣ) :=
  (constantTwistLineScalar_existsUnique D c X₀ S h b).exists.choose

/-- Canonical line identifications commute with the recorded balancing associator.
Source: item proof, step 3 (blueprint: lem-wf-constant-twist-coefficient-comparison).
Proof: the integral constant-object arrows multiply coefficient tensors. Both triple
routes therefore send (a tensor s) tensor t to a tensor st. The prescribed J scalar
maps obey the same cocycle. Rationalization and faithful forgetting give this equality. -/
theorem constantTwistLineScalar_assoc
    {E L N : Padic.FiniteCoefficientFields c.l c.Qbar} (h : E ≤ L) (k : L ≤ N)
    (b : E.valˣ) :
    HEq ((weilScalarExtension D c X₀ k).map
        (constantTwistLineScalar D c X₀ S h b).hom ≫
      (constantTwistLineScalar D c X₀ S k
        (Units.map (IntermediateField.inclusion h).toMonoidHom b)).hom)
      ((weilScalarAssociator D c X₀ h k).hom.app
          (pbcFiniteConstantWeilLine D c X₀ S E b) ≫
        (constantTwistLineScalar D c X₀ S (h.trans k) b).hom) := by
  sorry

/-- Integral extension of the completed tensor-unit identification. The comparison
on the tensor side is uniquely fixed by this square, so eta is compatible with finite
coefficient extension, including its balancing associators.
Source: item proof, steps 5--7
(blueprint: lem-wf-constant-twist-coefficient-comparison).
Proof: finite extension is finite free on the completed coefficient sheaves, so it
preserves completeness. The usual derived scalar/tensor comparison sends
(x tensor a) tensor t to (x tensor t) tensor a. Ordinary right multiplication
commutes with it; the reflector unit gives the same equation after completion.
Conjugate with the normalized J scalar comparison. Every map in the square is
invertible, proving existence and uniqueness. For successive extensions, both
comparisons reduce to multiplication of three coefficients; J's scalar cocycle
and the balancing associators identify the two routes. Localizing yields the
same square for finite eta, since its underlying map is this r and b is carried
to its field image. Thus this also specifies the rational tensor scalar map. -/
theorem constantTwistEta_scalar
    {E L : Padic.FiniteCoefficientFields c.l c.Qbar} (h : E ≤ L) :
    ∃ j : ∀ M : sfIntegralConstructibleCategory c.l
        (pbcFiniteField.{u} c.l c.Qbar E) (D.geometricFiber X₀).left,
      (pbcAmbientScalarExtension c.l c.Qbar (D.geometricFiber X₀).left h).obj
          (constantTwistIntegralCarrier D c X₀ S E M).obj ≅
        (constantTwistIntegralCarrier D c X₀ S L
          ((sfConstructibleIntegralScalarExtension 0 c.l
            (Nat.Prime.ne_zero (Fact.out : c.l.Prime))
            (pbcFiniteField.{u} c.l c.Qbar E) (pbcFiniteField.{u} c.l c.Qbar L)
            (pbcFiniteFieldInclusion c.l c.Qbar h) (D.geometricFiber X₀).left).obj M)).obj,
      (∀ M, HEq (j M).hom
        (((S.coefficients (D.geometricFiber X₀).left).integral_scalar h).hom.app M)) ∧
    ∃! t : ∀ M : sfIntegralConstructibleCategory c.l
        (pbcFiniteField.{u} c.l c.Qbar E) (D.geometricFiber X₀).left,
      (pbcAmbientScalarExtension c.l c.Qbar (D.geometricFiber X₀).left h).obj
          ((wfIntegralTensor (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E) 1
            (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
            (wfUniformizer_generates D c E)).obj
            (constantTwistIntegralCarrier D c X₀ S E M,
              constantTwistIntegralCarrier D c X₀ S E
                (constantWeilIntegralObject c.l (pbcFiniteField.{u} c.l c.Qbar E)
                  D c.different (D.geometricFiber X₀).left))).obj ≅
        ((wfIntegralTensor (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar L) 1
          (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar L)
          (wfUniformizer_generates D c L)).obj
          (constantTwistIntegralCarrier D c X₀ S L
            ((sfConstructibleIntegralScalarExtension 0 c.l
              (Nat.Prime.ne_zero (Fact.out : c.l.Prime))
              (pbcFiniteField.{u} c.l c.Qbar E) (pbcFiniteField.{u} c.l c.Qbar L)
              (pbcFiniteFieldInclusion c.l c.Qbar h) (D.geometricFiber X₀).left).obj M),
            constantTwistIntegralCarrier D c X₀ S L
              (constantWeilIntegralObject c.l (pbcFiniteField.{u} c.l c.Qbar L)
                D c.different (D.geometricFiber X₀).left))).obj,
      ∀ M,
        ((pbcAmbientScalarExtension c.l c.Qbar (D.geometricFiber X₀).left h).map
            (constantTwistCompletedRightUnit D c X₀ S E M).hom.hom ≫
          (j M).hom) =
          (t M).hom ≫
          (constantTwistCompletedRightUnit D c X₀ S L
            ((sfConstructibleIntegralScalarExtension 0 c.l
              (Nat.Prime.ne_zero (Fact.out : c.l.Prime))
              (pbcFiniteField.{u} c.l c.Qbar E) (pbcFiniteField.{u} c.l c.Qbar L)
              (pbcFiniteFieldInclusion c.l c.Qbar h) (D.geometricFiber X₀).left).obj M)).hom.hom
        := by
  sorry

/-- A common-stage stalk functor, using exactly the recorded point pullback and H0.
Source: item proof, step 8 (blueprint: lem-wf-constant-twist-coefficient-comparison). -/
def constantTwistStalkFunctor
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :=
  letI := frobeniusPointPrimeInvertible D c.l c.different
  letI := sfWeilPrimeInvertible D c.l c.different X₀
  sfCommonStageWeilForget D c.l c.different X₀ c.Qbar ⋙
    commonStageDerivedPullback c.l c.Qbar x ⋙ pointQbarFibre D c.l c.different c.Qbar ⋙
      DerivedCategory.coefficientQbarCohomology c.l c.Qbar 0

/-- Common-stage local Frobenius at a finite-extension rational point, retaining the
specified positive return comparison. The index n is the extension degree.
Source: item proof, step 8 (blueprint: lem-wf-constant-twist-coefficient-comparison). -/
def constantTwistExtensionOperator
    (K : sfCommonStageWeilComplex D c.l c.different X₀ c.Qbar)
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints X₀ n hn) :=
  letI := frobeniusPointPrimeInvertible D c.l c.different
  letI := sfWeilPrimeInvertible D c.l c.different X₀
  (DerivedCategory.coefficientQbarCohomology c.l c.Qbar 0).map
    (localQbarPointTransportIterate c.l c.Qbar D c.different
        (localQbarDerivedStalk c.l c.Qbar D c.different X₀ K
          (localExtensionPoint D X₀ n hn x)) (n - 1) ≫
      (pointQbarFibre D c.l c.different c.Qbar).map
        (localQbarReturnComparison c.l c.Qbar D c.different X₀ K
          (localExtensionPoint D X₀ n hn x) (n - 1)
          (localExtensionPoint_return D X₀ n hn x)).hom ≫
      (pointQbarFibre D c.l c.different c.Qbar).map
        ((commonStageDerivedPullback c.l c.Qbar (localExtensionPoint D X₀ n hn x)).map
          (localQbarWeilIterate c.l c.Qbar D c.different X₀ K (n - 1)).hom))

/-- Every Weil isomorphism, hence the transported eta, induces the specified linear
conjugacies at precisely the two domains of local geometric Frobenius.
Source: item proof, step 8 (blueprint: lem-wf-constant-twist-coefficient-comparison).
Proof: point-transport naturality and pullback-composition naturality allow the stalk
map to pass each factor of the local operator. The remaining square is the iterated
Weil square. Apply H0; functors preserve the inverse map, so the square is conjugacy. -/
theorem constantTwistLocalConjugacy
    (K L : sfCommonStageWeilComplex D c.l c.different X₀ c.Qbar) (e : K ≅ L) :
    (∀ (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints X₀ n hn),
      constantTwistExtensionOperator D c X₀ K n hn x ≫
          (constantTwistStalkFunctor D c X₀ (localExtensionPoint D X₀ n hn x)).map e.hom =
        (constantTwistStalkFunctor D c X₀ (localExtensionPoint D X₀ n hn x)).map e.hom ≫
          constantTwistExtensionOperator D c X₀ L n hn x) ∧
    ∀ (y : {y : X₀.left // y ∈ closedPoints X₀.left})
      (i : X₀.left.residueField y.val →+* D.k)
      (hi : i.comp (X₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k),
      localQbarClosedFrobeniusStalk c.l c.Qbar D c.different X₀ K y i hi ≫
          (constantTwistStalkFunctor D c X₀ (localClosedPoint D X₀ y i hi)).map e.hom =
        (constantTwistStalkFunctor D c X₀ (localClosedPoint D X₀ y i hi)).map e.hom ≫
          localQbarClosedFrobeniusStalk c.l c.Qbar D c.different X₀ L y i hi := by
  sorry

/-- The line's actual integral representative is a rank-one locally free module
in degree zero; changing its rational Weil structure does not change that module.
Source: item proof, step 2 (blueprint: lem-wf-constant-twist-coefficient-comparison).
Proof: the section-normalized integral-unit comparison identifies the representative
with the single regular module. The regular module is free on one generator, hence
locally free of rank one. Rationalization retains the representative. This argument
is local and therefore includes disconnected schemes and the empty scheme. -/
theorem constantTwistLine_rankOne
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) (b : E.valˣ) :
    ∃ M : pbcModules (D.geometricFiber X₀).left
        (pbcAdicCompletion (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E)),
      SheafOfModules.IsFiniteLocallyFreeOfRank M 1 ∧
      Nonempty ((pbcFiniteConstantWeilLine D c X₀ S E b).carrier.obj.obj ≅
        (DerivedCategory.singleFunctor _ 0).obj M) := by
  sorry

/-- The separated geometric fibre has the hypotheses of the etale lisse comparison.
Source: item proof, steps 1 and 2
(blueprint: lem-wf-constant-twist-coefficient-comparison).
Proof: separatedness and finite type are stable under base change. Over a field,
a separated scheme has separated structure map. The coefficient prime differs
from the residue characteristic, so it is invertible in every residue field. -/
theorem constantTwistLisseHypotheses :
    (D.geometricFiber X₀).left.IsSeparated ∧
      ∀ x : (D.geometricFiber X₀).left,
        IsUnit (c.l : (D.geometricFiber X₀).left.residueField x) := by
  sorry

/-- The concrete larger-universe coefficient presentation of the small PBC stage.
The lift changes only size, and retains the canonical equivalence with the finite field.
Source: BS 6.8.4 size convention, item proof step 2
(blueprint: lem-wf-constant-twist-coefficient-comparison). -/
def constantTwistLisseBase (E : Padic.FiniteCoefficientFields c.l c.Qbar) :
    AlgebraicGeometry.ProEtale.CompletedLisse.Base.{u} c.l where
  E := ULift.{u + 1} (pbcFiniteField.{u} c.l c.Qbar E)
  field := inferInstance
  algebra := inferInstance
  finiteDimensional := inferInstance
  X := (D.geometricFiber X₀).left
  noetherian := inferInstance
  separated := (constantTwistLisseHypotheses D c X₀).1
  invertible := fun x ↦ ((constantTwistLisseHypotheses D c X₀).2 x).invertible

/-- The coefficient lift relates the completed etale unit to the actual PBC line.
This is an isomorphism of the explicit degree-zero representatives, rather than a
comparison with an unrelated lisse object.
Source: BS 6.8.2, 6.8.4 and item proof step 2
(blueprint: lem-wf-constant-twist-coefficient-comparison).
Proof: the canonical field lift identifies valuation rings and their uniformizer
quotient diagrams. Apply the normalized finite constant-sheaf comparisons and
then the inverse-limit functor. This gives the displayed completed-ring iso.
Restriction of its regular module is the regular module by that ring iso.
Apply the single-complex functor, pass to the derived category, and compose
with the section-normalized integral J comparison. The rescaling does not
alter the carrier, so this is the underlying representative for every b.
All quotient maps fix the constant section one. Hence the Frobenius comparison
is the constant-section comparison, and after rationalization its rescaling
is precisely the theta defining constantTwistEtaleLine. -/
theorem constantTwistLine_etaleRepresentative
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) (b : E.valˣ) :
    ∃ a : AlgebraicGeometry.ProEtale.CompletedLisse.completedRing c.l
          (constantTwistLisseBase D c X₀ E) ≅
        pbcAdicCompletion (D.geometricFiber X₀).left
          (pbcStageDatum.{u} c.l c.Qbar E),
      Nonempty ((pbcFiniteConstantWeilLine D c X₀ S E b).carrier.obj.obj ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((SheafOfModules.restrictScalars ((adicLisseForget _).map a.inv)).obj
            (SheafOfModules.unit ((adicLisseForget _).obj
              (AlgebraicGeometry.ProEtale.CompletedLisse.completedRing c.l
                (constantTwistLisseBase D c X₀ E)))))) := by
  sorry

/-- The normalized completed-lisse comparison takes the coefficient unit to the
constant etale system. This is the actual system/completed-module bridge used for
the connected representation clause, with no replacement lisse category.
Source: item proof, steps 2 and 9
(blueprint: lem-wf-constant-twist-coefficient-comparison).
Proof: the n-th reduction of the regular module is the constant quotient ring of
exponent n+1. The prescribed coefficient projections identify the reduction maps
with the quotient transitions, and the stalks are free of rank one. The reduction
comparison is an equivalence, so the resulting levelwise identifications give the
displayed system isomorphism. Its inverse-limit normalization is the coefficient
ring's limit cone. Thus scalar rationalization and automorphism pullback preserve
these constant-section maps. -/
theorem constantTwistCompletedLisseUnit
    (P : AlgebraicGeometry.ProEtale.CompletedLisse.Base.{u} c.l)
    (C : AlgebraicGeometry.ProEtale.CompletedLisse.Comparison c.l P) :
    ∃ (h : SheafOfModules.isFiniteLocallyFree
        ((adicLisseForget P.X).obj
          (AlgebraicGeometry.ProEtale.CompletedLisse.completedRing c.l P))
        (SheafOfModules.unit ((adicLisseForget P.X).obj
          (AlgebraicGeometry.ProEtale.CompletedLisse.completedRing c.l P))))
      (hfree : AlgebraicGeometry.ProEtale.CompletedLisse.IsFreeSystem c.l P
        (lisseIntegralUnit c.l P.E P.X)),
      Nonempty (C.equivalence.functor.obj ⟨SheafOfModules.unit _, h⟩ ≅
        ⟨lisseIntegralUnit c.l P.E P.X, hfree⟩) := by
  sorry

/-- On the connected domain the constant etale presentation has dimension one,
trivial geometric monodromy, and exactly the character b to the degree. The arbitrary
degree datum is the interface supplied by the recorded Weil group and chosen lift.
Source: item proof, steps 9--10
(blueprint: lem-wf-constant-twist-coefficient-comparison).
Proof: every finite-fibre path fixes constant sections by naturality from the terminal
cover. This passes to inverse limits and scalar extension, so geometric monodromy is
the identity and the normalized degree-one operator is b. The recorded fundamental
representation extends these maps by rho(h s^n)=rho(h)T^n. Therefore rho(g)=b^deg(g),
including negative degrees since b is a unit. The constant fibre is the coefficient
field and has dimension one. Full faithfulness identifies it with the completed line
via the preceding unit comparison and the J integral-unit identification; the Weil
square holds on fibres, hence in the sheaf category. -/
theorem constantTwistLine_representation
    (Y : Scheme.{u}) [ConnectedSpace Y] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (c.l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[c.l] Q] [IsAlgClosure ℚ_[c.l] Q]
    (h : Y ≅ Y) (b : Qˣ) (κ : Type u) [Field κ] [IsAlgClosed κ]
    (x : Spec (.of κ) ⟶ Y) (G : Type v) [Group G] (d : Monodromy.DegreeDatum G)
    (W : EtaleWeilDegreeData h x G d) :
    Module.finrank Q (lisseAlgebraicFiber c.l Y Q x
      (constantTwistEtaleLine c.l Y Q h b).carrier) = 1 ∧
    (∀ g : Aut (FiniteEtale.fiber x), etaleGeometricRep c.l Q
      (constantTwistEtaleLine c.l Y Q h b).carrier x g = LinearMap.id) ∧
    ∀ g : G, etaleFundamentalRep c.l Q h x d W
      (constantTwistEtaleLine c.l Y Q h b) g =
        ((b ^ (d.deg g).toAdd : Qˣ) : Q) • LinearMap.id := by
  sorry

/-- The coefficient lift preserves the algebraic closure, with the existing lifted algebra.
Source: item coefficient-size transport; Mathlib IsAlgClosed.of_ringEquiv and
Algebra.IsAlgebraic.of_injective
(blueprint: lem-wf-constant-twist-coefficient-comparison).
Proof: transport splitting of every polynomial through the canonical ULift ring
isomorphism, mapping its roots back by the inverse. Algebraicity pulls back through
the injective ULift algebra homomorphism. These are exactly the two class fields. -/
@[instance]
theorem constantTwistLiftedClosure :
    IsAlgClosure ℚ_[c.l] (ULift.{u + 1} c.Qbar) := by
  sorry

/-- The constant etale Weil presentation realizes to the specified PBC line.
The conclusion supplies the realization, rather than assuming an arbitrary comparison.
Together with its fully faithful fibre construction this is the representation of
that PBC line, with exactly the normalized scalar b and the chosen degree-one path.
Source: BS 6.8.4, Weil II (1.1.10), item proof steps 9--10
(blueprint: lem-wf-constant-twist-coefficient-comparison).
Proof: take the reduction/inverse-limit realization and its rational localization.
The canonical coefficient lift gives its finite-stage integral comparison with J;
its quotient components fix constant sections. The pullback comparison is the same
constant-section map. Hence it lifts to Weil pairs and takes the normalized etale
theta to b times the coefficient theta. The rational realization is fully faithful,
and its scalar and pullback comparisons descend to common stages. Faithfulness
reflects Weil squares, proving full faithfulness on pairs. Evaluating at the
constant unit gives the displayed isomorphisms. Their underlying maps are the
completed coefficient maps in constantTwistLine_etaleRepresentative. -/
theorem constantTwistLine_etaleWeilRealization
    [ConnectedSpace (D.geometricFiber X₀).left] :
    ∃ R : (letI : (D.geometricFiber X₀).left.IsSeparated :=
          (constantTwistLisseHypotheses D c X₀).1
        letI : ∀ x : (D.geometricFiber X₀).left,
            Invertible (c.l : (D.geometricFiber X₀).left.residueField x) :=
          fun x ↦ ((constantTwistLisseHypotheses D c X₀).2 x).invertible
        EtaleLisseWeilSheaf c.l (ULift.{u + 1} c.Qbar)
          (D.geometricFrobenius X₀) ⥤ WeilDQbar D c X₀),
      Nonempty R.FullyFaithful ∧
      ∀ (E : Padic.FiniteCoefficientFields c.l c.Qbar) (b : E.valˣ),
        Nonempty (R.obj
          (letI : (D.geometricFiber X₀).left.IsSeparated :=
             (constantTwistLisseHypotheses D c X₀).1
           letI : ∀ x : (D.geometricFiber X₀).left,
               Invertible (c.l : (D.geometricFiber X₀).left.residueField x) :=
             fun x ↦ ((constantTwistLisseHypotheses D c X₀).2 x).invertible
           constantTwistEtaleLine c.l (D.geometricFiber X₀).left
             (ULift.{u + 1} c.Qbar) (D.geometricFrobenius X₀)
             (Units.map (ULift.ringEquiv.symm.toMonoidHom)
               (Units.map E.val.subtype.toMonoidHom b))) ≅
          pbcConstantWeilLine D c X₀ S E b) := by
  sorry

/-- Descent to a common finite coefficient stage keeps the coefficient scalar b,
its inverse, both inverse Weil identities and the constructible heart.
The ambient eta in the conclusion identifies the actual completed PBC tensor.
Source: item proof, steps 1 and 7
(blueprint: lem-wf-constant-twist-coefficient-comparison).
Proof: represent the carrier, theta, its inverse and b at finite stages, and pass to
a compositum until the inverse identities hold. The original heart-carrier object
represents both standard classes, and a further enlargement makes these identifications
hold. Apply finite eta. The scalar and associator equations show that it descends
independently of the enlargement. Applying J inverse yields precisely the stated
scalar twist, and the stalk conjugacy theorem applies to the resulting Weil iso. -/
theorem constantTwistCommonDescent
    (J : ConstantTwistWeilComparison D c X₀ S) (b : c.Qbarˣ)
    (F : sfCommonStageWeilSheaf D c.l c.different X₀ c.Qbar) :
    ∃ (E : Padic.FiniteCoefficientFields c.l c.Qbar) (bE : E.valˣ)
      (K : sfWeilSheaf D c.l c.different X₀ (pbcFiniteField.{u} c.l c.Qbar E)),
      Units.map E.val.subtype.toMonoidHom bE = b ∧
      Nonempty (sfWeilStageObject D c.l c.different X₀ c.Qbar E K.obj ≅ F.obj) ∧
      Nonempty (sfWeilStageObject D c.l c.different X₀ c.Qbar E
        (sfFiniteConstantTwist D c X₀ E bE K.obj) ≅
          sfCommonConstantTwist D c X₀ S b F.obj) ∧
      sfCommonStageHeartProperty c.l (D.geometricFiber X₀).left c.Qbar
        (sfCommonConstantTwist D c X₀ S b F.obj).carrier ∧
      Nonempty (pbcFiniteConstantWeilTensor D c X₀ S E bE
          ((constantTwistFiniteComparison D c X₀ S E).obj K.obj) ≅
        constantTwistAmbientPair D c X₀ E
          ((constantTwistFiniteComparison D c X₀ S E).obj
            (sfFiniteConstantTwist D c X₀ E bE K.obj))) ∧
      Nonempty (((weilScalarSystem D c X₀).ι E).obj
          ((constantTwistFiniteComparison D c X₀ S E).obj
            (sfFiniteConstantTwist D c X₀ E bE K.obj)) ≅
        J.common.functor.obj (sfCommonConstantTwist D c X₀ S b F.obj)) := by
  sorry

/-- Transport of the actual tensor target by J inverse is scalar rescaling of theta.
The finite tensor identifies with this target through the unique normalized eta.
Source: item consequence of eta
(blueprint: lem-wf-constant-twist-coefficient-comparison).
Proof: use common descent to represent F and b at E. Finite eta identifies the actual
ambient completed tensor with J of the scalar twist. Include its constructible target
in the common-stage Weil category. Apply J inverse, then the inverse of J's unit
isomorphism. This gives the displayed iso. It uses no preserved integral lattice for
theta, only a finite rational representative with both inverse identities. -/
theorem constantTwistTensor_inverse
    (J : ConstantTwistWeilComparison D c X₀ S) (b : c.Qbarˣ)
    (F : sfCommonStageWeilSheaf D c.l c.different X₀ c.Qbar) :
    ∃ (E : Padic.FiniteCoefficientFields c.l c.Qbar) (bE : E.valˣ)
      (K : sfWeilSheaf D c.l c.different X₀ (pbcFiniteField.{u} c.l c.Qbar E)),
      Units.map E.val.subtype.toMonoidHom bE = b ∧
      Nonempty (sfWeilStageObject D c.l c.different X₀ c.Qbar E K.obj ≅ F.obj) ∧
      Nonempty (J.common.inverse.obj
        (((weilScalarSystem D c X₀).ι E).obj
          ((constantTwistFiniteComparison D c X₀ S E).obj
            (sfFiniteConstantTwist D c X₀ E bE K.obj))) ≅
        sfCommonConstantTwist D c X₀ S b F.obj) := by
  sorry

end WeilConjectures
