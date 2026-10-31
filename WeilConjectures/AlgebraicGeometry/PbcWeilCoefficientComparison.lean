/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalCoefficientCategoryComparison
public import WeilConjectures.AlgebraicGeometry.PbcWeilCategory
public import Mathlib.CategoryTheory.Linear.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Coefficient comparison with the recorded PBC Weil categories

Source: blueprint, trace definition, coefficient comparison paragraph
(blueprint: def-wf-weil-coefficient-comparison-interface).

The published comparison uses completed pullback; `WeilD` uses its canonically
identified exact transport. The normalization below retains the completion unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]


/-- Finite dimension of the specified finite-type geometric fibre.
Source: coefficient comparison, finite-dimensional base hypotheses
(blueprint: def-wf-weil-coefficient-comparison-interface).
Proof: base change preserves finite type. A finite-type scheme over a field is
covered by finitely many affine schemes whose coordinate algebras are finitely
generated over that field; their Krull dimensions are finite. The maximum of
these finitely many bounds bounds the dimension of the geometric fibre. -/
theorem constantTwistDimension_bound :
    ∃ n : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤ n := by
  sorry

/-- The finite-dimensional instance carries no extra geometric hypothesis.
Source: coefficient comparison, finite-dimensional base hypotheses
(blueprint: def-wf-weil-coefficient-comparison-interface). -/
instance constantTwistDimension :
    Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤ n) :=
  ⟨constantTwistDimension_bound D X₀⟩

/-- Prime invertibility is inherited from the distinct coefficient and residue primes.
Source: coefficient comparison, final clause
(blueprint: def-wf-weil-coefficient-comparison-interface). -/
instance constantTwistPrimeUnit :
    Fact (∀ x : (D.geometricFiber X₀).left,
      IsUnit (c.l : (D.geometricFiber X₀).left.presheaf.stalk x)) :=
  ⟨(weilGeometricFiber_coefficientHypotheses D c X₀).2.2⟩

/-- Completed pullback and exact coefficient transport are canonically identified,
with the comparison fixed by the ordinary-pullback unit.
Source: coefficient comparison, scheme-isomorphism clause
(blueprint: def-wf-weil-coefficient-comparison-interface).
Proof: both functors compute inverse image under the same site equivalence and
constant-section coefficient map. The completion unit is invertible on complete
objects. Compose its inverse with the ordinary derived transport comparison.
The unit equation determines every component and hence proves uniqueness. -/
theorem constantTwistIntegralTransport_existsUnique
    [IsNoetherian (D.geometricFiber X₀).left]
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) :
    ∃! a : fdPbcIntegralPull c.l c.Qbar (D.geometricFrobenius X₀).hom E ≅
        pbcIsoIntegralPullback (hf := (D.geometricFrobenius X₀).isIso_hom)
          (D.geometricFrobenius X₀).hom
          (pbcStageDatum.{u} c.l c.Qbar E),
      ∀ K : pbcIntegralStage c.l c.Qbar (D.geometricFiber X₀).left E,
        (pbcActualCompletedPullUnit (D.geometricFrobenius X₀).hom
          (pbcStageDatum.{u} c.l c.Qbar E)).app K.obj ≫ (a.hom.app K).hom =
        (pbcIsoOrdinaryDerivedComparison (hf := (D.geometricFrobenius X₀).isIso_hom)
          (D.geometricFrobenius X₀).hom
          (pbcStageDatum.{u} c.l c.Qbar E)).hom.app K.obj := by
  sorry

/-- The unique unit-normalized integral comparison.
Source: coefficient comparison, scheme-isomorphism clause
(blueprint: def-wf-weil-coefficient-comparison-interface). -/
def constantTwistIntegralTransport
    [IsNoetherian (D.geometricFiber X₀).left]
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) :=
  (constantTwistIntegralTransport_existsUnique D c X₀ E).exists.choose

/-- Rationalization retains exactly the preceding integral comparison.
Source: coefficient comparison, raw-rationalization clause
(blueprint: def-wf-weil-coefficient-comparison-interface).
Proof: tensor each integral component with one. Naturality on integral arrows
extends to fractions, and every rational arrow is a sum of such fractions.
The objects are unchanged, so the normalization proves uniqueness. -/
theorem constantTwistRationalTransport_existsUnique
    [IsNoetherian (D.geometricFiber X₀).left]
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) :
    ∃! a : (pbcQbarPullFamily c.l c.Qbar (D.geometricFrobenius X₀).hom).Φ E ≅
        weilFrobeniusPullback D c X₀ E,
      ∀ K : pbcIntegralStage c.l c.Qbar (D.geometricFiber X₀).left E,
        HEq (a.hom.app ((pbcStageLocalization c.l c.Qbar
          (D.geometricFiber X₀).left E).obj K))
          ((pbcStageLocalization c.l c.Qbar (D.geometricFiber X₀).left E).map
            ((constantTwistIntegralTransport D c X₀ E).hom.app K)) := by
  sorry

/-- The canonical rational identification, rather than an arbitrary pair equivalence.
Source: coefficient comparison, raw-rationalization clause
(blueprint: def-wf-weil-coefficient-comparison-interface). -/
def constantTwistRationalTransport
    [IsNoetherian (D.geometricFiber X₀).left]
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) :=
  (constantTwistRationalTransport_existsUnique D c X₀ E).exists.choose

variable [IsNoetherian (D.geometricFiber X₀).left]
  (S : FdCoefficientComparisonSystem.{u} c.l c.Qbar)

/-- The supplied comparison, composed with the unit-normalized transport to WeilD.
Source: coefficient comparison, Frobenius clause
(blueprint: def-wf-weil-coefficient-comparison-interface). -/
def constantTwistFinitePullbackComparison (E : Padic.FiniteCoefficientFields c.l c.Qbar) :
    ((S.coefficients (D.geometricFiber X₀).left).stage E).rational.functor ⋙
        weilFrobeniusPullback D c X₀ E ≅
      sfWeilFrobeniusPullback D c.l c.different X₀ (pbcFiniteField.{u} c.l c.Qbar E) ⋙
        ((S.coefficients (D.geometricFiber X₀).left).stage E).rational.functor :=
  Functor.isoWhiskerLeft _ (constantTwistRationalTransport D c X₀ E).symm ≪≫
    ((S.pullback (D.geometricFrobenius X₀)).finite E).rational

/-- The finite-stage Weil-pair functor with its actual coefficient and Frobenius maps.
Source: coefficient comparison, Frobenius clause
(blueprint: def-wf-weil-coefficient-comparison-interface). -/
def constantTwistFiniteComparison (E : Padic.FiniteCoefficientFields c.l c.Qbar) :
    sfWeilComplex D c.l c.different X₀ (pbcFiniteField.{u} c.l c.Qbar E) ⥤
      WeilD D c X₀ E :=
  IsoAlgebra.mapOfNatIso (constantTwistFinitePullbackComparison D c X₀ S E)

/-- The finite functor is an equivalence. This is only the existing coefficient
equivalence applied to fixed pairs, with the canonical completion transport.
Source: coefficient comparison, Frobenius clause
(blueprint: def-wf-weil-coefficient-comparison-interface).
Proof: full faithfulness lifts each commuting square uniquely. Essential
surjectivity lifts a carrier and both inverse Frobenius maps; faithfulness checks
the inverse identities. The normalized transport does not change this argument. -/
theorem constantTwistFiniteComparison_isEquivalence
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) :
    (constantTwistFiniteComparison D c X₀ S E).IsEquivalence := by
  sorry

omit [IsSeparated X₀.hom] [AlgebraicGeometry.IsNoetherian
  (D.geometricFiber X₀).left] in
/-- The stage inclusion is determined on every underlying arrow, including the
self-transition conventions. Source: coefficient comparison, common-stage clause
(blueprint: def-wf-weil-coefficient-comparison-interface).
Proof: use the recorded stage pullback identification and map theta. Naturality of
that identification gives the Weil square. The underlying inclusion preserves
identities and composition; faithful forgetting gives the same laws on pairs.
Its object and arrow formulas determine the functor uniquely. -/
theorem constantTwistSfInclusion_existsUnique
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) :
    ∃! F : sfWeilComplex D c.l c.different X₀ (pbcFiniteField.{u} c.l c.Qbar E) ⥤
        sfCommonStageWeilComplex D c.l c.different X₀ c.Qbar,
      (∀ K, F.obj K = sfWeilStageObject D c.l c.different X₀ c.Qbar E K) ∧
      ∀ (K L : sfWeilComplex D c.l c.different X₀
        (pbcFiniteField.{u} c.l c.Qbar E)) (f : K ⟶ L)
        (K' L' : GeneralAlgebraicallyClosedCoefficients.Stage c.l c.Qbar
          (D.geometricFiber X₀).left E) (f' : K' ⟶ L'),
        HEq K.carrier K' → HEq L.carrier L' → HEq f.hom.f f' →
        HEq (F.map f).hom.f
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := c.l) (Ω := c.Qbar) (Y := (D.geometricFiber X₀).left) E).map f') := by
  sorry

/-- The specified finite-stage inclusion on Weil pairs.
Source: coefficient comparison, common-stage clause
(blueprint: def-wf-weil-coefficient-comparison-interface). -/
def constantTwistSfInclusion (E : Padic.FiniteCoefficientFields c.l c.Qbar) :=
  (constantTwistSfInclusion_existsUnique D c X₀ E).exists.choose

/-- Coefficient extension on SF Weil pairs, with the recorded pullback/scalar comparison.
Source: coefficient comparison, scalar clause
(blueprint: def-wf-weil-coefficient-comparison-interface). -/
def constantTwistSfScalar {E L : Padic.FiniteCoefficientFields c.l c.Qbar} (h : E ≤ L) :=
  IsoAlgebra.mapOfNatIso
    ((@rationalPullbackScalarComparison c.l _ (pbcFiniteField.{u} c.l c.Qbar E) _ _ _
      (pbcFiniteField.{u} c.l c.Qbar L) _ _ _ (pbcFiniteFieldInclusion c.l c.Qbar h)
      _ _ (D.geometricFrobenius X₀).hom
      (sfWeilPrimeInvertible D c.l c.different X₀)
      (sfWeilPrimeInvertible D c.l c.different X₀)).symm)

/-- The coefficient comparison on fixed pairs retains the normalized scalar map.
Source: coefficient comparison, scalar/Frobenius mixed square
(blueprint: def-wf-weil-coefficient-comparison-interface).
Proof: the mixed pullback/scalar square makes the coefficient scalar comparison
Frobenius-equivariant. Its inverse is equivariant too. Lift both to fixed pairs.
Naturality follows after faithful forgetting, and the prescribed underlying
comparison determines the natural isomorphism uniquely. -/
theorem constantTwistFiniteScalar_existsUnique
    {E L : Padic.FiniteCoefficientFields c.l c.Qbar} (h : E ≤ L) :
    ∃! e : constantTwistFiniteComparison D c X₀ S E ⋙ weilScalarExtension D c X₀ h ≅
        constantTwistSfScalar D c X₀ h ⋙ constantTwistFiniteComparison D c X₀ S L,
      ∀ (K : sfWeilComplex D c.l c.different X₀ (pbcFiniteField.{u} c.l c.Qbar E))
        (K' : GeneralAlgebraicallyClosedCoefficients.Stage c.l c.Qbar
          (D.geometricFiber X₀).left E),
        HEq K.carrier K' →
        HEq (e.hom.app K).hom.f
          (((S.coefficients (D.geometricFiber X₀).left).family.β h).hom.app K') := by
  sorry

/-- The unique scalar comparison on the actual fixed-pair categories.
Source: coefficient comparison, scalar clause
(blueprint: def-wf-weil-coefficient-comparison-interface). -/
def constantTwistFiniteScalar
    {E L : Padic.FiniteCoefficientFields c.l c.Qbar} (h : E ≤ L) :=
  (constantTwistFiniteScalar_existsUnique D c X₀ S h).exists.choose

omit [IsSeparated X₀.hom] [AlgebraicGeometry.IsNoetherian
  (D.geometricFiber X₀).left] in
/-- The stage transition identification is the recorded coefficient-pair transition.
Source: coefficient comparison, common-stage clause
(blueprint: def-wf-weil-coefficient-comparison-interface).
Proof: include the scalar/pullback comparison and compare to the original pair.
The prescribed common-stage arrow is the same stage transition on carriers.
The scalar associator cocycle gives its Weil square. Faithful forgetting gives
naturality, inverse identities and uniqueness with this underlying normalization. -/
theorem constantTwistSfTransition_existsUnique
    {E L : Padic.FiniteCoefficientFields c.l c.Qbar} (h : E ≤ L) :
    ∃! e : constantTwistSfScalar D c X₀ h ⋙ constantTwistSfInclusion D c X₀ L ≅
        constantTwistSfInclusion D c X₀ E,
      ∀ (K : sfWeilComplex D c.l c.different X₀ (pbcFiniteField.{u} c.l c.Qbar E))
        (K' : GeneralAlgebraicallyClosedCoefficients.Stage c.l c.Qbar
          (D.geometricFiber X₀).left E), HEq K.carrier K' →
        HEq (e.hom.app K).hom.f
          (((GeneralAlgebraicallyClosedCoefficients.stageSystem c.l c.Qbar
            (D.geometricFiber X₀).left).transIso h).hom.app K') := by
  sorry

/-- The normalized common-stage transition on Weil pairs.
Source: coefficient comparison, common-stage clause
(blueprint: def-wf-weil-coefficient-comparison-interface). -/
def constantTwistSfTransition
    {E L : Padic.FiniteCoefficientFields c.l c.Qbar} (h : E ≤ L) :=
  (constantTwistSfTransition_existsUnique D c X₀ h).exists.choose

/-- Common-stage comparison into the colimit of the actual finite Weil categories.
The stage_transition square pins the inclusion comparisons to the normalized finite
scalar map, the SF transition and the actual PBC stage-system transition. Thus their
choices cannot vary independently at different stages.
Source: coefficient comparison, common-stage and Frobenius clauses
(blueprint: def-wf-weil-coefficient-comparison-interface). -/
structure ConstantTwistWeilComparison where
  common : sfCommonStageWeilComplex D c.l c.different X₀ c.Qbar ≌ WeilDQbar D c X₀
  stage : ∀ E : Padic.FiniteCoefficientFields c.l c.Qbar,
    constantTwistSfInclusion D c X₀ E ⋙ common.functor ≅
      constantTwistFiniteComparison D c X₀ S E ⋙ (weilScalarSystem D c X₀).ι E
  /-- The two routes from an enlarged SF stage to the original PBC stage agree. -/
  stage_transition : ∀ {E L : Padic.FiniteCoefficientFields c.l c.Qbar} (h : E ≤ L)
    (K : sfWeilComplex D c.l c.different X₀ (pbcFiniteField.{u} c.l c.Qbar E)),
    common.functor.map ((constantTwistSfTransition D c X₀ h).hom.app K) ≫
        (stage E).hom.app K =
      (stage L).hom.app ((constantTwistSfScalar D c X₀ h).obj K) ≫
        ((weilScalarSystem D c X₀).ι L).map
          ((constantTwistFiniteScalar D c X₀ S h).inv.app K) ≫
        ((weilScalarSystem D c X₀).transIso h).hom.app
          ((constantTwistFiniteComparison D c X₀ S E).obj K)

/-- The canonical coefficient comparison also supplies this colimit presentation.
Source: coefficient comparison, common-stage and Frobenius clauses
(blueprint: def-wf-weil-coefficient-comparison-interface).
Proof: represent a carrier, its Frobenius and inverse at one finite stage, enlarging
until both inverse identities hold. The finite comparison above gives its image.
Represent every morphism at a common stage and conjugate by the same scalar
comparison maps. The mixed square and scalar associator cocycle show independence
of representatives, preserve composition, and give the displayed inclusion maps.
The same representative formula gives stage_transition: both routes include the
same normalized finite scalar comparison at L. This also applies when E=L.
Apply the inverse finite equivalences to obtain a quasi-inverse; the same common-stage
calculus gives unit and counit. No stable integral Frobenius lattice is required. -/
theorem constantTwistWeilComparison_exists :
    Nonempty (ConstantTwistWeilComparison D c X₀ S) := by
  sorry

end WeilConjectures
