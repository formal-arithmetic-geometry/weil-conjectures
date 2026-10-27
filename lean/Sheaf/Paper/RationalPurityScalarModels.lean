/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.Paper.RationalPurityCoefficientModels
public import Sheaf.Paper.IntegralTwistDerivedScalarCanonical
public import Sheaf.Paper.PbcCoefficientTwists
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.IntegralCompactSupportUniformRestriction
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
import all Sheaf.Paper.IntegralCompactSupportUniformRestriction
import all Sheaf.Paper.PbcScalarExtension
import all Sheaf.Paper.PbcFiniteRawScalarComparison
import Sheaf.Paper.RationalPurityCompactLattices
import Sheaf.Paper.RationalPurityCompactScalarInvertible

/-! # Scalar models for the rational PBC purity presentation

Source: main-20261015, sec-smooth-purity/sk-lem-sp-field-extension,
prop-pur-rational-purity-transitivity-summands, proof Steps 1--7.
(blueprint: prop-pur-rational-purity-transitivity-summands).

The functors below have the actual PBC integral and rational categories as their
source and target. Twisted pullback is completed pullback followed by the published
Tate tensor and the shift [2d]. Compact support is Rp_* j_! at a compactification,
with the published completed coefficient inverse-image identifications. Exceptional
inverse image is specified by its adjunction to that particular compact support.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option linter.all false
set_option linter.unusedVariables false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open WeilConjectures
open scoped TensorProduct

attribute [local instance high] Algebra.toModule ScalarLocalization.category
attribute [local irreducible] ScalarLocalization.composition ScalarLocalization.transportHom
  AlgebraicGeometry.Scheme.pbcRationalScalarHom

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f) (d : ℕ)
    [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

attribute [local irreducible] pbcPurityTateModel pbcPurityDerivedScalarModel
  purCoefficientModel integralSheafTwist completedDerivedScalarExtension pbcTateAmbient
  purScalarModel integralTwistOrdinaryBeta pbcPurityTateScalarModel
  pbcPurityTateScalarComponent pbcActualCompletedPull

/-- The two actual ambient functors preserve lattices and their scalar action.
Source: proof Steps 1--2 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: pbcPurityPull_mem, Tate tensor preservation and shift preservation give the
first assertion. For compact support use exact extension by zero followed by
proper direct image and integral-stratified-perfect-characterization. Both preserve
the uniform reduction interval and compatible etale origins. On chain maps both
functors are additive and commute with the canonical constant scalar action;
these equations descend through the derived localization. -/
theorem pbcPurityAmbientProperties [QuasiCompact f] :
    (∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E),
      PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
        ((pbcPurityTwistedAmbient l E f d).obj K.obj)) ∧
    (∀ K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E),
      PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)
        ((pbcPurityCompactAmbient l E c).obj K.obj)) ∧
    (pbcPurityTwistedAmbient l E f d).Additive ∧
    (pbcPurityTwistedAmbient l E f d).Linear (PbcIntegralRing l E) ∧
    (pbcPurityCompactAmbient l E c).Additive ∧
    (pbcPurityCompactAmbient l E c).Linear (PbcIntegralRing l E) := by
  have hlin := completedModulePullLinear c.i (pbcIntegralDatum l E)
  have hpush := completedModulePullLinear c.g (pbcIntegralDatum l E)
  have hj : (proEtaleRingOpenExtension c.i
      (pbcAdicCompletion c.Z (pbcIntegralDatum l E))
      (pbcAdicCompletion X (pbcIntegralDatum l E))
      (cbcCompletedCoefficientIso c.i (pbcIntegralDatum l E))).Linear
        (PbcIntegralRing l E) :=
    (Adjunction.ofIsRightAdjoint (proEtaleRingModulePullback c.i _ _ _)).left_adjoint_linear
  have hp : (proEtaleRingDerivedDirectImage c.g
      (pbcAdicCompletion Y (pbcIntegralDatum l E))
      (pbcAdicCompletion c.Z (pbcIntegralDatum l E))
      (cbcCompletedCoefficientIso c.g (pbcIntegralDatum l E))).Linear
        (PbcIntegralRing l E) :=
    (proEtaleRingDerivedAdjunction c.g _ _ _).right_adjoint_linear
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K
    let P : ObjectProperty (PbcCompletedDerived X (pbcIntegralDatum l E)) :=
      PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
    have := (pbcIntegralUniformComplete_isTriangulated l E X dX.out iX.out).2
    exact P.le_shift (2 * (d : ℤ)) _
      (pbcTateAmbient_mem l X E dX.out (d : ℤ)
        ⟨_, pbcPurityPull_mem l E f K⟩)
  · intro K
    exact pbcPurityCompact_lattices l E f c K
  · unfold pbcPurityTwistedAmbient
    infer_instance
  · unfold pbcPurityTwistedAmbient
    infer_instance
  · unfold pbcPurityCompactAmbient PurCompactSupport.image
      PurCompactSupport.openExtension pbcPurityCoefficients
    infer_instance
  · unfold pbcPurityCompactAmbient PurCompactSupport.image
      PurCompactSupport.openExtension pbcPurityCoefficients
    infer_instance

/-- Lf^*(-)(d)[2d] on the actual raw PBC rational category.
Source: proof Step 2 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityTwisted [QuasiCompact f] :
    PbcRationalDerivedCategory l E Y dY.out iY.out ⥤
      PbcRationalDerivedCategory l E X dX.out iX.out :=
  letI := (pbcPurityAmbientProperties l E f c d).2.2.1
  letI := (pbcPurityAmbientProperties l E f c d).2.2.2.1
  pbcConditionalRational (pbcIntegralDatum l E) (pbcPurityTwistedAmbient l E f d)
    (pbcPurityAmbientProperties l E f c d).1 (pbcUniformizer l E)

/-- Rp_* j_! on the same raw PBC rational categories.
Source: proof Step 2 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityCompact [QuasiCompact f] :
    PbcRationalDerivedCategory l E X dX.out iX.out ⥤
      PbcRationalDerivedCategory l E Y dY.out iY.out :=
  letI := (pbcPurityAmbientProperties l E f c d).2.2.2.2.1
  letI := (pbcPurityAmbientProperties l E f c d).2.2.2.2.2
  pbcConditionalRational (pbcIntegralDatum l E) (pbcPurityCompactAmbient l E c)
    (pbcPurityAmbientProperties l E f c d).2.1 (pbcUniformizer l E)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F)

/-- The published completed coefficient inclusion commutes with pullback.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: compose with each finite projection. Both paths restrict the same locally
constant function and apply the same residue-ring inclusion. Limit projections
are jointly monic, giving the equality, including ramified extensions. -/
theorem pbcPurityCoefficientChange_square {U V : Scheme.{u}} (g : U ⟶ V) :
    ((pbcPurityCoefficients l E).pull g).hom ≫ pbcScalarCoefficientMap l E F i U =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (pbcScalarCoefficientMap l E F i V) ≫ ((pbcPurityCoefficients l F).pull g).hom := by
  change (cbcCompletedCoefficientIso g (pbcIntegralDatum l E)).hom ≫ _ =
    _ ≫ (cbcCompletedCoefficientIso g (pbcIntegralDatum l F)).hom
  rw [coefficientIso_eq, coefficientIso_eq]
  rw [← cbcDatumCoefficient_eq, ← cbcDatumCoefficient_eq]
  let dE := pbcIntegralDatum l E
  let dF := pbcIntegralDatum l F
  let c (T : Scheme.{u}) := pbcScalarCoefficientMap l E F i T
  let L := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  have hc (T : Scheme.{u}) (n : ℕ) :
      c T ≫ pbcAdicProjection T dF n = pbcAdicProjection T dE n ≫
        AdicCoefficients.coefficientMap T (pbcScalarQuotientMap l E F i n) :=
    (pbcScalarCoefficientMap_exists l E F i T).exists.choose_spec n
  symm
  apply limit.hom_ext
  intro n
  change (L.map (c V) ≫ completedCoefficientMap g dF) ≫
      pbcAdicProjection U dF n.unop =
    (completedCoefficientMap g dE ≫ c U) ≫ pbcAdicProjection U dF n.unop
  simp only [Category.assoc, hc]
  rw [scalarCompletedCoefficientMap_projection]
  erw [← Category.assoc (completedCoefficientMap g dE),
    scalarCompletedCoefficientMap_projection]
  erw [← L.map_comp_assoc, hc, L.map_comp, Category.assoc]
  exact (congrArg (fun k ↦ L.map (pbcAdicProjection V dE n.unop) ≫ k)
    (scalarFiniteCoefficientMap_naturality g dE dF n.unop
      (pbcScalarQuotientMap l E F i n.unop))).trans (Category.assoc _ _ _).symm

attribute [local irreducible] pbcScalarCoefficientMap

/-- The actual coefficient change, with no comparison map chosen independently.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityCoefficientChange :
    PurCompactSupport.Change (pbcPurityCoefficients l E) (pbcPurityCoefficients l F) where
  map W := pbcScalarCoefficientMap l E F i W
  square g := pbcPurityCoefficientChange_square l E F i g

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f) (d : ℕ)
    [QuasiCompact f] [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- The actual pullback/tensor/twist/shift coefficient comparison at a lattice.
Its three factors are shift/scalar interchange, the pure-tensor Tate comparison,
and the inverse of the published completed-pullback scalar comparison.
Source: proof Step 3, a (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityTwistedScalarComponent
    (K : PbcRationalDerivedCategory l E Y dY.out iY.out) :
    (pbcRationalScalarExtension l E F i X dX.out iX.out).obj
        ((pbcPurityTwisted l E f c d).obj K) ≅
      (pbcPurityTwisted l F f c d).obj
        ((pbcRationalScalarExtension l E F i Y dY.out iY.out).obj K) :=
  letI : (pbcEmbeddingAmbientTensor l E F i X).CommShift ℤ :=
    PurCompactSupport.scalarCommShift (pbcScalarCoefficientMap l E F i X)
  (pbcRationalization X (pbcIntegralDatum l F) (pbcUniformizer l F)).mapIso
    (ObjectProperty.isoMk (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l F))
      (((pbcEmbeddingAmbientTensor l E F i X).commShiftIso (2 * (d : ℤ))).app
          ((pbcTateAmbient l X E (d : ℤ)).obj
            ((pbcActualCompletedPull f (pbcIntegralDatum l E)).obj K.obj.obj)) ≪≫
        (shiftFunctor _ (2 * (d : ℤ))).mapIso
          (pbcPurityTateScalarComponent l E F i X (d : ℤ)
            ⟨(pbcActualCompletedPull f (pbcIntegralDatum l E)).obj K.obj.obj,
              pbcPurityPull_mem l E f K.obj⟩) ≪≫
        (shiftFunctor _ (2 * (d : ℤ))).mapIso
          ((pbcTateAmbient l X F (d : ℤ)).mapIso
            (((pbcScalarCompletedPullIso l E F i f).app K.obj.obj).symm))))

private theorem purityTransport_integral
    {R : Type*} [CommRing R] {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (p : R) (H : C ⥤ D) [H.Additive] [H.Linear R] {K L : C} (v : K ⟶ L) :
    (ScalarLocalization.transport R p H).map
        ((ScalarLocalization.localization R C p).map v) =
      (ScalarLocalization.localization R D p).map (H.map v) := by
  change ScalarLocalization.transportHom R p H K L
    ((1 : Localization.Away p) ⊗ₜ[R] v) = (1 : Localization.Away p) ⊗ₜ[R] H.map v
  simp only [ScalarLocalization.transportHom, LinearMap.baseChange_tmul,
    Functor.mapLinearMap_apply]
  rfl

private structure PurityScalarLift
    {R S : Type*} [CommRing R] [CommRing S] {C D : Type*}
    [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [Linear R C] [Linear S D] (p : R) (q : S) (I : C ⥤ D) where
  hom : {K L : ScalarLocalization R C p} → (K ⟶ L) →
    (ScalarLocalization.mk (R := S) (p := q) (I.obj K.obj) ⟶
      ScalarLocalization.mk (R := S) (p := q) (I.obj L.obj))
  map_id (K : ScalarLocalization R C p) : hom (𝟙 K) = 𝟙 _
  map_comp {K L M : ScalarLocalization R C p} (f : K ⟶ L) (g : L ⟶ M) :
    hom (f ≫ g) = hom f ≫ hom g
  map_integral {K L : C} (f : K ⟶ L) :
    hom ((ScalarLocalization.localization R C p).map f) =
      (ScalarLocalization.localization S D q).map (I.map f)

private def PurityScalarLift.toFunctor
    {R S : Type*} [CommRing R] [CommRing S] {C D : Type*}
    [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [Linear R C] [Linear S D] {p : R} {q : S} {I : C ⥤ D}
    (s : PurityScalarLift p q I) : ScalarLocalization R C p ⥤ ScalarLocalization S D q where
  obj K := ScalarLocalization.mk (I.obj K.obj)
  map f := s.hom f
  map_id := s.map_id
  map_comp := s.map_comp

private theorem purityScalarLift_naturality
    {R S : Type*} [CommRing R] [CommRing S] {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    [Linear R A] [Linear R B] [Linear S C] [Linear S D]
    (p : R) (q : S) (H : A ⥤ B) (J : C ⥤ D)
    [H.Additive] [H.Linear R] [J.Additive] [J.Linear S]
    (IX : B ⥤ D) (IY : A ⥤ C) (SX : PurityScalarLift p q IX)
    (SY : PurityScalarLift p q IY) (e : H ⋙ IX ⟶ IY ⋙ J)
    {K L : ScalarLocalization R A p} (u : K ⟶ L) :
    (ScalarLocalization.transport R p H ⋙ SX.toFunctor).map u ≫
        (ScalarLocalization.localization S D q).map (e.app L.obj) =
      (ScalarLocalization.localization S D q).map (e.app K.obj) ≫
        (SY.toFunctor ⋙ ScalarLocalization.transport S q J).map u := by
  let F := ScalarLocalization.transport R p H ⋙ SX.toFunctor
  let G := SY.toFunctor ⋙ ScalarLocalization.transport S q J
  let Q := ScalarLocalization.localization S D q
  apply rawScalar_naturality p F G (fun K ↦ Q.map (e.app K)) ?_ K.obj L.obj u
  intro K L v
  have hF : F.map ((ScalarLocalization.localization R A p).map v) =
      Q.map ((H ⋙ IX).map v) :=
    (congrArg SX.toFunctor.map (purityTransport_integral p H v)).trans
      (SX.map_integral (H.map v))
  have hG : G.map ((ScalarLocalization.localization R A p).map v) =
      Q.map ((IY ⋙ J).map v) :=
    (congrArg (ScalarLocalization.transport S q J).map (SY.map_integral v)).trans
      (purityTransport_integral q J (IY.map v))
  have hn : Q.map ((H ⋙ IX).map v) ≫ Q.map (e.app L) =
      Q.map (e.app K) ≫ Q.map ((IY ⋙ J).map v) :=
    (Q.map_comp _ _).symm.trans
      ((congrArg Q.map (e.naturality v)).trans (Q.map_comp _ _))
  exact (congrArg (fun z ↦ z ≫ Q.map (e.app L)) hF).trans
    (hn.trans (congrArg (fun z ↦ Q.map (e.app K) ≫ z) hG.symm))

private theorem purityScalar_integral (W : Scheme.{u}) [IsNoetherian W]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim W ≤ (n : WithBot ℕ∞))]
    [hInv : Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]
    {K L : PbcIntegralCategory l E W hDim.out hInv.out} (v : K ⟶ L) :
    (pbcRationalScalarExtension l E F i W hDim.out hInv.out).map
        ((pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E)).map v) =
      (pbcRationalization W (pbcIntegralDatum l F) (pbcUniformizer l F)).map
        ((pbcEmbeddingIntegralTensor l E F i W hDim.out hInv.out).map v) := by
  let Q := pbcRationalization W (pbcIntegralDatum l F) (pbcUniformizer l F)
  let I := pbcEmbeddingIntegralTensor l E F i W hDim.out hInv.out
  change @Eq (Q.obj (I.obj K) ⟶ Q.obj (I.obj L)) _ _
  have h := pbcScalarLocalization_naturality l E F i W v
  simp only [Category.comp_id, Category.id_comp] at h
  exact h.symm

/-- The specified coefficient maps extend naturally to every rational morphism.
Source: proof Steps 2--3 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: each integral factor is natural. Linear transport and the published scalar
localization square identify the integral-generator equation with its rationalization.
Clear a power-of-uniformizer denominator and cancel its invertible image to extend
that equation to every rational arrow. -/
theorem pbcPurityTwistedScalar_naturality
    {K L : PbcRationalDerivedCategory l E Y dY.out iY.out} (u : K ⟶ L) :
    (pbcPurityTwisted l E f c d ⋙
        pbcRationalScalarExtension l E F i X dX.out iX.out).map u ≫
        (pbcPurityTwistedScalarComponent l E F i f c d L).hom =
      (pbcPurityTwistedScalarComponent l E F i f c d K).hom ≫
        (pbcRationalScalarExtension l E F i Y dY.out iY.out ⋙
          pbcPurityTwisted l F f c d).map u := by
  let := (pbcPurityAmbientProperties l E f c d).2.2.1
  let := (pbcPurityAmbientProperties l E f c d).2.2.2.1
  let := (pbcPurityAmbientProperties l F f c d).2.2.1
  let := (pbcPurityAmbientProperties l F f c d).2.2.2.1
  let HE := pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcPurityTwistedAmbient l E f d) (pbcPurityAmbientProperties l E f c d).1
  let HF := pbcConditionalIntegral (pbcIntegralDatum l F)
    (pbcPurityTwistedAmbient l F f d) (pbcPurityAmbientProperties l F f c d).1
  let IX := pbcEmbeddingIntegralTensor l E F i X dX.out iX.out
  let IY := pbcEmbeddingIntegralTensor l E F i Y dY.out iY.out
  let Q := pbcRationalization X (pbcIntegralDatum l F) (pbcUniformizer l F)
  let I := ObjectProperty.ι (PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E))
  let PX := ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E))
  let P := pbcActualCompletedPull f (pbcIntegralDatum l E)
  let S := pbcEmbeddingAmbientTensor l E F i X
  let TE := pbcTateAmbient l X E (d : ℤ)
  let TF := pbcTateAmbient l X F (d : ℤ)
  let sh := shiftFunctor (PbcCompletedDerived X (pbcIntegralDatum l F)) (2 * (d : ℤ))
  let : S.CommShift ℤ :=
    PurCompactSupport.scalarCommShift (pbcScalarCoefficientMap l E F i X)
  let J := ObjectProperty.lift
    (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) (I ⋙ P)
    (fun K ↦ pbcPurityPull_mem l E f K)
  let t : PX ⋙ TE ⋙ S ≅ PX ⋙ S ⋙ TF :=
    pbcPurityTateScalarModel l E F i X (d : ℤ)
  let q : I ⋙ pbcPurityTwistedAmbient l E f d ⋙ S ≅
      I ⋙ pbcEmbeddingAmbientTensor l E F i Y ⋙ pbcPurityTwistedAmbient l F f d :=
    Functor.isoWhiskerLeft (I ⋙ P ⋙ TE) (S.commShiftIso (2 * (d : ℤ))) ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft J t) sh ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft I (pbcScalarCompletedPullIso l E F i f).symm) TF) sh
  let α : HE ⋙ IX ≅ IY ⋙ HF :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk
      (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l F)) (q.app K))
      (fun v ↦ by
        apply ObjectProperty.hom_ext
        exact q.hom.naturality v)
  let FR := pbcPurityTwisted l E f c d ⋙
    pbcRationalScalarExtension l E F i X dX.out iX.out
  let GR := pbcRationalScalarExtension l E F i Y dY.out iY.out ⋙
    pbcPurityTwisted l F f c d
  change FR.map u ≫ Q.map (α.hom.app L.obj) = Q.map (α.hom.app K.obj) ≫ GR.map u
  let SX : PurityScalarLift (pbcUniformizer l E) (pbcUniformizer l F) IX :=
    { hom := fun {K L} v ↦ pbcRationalScalarHom l E F i X dX.out iX.out K.obj L.obj v
      map_id := (pbcRationalScalarHom_laws l E F i X dX.out iX.out).1
      map_comp := (pbcRationalScalarHom_laws l E F i X dX.out iX.out).2 _ _ _
      map_integral := fun v ↦ purityScalar_integral l E F i X v }
  let SY : PurityScalarLift (pbcUniformizer l E) (pbcUniformizer l F) IY :=
    { hom := fun {K L} v ↦ pbcRationalScalarHom l E F i Y dY.out iY.out K.obj L.obj v
      map_id := (pbcRationalScalarHom_laws l E F i Y dY.out iY.out).1
      map_comp := (pbcRationalScalarHom_laws l E F i Y dY.out iY.out).2 _ _ _
      map_integral := fun v ↦ purityScalar_integral l E F i Y v }
  exact purityScalarLift_naturality (pbcUniformizer l E) (pbcUniformizer l F)
    HE HF IX IY SX SY α.hom u

/-- The canonical a comparison, defined from the actual three normalized factors.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityTwistedScalar :
    pbcPurityTwisted l E f c d ⋙ pbcRationalScalarExtension l E F i X dX.out iX.out ≅
      pbcRationalScalarExtension l E F i Y dY.out iY.out ⋙ pbcPurityTwisted l F f c d :=
  NatIso.ofComponents (pbcPurityTwistedScalarComponent l E F i f c d)
    (fun u ↦ pbcPurityTwistedScalar_naturality l E F i f c d u)

/-- Rationalization of the actual proper/open compact-support scalar mate.
Source: proof Step 3, c (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityCompactScalarComponent
    (K : PbcRationalDerivedCategory l E X dX.out iX.out) :
    (pbcRationalScalarExtension l E F i Y dY.out iY.out).obj
        ((pbcPurityCompact l E f c d).obj K) ⟶
      (pbcPurityCompact l F f c d).obj
        ((pbcRationalScalarExtension l E F i X dX.out iX.out).obj K) :=
  (pbcRationalization Y (pbcIntegralDatum l F) (pbcUniformizer l F)).map
    (ObjectProperty.homMk
      ((PurCompactSupport.comparison (pbcPurityCoefficientChange l E F i) c).app K.obj.obj))

/-- Naturality and invertibility of the specified compact-support scalar mate.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: integral coefficient comparison is natural. Finite freeness makes that
comparison invertible on complete inputs; restrict it to the actual lattice
categories and rationalize its inverse. The fraction formula gives naturality on
all rational arrows and preserves the two inverse equations. -/
theorem pbcPurityCompactScalar_properties :
    (∀ (K : PbcRationalDerivedCategory l E X dX.out iX.out),
      IsIso (pbcPurityCompactScalarComponent l E F i f c d K)) ∧
    ∀ {K L : PbcRationalDerivedCategory l E X dX.out iX.out} (u : K ⟶ L),
      (pbcPurityCompact l E f c d ⋙
          pbcRationalScalarExtension l E F i Y dY.out iY.out).map u ≫
          pbcPurityCompactScalarComponent l E F i f c d L =
        pbcPurityCompactScalarComponent l E F i f c d K ≫
          (pbcRationalScalarExtension l E F i X dX.out iX.out ⋙
            pbcPurityCompact l F f c d).map u := by
  let := (pbcPurityAmbientProperties l E f c d).2.2.2.2.1
  let := (pbcPurityAmbientProperties l E f c d).2.2.2.2.2
  let := (pbcPurityAmbientProperties l F f c d).2.2.2.2.1
  let := (pbcPurityAmbientProperties l F f c d).2.2.2.2.2
  let CE := pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcPurityCompactAmbient l E c) (pbcPurityAmbientProperties l E f c d).2.1
  let CF := pbcConditionalIntegral (pbcIntegralDatum l F)
    (pbcPurityCompactAmbient l F c) (pbcPurityAmbientProperties l F f c d).2.1
  let IX := pbcEmbeddingIntegralTensor l E F i X dX.out iX.out
  let IY := pbcEmbeddingIntegralTensor l E F i Y dY.out iY.out
  let Q := pbcRationalization Y (pbcIntegralDatum l F) (pbcUniformizer l F)
  let q := PurCompactSupport.comparison (pbcPurityCoefficientChange l E F i) c
  let α : CE ⋙ IY ⟶ IX ⋙ CF :=
    { app := fun K ↦ ObjectProperty.homMk (q.app K.obj)
      naturality := fun {K L} v ↦ by
        apply ObjectProperty.hom_ext
        exact q.naturality v.hom }
  constructor
  · intro K
    have h := pbcPurityCompactScalar_integral_isIso l E F i
      (pbcPurityCoefficientChange l E F i) (fun W ↦ rfl) f c K.obj
    have : IsIso ((ObjectProperty.ι
        (PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l F))).map
          (α.app K.obj)) := h
    have : IsIso (α.app K.obj) := isIso_of_reflects_iso (α.app K.obj)
      (ObjectProperty.ι (PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l F)))
    change IsIso (Q.map (α.app K.obj))
    infer_instance
  · intro K L u
    let SX : PurityScalarLift (pbcUniformizer l E) (pbcUniformizer l F) IX :=
      { hom := fun {K L} v ↦ pbcRationalScalarHom l E F i X dX.out iX.out K.obj L.obj v
        map_id := (pbcRationalScalarHom_laws l E F i X dX.out iX.out).1
        map_comp := (pbcRationalScalarHom_laws l E F i X dX.out iX.out).2 _ _ _
        map_integral := fun v ↦ purityScalar_integral l E F i X v }
    let SY : PurityScalarLift (pbcUniformizer l E) (pbcUniformizer l F) IY :=
      { hom := fun {K L} v ↦ pbcRationalScalarHom l E F i Y dY.out iY.out K.obj L.obj v
        map_id := (pbcRationalScalarHom_laws l E F i Y dY.out iY.out).1
        map_comp := (pbcRationalScalarHom_laws l E F i Y dY.out iY.out).2 _ _ _
        map_integral := fun v ↦ purityScalar_integral l E F i Y v }
    exact purityScalarLift_naturality (pbcUniformizer l E) (pbcUniformizer l F)
      CE CF IY IX SY SX α u

/-- The canonical compact-support scalar isomorphism, with its mate normalization.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityCompactScalar :
    pbcPurityCompact l E f c d ⋙ pbcRationalScalarExtension l E F i Y dY.out iY.out ≅
      pbcRationalScalarExtension l E F i X dX.out iX.out ⋙ pbcPurityCompact l F f c d :=
  NatIso.ofComponents
    (fun K ↦ by
      letI := (pbcPurityCompactScalar_properties l E F i f c d).1 K
      exact asIso (pbcPurityCompactScalarComponent l E F i f c d K))
    (fun u ↦ (pbcPurityCompactScalar_properties l E F i f c d).2 u)

attribute [local irreducible] pbcPurityTwisted pbcPurityCompact
  pbcPurityTwistedAmbient pbcPurityCompactAmbient

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) [IsNoetherian W]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim W ≤ (n : WithBot ℕ∞))]
    [hInv : Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]

private theorem purityInverse_heq {C : Type*} [Category* C] {A B B' : C}
    (e : A ≅ B) (e' : A ≅ B') (h : B = B') (he : HEq e.hom e'.hom) :
    HEq e.inv e'.inv := by
  subst B'
  exact heq_of_eq ((Iso.inv_eq_inv e e').mpr (eq_of_heq he))

private theorem purityInverseNormalization
    {A C D : Type*} [Category* A] [Category* C] [Category* D]
    (I : A ⥤ C) (F G : C ⥤ D) (J : A ⥤ D) (e : F ≅ G) (s : I ⋙ F ≅ J)
    (hobj : ∀ K : A, G.obj (I.obj K) = J.obj K)
    (he : ∀ K : A, HEq (e.hom.app (I.obj K)) (s.hom.app K))
    (hI : Function.Surjective I.obj) :
    ∃! n : G ≅ F, ∀ K : A, HEq (n.hom.app (I.obj K)) (s.inv.app K) := by
  have hi (K : A) : HEq (e.inv.app (I.obj K)) (s.inv.app K) :=
    purityInverse_heq (e.app (I.obj K)) (s.app K) (hobj K) (he K)
  refine ⟨e.symm, hi, ?_⟩
  intro e' he'
  apply Iso.ext
  ext K
  obtain ⟨K, rfl⟩ := hI K
  exact eq_of_heq ((he' K).trans (hi K).symm)

/-- Compare actual rational tensor with the literal-unit normalized stage transition.
The component is specified by the recorded integral comparison, including repeated
stages. No scalar extension or associator is supplied as a free variable.
Source: proof Steps 3--4 (blueprint: prop-pur-rational-purity-transitivity-summands).
Proof: the two completed coefficient inclusions agree on every finite quotient,
hence agree. Their derived tensors and raw localizations agree. Conjugate by the
recorded integral comparison; its normalization at equal stages is multiplication
by one. Extend its integral naturality to every tensor-Hom fraction. Components
on all integral representatives determine a natural isomorphism uniquely. -/
theorem pbcPurityScalarNormalization_existsUnique
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    ∃! n : pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) W hDim.out hInv.out ≅
        (pbcScalarSystem l Ω W hDim.out hInv.out).T h,
      ∀ K : pbcIntegralStage l Ω W E,
        HEq (n.hom.app (ScalarLocalization.mk K))
          ((pbcScalarIntegralComparison l Ω W hDim.out hInv.out h).inv.app K) := by
  obtain ⟨e, he, _⟩ := pbcFiniteRawScalarComparison_existsUnique l Ω W h
  have hobj (K : pbcIntegralStage l Ω W E) :
      (pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h)
        W hDim.out hInv.out).obj (ScalarLocalization.mk K) =
      (pbcStageLocalization l Ω W F).obj
        ((pbcIntegralScalarExtension l Ω W hDim.out hInv.out h).obj K) := by
    exact congrArg (fun T ↦ (pbcStageLocalization l Ω W F).obj (T.obj K))
      (rawScalar_integralTensor l Ω W h).symm
  exact purityInverseNormalization (pbcStageLocalization l Ω W E) _ _ _ e
    (pbcScalarIntegralComparison l Ω W hDim.out hInv.out h) hobj he
    (fun K ↦ ⟨K.obj, rfl⟩)

/-- The canonical normalization of rational scalar transitions.
Source: proof Steps 3--4 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityScalarNormalization
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :=
  (pbcPurityScalarNormalization_existsUnique l Ω W h).exists.choose

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f) (d : ℕ)
    [QuasiCompact f] [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- The actual twisted inverse image at a finite coefficient stage of Qbar.
Source: proof Step 2 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityStageTwisted (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageCategory l Ω Y E ⥤ pbcStageCategory l Ω X E :=
  pbcPurityTwisted l (pbcFiniteField.{u} l Ω E) f c d

/-- The actual proper/open compact support at that same finite stage.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityStageCompact (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageCategory l Ω X E ⥤ pbcStageCategory l Ω Y E :=
  pbcPurityCompact l (pbcFiniteField.{u} l Ω E) f c d

/-- The specified a comparison in the normalized stage coordinates.
Source: proof Steps 3--4 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityStageA {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcPurityStageTwisted l Ω f c d E ⋙ (pbcScalarSystem l Ω X dX.out iX.out).T h ≅
      (pbcScalarSystem l Ω Y dY.out iY.out).T h ⋙ pbcPurityStageTwisted l Ω f c d F :=
  Functor.isoWhiskerLeft _ (pbcPurityScalarNormalization l Ω X h).symm ≪≫
    pbcPurityTwistedScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
      (pbcFiniteFieldInclusion l Ω h) f c d ≪≫
    Functor.isoWhiskerRight (pbcPurityScalarNormalization l Ω Y h) _

/-- The compact-support comparison in normalized stage coordinates.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityStageC {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcPurityStageCompact l Ω f c d E ⋙ (pbcScalarSystem l Ω Y dY.out iY.out).T h ≅
      (pbcScalarSystem l Ω X dX.out iX.out).T h ⋙ pbcPurityStageCompact l Ω f c d F :=
  Functor.isoWhiskerLeft _ (pbcPurityScalarNormalization l Ω Y h).symm ≪≫
    pbcPurityCompactScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
      (pbcFiniteFieldInclusion l Ω h) f c d ≪≫
    Functor.isoWhiskerRight (pbcPurityScalarNormalization l Ω X h) _

end AlgebraicGeometry.Scheme
