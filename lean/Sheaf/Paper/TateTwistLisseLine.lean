/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.PbcCoefficientTwists
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.Paper.LisseAdicFiberFunctors
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.TateTwistLocallyFree
public import Sheaf.CategoryTheory.StageSystemFunctorDescent
public import Sheaf.Paper.SfScalarExtensionComposition
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
public import Sheaf.SixFunctors.ConstructibleTensorCompletion
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Paper.PbcScalarExtension
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.IntrinsicQbarCategory
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.TwistPreservesFiniteness

/-! # The Tate line as a lisse adic system

Source: Bhatt--Scholze, Corollary 5.1.5, Proposition 6.8.4(1), Remark 6.8.15;
main-20261015, lem-per-smooth-pullback-t-exact.proof.md, second paragraph
(blueprint: lem-per-tate-twist-lisse-line).
All positive quotient indices mean n+1. The etale system is constructed by restricting
its canonical ordinary quotient tower; it carries no choice of transition maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme WeilConjectures
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual constant integer action on the PBC completed ring, normalized on residues.
Source: Bhatt--Scholze 6.8.4(1) (blueprint: lem-per-tate-twist-lisse-line). -/
def perTateScalar :
    (Functor.const X.ProEtᵒᵖ).obj (RingCat.of (PbcIntegralRing l E)) ⟶
      ((adicLisseForget X).obj (pbcAdicCompletion X (pbcIntegralDatum l E))).obj :=
  adicLisseConstantUnit X (PbcIntegralRing l E) ≫
    ((adicLisseForget X).map
      (adicDatumScalar X
        { (pbcIntegralDatum l E).toCompleteCoefficientDatum with
          quotientFinite := (pbcIntegralDatum l E).quotientFinite } ≫
        (pbcCompletedComparison X (pbcIntegralDatum l E)).hom)).hom

/-- Restrict scalars to a constant ring presheaf without changing sections.
Source: Stacks 03CY (blueprint: lem-per-tate-twist-lisse-line). -/
def perTateScalarPresheaf (A : Type (u + 1)) [CommRing A]
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (α : (Functor.const X.ProEtᵒᵖ).obj (RingCat.of A) ⟶ R.obj)
    (M : SheafOfModules.{u + 1} R) : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} A :=
  { obj := ((PresheafOfModules.restrictScalars α).obj M.val).obj
    map := fun f ↦ ((PresheafOfModules.restrictScalars α).obj M.val).map f
    map_id := fun U ↦ by
      ext x
      exact congrArg (fun f ↦ f x)
        (((PresheafOfModules.restrictScalars α).obj M.val).map_id U)
    map_comp := fun f g ↦ by
      ext x
      exact ((PresheafOfModules.restrictScalars α).obj M.val).map_comp_apply f g x }

/-- Constant-scalar restriction retains the underlying sheaf and every section map.
Source: Stacks 03CY (blueprint: lem-per-tate-twist-lisse-line). -/
def perTateScalarSheaf (A : Type (u + 1)) [CommRing A]
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (α : (Functor.const X.ProEtᵒᵖ).obj (RingCat.of A) ⟶ R.obj) :
    SheafOfModules.{u + 1} R ⥤ Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A) where
  obj M := ⟨perTateScalarPresheaf X A R α M,
    Presheaf.isSheaf_of_isSheaf_comp (ProEt.topology X) _
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map f := { hom :=
    { app := fun U ↦ ((PresheafOfModules.restrictScalars α).map f.val).app U
      naturality := fun _ _ g ↦ by
        ext x
        exact PresheafOfModules.naturality_apply
          ((PresheafOfModules.restrictScalars α).map f.val) g x } }
  map_id M := by ext U x; rfl
  map_comp f g := by ext U x; rfl

/-- Apply the constant-scalar restriction to the actual completed integer ring.
Source: Bhatt--Scholze 6.8.4(1) (blueprint: lem-per-tate-twist-lisse-line). -/
def perTateFixedLift :=
  perTateScalarSheaf X (PbcIntegralRing l E)
    ((adicLisseForget X).obj (pbcAdicCompletion X (pbcIntegralDatum l E)))
    (perTateScalar l X E)

/-- Remove only the coefficient size lift, keeping the original integer scalar action.
Source: Weil II (1.1.1) b) (blueprint: lem-per-tate-twist-lisse-line). -/
def perTateFixed :=
  perTateFixedLift l X E ⋙ sheafCompose (ProEt.topology X)
    (ModuleCat.restrictScalars.{u + 1}
      ((ULift.ringEquiv :
        ULift.{u + 1} (Padic.coefficientExtensionIntegers l E) ≃+*
          Padic.coefficientExtensionIntegers l E).symm.toRingHom))

variable [hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- The canonical quotient tower of the signed integral line, as fixed-integer sheaves.
Source: Bhatt--Scholze 6.8.4(1) (blueprint: lem-per-tate-twist-lisse-line). -/
def perTateProEtaleTower (m : ℤ) :=
  completedReductionModuleTower X (pbcIntegralDatum l E) (pbcTateLineSheaf l X E m) ⋙
    perTateFixed l X E

/-- The etale Tate system is restriction of these canonical quotients. Its transitions
are precisely the quotient maps, including the dual reductions for negative m.
Source: Bhatt--Scholze 5.1.5, 6.8.4(1) (blueprint: lem-per-tate-twist-lisse-line). -/
def perTateEtaleTower (m : ℤ) : AdicIntegralDiagramOfUniverses l E X :=
  perTateProEtaleTower l X E m ⋙
    ProEtale.comparisonLowerStar (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) X

/-- l^(n+1) kills the coefficient quotient, even in ramified extensions.
Source: Serre, Local Fields II.2 (blueprint: lem-per-tate-twist-lisse-line).
Proof: write l=u varpi^e with e>=1. The valuation of l^(n+1) is e(n+1)>=n+1,
so it belongs to the defining quotient ideal. ULift preserves this equation. -/
theorem perTateAnnihilator (n : ℕ) :
    ((l ^ (n + 1) : ℕ) : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) = 0 := by
  sorry

/-- The finite etale Tate sheaf specified by the node, with N=l^(n+1).
Source: Stacks 03PK (blueprint: lem-per-tate-twist-lisse-line). -/
def perTateFiniteEtale (n : ℕ) (m : ℤ) :=
  finiteEtaleTateSheaf (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
    (l ^ (n + 1)) X (perTateAnnihilator l E n) m

/-- The same finite sheaf with its original integer-ring action.
Source: Weil II (1.1.1) b) (blueprint: lem-per-tate-twist-lisse-line). -/
def perTateFiniteEtaleIntegral (n : ℕ) (m : ℤ) :=
  (sheafCompose X.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1}
      ((ULift.ringEquiv :
        ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)) ≃+*
          Padic.coefficientExtensionRing l E (n + 1)).symm.toRingHom.comp
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))))).obj
    (perTateFiniteEtale l X E n m)

/-- The counit on this canonical quotient diagram; its naturality includes every
transition, and hence does not assert that inverse image commutes with infinite limits.
Source: Bhatt--Scholze 5.1.5 (blueprint: lem-per-tate-twist-lisse-line). -/
def perTateComparison (m : ℤ) :=
  Functor.whiskerLeft (perTateProEtaleTower l X E m)
    (ProEtale.comparisonAdjunction
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) X).counit

/-- The signed finite pro-etale twist with its constant quotient action.
Source: coefficient-twist definition, Bhatt--Scholze 5.1.5
(blueprint: lem-per-tate-twist-lisse-line). -/
def perTateFiniteProEtale (n : ℕ) (m : ℤ) :=
  (perTateScalarSheaf X
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
    (integralCoefficientSheaf l E X n)
    (adicLisseConstantUnit X
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).obj
    (coefficientTwistLine X (purTwistFiniteOne X l E n) m)

/-- The actual quotient augmentation, linear over completed coefficients.
Source: Bhatt--Scholze 6.8.4(1) (blueprint: lem-per-tate-twist-lisse-line). -/
def perTateQuotientUnit (m : ℤ) (n : ℕ) :
    pbcTateLineSheaf l X E m ⟶
      (completedReductionModuleTower X (pbcIntegralDatum l E)
        (pbcTateLineSheaf l X E m)).obj (op n) :=
  (pbcScalarAdjunction (pbcAdicProjection X (pbcIntegralDatum l E) n)).unit.app
    (pbcTateLineSheaf l X E m)

include hInv in
/-- The finite-system and comparison assertions, including the specified inverse limit.
Source: Bhatt--Scholze 5.1.5, 6.8.4(1), and the blueprint smooth-pullback proof
(blueprint: lem-per-tate-twist-lisse-line).
Proof:
1. The finite Kummer line is etale locally the constant quotient line. Its reduction
sends a primitive root zeta to zeta^l, so the matrix on these generators is one.
Positive powers inherit this reduction; negative powers use the inverse dual
base-change isomorphism. Thus the recorded quotient tower restricts to the signed
finite etale Tate sheaves, and its stalk transitions have precisely the quotient
kernels in IsLisseIntegralDiagramOfUniverses. Use lem-asd-finite-etale-twist-line,
lem-pur-twist-sheaf-locally-free, and det-def-sp-tate-twist-locally-free.
2. For finite etale represented sheaves, comparison pullback represents the same
scheme. Apply this to the root schemes and their power maps, then use exact tensor
pullback and duality of rank-one lines. The comparison counit is therefore invertible
on all quotients. Its naturality gives compatibility with every transition. Use
lem-sf-comparison-pullback-exact and lem-weil-pbc-ringed-topoi-module-pullback-tensor.
3. On a compatible primitive-root pro-etale cover the signed integral line is the
completed coefficient ring and the augmentations are its residue maps. Slice
restriction commutes with sectionwise limits. Hence their inverse limit comparison
is invertible globally, without commuting nu-star with an infinite limit.
4. The integral-category comparison and finite-free scalar comparison identify this
same degree-zero line in the PBC category. Completed constructible tensor is the
ordinary tensor for this line, by lem-fix-constructible-tensor-completion. These last
assertions are stated by the derived companion declarations below. -/
theorem perTateTwistLisseLine [IsNoetherian X] [X.IsSeparated] (m : ℤ) :
    IsLisseIntegralDiagramOfUniverses l E X (perTateEtaleTower l X E m) ∧
    (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X),
      Nonempty (Module.Basis (Fin 1) (Padic.coefficientExtensionIntegers l E)
        (adicIntegralFiberOfUniverses l E X (perTateEtaleTower l X E m) κ x))) := by
  sorry

/-- The actual rank-one lisse integral object, with its previously constructed tower.
Source: Bhatt--Scholze 6.8.4(1) (blueprint: lem-per-tate-twist-lisse-line). -/
def perTateLisseIntegral [IsNoetherian X] [X.IsSeparated] (m : ℤ) :
    LisseIntegralSheafOfUniverses l E X :=
  ⟨perTateEtaleTower l X E m, (perTateTwistLisseLine l X E m).1⟩

include hInv in
/-- Finite Tate identification and etale-to-pro-etale comparison, including local bases.
Source: Bhatt--Scholze 5.1.5, 6.8.4(1) (blueprint: lem-per-tate-twist-lisse-line).
Proof: finite Kummer generators are etale locally primitive roots. Taking positive
powers, the unit, and inverse dual base-change for negative powers gives the signed
finite line. Comparison inverse image represents the same root scheme and power maps.
Exact tensor pullback and rank-one duality identify it with the finite pro-etale line.
The recorded canonical quotient tower and comparison counit retain every transition.
These are steps 1 and 2 of the node's proof, with root transition zeta to zeta^l. -/
theorem perTateFiniteSystem [IsNoetherian X] [X.IsSeparated] (m : ℤ) :
    (∀ n : ℕ,
      Nonempty ((perTateEtaleTower l X E m).obj (op n) ≅
        perTateFiniteEtaleIntegral l X E n m) ∧
      (∃ cover : Cover.{u} etalePrecoverage X, ∀ i : cover.I₀,
        Nonempty
          ((perTateFiniteEtale l X E n m).over (cover.etalePrecoverageToEtale i) ≅
            (constantSheaf (X.smallEtaleTopology.over (cover.etalePrecoverageToEtale i))
              (ModuleCat.{u + 1}
                (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).obj
                (ModuleCat.of
                  (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
                  (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))) ∧
      Nonempty
        ((ProEtale.comparisonUpperStar.{u + 2, u}
          (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) X).obj
            (perTateFiniteEtale l X E n m) ≅ perTateFiniteProEtale l X E n m) ∧
      IsIso ((perTateComparison l X E m).app (op n))) := by
  sorry

/-- The quotient augmentations commute with every transition.
Source: Bhatt--Scholze 6.8.4(1) (blueprint: lem-per-tate-twist-lisse-line).
Proof: ordinary coefficient-extension units send each section x to 1 tensor x.
The quotient transition sends this to the same unit tensor at the smaller quotient.
This holds after sheafification, and constant-scalar restriction preserves the equation.
The signed line is unchanged as input, so the assertion covers all m. -/
theorem perTateQuotientUnit_naturality (m : ℤ) (i j : ℕᵒᵖ) (f : i ⟶ j) :
    (perTateFixed l X E).map (perTateQuotientUnit l X E m i.unop) ≫
        (perTateProEtaleTower l X E m).map f =
      (perTateFixed l X E).map (perTateQuotientUnit l X E m j.unop) := by
  sorry

/-- The actual quotient cone, with its specified point and all its augmentation maps.
Source: Bhatt--Scholze 6.8.4(1) (blueprint: lem-per-tate-twist-lisse-line). -/
def perTateQuotientCone (m : ℤ) : Cone (perTateProEtaleTower l X E m) where
  pt := (perTateFixed l X E).obj (pbcTateLineSheaf l X E m)
  π :=
    { app := fun i ↦ (perTateFixed l X E).map (perTateQuotientUnit l X E m i.unop)
      naturality := fun i j f ↦ by
        exact (Category.id_comp _).trans
          (perTateQuotientUnit_naturality l X E m i j f).symm }

include hInv in
/-- The integral line is the inverse limit via its actual quotient augmentations.
The universal-property formulation avoids any choice of an unrelated limit object.
Source: Bhatt--Scholze 6.8.4(1) (blueprint: lem-per-tate-twist-lisse-line).
Proof: on the compatible primitive-root pro-etale cover the integral line is the
completed ring in its induced tensor or dual basis. The augmentations are its finite
residue projections, whose limit is the completed ring by its definition. Restriction
to slice sites commutes with these limits sectionwise. Invertibility descends, proving
the global universal property, without commuting nu-star with an infinite limit.
This is step 2 of the node's proof. -/
theorem perTateInverseLimit [IsNoetherian X] [X.IsSeparated] (m : ℤ) :
    Nonempty (IsLimit (perTateQuotientCone l X E m)) := by
  sorry

/-- The same signed line, in degree zero over the original completed coefficient ring.
Source: coefficient-twist definition (blueprint: lem-per-tate-twist-lisse-line). -/
def perTateIntrinsicLine (m : ℤ) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (coefficientTwistLine X
      (R := completedIntegralCommRingSheafUnrestricted l E X)
      (purTwistIntegralModule X l E) m)

include hInv in
/-- The degree-zero signed line is in the intrinsic integral category.
Source: Bhatt--Scholze 6.8.4(1), 6.8.11(3)
(blueprint: lem-per-tate-twist-lisse-line).
Proof: positive powers and duals are locally free rank one. Each derived reduction
is the finite signed line in degree zero, constructible on the one-stratum
stratification, with the common interval [0,0]. The compatible quotient tower
recovers the line and its canonical Roos completeness unit. These are the two
conditions of sfIntegralConstructible; the empty scheme has the same vanishing bounds. -/
theorem perTateIntrinsicLine_mem (m : ℤ) :
    sfIntegralConstructible l E X (perTateIntrinsicLine l X E m) := by
  sorry

variable [IsNoetherian X] [X.IsSeparated]

include hInv in
/-- Ordinary tensor by the integral Tate line is already complete and its canonical
comparison with completed tensor is invertible, naturally in the integral representative.
The total-tensor and Roos-coordinate equations specify the canonical comparison.
Source: Bhatt--Scholze 6.5.5, 3.4.12(4) (blueprint: lem-per-tate-twist-lisse-line).
Proof: apply constructibleTensorCompletion to the integral constructible input and
perTateIntrinsicLine_mem. The line is flat, so its exact termwise tensor computes
ordinary derived tensor. The representative comparison e descends the identity
between this tensor and ordinary K-flat total tensor, giving the natural isomorphism.
The specified chi sends each pure tensor to its two quotient factors and is zero
on the other Roos coordinate. Its descended tau is the canonical ordinary-to-completed
map. The source theorem gives both derived completeness and invertibility of tau.
The natural isomorphism transports completeness to the literal termwise twist.
This is step 4 of the node's proof. -/
theorem perTateIntegralTensor :
    ∃ (T : DerivedCategory (integralTowerModules l E X) ×
        DerivedCategory (integralTowerModules l E X) ⥤
          DerivedCategory (integralTowerModules l E X))
      (e : ((integralOperationsGoodComplex l E X).ι.prod
          (integralOperationsGoodComplex l E X).ι) ⋙ constructibleTensorTotal l E X ⋙
          DerivedCategory.Q ≅
        ((integralOperationsGoodLocalization l E X).prod
          (integralOperationsGoodLocalization l E X)) ⋙ T)
      (chi : constructibleTensorTotal l E X ⟶ integralOperationsTensorComplexFunctor l E X),
      (∀ (P Q : CochainComplex (integralTowerModules l E X) ℤ) (p q : ℤ) (n : ℕ)
        (U : X.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (((chi.app (P, Q) ≫ CochainComplex.mappingCocone.fst
          (constructibleTensorBoundary l E X P Q) ≫
          Pi.π (fun n ↦ (integralOperationsTensorLevel l E X n).obj (P, Q)) n).f
            (p + q)).val.app U)
          (constructibleTensorTotalSection l E X P Q p q U x y) =
        integralOperationsTotalTensorSection l E X n P Q p q U
          (unrestrictedIntegralTensorSection l E X n (P.X p) U 1 x)
          (unrestrictedIntegralTensorSection l E X n (Q.X q) U 1 y)) ∧
      (∀ (P Q : CochainComplex (integralTowerModules l E X) ℤ) (i j : ℤ)
        (h : i + -1 = j),
        (chi.app (P, Q)).f i ≫ (CochainComplex.mappingCocone.snd
          (constructibleTensorBoundary l E X P Q)).v i j h = 0) ∧
      ∃ tau : T ⟶ integralCompletedTensor l E X,
        (∀ (P Q : (integralOperationsGoodComplex l E X).FullSubcategory),
          e.hom.app (P, Q) ≫ tau.app (DerivedCategory.Q.obj P.obj,
              DerivedCategory.Q.obj Q.obj) ≫
            (integralCompletedTensorComparison l E X).hom.app (P, Q) =
          DerivedCategory.Q.map (chi.app (P.obj, Q.obj))) ∧
        ∀ m : ℤ,
          Nonempty
            ((integralSheafTwist l E X m).mapDerivedCategory ≅
              tateTensorRight T (perTateIntrinsicLine l X E m)) ∧
          ∀ K : sfIntegralConstructibleCategory l E X,
            IsDerivedCompleteUnrestricted l E X
              (T.obj (K.obj, perTateIntrinsicLine l X E m)) ∧
            IsDerivedCompleteUnrestricted l E X
              (((integralSheafTwist l E X m).mapDerivedCategory).obj K.obj) ∧
            IsIso (tau.app (K.obj, perTateIntrinsicLine l X E m)) := by
  sorry

variable [hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]

include hInv in
/-- The same line in the PBC integral category, transported by the normalized
coefficient-ring comparison. Source: Bhatt--Scholze 6.8.11(3)
(blueprint: lem-per-tate-twist-lisse-line).
Proof: integralStratifiedPerfectDetailed compares the intrinsic and PBC conditions
on the same completed ring and finite reductions. Apply it to the constructible
complete signed line, and use the identity-on-sections coefficient round trip.
Finite dimensionality and local invertibility are exactly the source hypotheses. -/
theorem perTatePbcLine_mem (m : ℤ) :
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
      ((DerivedCategory.singleFunctor _ 0).obj (pbcTateLineSheaf l X E m)) := by
  sorry

/-- Its integral PBC representative has literal degree-zero underlying object.
Source: Bhatt--Scholze 6.8.11(3) (blueprint: lem-per-tate-twist-lisse-line). -/
def perTatePbcLine (m : ℤ) : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E) :=
  ⟨(DerivedCategory.singleFunctor _ 0).obj (pbcTateLineSheaf l X E m),
    perTatePbcLine_mem l X E m⟩

include hInv in
/-- The canonical coefficient restriction takes PBC representatives to the intrinsic
integral category. Source: Bhatt--Scholze 6.8.11(3)
(blueprint: lem-per-tate-twist-lisse-line).
Proof: apply the integral-category characterization through purCoefficientModel,
whose inverse is the recorded integralDetailedTransport. Its normalized projections
identify all reductions. The local inverses of l glue to its global inverse.
The unit isomorphism of the coefficient equivalence identifies the transported
representative with the original one; isomorphism closure preserves all three PBC
conditions. This is step 3 of the node's proof. -/
theorem perTateIntegralModel_mem
    (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)) :
    sfIntegralConstructible l E X ((purCoefficientModel l E X).functor.obj K.obj) := by
  sorry

/-- The full-subcategory restriction of the actual normalized coefficient transport.
Source: Bhatt--Scholze 6.8.11(3) (blueprint: lem-per-tate-twist-lisse-line). -/
def perTateIntegralModel : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E) ⥤
    sfIntegralConstructibleCategory l E X :=
  (sfIntegralConstructible l E X).lift
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) ⋙
      (purCoefficientModel l E X).functor)
    (perTateIntegralModel_mem l X E)

section AlgebraicCoefficients
variable (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The finite integral model of the lisse algebraic-coefficient sheaf. As in the
recorded lisse rationalization, rationalizing morphisms retains this integral object.
It is exactly the pair (F,T_F tensor F), before identifying different finite models.
Source: Weil II (1.1.1) c), d), Bhatt--Scholze 6.8.14
(blueprint: lem-per-tate-twist-lisse-line). -/
def perTateLisseModel (F : Padic.FiniteCoefficientFields l Ω) (m : ℤ) :
    Σ G : Padic.FiniteCoefficientFields l Ω,
      LisseIntegralSheafOfUniverses l (pbcFiniteField.{u} l Ω G) X :=
  ⟨F, perTateLisseIntegral l X (pbcFiniteField.{u} l Ω F) m⟩

/-- The degree-zero intrinsic line in its integral full subcategory at the finite stage.
Source: Bhatt--Scholze 6.8.11(3) (blueprint: lem-per-tate-twist-lisse-line). -/
def perTateStageIntegralLine (F : Padic.FiniteCoefficientFields l Ω) (m : ℤ) :
    sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω F) X :=
  ⟨perTateIntrinsicLine l X (pbcFiniteField.{u} l Ω F) m,
    perTateIntrinsicLine_mem l X (pbcFiniteField.{u} l Ω F) m⟩

/-- Rationalize exactly that integral line, without adjoining any retracts.
Source: Bhatt--Scholze 6.8.14(2) (blueprint: lem-per-tate-twist-lisse-line). -/
def perTateStageLine (F : Padic.FiniteCoefficientFields l Ω) (m : ℤ) :=
  (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω F) X).obj
    (perTateStageIntegralLine l X Ω F m)

/-- The literal common-stage object represented by the signed degree-zero line at F.
Source: Bhatt--Scholze 6.8.14, coefficient definitions
(blueprint: lem-per-tate-twist-lisse-line). -/
def perTateCommonLine (F : Padic.FiniteCoefficientFields l Ω) (m : ℤ) :
    generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  ⟨F, perTateStageLine l X Ω F m⟩

/-- Transport the actual integral representative and then rationalize its Hom groups.
Source: Bhatt--Scholze 6.8.14(2) (blueprint: lem-per-tate-twist-lisse-line). -/
def perTateStageObject (F : Padic.FiniteCoefficientFields l Ω)
    (K : pbcStageCategory l Ω X F) : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X F :=
  (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω F) X).obj
    ((perTateIntegralModel l X (pbcFiniteField.{u} l Ω F)).obj K.obj)

include hInv in
/-- The stage comparison is uniquely specified by its composite with integral
localization, including its object function and every rationalized arrow.
Source: Bhatt--Scholze 6.8.14(2)
(blueprint: lem-per-tate-twist-lisse-line).
Proof: restrict the normalized completed-ring equivalence using the integral-category
characterization. Both rationalizations have the integral objects and Hom tensor E.
Apply the integral functor to f and send the scalar a through the canonical Shrink
field equivalence. Tensor balancing, additivity and composition hold on pure tensors
and then on sums. The inverse coefficient restriction constructs an inverse functor.
The localization equation determines objects and all fractions uniquely.
Use lem-weil-pbc-integral-stratified-perfect-characterization and the raw
rationalizations def-weil-pbc-qbar-category and def-weil-rationalization-karoubi. -/
theorem perTateRationalModel_existsUnique (F : Padic.FiniteCoefficientFields l Ω) :
    ∃! T : pbcStageCategory l Ω X F ⥤
        sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω F) X,
      T.IsEquivalence ∧
      pbcStageLocalization l Ω X F ⋙ T =
        perTateIntegralModel l X (pbcFiniteField.{u} l Ω F) ⋙
          sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω F) X := by
  sorry

/-- The unique normalized rational comparison, including its specified arrow action.
Source: Bhatt--Scholze 6.8.14(2) (blueprint: lem-per-tate-twist-lisse-line). -/
@[irreducible] def perTateRationalModel (F : Padic.FiniteCoefficientFields l Ω) :
    pbcStageCategory l Ω X F ⥤
      sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω F) X :=
  (perTateRationalModel_existsUnique l X Ω F).exists.choose

include hInv in
/-- The finite-stage comparisons intertwine literal Tate twisting with the completed
integral tensor rationalized at the same stage. They also identify its one-dimensional
geometric fibre and the coefficient-independent common-stage line.
Source: Bhatt--Scholze 6.8.4(1), 6.8.14, 6.8.15
(blueprint: lem-per-tate-twist-lisse-line).
Proof:
1. The finite-system theorem identifies the signed line as lisse rank one. Its
integral fibre is free with one basis element. Scalar extension along the actual
integer inclusion to Ω therefore has dimension one, including negative and zero m.
2. The integral tensor comparison perTateIntegralTensor is the specified quotient-tower
map. Raw rationalization carries it to an isomorphism natural for every tensor Hom,
so it intertwines pbcTateRational and rationalDerivedTensor after the uniquely
normalized perTateRationalModel. No choice of a different tensor operation occurs.
3. Coefficient extension respects the root tower, powers, and duals. The recorded
ordinary scalar comparisons and finite-free ordinary/completed comparison identify
successive finite-stage line models. Their normalized pure-tensor formulas give
identity, tower, and associativity compatibility. The common-stage line is therefore
independent of F; its finite representative is precisely the integral line in degree zero.
4. These comparisons descend on morphism representatives to the common-stage
categories. The canonical category comparison sends exactly the integral
representatives through purCoefficientModel and rationalizes. Its intertwining
isomorphism is the scalar extension of the preceding natural comparison. -/
theorem perTateRationalTensor (m : ℤ) :
    (∀ F : Padic.FiniteCoefficientFields l Ω,
      Nonempty
        (pbcTateRational l X Ω F m ⋙ perTateRationalModel l X Ω F ≅
          perTateRationalModel l X Ω F ⋙
            tateTensorRight (rationalDerivedTensor l (pbcFiniteField.{u} l Ω F) X)
              (perTateStageLine l X Ω F m))) ∧
    (∀ F G : Padic.FiniteCoefficientFields l Ω,
      Nonempty (perTateCommonLine l X Ω F m ≅ perTateCommonLine l X Ω G m)) ∧
    ∀ (F : Padic.FiniteCoefficientFields l Ω)
      (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X),
      Module.finrank Ω
        ((ModuleCat.extendScalars (pbcFibreCoefficient.{u} l Ω F)).obj
          (adicIntegralFiberOfUniverses l (pbcFiniteField.{u} l Ω F) X
            (perTateEtaleTower l X (pbcFiniteField.{u} l Ω F) m) κ x)) = 1 := by
  sorry

/-- The two published coefficient-map presentations have the same finite projections.
Source: Bhatt--Scholze 6.8.2(1) (blueprint: lem-per-tate-twist-lisse-line).
Proof: both maps restrict on constant integers to the same field inclusion. Their
finite projections are the same quotient inclusion, including its cofinal ramification
indices. The completed coefficient sheaf is the inverse limit of these quotients,
whose jointly monic projections identify the two maps. -/
theorem perTateScalarMap_eq {F G : Padic.FiniteCoefficientFields l Ω} (h : F ≤ G) :
    pbcCompletedScalarMap l Ω X h =
      pbcScalarCoefficientMap l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G)
        (pbcFiniteFieldInclusion l Ω h) X := by
  sorry

/-- The integral comparison of coefficient extension, fixed by the ordinary balanced
scalar comparison followed by its canonical quotient completion.
Source: Bhatt--Scholze 6.8.2(1), 6.8.11(3), 6.8.14
(blueprint: lem-per-tate-twist-lisse-line).
Proof: purScalarModel compares ordinary coefficient extension under the normalized
ring equivalence. sfIntegralOrdinaryComparison then completes that ordinary tensor.
The integral-category characterization permits restriction to the full subcategories.
Their inclusions are fully faithful, so the displayed component equation lifts these
comparisons and uniquely specifies the natural isomorphism, including identity fields. -/
theorem perTateIntegralScalarModel_existsUnique
    {F G : Padic.FiniteCoefficientFields l Ω} (h : F ≤ G) :
    ∃! e : perTateIntegralModel l X (pbcFiniteField.{u} l Ω F) ⋙
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X F G h ≅
      pbcIntegralScalarExtension l Ω X hDim.out hInv.out h ⋙
        perTateIntegralModel l X (pbcFiniteField.{u} l Ω G),
      ∀ K : pbcIntegralStage l Ω X F,
        HEq ((e.inv.app K).hom)
          ((purCoefficientModel l (pbcFiniteField.{u} l Ω G) X).functor.map
              (eqToHom (congrArg (fun f ↦ (pbcDerivedExtend f).obj K.obj)
                (perTateScalarMap_eq l X Ω h))) ≫
          (purScalarModel l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G)
            (pbcFiniteFieldInclusion l Ω h) X).hom.app K.obj ≫
          (sfIntegralOrdinaryComparison l (pbcFiniteField.{u} l Ω F)
            (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) X).hom.app
              ((perTateIntegralModel l X (pbcFiniteField.{u} l Ω F)).obj K)) := by
  sorry

/-- The uniquely fixed integral scalar comparison.
Source: Bhatt--Scholze 6.8.2(1) (blueprint: lem-per-tate-twist-lisse-line). -/
@[irreducible] def perTateIntegralScalarModel
    {F G : Padic.FiniteCoefficientFields l Ω} (h : F ≤ G) :=
  (perTateIntegralScalarModel_existsUnique l X Ω h).exists.choose

/-- The named stages use precisely the same small coefficient field and category data.
This equality transports only the spelling, with no change to the derived objects.
Source: coefficient size convention in Bhatt--Scholze 6.8.14 and the two recorded
coefficient constructions (blueprint: lem-per-tate-twist-lisse-line).
Proof: unfold GeneralAlgebraicallyClosedCoefficients.Stage and its cached category
instance, and the pbcFiniteField field and algebra instances. Both are Shrink F.val
with its canonical transported structures. Smallness and finite-dimensionality are
propositions, so their proofs are irrelevant. The intrinsic predicate, raw localization
and category operations are then identical, giving equality of the bundled categories. -/
theorem perTateStageCategory_eq (F : Padic.FiniteCoefficientFields l Ω) :
    Cat.of (sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω F) X) =
      Cat.of (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X F) := by
  sorry

/-- Regard the normalized rational functor in the named intrinsic stage using the
canonical equality of the coefficient spellings, including category structures.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-tate-twist-lisse-line). -/
@[irreducible] def perTateRationalStageModel (F : Padic.FiniteCoefficientFields l Ω) :
    pbcStageCategory l Ω X F ⥤ GeneralAlgebraicallyClosedCoefficients.Stage l Ω X F :=
  perTateRationalModel l X Ω F ⋙ (eqToHom (perTateStageCategory_eq l X Ω F)).toFunctor

-- Keep the published stage system opaque during dependent representative elaboration.
-- This changes transparency only; its transitions and associators remain the recorded data.
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

set_option backward.isDefEq.respectTransparency false in
/-- The concrete common-stage descent is fixed on every object and morphism
representative. This specializes the existing coherent-pair descent to these categories.
Source: Bhatt--Scholze 6.8.14 and the common-stage coefficient construction
(blueprint: lem-per-tate-twist-lisse-line).
Proof: apply StageSystem.coefficientPairFunctor_exists to the displayed finite-stage
functors and scalar comparisons. The hypothesis hb is exactly its tower equation.
Conjugating every representative by b gives the displayed arrow formula. That equation
respects further coefficient extension and eventual equality. Every arrow has a
representative, proving uniqueness of the descended functor with this formula. -/
theorem perTateCommonModel_existsUnique
    (b : ∀ {F G : Padic.FiniteCoefficientFields l Ω} (h : F ≤ G),
      perTateRationalStageModel l X Ω F ⋙
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h ≅
        (pbcScalarSystem l Ω X hDim.out hInv.out).T h ⋙ perTateRationalStageModel l X Ω G)
    (_hb : CategoryTheory.StageSystem.pairFunctorCoherent
      (pbcScalarSystem l Ω X hDim.out hInv.out)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X)
      (perTateRationalStageModel l X Ω) b) :
    ∃! T : pbcQbarCategory l Ω X ⥤ generalAlgebraicallyClosedConstructibleCategory l Ω X,
      (∀ P : pbcQbarCategory l Ω X,
        T.obj P = ⟨P.stage, (perTateRationalStageModel l X Ω P.stage).obj P.obj⟩) ∧
      ∀ (P Q : pbcQbarCategory l Ω X) (M : Padic.FiniteCoefficientFields l Ω)
        (hP : P.stage ≤ M) (hQ : Q.stage ≤ M) (f : P.toStage hP ⟶ Q.toStage hQ),
        HEq (T.map (CategoryTheory.StageSystem.PairCategory.mkHom M hP hQ f))
          (CategoryTheory.StageSystem.PairCategory.mkHom
            (X := (⟨P.stage, (perTateRationalStageModel l X Ω P.stage).obj P.obj⟩ :
              generalAlgebraicallyClosedConstructibleCategory l Ω X))
            (Y := (⟨Q.stage, (perTateRationalStageModel l X Ω Q.stage).obj Q.obj⟩ :
              generalAlgebraicallyClosedConstructibleCategory l Ω X)) M hP hQ
            ((b hP).hom.app P.obj ≫ (perTateRationalStageModel l X Ω M).map f ≫
              (b hQ).inv.app Q.obj)) := by
  sorry

/-- The uniquely specified common-stage functor, retaining the representative formula.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-tate-twist-lisse-line). -/
@[irreducible] def perTateCommonModel
    (b : ∀ {F G : Padic.FiniteCoefficientFields l Ω} (h : F ≤ G),
      perTateRationalStageModel l X Ω F ⋙
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h ≅
        (pbcScalarSystem l Ω X hDim.out hInv.out).T h ⋙ perTateRationalStageModel l X Ω G)
    (hb : CategoryTheory.StageSystem.pairFunctorCoherent
      (pbcScalarSystem l Ω X hDim.out hInv.out)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X)
      (perTateRationalStageModel l X Ω) b) :
    pbcQbarCategory l Ω X ⥤ generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  (perTateCommonModel_existsUnique l X Ω b hb).exists.choose

set_option backward.isDefEq.respectTransparency false in
/-- The common-stage comparison and the natural tensor interpretation of the literal
Qbar twist, with its full finite-stage arrow action. The coefficient comparison b is
normalized by integral scalar extension; its tower equation supplies descent on the
actual quotient. Equal coefficient fields use the specified unit comparison.
Source: Bhatt--Scholze 6.8.4(1), 6.8.11(3), 6.8.14, Remark 6.8.15
(blueprint: lem-per-tate-twist-lisse-line).
Proof: rationalize perTateIntegralScalarModel; the normalization fixes every integral
arrow and hence every fraction. For equal stages replace ordinary scalar extension by
its normalized multiplication unit. The ordinary scalar tower equations, transported
through sfIntegralOrdinaryComparison, give pairFunctorCoherent. Descent on morphism
representatives yields the common-stage comparison; its inverse is constructed from
the inverse coefficient equivalence by the same formulas, proving IsEquivalence.
The inverse-limit comparison identifies the rational degree-zero PBC line with the
intrinsic stage line. For twisting, tensor scalar extension commutes with the root
transition maps, tensor powers and duals. Its pure-tensor comparisons obey the same
unit and tower equations, so the finite-stage pbcTateRational functors descend with
exactly the object function pbcTateTwist and the displayed stage restrictions.
perTateIntegralTensor rationalizes to the finite-stage tensor comparison. The canonical
common-stage tensor comparisons carry it to the descended natural isomorphism.
Their tower equations remove the choice of the finite model of the line, proving the
assertion for every F. Empty schemes, zero complexes, and identity extensions are
included by the same unit and zero-coordinate normalizations. -/
theorem perTateCommonTensor :
    ∃ b : ∀ {F G : Padic.FiniteCoefficientFields l Ω} (h : F ≤ G),
      perTateRationalStageModel l X Ω F ⋙
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h ≅
        (pbcScalarSystem l Ω X hDim.out hInv.out).T h ⋙ perTateRationalStageModel l X Ω G,
      (∀ (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G) (_hne : F ≠ G)
        (K : pbcIntegralStage l Ω X F),
        HEq ((b h).inv.app ((pbcStageLocalization l Ω X F).obj K))
          ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω G) X).map
            ((perTateIntegralScalarModel l X Ω h).inv.app K))) ∧
      (∀ F : Padic.FiniteCoefficientFields l Ω,
        HEq (b (le_refl F))
          (Functor.isoWhiskerLeft (perTateRationalStageModel l X Ω F)
              (GeneralAlgebraicallyClosedCoefficients.unitor l Ω X F) ≪≫
            Functor.rightUnitor (perTateRationalStageModel l X Ω F) ≪≫
            (Functor.leftUnitor (perTateRationalStageModel l X Ω F)).symm)) ∧
      ∃ hb : CategoryTheory.StageSystem.pairFunctorCoherent
          (pbcScalarSystem l Ω X hDim.out hInv.out)
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X)
          (perTateRationalStageModel l X Ω) b,
        let T := perTateCommonModel l X Ω b hb
        T.IsEquivalence ∧
        (∀ (F : Padic.FiniteCoefficientFields l Ω) (m : ℤ),
          Nonempty
            (T.obj ⟨F, (pbcStageLocalization l Ω X F).obj
                (perTatePbcLine l X (pbcFiniteField.{u} l Ω F) m)⟩ ≅
              perTateCommonLine l X Ω F m)) ∧
        ∀ m : ℤ, ∃ U : pbcQbarCategory l Ω X ⥤ pbcQbarCategory l Ω X,
          (∀ K : pbcQbarCategory l Ω X, U.obj K = pbcTateTwist l X Ω K m) ∧
          (∀ F : Padic.FiniteCoefficientFields l Ω,
            (pbcScalarSystem l Ω X hDim.out hInv.out).ι F ⋙ U =
              pbcTateRational l X Ω F m ⋙
                (pbcScalarSystem l Ω X hDim.out hInv.out).ι F) ∧
          ∀ F : Padic.FiniteCoefficientFields l Ω,
            Nonempty
              (U ⋙ T ≅ T ⋙
                tateTensorRight (commonStageDerivedTensor l Ω X)
                  (perTateCommonLine l X Ω F m)) := by
  sorry

end AlgebraicCoefficients

end AlgebraicGeometry.Scheme
