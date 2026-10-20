/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Paper.FiniteCoefficientReductionFlatModel
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ExceptionalCoefficientComparison
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

/-! # Finite coefficient change for internal Hom

Source: blueprint sec-six-functors/sk-prop-sf-biduality-general,
node thm-coef-finite-hom (blueprint: def-sf-etale-finite-coefficient-hom-arrow).
Indices n and m below denote exponents n + 1 and m + 1; thus every positive
exponent, including the identity quotient, occurs. All comparison maps are
closed transposes of reduced evaluation, never choices of arbitrary arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u a b w c d e f g
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Right-tensor adjunction obtained from the published internal Hom and braiding.
Source: blueprint tensor-Hom adjunction (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomRightAdjunction {C : Type a} [Category.{b} C] [MonoidalCategory C]
    [BraidedCategory C] [MonoidalClosed C] (P : C) :
    tensorRight P ⊣ Prod.sectR (op P) C ⋙
      Functor.uncurry.obj (MonoidalClosed.internalHom (C := C)) :=
  ((ihom.adjunction P).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight P)).ofNatIsoRight
    (((Functor.currying (C := Cᵒᵖ) (D := C) (E := C)).unitIso.app
      (MonoidalClosed.internalHom (C := C))).app (op P))


/-- Naturality of the right-tensor evaluation obtained by symmetry.
Source: blueprint evaluation paragraph (blueprint: def-sf-etale-finite-coefficient-hom-arrow).
Proof: move the braiding across the internal-Hom map by naturality, then use
internalHomAdjunction₂'s counit naturality in its parameter. -/
theorem finiteHomEvaluation_naturality
    {C : Type a} [Category.{b} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] (P P' Q : C) (f : P' ⟶ P) :
    (tensorRight P').map ((Functor.uncurry.obj (MonoidalClosed.internalHom (C := C))).map
        (Prod.mkHom f.op (𝟙 Q))) ≫
      ((finiteHomRightAdjunction P').counit.app Q) =
    (tensorLeft ((ihom P).obj Q)).map f ≫
      ((finiteHomRightAdjunction P).counit.app Q) := by
  sorry


/-- The existing closed structure, with Hom tensor P evaluation order.
Source: blueprint tensor-Hom adjunction paragraph
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomClosed {C : Type a} [Category.{b} C] [MonoidalCategory C]
    [BraidedCategory C] [MonoidalClosed C] :
    CoefficientClosedStructure (Functor.uncurry.obj (MonoidalClosed.internalHom (C := C))) where
  monoidal := inferInstance
  adjunction := finiteHomRightAdjunction
  evaluation_naturality := finiteHomEvaluation_naturality

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The actual positive-level etale category.
Source: blueprint coefficient convention (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev finiteHomEtale (n : ℕ) :=
  Etale.DerivedCategoryModule (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X

/-- The etale derived category uses the published small morphism universe.
Source: blueprint etale size convention (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
@[instance_reducible] def finiteHomEtaleCategory (n : ℕ) :
    Category.{u + 1} (finiteHomEtale l E X n) := inferInstance

attribute [instance] finiteHomEtaleCategory

/-- Canonical quotient A_(n + 1) to A_(m + 1).
Source: blueprint coefficient convention (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev finiteHomQuotient {n m : ℕ} (h : m ≤ n) :=
  Scheme.flatModelReductionCoefficientMap l E (m + 1) (n + 1) (Nat.add_le_add_right h 1)

/-- The published Koszul isomorphism, computed before coefficient specialization.
Source: Stacks 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomKoszulIso (C : Type a)
    [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (P Q : DerivedCategory C) :=
  letI : HasColimitsOfShape ℤ C := HasColimitsOfSize.has_colimits_of_shape ℤ
  letI : HasExactColimitsOfShape ℤ C := hasExactColimitsOfShape_int C
  letI : ∀ T : C, PreservesColimitsOfShape ℤ (tensorLeft T) := fun T ↦
    letI : PreservesColimitsOfSize.{0, 0} (tensorLeft T) :=
      (ihom.adjunction T).leftAdjoint_preservesColimits
    PreservesColimitsOfSize.preservesColimitsOfShape
  letI : ∀ T : C, PreservesColimitsOfShape ℤ (tensorRight T) := fun T ↦
    preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight T)
  DerivedMonoidal.braiding' DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) P Q

/-- The braid structure is fixed componentwise by the actual Koszul isomorphism.
Source: Stacks 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow).
Proof: use the published derived braiding, whose components are these isomorphisms.
Naturality and the hexagons descend from complexes. Equality of all components
and proof irrelevance give uniqueness. -/
theorem finiteHomDerivedBraiding_existsUnique (C : Type a)
    [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] :
    ∃! S : BraidedCategory (DerivedCategory C),
      ∀ P Q : DerivedCategory C, HEq (S.braiding P Q) (finiteHomKoszulIso C P Q) := by
  sorry

/-- The uniquely normalized Koszul braid structure.
Source: Stacks 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
@[instance_reducible] def finiteHomDerivedBraiding (C : Type a)
    [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] :=
  (finiteHomDerivedBraiding_existsUnique C).choose

/-- Right-tensor adjunction on the published etale derived Hom.
Source: blueprint evaluation paragraph (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleRightAdjunctionGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) (P : DerivedCategory (Sheaf W.smallEtaleTopology A)) :=
  letI := finiteHomDerivedBraiding (Sheaf W.smallEtaleTopology A)
  finiteHomRightAdjunction P

/-- The closed record has the published tensor and the specified right adjunction.
Source: blueprint tensor-Hom paragraph (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def FiniteHomEtaleClosedNormalization
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u})
    (S : CoefficientClosedStructure (Functor.uncurry.obj (Etale.derivedHom A W))) : Prop :=
  S.monoidal = (inferInstance : MonoidalCategory (DerivedCategory
    (Sheaf W.smallEtaleTopology A))) ∧
  ∀ P : DerivedCategory (Sheaf W.smallEtaleTopology A),
    HEq (S.adjunction P) (finiteHomEtaleRightAdjunctionGeneral A W P)

/-- Existence and uniqueness of the normalized closed record.
Source: blueprint tensor-Hom paragraph (blueprint: def-sf-etale-finite-coefficient-hom-arrow).
Proof: use the published derived monoidal instance and the specified braiding of
its tensor-Hom adjunction. Naturality of evaluation supplies the last field.
The normalization fixes both data fields; all remaining fields are propositions. -/
theorem finiteHomEtaleClosed_existsUnique
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) : ∃! S, FiniteHomEtaleClosedNormalization A W S := by
  sorry

/-- The uniquely normalized etale closed structure, before specializing coefficients.
Source: blueprint tensor-Hom paragraph (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleClosedGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) := (finiteHomEtaleClosed_existsUnique A W).choose

/-- Closed etale structure for an arbitrary coefficient ring.
Source: blueprint tensor-Hom paragraph (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleClosedRing (R : Type (u + 1)) [CommRing R] (W : Scheme.{u}) :=
  finiteHomEtaleClosedGeneral (ModuleCat.{u + 1} R) W

/-- Shared closed and tensor data for the positive coefficient quotient diagram.
Source: blueprint successive quotient comparisons
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
structure FiniteHomQuotientClosedData
    (C : ℕ → Type a) [∀ n : ℕ, Category.{b} (C n)]
    (H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n)
    (F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m) where
  closed : ∀ n : ℕ, CoefficientClosedStructure (H n)
  tensor : ∀ {n m : ℕ} (h : m ≤ n),
    (closed n).tensor ⋙ F h ≅ (F h).prod (F h) ⋙ (closed m).tensor

/-- The canonical transpose within shared quotient data.
Source: blueprint definition of v (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def FiniteHomQuotientClosedData.comparison
    {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
    {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m}
    (S : FiniteHomQuotientClosedData C H F) {n m : ℕ} (h : m ≤ n) :=
  coefficientBaseChangeHom (S.closed n) (S.closed m) (F h) (S.tensor h)

/-- The published etale Hom, with its contravariant first input.
Source: blueprint derived Hom (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev finiteHomEtaleInternalHom (n : ℕ) :=
  Functor.uncurry.obj (Etale.derivedHom (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X)

/-- Derived scalar extension in the recorded etale presentation.
Source: blueprint definition of T_B (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev finiteHomEtaleReduction {n m : ℕ} (h : m ≤ n) :=
  Etale.scalarExtension (finiteHomQuotient l E h) X

/-- A closed family is fixed by its canonical records, with all category data shared.
Source: blueprint evaluation normalization
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def FiniteHomClosedFamilyNormalizationAux
    {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
    {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m}
    (S : FiniteHomQuotientClosedData C H F)
    {V : ℕ → Type (max a b)} (v : ∀ n : ℕ, V n) : Prop :=
  ∀ n : ℕ, HEq (S.closed n) (v n)

/-- A scalar tensor family is fixed by its published isomorphisms.
Source: blueprint scalar tensor normalization
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def FiniteHomTensorFamilyNormalizationAux
    {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
    {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m}
    (S : FiniteHomQuotientClosedData C H F)
    {V : ∀ {n m : ℕ}, m ≤ n → Type (max a b)}
    (v : ∀ {n m : ℕ} (h : m ≤ n), V h) : Prop :=
  ∀ (n m : ℕ) (h : m ≤ n), HEq (S.tensor h) (v h)

/-- The canonical derived closed record, specialized without changing its data.
Source: blueprint tensor-Hom adjunction (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleClosedWitnessRing (R : Type (u + 1)) [CommRing R] (W : Scheme.{u}) :=
  finiteHomEtaleClosedRing R W

/-- The canonical closed record at every positive coefficient level.
Source: blueprint tensor-Hom adjunction (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleClosedWitness (n : ℕ) :=
  finiteHomEtaleClosedWitnessRing
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X

/-- The published tensor isomorphism at every positive quotient.
Source: blueprint scalar tensor normalization
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev finiteHomEtaleTensorWitness {n m : ℕ} (h : m ≤ n) :=
  Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E h) X

/-- The canonical normalization fixes every data field of the coefficient diagram.
Source: blueprint evaluation and scalar tensor maps
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
structure FiniteHomEtaleDataNormalization
    (S : FiniteHomQuotientClosedData (finiteHomEtale l E X)
      (finiteHomEtaleInternalHom l E X) (finiteHomEtaleReduction l E X)) : Prop where
  closed : FiniteHomClosedFamilyNormalizationAux S (finiteHomEtaleClosedWitness l E X)
  tensor : FiniteHomTensorFamilyNormalizationAux S (finiteHomEtaleTensorWitness l E X)

/-- The coefficient diagram has uniquely normalized closed and tensor data.
Source: blueprint evaluation and coefficient-change paragraphs
(blueprint: def-sf-etale-finite-coefficient-hom-arrow).
Proof: use the canonical derived closed structure and the published scalar tensor
isomorphisms. The site's tensor and Hom are their underlying functors, so these
components have the required types. Heterogeneous equality fixes each field;
function extensionality and record extensionality prove uniqueness. -/
theorem finiteHomEtaleData_existsUnique :
    ∃! S, FiniteHomEtaleDataNormalization l E X S := by
  sorry

/-- The canonical etale coefficient diagram, with every data field fixed.
Source: blueprint evaluation and coefficient-change paragraphs
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleData := (finiteHomEtaleData_existsUnique l E X).choose

/-- The canonical closed structure at one coefficient level.
Source: blueprint tensor-Hom adjunction (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleClosed (n : ℕ) :
    CoefficientClosedStructure (finiteHomEtaleInternalHom l E X n) :=
  (finiteHomEtaleData l E X).closed n

/-- The published canonical scalar tensor comparison.
Source: blueprint coefficient change (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleTensor {n m : ℕ} (h : m ≤ n) :
    (finiteHomEtaleClosed l E X n).tensor ⋙ finiteHomEtaleReduction l E X h ≅
      (finiteHomEtaleReduction l E X h).prod (finiteHomEtaleReduction l E X h) ⋙
        (finiteHomEtaleClosed l E X m).tensor :=
  (finiteHomEtaleData l E X).tensor h

/-- The etale arrow is exactly the closed transpose of reduced evaluation.
Source: blueprint definition of v (blueprint: def-sf-etale-finite-coefficient-hom-arrow).
The body is the evaluation-defined `coefficientBaseChangeHom`; it does not
select an unconstrained arrow from an existence theorem. -/
abbrev etaleFiniteHomCanonical {n m : ℕ} (h : m ≤ n)
    (K M : finiteHomEtale l E X n) :
    (finiteHomEtaleReduction l E X h).obj
        ((finiteHomEtaleInternalHom l E X n).obj (op K, M)) ⟶
      (finiteHomEtaleInternalHom l E X m).obj
        (op ((finiteHomEtaleReduction l E X h).obj K),
          (finiteHomEtaleReduction l E X h).obj M) :=
  coefficientBaseChangeHom (finiteHomEtaleClosed l E X n)
    (finiteHomEtaleClosed l E X m) (finiteHomEtaleReduction l E X h)
    (finiteHomEtaleTensor l E X h) K M

/-- The intrinsic pro-etale arrow is the published normalized quotient transpose.
Source: blueprint definition of v (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev proEtaleFiniteHomCanonical {n m : ℕ} (h : m ≤ n)
    (K M : normalizedDVRDerived l E X n) := finiteIntrinsicReductionHom l E X h K M

/-- The canonical reassociation of intrinsic scalar extensions, as a left-adjoint mate.
Source: blueprint quotient cocycle (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomIntrinsicAssoc {n m r : ℕ} (h : m ≤ n) (k : r ≤ m) :=
  Adjunction.leftAdjointCompIso
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h)
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction k)
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction
      (k.trans h)) (normalizedDVRResComp l E X h k)

/-- Quotient maps compose as the actual quotient factor homomorphisms.
Source: blueprint quotient cocycle (blueprint: def-sf-etale-finite-coefficient-hom-arrow).
Proof: lift to the valuation ring using quotient induction; both composites send
an element to its residue class at exponent r + 1. -/
theorem finiteHomQuotient_comp {n m r : ℕ} (h : m ≤ n) (k : r ≤ m) :
    finiteHomQuotient l E (k.trans h) =
      (finiteHomQuotient l E k).comp (finiteHomQuotient l E h) := by
  sorry

/-- The canonical etale scalar associator, with quotient-factor equality.
Source: blueprint quotient cocycle (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleAssoc {n m r : ℕ} (h : m ≤ n) (k : r ≤ m) :=
  ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology
    (finiteHomQuotient l E h) (finiteHomQuotient l E k)
    (finiteHomQuotient l E (k.trans h)) (finiteHomQuotient_comp l E h k)


/-- Small coproducts of etale module sheaves, exposed before totalizing complexes.
Source: Stacks 06YN (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
instance finiteHomEtaleSmallColimits (R : Type (u + 1)) [CommRing R] (W : Scheme.{u}) :
    HasColimitsOfSize.{0, 0} (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  hasColimitsOfSizeShrink _

/-- Every pair of etale module complexes has its signed total tensor product.
Source: Stacks 06YN (blueprint: def-sf-etale-finite-coefficient-hom-arrow).
Proof: module-valued sheaves have small coproducts. In each integer degree the
required coproduct is indexed by the set of pairs of integers with prescribed sum,
which is small. These coproducts provide HasMapBifunctor and hence HasTensor. -/
@[instance] theorem finiteHomEtaleHasTensor
    (R : Type (u + 1)) [CommRing R] (W : Scheme.{u})
    (P Q : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ) :
    HomologicalComplex.HasTensor P Q := by
  sorry

/-- The ordinary sheaf tensor generator before deriving.
Source: blueprint pure-tensor comparison; Stacks 03EK
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleTensorSection (n : ℕ)
    (M N : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))
    (U : X.Etale) (x : M.obj.obj (op U)) (y : N.obj.obj (op U)) :
    (M ⊗ N).obj.obj (op U) :=
  ((Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) M N).app (op U))
      (x ⊗ₜ y)

/-- Inclusion of one signed-total-tensor summand with shared monoidal data.
Source: Stacks 06YN (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomTensorInclusionGeneral
    {C : Type a} [Category.{b} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    (p q k : ℤ) (h : p + q = k) :
    P.X p ⊗ Q.X q ⟶ (HomologicalComplex.tensorObj P Q).X k :=
  HomologicalComplex.ιTensorObj P Q p q k h

/-- Localization in the published small etale derived category.
Source: blueprint etale size convention (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev finiteHomEtaleQ (n : ℕ) :
    CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ ⥤
      finiteHomEtale l E X n := DerivedCategory.Q

/-- Localization in the recorded intrinsic standard derived category.
Source: blueprint intrinsic size convention
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomIntrinsicQ (n : ℕ) :
    CochainComplex (normalizedDVRModules l E X n) ℤ ⥤ normalizedDVRDerived l E X n :=
  letI := HasDerivedCategory.standard (normalizedDVRModules l E X n)
  DerivedCategory.Q

/-- Tensor representatives with all category and functor data kept shared.
Source: blueprint tensor representative calculation
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
structure FiniteHomQuotientClosedData.Representatives
    {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
    {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m}
    (S : FiniteHomQuotientClosedData C H F)
    (A : ℕ → Type c) [∀ n : ℕ, Category.{d} (A n)]
    (Q : ∀ n : ℕ, A n ⥤ C n) (T : ∀ n : ℕ, A n → A n → A n)
    (I : Type e) (V : I → Type f) where
  generator : ∀ i : I, V i
  model : ∀ (n : ℕ) (P R : A n),
    (S.closed n).tensor.obj ((Q n).obj P, (Q n).obj R) ⟶ (Q n).obj (T n P R)

/-- A local pair of sections in a prescribed total-tensor degree.
Source: blueprint pure-tensor site formula
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
structure FiniteHomEtaleTensorSectionInput where
  n : ℕ
  P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ
  Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ
  p : ℤ
  q : ℤ
  k : ℤ
  h : p + q = k
  U : X.Etale
  x : (P.X p).obj.obj (op U)
  y : (Q.X q).obj.obj (op U)

/-- The actual total tensor object of two etale cochain complexes.
Source: Stacks 06YN (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev finiteHomEtaleTotalObject (n : ℕ)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) :=
  HomologicalComplex.tensorObj P Q

/-- The carrier in which a prescribed total-tensor generator lies.
Source: Stacks 06YN (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev finiteHomEtaleTensorSectionCarrier (i : FiniteHomEtaleTensorSectionInput l E X) :
    Type (u + 1) :=
  ((finiteHomEtaleTotalObject l E X i.n i.P i.Q).X i.k).obj.obj (op i.U)

/-- Canonical generators and localization tensorators in the recorded etale categories.
Source: blueprint pure-tensor site formula
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
abbrev FiniteHomEtaleRepresentativeData :=
  (finiteHomEtaleData l E X).Representatives
    (fun n : ℕ ↦ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ)
    (finiteHomEtaleQ l E X) (finiteHomEtaleTotalObject l E X)
    (FiniteHomEtaleTensorSectionInput l E X) (finiteHomEtaleTensorSectionCarrier l E X)

/-- Both representative maps are fixed by existing tensor constructions.
Source: blueprint pure-tensor site formula
(blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
structure FiniteHomEtaleRepresentativeNormalization
    (S : FiniteHomEtaleRepresentativeData l E X) : Prop where
  generator : ∀ i : FiniteHomEtaleTensorSectionInput l E X,
    HEq (S.generator i)
      (((finiteHomTensorInclusionGeneral i.P i.Q i.p i.q i.k i.h).hom.app (op i.U))
        (finiteHomEtaleTensorSection l E X i.n (i.P.X i.p) (i.Q.X i.q) i.U i.x i.y))
  model : ∀ (n : ℕ)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ),
    HEq (S.model n P Q) (Functor.LaxMonoidal.μ (finiteHomEtaleQ l E X n) P Q)

/-- The local generators and localization tensorator determine the representative data.
Source: Stacks 06YN, 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow).
Proof: define totalSection by the ordinary sheaf tensor generator followed by the
actual total-summand inclusion. The closed normalization identifies its tensor
with the published derived tensor. Transport the localization tensorator along
that equality to define tensorModel. These constructions give the stated
heterogeneous equalities. Each equality fixes a field value; function and record
extensionality therefore prove uniqueness of the entire representative family. -/
theorem finiteHomEtaleRepresentativeData_existsUnique :
    ∃! S, FiniteHomEtaleRepresentativeNormalization l E X S := by
  sorry

/-- The uniquely specified local generators and localization tensorator.
Source: blueprint site formula (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleRepresentativeData :=
  (finiteHomEtaleRepresentativeData_existsUnique l E X).choose

/-- The actual total-tensor generator, fixed by its total-summand inclusion.
Source: Stacks 06YN (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleTotalSection (n : ℕ)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ)
    (p q k : ℤ) (h : p + q = k) (U : X.Etale)
    (x : (P.X p).obj.obj (op U)) (y : (Q.X q).obj.obj (op U)) :=
  (finiteHomEtaleRepresentativeData l E X).generator ⟨n, P, Q, p, q, k, h, U, x, y⟩

/-- The actual localization tensorator with the normalized closed-tensor endpoint.
Source: Stacks 07A4 (blueprint: def-sf-etale-finite-coefficient-hom-arrow). -/
def finiteHomEtaleTensorModel (n : ℕ)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) :=
  (finiteHomEtaleRepresentativeData l E X).model n P Q


end WeilConjectures
