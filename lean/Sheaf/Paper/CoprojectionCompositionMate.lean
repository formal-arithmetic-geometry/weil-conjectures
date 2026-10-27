/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.PurityCoprojection
public import Sheaf.Paper.StandingExceptionalComposition
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Adjunction.Basic

import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.FiniteCoefficientTensorCtf
import Sheaf.Algebra.Homology.DerivedTensor
import Sheaf.Paper.FiniteFieldFiber
import Sheaf.Paper.FiniteTorAmplitude
import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.Paper.SfDerivedComplete
import Sheaf.Paper.FiniteCompactSupportConstructibility
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.DerivedPullbackTensorIso
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.PfRefinementCompatibility
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
import Sheaf.Paper.IntegralFinitePullbackComposition
import WeilConjectures.Compactification.NagataCompactification
import Sheaf.SixFunctors.CompositionProjectionMate

/-!
# Composition of co-projection mates

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
  sk-thm-regular/sk-thm-regular.proof.md, Step 4(ii)
(blueprint: lem-pur-coprojection-composition-mate).

The maps below use the specified projection, evaluation-normalized tensor adjunction,
and standing exceptional Hom bijection. The harmless zero extension outside the standing
bounded constructible domain makes their ambient types independent of domain witnesses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v w t
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The finite coefficient pro-etale derived category.
Source: blueprint finite purity conventions (blueprint: lem-pur-coprojection-composition-mate). -/
abbrev purityDerived (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} P.Coefficient))

/-- Cache the published K-flat pullback with its generic coefficient instances.
Source: blueprint derived operations (blueprint: lem-pur-coprojection-composition-mate). -/
def coprojectionDerivedPullback (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {S T : Scheme.{u}} (h : S ⟶ T) :=
  (upperStar C h).leftDerivedFunctor

/-- The canonical finite-coefficient pullback compositor used by the composition
statement. It is induced by the published upperStarComp construction and its
K-flat derivation; no comparison isomorphism is supplied as extra data. It is the
fixed-scalar form of the recorded comparison of
lem-weil-pbc-proetale-derived-pullback-composition.
Source: Stacks Project, Tags 0D6D and 03D3
(blueprint: lem-pur-coprojection-composition-mate). -/
abbrev purityFinitePullbackComposition (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (upperStar (ModuleCat.{u + 1} A) (f ≫ g)).leftDerivedFunctor ≅
      (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor ⋙
        (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor :=
  leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g

/-- Cache the actual derived tensor unit before specializing coefficients.
Source: finite purity derived tensor (blueprint: lem-pur-coprojection-composition-mate). -/
def coprojectionDerivedUnit (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (T : Scheme.{u}) :=
  𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology T) C))

/-- Cache the entire inverse-data type at generic coefficient instances.
This is exactly TensorInvertibleData for the published derived tensor and its unit.
Source: pur9-cs-def-invertible (blueprint: lem-pur-coprojection-composition-mate). -/
def coprojectionInverseData (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (T : Scheme.{u}) (N : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)) :=
  TensorInvertibleData (fun B D ↦ ((derivedTensor C T).obj B).obj D)
    (coprojectionDerivedUnit C T) N

/-- Freeze tensor objects to keep homology-domain inference from expanding K-flat totals.
This is the published derived tensor, with no change of mathematical object.
Source: derived tensor clause (blueprint: lem-pur-coprojection-composition-mate). -/
@[irreducible]
def coprojectionTensorObj (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (T : Scheme.{u}) (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology T) C) :=
  ((derivedTensor C T).obj M).obj N

/-- The actual derived tensor object in finite coefficient coordinates.
Source: derived tensor clause (blueprint: lem-pur-coprojection-composition-mate). -/
abbrev purityTensorObject (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (M N : purityDerived P T) :=
  coprojectionTensorObj (ModuleCat.{u + 1} P.Coefficient) T M N

/-- The specified tensor product of two morphisms, cached at general coefficients.
Source: tensor clause in the composition equation
(blueprint: lem-pur-coprojection-composition-mate). -/
def coprojectionDerivedTensorMap (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (T : Scheme.{u})
    {M M' N N' : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)}
    (a : M ⟶ M') (b : N ⟶ N') :
    coprojectionTensorObj C T M N ⟶ coprojectionTensorObj C T M' N' := by
  unfold coprojectionTensorObj
  exact a ⊗ₘ b

/-- The K-flat derived pullback, with its published canonical composition comparison.
Source: blueprint derived operations (blueprint: lem-pur-coprojection-composition-mate). -/
abbrev purityPullback (P : WeilConjectures.PurityFiniteSetting.{u})
    {S T : Scheme.{u}} (h : S ⟶ T) : purityDerived P T ⥤ purityDerived P S :=
  coprojectionDerivedPullback (ModuleCat.{u + 1} P.Coefficient) h

/-- The source-implied compactification is supplied internally.
Source: blueprint exceptional inverse image (blueprint: lem-pur-coprojection-composition-mate). -/
abbrev purityExceptional (P : WeilConjectures.PurityFiniteSetting.{u})
    {S T : Scheme.{u}} (h : S ⟶ T)
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] :
    purityDerived P T ⥤ purityDerived P S := by
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  letI := isNoetherian_of_locallyOfFiniteType aT
  letI := isNoetherian_of_locallyOfFiniteType (h ≫ aT)
  letI : HasCompactification h := inferInstance
  exact rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) h

/-- The tensor adjunction normalized to the chosen evaluation counit.
Equivalence.mk corrects the initial unit while retaining the evaluation counit.
The braiding is used only for the opposite evaluation in that adjointification.
Source: lem-weil-pbc-quasi-inverse-adjoint
(blueprint: lem-pur-coprojection-composition-mate). -/
def coprojectionTensorAdjunction (C : Type v) [Category.{u} C]
    [MonoidalCategory C] [b : BraidedCategory C] {N : C}
    (d : TensorInvertibleData (fun B D ↦ B ⊗ D) (𝟙_ C) N) :
    MonoidalCategory.tensorRight d.inverse ⊣ MonoidalCategory.tensorRight N :=
  (tensorRightEquivalenceOfTensorIso ((β_ d.inverse N) ≪≫ d.iso) d.iso).toAdjunction

/-- The actual upstream tensor comparison, retaining its cached coefficient instances.
Source: def-exchange-projection, mu (blueprint: lem-pur-coprojection-composition-mate). -/
def coprojectionTensorComparison (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [hFlat : UpperStarPreservesFlat C] {S T : Scheme.{u}} (h : S ⟶ T)
    (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)) :=
  (leftDerivedUpperStarTensorIso C h M N).symm

/-- The actual upstream unit comparison in the same cached presentation.
Source: def-exchange-projection, unit (blueprint: lem-pur-coprojection-composition-mate). -/
def coprojectionUnitComparison (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {S T : Scheme.{u}} (h : S ⟶ T) :=
  leftDerivedUpperStarUnitIso C h

/-- Pull back the chosen inverse with the published monoidal comparisons.
Source: def-exchange-projection, mu (blueprint: lem-pur-coprojection-composition-mate). -/
def coprojectionPullbackInverse (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [hFlat : UpperStarPreservesFlat C] {S T : Scheme.{u}} (h : S ⟶ T)
    {N : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)}
    (d : coprojectionInverseData C T N) :
    coprojectionInverseData C S ((coprojectionDerivedPullback C h).obj N) :=
  ⟨(coprojectionDerivedPullback C h).obj d.inverse,
    coprojectionTensorComparison C h N d.inverse ≪≫
      (coprojectionDerivedPullback C h).mapIso d.iso ≪≫
      coprojectionUnitComparison C h⟩

/-- The actual projectionMap in its original cached tensor presentation.
Source: def-exchange-projection (blueprint: lem-pur-coprojection-composition-mate). -/
def coprojectionProjectionComponent (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [hFlat : UpperStarPreservesFlat C] {S T : Scheme.{u}} (h : S ⟶ T)
    [HasCompactification h]
    (U : DerivedCategory (Sheaf (Scheme.ProEt.topology S) C))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)) :=
  ((projectionMap C h).app U).app M

/-- Assemble the tensor mate of a projection component and an exceptional counit.
The callers below supply the published maps, rather than quantify over replacements.
Source: the displayed kappa composite, Step 4(ii)
(blueprint: lem-pur-coprojection-composition-mate). -/
def coprojectionTensorMate {C : Type v} {D : Type u} [Category.{w} C] [Category.{t} D]
    [MonoidalCategory C] [MonoidalCategory D] [b : BraidedCategory D]
    (F : C ⥤ D) (Q : D ⥤ C) {N : D}
    (d : TensorInvertibleData (fun B E ↦ B ⊗ E) (𝟙_ D) N)
    (L : C) (K : D) (e : Q.obj N ⊗ Q.obj d.inverse ≅ 𝟙_ C)
    (pf : F.obj (L ⊗ Q.obj N) ⊗ d.inverse ⟶
      F.obj ((L ⊗ Q.obj N) ⊗ Q.obj d.inverse))
    (eps : F.obj L ⟶ K) : F.obj (L ⊗ Q.obj N) ⟶ K ⊗ N :=
  (coprojectionTensorAdjunction D d).unit.app (F.obj (L ⊗ Q.obj N)) ≫
    (pf ▷ N) ≫
    (F.map ((α_ L (Q.obj N) (Q.obj d.inverse)).hom ≫ L ◁ e.hom ≫ (ρ_ L).hom) ▷ N) ≫
    (eps ▷ N)

/-- The explicit tensor mate using precisely the published pro-etale PF and mu.
All tensor operations are assembled at generic coefficient instances before specialization.
Source: the displayed kappa composite, Step 4(ii)
(blueprint: lem-pur-coprojection-composition-mate). -/
def coprojectionProEtaleTensorMateRepresentative (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [hFlat : UpperStarPreservesFlat C] {S T : Scheme.{u}} (h : S ⟶ T)
    [HasCompactification h]
    {N : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)}
    (d : TensorInvertibleData (fun B D ↦ B ⊗ D) (𝟙_ _) N)
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology S) C))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C))
    (eps : (rightDerivedLowerShriek C h).obj L ⟶ K) :
    (rightDerivedLowerShriek C h).obj (L ⊗ (coprojectionDerivedPullback C h).obj N) ⟶
      K ⊗ N :=
  coprojectionTensorMate (b := DerivedCategory.braidedCategory' _)
    (rightDerivedLowerShriek C h) (coprojectionDerivedPullback C h) d L K
    (coprojectionTensorComparison C h N d.inverse ≪≫
      (coprojectionDerivedPullback C h).mapIso d.iso ≪≫ coprojectionUnitComparison C h)
    (coprojectionProjectionComponent C h (L ⊗ (coprojectionDerivedPullback C h).obj N)
      d.inverse) eps

/-- The specified tensor mate in the published cached tensor coordinates.
Source: displayed kappa construction, Step 4(ii)
(blueprint: lem-pur-coprojection-composition-mate).
Proof: unfold derivedTensor and coprojectionDerivedUnit in the displayed endpoints.
They are precisely the tensor and unit of the derived monoidal structure used by the
representative. First transport the inverse datum itself, obtaining the unique d'
with HEq d' d. Then transport the explicit representative map, obtaining the displayed
HEq. Both HEq conditions determine all their data, proving uniqueness. No projection or evaluation
map is chosen by endpoints alone.
-/
theorem coprojectionProEtaleTensorMate_existsUnique (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [hFlat : UpperStarPreservesFlat C] {S T : Scheme.{u}} (h : S ⟶ T)
    [HasCompactification h]
    {N : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)}
    (d : coprojectionInverseData C T N)
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology S) C))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C))
    (eps : (rightDerivedLowerShriek C h).obj L ⟶ K) :
    ∃! m : (rightDerivedLowerShriek C h).obj
      (coprojectionTensorObj C S L ((coprojectionDerivedPullback C h).obj N)) ⟶
        coprojectionTensorObj C T K N,
      ∃ d' : TensorInvertibleData (fun B D ↦ B ⊗ D)
          (𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology T) C))) N,
        HEq d' d ∧ HEq m (coprojectionProEtaleTensorMateRepresentative C h d' L K eps) := by
  sorry

/-- The unique fixed-coordinate form of the explicit upstream PF tensor mate.
Source: displayed kappa construction, Step 4(ii)
(blueprint: lem-pur-coprojection-composition-mate). -/
def coprojectionProEtaleTensorMate (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [hFlat : UpperStarPreservesFlat C] {S T : Scheme.{u}} (h : S ⟶ T)
    [HasCompactification h]
    {N : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)}
    (d : coprojectionInverseData C T N)
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology S) C))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C))
    (eps : (rightDerivedLowerShriek C h).obj L ⟶ K) :
    (rightDerivedLowerShriek C h).obj
      (coprojectionTensorObj C S L ((coprojectionDerivedPullback C h).obj N)) ⟶
        coprojectionTensorObj C T K N :=
  (coprojectionProEtaleTensorMate_existsUnique C h d L K eps).exists.choose

/-- Cache the inverse standing Hom bijection before substituting tensor objects.
This is the recorded standing comparison, with no replacement adjunction.
Source: pur9-def-upper-shriek-composition, standing counit normalization
(blueprint: lem-pur-coprojection-composition-mate). -/
def coprojectionStandingHomInverse (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {S T : Scheme.{u}} (h : S ⟶ T) [HasCompactification h] [CompactSpace T]
    {U : DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} Λ))}
    {V : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))}
    (hU : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) S U)
    (hV : DerivedCategory.TStructure.t.plus V)
    (k : U ⟶ (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) h).obj V) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) h).obj U ⟶ V :=
  (standingExceptionalHomEquiv Λ h (K := U) (L := V) hU hV).symm k

/-- The specified exceptional counit: inverse standing Hom image of the identity.
Source: pur9-def-upper-shriek-composition, standing counit normalization
(blueprint: lem-pur-coprojection-composition-mate). -/
def coprojectionStandingCounit (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {S T : Scheme.{u}} (h : S ⟶ T) [HasCompactification h] [CompactSpace T]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.TStructure.t.plus K) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) h).obj
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) h).obj K) ⟶ K :=
  coprojectionStandingHomInverse Λ h
    (plusEtaleOrigin_rightDerivedUpperShriek_obj h hK) hK (𝟙 _)

/-- Characterize kappa by its exact inverse standing Hom image.
The tensor-mate map is specified above. Outside the standing domain, the value is zero.
Source: displayed kappa definition, Step 4(ii)
(blueprint: lem-pur-coprojection-composition-mate). -/
def coprojectionKappaProperty (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [UpperStarPreservesFlat (ModuleCat.{u + 1} Λ)]
    {S T : Scheme.{u}} (h : S ⟶ T) [HasCompactification h] [CompactSpace T]
    {N : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))}
    (d : coprojectionInverseData (ModuleCat.{u + 1} Λ) T N)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)))
    (k : coprojectionTensorObj (ModuleCat.{u + 1} Λ) S
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) h).obj K)
      ((coprojectionDerivedPullback (ModuleCat.{u + 1} Λ) h).obj N) ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) h).obj
        (coprojectionTensorObj (ModuleCat.{u + 1} Λ) T K N)) : Prop :=
  let A := ModuleCat.{u + 1} Λ
  let G := rightDerivedUpperShriek A h
  let U := coprojectionTensorObj A S (G.obj K) ((coprojectionDerivedPullback A h).obj N)
  let V := coprojectionTensorObj A T K N
  (∀ (hK : DerivedCategory.TStructure.t.plus K)
    (hV : DerivedCategory.TStructure.t.plus V)
    (hU : DerivedCategory.plusEtaleOrigin A S U),
    HEq (coprojectionStandingHomInverse Λ h (U := U) (V := V) hU hV k)
      (coprojectionProEtaleTensorMate A h d (G.obj K) K
        (coprojectionStandingCounit Λ h K hK))) ∧
    ((¬DerivedCategory.TStructure.t.plus K ∨ ¬DerivedCategory.TStructure.t.plus V ∨
      ¬DerivedCategory.plusEtaleOrigin A S U) → k = 0)

/-- Existence and uniqueness for the node's prescribed exceptional transpose.
Source: displayed kappa definition and standing Hom bijection, Step 4(ii)
(blueprint: lem-pur-coprojection-composition-mate).
Proof: if all three standing domain predicates hold, the fixed tensor-mate composite
has source F(U) and target K tensor N. Apply the recorded standing Hom bijection to it.
Its inverse recovers that exact composite, giving the first clause. Proof irrelevance
makes the result independent of all domain witnesses. Injectivity of that bijection
proves uniqueness. If a domain predicate fails, choose zero; the first clause is
vacuous and the second clause forces every witness to be zero. These cases exhaust
all inputs, without introducing an ambient exceptional adjunction.
-/
theorem coprojectionStandingKappa_existsUnique (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [UpperStarPreservesFlat (ModuleCat.{u + 1} Λ)]
    {S T : Scheme.{u}} (h : S ⟶ T) [HasCompactification h] [CompactSpace T]
    {N : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))}
    (d : coprojectionInverseData (ModuleCat.{u + 1} Λ) T N)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))) :
    ∃! k : coprojectionTensorObj (ModuleCat.{u + 1} Λ) S
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) h).obj K)
      ((coprojectionDerivedPullback (ModuleCat.{u + 1} Λ) h).obj N) ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) h).obj
        (coprojectionTensorObj (ModuleCat.{u + 1} Λ) T K N),
      coprojectionKappaProperty Λ h d K k := by
  sorry

/-- The unique prescribed exceptional transpose; all map data is fixed by its property.
Source: displayed kappa definition, Step 4(ii)
(blueprint: lem-pur-coprojection-composition-mate). -/
def coprojectionStandingKappa (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [UpperStarPreservesFlat (ModuleCat.{u + 1} Λ)]
    {S T : Scheme.{u}} (h : S ⟶ T) [HasCompactification h] [CompactSpace T]
    {N : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))}
    (d : coprojectionInverseData (ModuleCat.{u + 1} Λ) T N)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))) :
    coprojectionTensorObj (ModuleCat.{u + 1} Λ) S
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) h).obj K)
      ((coprojectionDerivedPullback (ModuleCat.{u + 1} Λ) h).obj N) ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) h).obj
        (coprojectionTensorObj (ModuleCat.{u + 1} Λ) T K N) :=
  (coprojectionStandingKappa_existsUnique Λ h d K).exists.choose

/-- The prescribed double mate with the source-implied standing finite-level choices.
PF, the evaluation-normalized tensor unit, the pulled-back evaluation, and the
standing exceptional counit are all constructed; no map is a parameter.
Source: displayed kappa definition, Step 4(ii)
(blueprint: lem-pur-coprojection-composition-mate). -/
def purityKappa (P : WeilConjectures.PurityFiniteSetting.{u})
    {S T : Scheme.{u}} (h : S ⟶ T)
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    {N : purityDerived P T}
    (d : coprojectionInverseData (ModuleCat.{u + 1} P.Coefficient) T N)
    (K : purityDerived P T) :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  letI : UpperStarPreservesFlat (ModuleCat.{u + 1} P.Coefficient) := by
    let : IsNoetherianRing P.Coefficient :=
      isNoetherian_of_finite P.Coefficient P.Coefficient
    exact upperStarPreservesFlat_moduleCat P.Coefficient
  letI := isNoetherian_of_locallyOfFiniteType aT
  letI := isNoetherian_of_locallyOfFiniteType (h ≫ aT)
  letI : HasCompactification h := inferInstance
  letI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace aT
  coprojectionStandingKappa P.Coefficient h d K

/-- The inverse of the prescribed kappa component when invertible.
Source: lem-pur-coprojection and the node's inverse clause
(blueprint: lem-pur-coprojection-composition-mate). -/
def purityCoProjection (P : WeilConjectures.PurityFiniteSetting.{u})
    {S T : Scheme.{u}} (h : S ⟶ T)
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    {N : purityDerived P T}
    (d : coprojectionInverseData (ModuleCat.{u + 1} P.Coefficient) T N)
    (K : purityDerived P T) (ha : IsIso (purityKappa P h aT d K)) :
    (purityExceptional P h aT).obj (purityTensorObject P T K N) ⟶
      purityTensorObject P S ((purityExceptional P h aT).obj K) ((purityPullback P h).obj N) := by
  letI := ha
  exact inv (purityKappa P h aT d K)

section Composition
variable (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]

/-- The recorded standing exceptional comparison, extended by zero off Dbc.
Its value on every object in the theorem's finite-Tor domain is literally the recorded c.
Source: pur9-def-upper-shriek-composition
(blueprint: lem-pur-coprojection-composition-mate). -/
def purityExceptionalComposition (K : purityDerived P Z) :
    (purityExceptional P (f ≫ g) (Z ↘ Spec (.of P.field.k))).obj K ⟶
      (purityExceptional P f (Y ↘ Spec (.of P.field.k))).obj
        ((purityExceptional P g (Z ↘ Spec (.of P.field.k))).obj K) := by
  classical
  if hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) Z K then
    exact standingExceptionalComposition P f g ⟨K, hK⟩
  else exact 0

/-- Composition compatibility of the specified projection mates, and its inverse form.
Source: sk-thm-regular Step 4(ii), with the compatible tower of Stacks Tag 0F7J
(blueprint: lem-pur-coprojection-composition-mate).

Proof:
1. Write $F_h=Rh_!$, $H_h=Rh^!$, $p_h=Lh^*$, and suppress only canonical tensor associators and
unitors. All tensor inverses below are inverse data for the invertible object in $D^b_{ctf}$. By
[lem-sf-pullback-tor-amplitude] and [lem-sf-tensor-ctf], pulling back an inverse or tensoring
any bounded constructible object with it stays bounded constructible, and stays finite-Tor when
both factors are finite-Tor. By [prop-finite-compact-support-constructibility], $F_h$ carries
bounded constructible objects to bounded constructible objects. The constructible exceptional
adjunctions and finite-Tor preservation are those specified in
[def-weil-exceptional-inverse-image]. Thus every subsequent Hom bijection can be used on bounded
constructible objects; no right adjoint on the arbitrary ambient pro-etale category is used. The
tensor comparisons of [lem-pur-derived-pullback-tensor-iso] carry inverse evaluations to inverse
evaluations and respect composition.

2. For an invertible $N$ on $T$ with evaluation $e:N\otimes N'\to A_T$, put $T_M(Q)=Q\otimes M$.
Tensoring with $N'$ and with $N$ gives quasi-inverse functors: the inverse identifications are
obtained by the associators, $e$, and the symmetry. Apply [lem-weil-pbc-quasi-inverse-adjoint]
with prescribed counit $T_{N'}T_N(Q)=(Q\otimes N)\otimes N'\xrightarrow{1\otimes e}Q$. It
supplies the normalized adjunction $T_{N'}\dashv T_N$. Write $u:A_T\to N'\otimes N$ for its unit
at $A_T$; its unit at $Q$ is $1_Q\otimes u$, with associators. Equivalently $u$ is uniquely
specified by $(e\otimes1_N)(1_N\otimes u)=1_N$ and $(1_{N'}\otimes e)(u\otimes1_{N'})=1_{N'}$.
Applying the strong monoidal $p_h$ carries these two equations to the same equations on $S$
[lem-pur-derived-pullback-tensor-iso], so it gives the normalized adjunction $T_{p_hN'}\dashv
T_{p_hN}$.

3. Regard $\operatorname{PF}_{h,(-),N'}:T_{N'}F_h\to F_hT_{p_hN'}$ as a square whose horizontal
adjunctions are $T_{p_hN'}\dashv T_{p_hN}$ and $T_{N'}\dashv T_N$, and whose two vertical
functors are $F_h$. Its square mate [def-weil-pbc-adjunction-mate] is a natural transformation
$b_h:F_hT_{p_hN}\to T_NF_h$. The unit/counit recipe gives its component at $P$ explicitly as
$$F_h(P\otimes p_hN)\xrightarrow{\eta^N}(F_h(P\otimes p_hN)\otimes N')\otimes
N\xrightarrow{\operatorname{PF}_{h,P\otimes p_hN,N'}\otimes1}F_h(P\otimes p_hN\otimes
p_hN')\otimes N\xrightarrow{F_h(1\otimes p_he)\otimes1}F_hP\otimes N.$$ Here the last evaluation
uses the specified $\mu_h$ [def-exchange-projection], and the first arrow is the normalized unit
of step 2. This establishes the actual transformation, including its direction and sign, rather
than an arbitrary map between its source and target.

4. Take the square mate of $b_h:F_hT_{p_hN}\to T_NF_h$ across the two copies of $F_h\dashv H_h$.
By [def-weil-pbc-adjunction-mate] it is $T_{p_hN}H_h\to H_hT_N$, with transpose
$(\varepsilon_{h,K}\otimes1_N)b_{h,H_hK}$. Substituting step 3 is exactly the displayed defining
composite for $\kappa_{h,K,N}$. This also proves naturality. For clarity, the induced map on Hom
sets is $$\operatorname{Hom}(P,H_hK\otimes p_hN)\cong\operatorname{Hom}(P\otimes
p_hN',H_hK)\cong\operatorname{Hom}(F_h(P\otimes
p_hN'),K)\xrightarrow{(-)\circ\operatorname{PF}_{h,P,N'}}\operatorname{Hom}(F_hP\otimes
N',K)\cong\operatorname{Hom}(P,H_h(K\otimes N)).$$ The composite adjunction rule
[def-weil-pbc-composite-adjunction] and the iterated-square identity
[lem-trf-iterated-square-mates] show that this is precisely conjugation of
$\operatorname{PF}_{h,(-),N'}$ under the two composite adjunctions.

5. The construction is independent of inverse data. If $(M',d)$ is another inverse of $N$, write
$v:A_T\to M'\otimes N$ for its normalized coevaluation. The inverse-comparison isomorphism is
$$a:N'\xrightarrow{1\otimes d^{-1}}N'\otimes N\otimes M'\xrightarrow{u^{-1}\otimes1}M'.$$ The
two triangle identities in step 2 give $d(1_N\otimes a)=e$ and $(a\otimes1_N)u=v$; inserting the
analogous expression with $N',M'$ interchanged cancels successive unit/counit pairs and gives
$a^{-1}$. This is the usual unique comparison of the inverse tensor adjunctions
[det-sp-unique-right-adjoint]. Naturality of $\operatorname{PF}$ in its coefficient input
[def-exchange-projection] makes its square at $a:N'\to M'$ commute. In the expression of step 3
the inserted $a$ from the unit and the inverse $a$ from evaluation therefore cancel. Thus both
choices give the same $b_h$, and hence the same $\kappa_h$ by the bijection in
[def-weil-pbc-adjunction-mate].

6. Let $F=F_gF_f$ and $H=H_fH_g$. The composite adjunction [def-weil-pbc-composite-adjunction]
has counit $\varepsilon_{g,K}\,F_g(\varepsilon_{f,H_gK})$. By the definition of $c$
[pur9-def-upper-shriek-composition], $$\varepsilon_{g,K}\,F_g(\varepsilon_{f,H_gK})\,F(c_K)=\var
epsilon_{gf,K}\,\alpha_{g,f,H_{gf}K}.$$ The isomorphism $\alpha_{g,f}$ of
[thm-sf-comp-composition] transports the adjunction for $F_{gf}$ to a right adjunction for $F$.
Both $H_{gf}$ and $H$ are therefore right adjoints of this same $F$ on the stated bounded
constructible categories. The counit equation just written identifies $c$ with the unique
comparison [det-sp-unique-right-adjoint], so it is a natural isomorphism. This uses the standing
constructible adjunctions, without assuming a separate ambient six-functor datum.

7. Choose a compatible compactification tower for $f,g$. Such a tower exists: finite-type
schemes over $k$ are Noetherian by [lem-weil-pbc-finite-type-over-noetherian] (the field has
only the ideals $0,k$), hence quasi-compact, and are quasi-separated by
[lem-weil-pbc-locally-noetherian-quasi-separated]; [thm-nagata-compactification] compactifies
$g$, and [lem-weil-pbc-compatible-compactification-triangle] supplies the required tower for
$f$. The finite-coefficient clause of [lem-sf-composition-projection-mate], with its input
called $P$ and coefficient input $N'$, gives the actual equation $$\alpha_{P\otimes p_fp_gN'}\,F
_g(\operatorname{PF}_{f,P,p_gN'})\,\operatorname{PF}_{g,F_fP,N'}=\operatorname{PF}_{gf,P,N'}(\al
pha_P\otimes1_{N'}).$$ Here and below $\alpha=\alpha_{g,f}$. This is the projection identity for
the canonical compact-support compositor, not an inference from abstract isomorphy of its ends.

8. The tower equation of step 7 holds for the chosen compact-support functors in the statement
as well. Indeed every tensor input in that equation is bounded constructible by step 1, so has
an etale-origin witness by [lem-sf-proetale-constructible-origin]. For each of $f,g,gf$,
[lem-pur-pf-refinement-compatibility] says exactly that the compactification comparison
intertwines these projection transformations, also for two choices through a common refinement.
The compositor $\alpha$ is independent of choices under the same comparisons by
[thm-sf-comp-composition]. Conjugating the equation in step 7 by those comparisons cancels the
comparisons at the intermediate objects. Finally [lem-pur-derived-pullback-tensor-iso] and
[lem-weil-pbc-proetale-derived-pullback-composition] identify $p_{gf}N'$ with $p_fp_gN'$ and
identify their evaluations and normalized tensor units. Thus the two sides now use the specified
maps of the item on exactly the same objects.

9. First take mates of the equation in step 7 across the tensor-inverse adjunctions of step 2.
Clause (1) of [lem-weil-pbc-mate-pasting] applies to the two squares of step 3 for $f,g$: their
common tensor adjunction on $Y$ is $T_{p_gN'}\dashv T_{p_gN}$, so their pasted mate is
$(b_gF_f)(F_gb_f)$. The two occurrences of $\alpha$ change the vertical functors, not the tensor
adjunctions, so clause (3) is not what is used here. Directly from the unit/counit formula of
[def-weil-pbc-adjunction-mate]: if a square $\gamma:L_2G\to HL_1$ is followed by $\sigma L_1$
for $\sigma:H\to H'$, its mate becomes $(R_2\sigma)\gamma^\flat$, by naturality of the unit
$\eta_2$; if it is preceded by $L_2\sigma'$ for $\sigma':G'\to G$, its mate becomes
$\gamma^\flat(\sigma'R_1)$, by naturality of the counit $\varepsilon_1$. With $\sigma=\alpha$
(left side, $H=F_gF_f$, $H'=F_{gf}$) and $\sigma'=\alpha$ (right side, $G'=F_gF_f$, $G=F_{gf}$)
this gives the factors $T_N\alpha=\alpha\otimes1_N$ and $\alpha T_{p_{gf}N}$. Hence the equation
is $$b_{gf,P}\,\alpha_{P\otimes p_{gf}N}=(\alpha_P\otimes1_N)\,b_{g,F_fP}\,F_g(b_{f,P}).$$ Its
source is $F_gF_f(P\otimes p_fp_gN)$ and its target is $F_{gf}P\otimes N$. The tensor adjunction
on $X$ uses $p_fp_gN'$, identified with $p_{gf}N'$ by step 8. Since the mate correspondence is a
bijection [def-weil-pbc-adjunction-mate], the equality is retained without an invertibility
assumption on any projection component.

10. Now take mates across the exceptional adjunctions. Clause (2) of
[lem-weil-pbc-mate-pasting], with $L_1=L_2=F_f$, $L_3=L_4=F_g$ and vertical functors
$T_{p_fp_gN},T_{p_gN},T_N$, says that the mate of $(b_gF_f)(F_gb_f)$ is
$(H_f\kappa_g)(\kappa_fH_g)$. The mate of the compositor $\alpha:F_gF_f\to F_{gf}$ is
$c:H_{gf}\to H_fH_g$ by step 6. Clause (3) of the same lemma therefore sends the two whiskerings
by $\alpha$ in step 9 to the two whiskerings by $c$. Substitution yields $$c_{K\otimes
N}\,\kappa_{gf,K,N}=H_f(\kappa_{g,K,N})\,\kappa_{f,H_gK,p_gN}\,(c_K\otimes\mathrm{can}).$$ The
composite adjunction here has the pasted counit of [def-weil-pbc-composite-adjunction], exactly
as used to define $c$, so no alternate normalization is introduced. Inserting the
identifications $\mathrm{can}$ and $\mu$ of step 8 between $p_{gf}N$ and $p_fp_gN$ (with their
evaluations and normalized units) gives the first asserted equality.

11. When $h$ is a closed immersion, [lem-pur-coprojection] defines its co-projection to be the
right-adjoint comparison induced by the projection isomorphism at $N'$. Step 4 identifies
$\kappa_h$ with the conjugate of that same projection transformation in the reverse direction.
By [def-weil-pbc-adjunction-conjugate], conjugation carries an inverse to the inverse conjugate,
so $\kappa_h^{-1}$ is precisely this co-projection. More generally, under the last clause's
explicit invertibility assumptions, multiply the equation of step 10 on the left by
$\kappa_{f,H_gK,p_gN}^{-1}H_f(\kappa_{g,K,N}^{-1})$ and on the right by $\kappa_{gf,K,N}^{-1}$.
Functors preserve inverses, and the adjacent inverse pairs cancel, leaving $$(c_K\otimes\mathrm{
can})\operatorname{coProj}_{gf,K,N}=\operatorname{coProj}_{f,H_gK,p_gN}\,H_f(\operatorname{coPro
j}_{g,K,N})\,c_{K\otimes N},$$ which is the second asserted equality.
-/
theorem purityCoprojectionCompositionMate
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (N : purityDerived P Z)
    (d : coprojectionInverseData (ModuleCat.{u + 1} P.Coefficient) Z N)
    (K : purityDerived P Z)
    (_hK : WeilConjectures.finiteTorConstructibleProEtaleModule
      P.coefficients.l P.extension P.level P.level_pos Z K)
    (_hN : WeilConjectures.finiteTorConstructibleProEtaleModule
      P.coefficients.l P.extension P.level P.level_pos Z N)
    (_hN' : WeilConjectures.finiteTorConstructibleProEtaleModule
      P.coefficients.l P.extension P.level P.level_pos Z d.inverse) :
    (purityKappa P (f ≫ g) (Z ↘ Spec (.of P.field.k)) d K ≫
        purityExceptionalComposition P f g (purityTensorObject P Z K N) =
      (coprojectionDerivedTensorMap (ModuleCat.{u + 1} P.Coefficient) X
          (purityExceptionalComposition P f g K)
          ((purityFinitePullbackComposition P.Coefficient f g).hom.app N)) ≫
        purityKappa P f (Y ↘ Spec (.of P.field.k))
          (coprojectionPullbackInverse (ModuleCat.{u + 1} P.Coefficient)
          (hFlat := by
            let : Finite P.Ring := Padic.finite_coefficientExtensionRing
              P.coefficients.l P.extension P.level P.level_pos
            let : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
            let : IsNoetherianRing P.Coefficient :=
              isNoetherian_of_finite P.Coefficient P.Coefficient
            exact upperStarPreservesFlat_moduleCat P.Coefficient) g d)
          ((purityExceptional P g (Z ↘ Spec (.of P.field.k))).obj K) ≫
        (purityExceptional P f (Y ↘ Spec (.of P.field.k))).map
          (purityKappa P g (Z ↘ Spec (.of P.field.k)) d K)) ∧
    (∀ (hgf : IsIso (purityKappa P (f ≫ g) (Z ↘ Spec (.of P.field.k)) d K))
      (hg : IsIso (purityKappa P g (Z ↘ Spec (.of P.field.k)) d K))
      (hf : IsIso (purityKappa P f (Y ↘ Spec (.of P.field.k))
          (coprojectionPullbackInverse (ModuleCat.{u + 1} P.Coefficient)
          (hFlat := by
            let : Finite P.Ring := Padic.finite_coefficientExtensionRing
              P.coefficients.l P.extension P.level P.level_pos
            let : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
            let : IsNoetherianRing P.Coefficient :=
              isNoetherian_of_finite P.Coefficient P.Coefficient
            exact upperStarPreservesFlat_moduleCat P.Coefficient) g d)
        ((purityExceptional P g (Z ↘ Spec (.of P.field.k))).obj K))),
      purityCoProjection P (f ≫ g) (Z ↘ Spec (.of P.field.k)) d K hgf ≫
          (coprojectionDerivedTensorMap (ModuleCat.{u + 1} P.Coefficient) X
            (purityExceptionalComposition P f g K)
            ((purityFinitePullbackComposition P.Coefficient f g).hom.app N)) =
        purityExceptionalComposition P f g (purityTensorObject P Z K N) ≫
          (purityExceptional P f (Y ↘ Spec (.of P.field.k))).map
            (purityCoProjection P g (Z ↘ Spec (.of P.field.k)) d K hg) ≫
          purityCoProjection P f (Y ↘ Spec (.of P.field.k))
          (coprojectionPullbackInverse (ModuleCat.{u + 1} P.Coefficient)
          (hFlat := by
            let : Finite P.Ring := Padic.finite_coefficientExtensionRing
              P.coefficients.l P.extension P.level P.level_pos
            let : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
            let : IsNoetherianRing P.Coefficient :=
              isNoetherian_of_finite P.Coefficient P.Coefficient
            exact upperStarPreservesFlat_moduleCat P.Coefficient) g d)
            ((purityExceptional P g (Z ↘ Spec (.of P.field.k))).obj K) hf) := by
  sorry

end Composition
end AlgebraicGeometry.ProEtale
