/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributor Q124
-/
module
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.Paper.CoefficientSystemDerivedComparison
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.NumberTheory.Padics.PadicIntegersIntegralClosure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor
import Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Sheaf.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.SystemLevelLeftExtension
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.SemilinearDerivedSections
/-!
# The strict étale coefficient-system adjoint
Source: Zheng, Six Operations and Lefschetz--Verdier, Constructions 5.14--5.15,
Lemmas 5.16 and 5.22, and Proposition 5.24 (blueprint:
lem-pur-etale-coefficient-system-adjoint).
The structure records the actual compact-support system functor, its right adjoint,
the finite-level adjunctions, and the asserted coefficient-system coherences.
* `StrictEtaleCompactSupport` specifies the ordinary and unbounded derived functors.
* `StrictEtaleExceptionalAdjoint` records the exact linear adjoint and finite-level mates.
* `StrictEtaleExceptionalTransport` specifies the scalar and cofinal comparison maps.
* `etaleCoefficientSystemAdjoint` and its scalar/cofinal companions assert existence.
* The identity/composition theorems state coherence with canonical tensor identifications.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry
open SheafOfModules
/-- Reuse the existing ring-sheafification witness once at the concrete etale-site size.
This instance only caches an existing proof, so the constant sheaf construction is unchanged.
Source: Stacks Tag 00W1; Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
instance (priority := 2000) strictEtaleCommRingSheafify (T : Scheme.{u}) :
    HasWeakSheafify T.smallEtaleTopology CommRingCat.{u + 1} := inferInstance
/-- Reuse the existing additive-sheafification witness at the ordinary etale-site size.
Source: Stacks Tag 00W1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
instance (priority := 2000) strictEtaleAddCommGrpSheafify (T : Scheme.{u}) :
    HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1} := inferInstance
/-- Reuse the existing local-bijection characterization for additive sheaves.
Source: Stacks Tag 00W1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
instance (priority := 2000) strictEtaleAddCommGrpLocal (T : Scheme.{u}) :
    T.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance
/-- Reuse the existing forgetful composition witness for constant coefficient rings.
Source: Stacks Tag 03D7
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
instance (priority := 2000) strictEtaleRingCompose (T : Scheme.{u}) :
    T.smallEtaleTopology.HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := inferInstance
/-- Cache the existing set-sheafification witness at the concrete etale-site size.
Source: Stacks Tag 00W1; Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
instance (priority := 2000) strictEtaleTypeSheafify (T : Scheme.{u}) :
    HasWeakSheafify T.smallEtaleTopology (Type (u + 1)) := inferInstance
/-- Cache the existing ring-to-set sheaf composition witness.
Source: Stacks Tag 03D7; Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
instance (priority := 2000) strictEtaleRingSetCompose (T : Scheme.{u}) :
    T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget CommRingCat.{u + 1}) :=
  inferInstance
/-- Cache the existing additive-to-set sheaf composition witness.
Source: Stacks Tag 03D7; Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
instance (priority := 2000) strictEtaleAddCommGrpSetCompose (T : Scheme.{u}) :
    T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  inferInstance
/-- The recorded strict system category on the ordinary étale site.
Source: Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev strictEtaleCoefficientSystem (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O) :=
  CoefficientSystem (J := T.smallEtaleTopology) O ell
/-- The recorded coefficient-level category, with positive exponent `n+1`.
Source: Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev strictEtaleLevel (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O) (n : ℕ) :=
  coefficientLevelModules (J := T.smallEtaleTopology) O ell n
/-- Use Mathlib's standard localization for the strict system category.
Source: Zheng, Construction 4.1; Stacks Tag 05RU
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
@[irreducible]
instance (priority := 100) strictEtaleSystemDerived (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O) :
    HasDerivedCategory.{u + 2} (strictEtaleCoefficientSystem T O ell) :=
  HasDerivedCategory.standard _
/-- Use the same standard localization at every finite coefficient level.
Source: Zheng, Construction 4.1; Stacks Tag 05RU
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
@[irreducible]
instance (priority := 100) strictEtaleLevelDerived (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O) (n : ℕ) :
    HasDerivedCategory.{u + 2} (strictEtaleLevel T O ell n) :=
  HasDerivedCategory.standard _
/-- Specialize the existing levelwise additive witness before elaborating projections
of the evaluation package. No additive structure is changed.
Source: Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
instance (priority := 3000) strictEtaleEvaluationAdditive
    (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O] (ell : O) :
    ∀ n, (coefficientEvaluation.{u + 1, u, u + 1}
      (J := T.smallEtaleTopology) (O := O) (ell := ell) n).Additive :=
  fun n ↦ coefficientEvaluation_additive.{u + 1, u, u + 1} n
/-- The recorded derived evaluation interface at the ordinary etale-site sizes.
Source: Zheng, Construction 4.1 and Lemma 4.10
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleEvaluation (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O] (ell : O) :=
  CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2}
    (J := T.smallEtaleTopology) (O := O) (ell := ell)
/-- The actual set-sheaf adjunction along base change.
Source: Zheng, Constructions 4.1 and 5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev strictEtaleSetAdjunction {T S : Scheme.{u}} (g : T ⟶ S) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
    (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)
/-- The canonical geometric lift already specified by the system-comparison node.
Source: Zheng, Constructions 4.1 and 5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleOrdinaryImage (O : Type (u + 1)) [CommRing O] (ell : O)
    {T S : Scheme.{u}} (g : T ⟶ S) :=
  CoefficientSystemOrdinaryImage (J := S.smallEtaleTopology) (K := T.smallEtaleTopology)
    O ell (Scheme.etaleSetPullback g)
    ((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
      (Type (u + 1)) (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale))
    (strictEtaleSetAdjunction g)
section CoefficientMaps
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] (ell : O) (φ : O →+* O')
/-- The coefficient homomorphism kills the indicated power in the quotient.
Source: Zheng, Construction 4.1 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint).
Proof: the image of the principal ideal generated by `ell^(n+1)` is contained in
that generated by `(φ ell)^(n+1)`, since a ring map preserves powers and products.
Thus its composite with the quotient homomorphism vanishes on that ideal. -/
theorem strictCoefficientMap_kills (n : ℕ) (x : O)
    (hx : x ∈ (Ideal.span ({ell} : Set O)) ^ (n + 1)) :
    Ideal.Quotient.mk ((Ideal.span ({φ ell} : Set O')) ^ (n + 1)) (φ x) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [Ideal.span_singleton_pow] at hx ⊢
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
  apply Ideal.mem_span_singleton.mpr
  exact ⟨φ y, by simp⟩
/-- The actual homomorphism on coefficient quotients.
Source: Zheng, Construction 4.1 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def strictCoefficientRingMap (n : ℕ) :
    O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1) →+*
      O' ⧸ (Ideal.span ({φ ell} : Set O')) ^ (n + 1) :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp φ)
    (strictCoefficientMap_kills ell φ n)
/-- The actual constant-ring sheaf map, not an arbitrary coefficient map.
Source: Zheng, Construction 4.1 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def strictCoefficientSheafMap (T : Scheme.{u}) (n : ℕ) :
    coefficientQuotientSheaf (J := T.smallEtaleTopology) O ell n ⟶
      coefficientQuotientSheaf (J := T.smallEtaleTopology) O' (φ ell) n :=
  (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (strictCoefficientRingMap ell φ n))
end CoefficientMaps
/-- Multiplication by a coefficient on strict and derived systems. Its normalization
is the actual constant-ring sheafification unit and its localization on complexes.
Together with additivity, preservation of this action means `O`-linearity on all Homs.
Source: Zheng, the Brown adjoint after Lemma 5.16
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleScalarActionCoherence (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O)
    (ordinary : O → (𝟭 (strictEtaleCoefficientSystem T O ell) ⟶ 𝟭 _))
    (derived : O → (𝟭 (DerivedCategory (strictEtaleCoefficientSystem T O ell)) ⟶ 𝟭 _)) : Prop :=
    -- ordinaryNormalized
    (∀ r M n (U : T.Etaleᵒᵖ) (x : (M.level n).val.obj U),
      (((ordinary r).app M).app n).val.app U x =
        ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))))).app U
            (Ideal.Quotient.mk _ r)) • x) ∧
    -- representative
    (∀ r K,
      (derived r).app (DerivedCategory.Q.obj K) =
        DerivedCategory.Q.map
          (((ordinary r).mapHomologicalComplex (.up ℤ)).app K))

/-- The coherence predicate for `StrictEtaleScalarAction`, separated from its data to share
its type during kernel checking. It is exactly the displayed canonical diagram equations.
Source: Zheng, Construction 4.1, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleScalarAction (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O) :=
  { record : (O → (𝟭 (strictEtaleCoefficientSystem T O ell) ⟶ 𝟭 _)) ×
      (O → (𝟭 (DerivedCategory (strictEtaleCoefficientSystem T O ell)) ⟶ 𝟭 _)) //
    StrictEtaleScalarActionCoherence T O ell record.1 record.2 }

section
variable (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O)
variable {T O ell}


/-- The specified component of `StrictEtaleScalarAction`.
Source: Zheng, Construction 4.1, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleScalarAction.derived (record : StrictEtaleScalarAction T O ell) :
    O → (𝟭 (DerivedCategory (strictEtaleCoefficientSystem T O ell)) ⟶ 𝟭 _) :=
  record.val.2


end

/-- The additive-sheaf successor transition, forgetting its semilinear coefficient
restriction. Source: Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def strictEtaleTransition {T : Scheme.{u}} {O : Type (u + 1)} [CommRing O] {ell : O}
    (M : strictEtaleCoefficientSystem T O ell) (n : ℕ) :=
  (SheafOfModules.toSheaf.{u + 1} _).map (M.transition n) ≫
    (siteScalarUnderlyingIso.{u + 1, u, u + 1}
      (coefficientQuotientMap (J := T.smallEtaleTopology) O ell (Nat.le_succ n))).hom.app
        (M.level n)
/-- A coefficient change and its index map, fixed on every quotient generator.
Source: Zheng, Construction 4.1 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
structure StrictEtaleCoefficientChange (O O' : Type (u + 1)) [CommRing O] [CommRing O']
    (ell : O) (mu : O') (phi : O →+* O') (index : ℕ →o ℕ) where
  ring : ∀ n, O ⧸ (Ideal.span ({ell} : Set O)) ^ (index n + 1) →+*
    O' ⧸ (Ideal.span ({mu} : Set O')) ^ (n + 1)
  generators : ∀ n x, ring n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (phi x)
/-- The actual induced map on constant coefficient sheaves.
Source: Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleCoefficientChange.sheaf
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) (T : Scheme.{u}) (n : ℕ) :
    coefficientQuotientSheaf (J := T.smallEtaleTopology) O ell (index n) ⟶
      coefficientQuotientSheaf (J := T.smallEtaleTopology) O' mu n :=
  (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (a.ring n))
/-- The recorded universal derived scalar extension at an etale coefficient level.
This abbreviation retains the actual quotient-sheaf tensor/restriction adjunction and
its independent-coefficient K-flat representatives.
Source: Zheng, Construction 4.1 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleLevelScalar
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) (T : Scheme.{u})
     (n : ℕ) :=
  DerivedCoefficientScalarExtension
    (siteCoefficientTensor.{u + 1, u, u + 1} (J := T.smallEtaleTopology) (a.sheaf T n))
    (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose T.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
        RingCat.{u + 1})).map (a.sheaf T n)))
    (siteCoefficientTensorAdj.{u + 1, u, u + 1} (J := T.smallEtaleTopology) (a.sheaf T n))
    (CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientQuotientSheaf (J := T.smallEtaleTopology) O ell (index n)))
/-- Exact extension after the specified reindexing, including all successor maps.
The evaluation isomorphisms and tensor-unit equations fix the ordinary functor on
objects and maps. The factorization and representative equation fix its exact descent.
Source: Zheng, Construction 4.1, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
structure StrictEtaleCoefficientTransportData
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) (T : Scheme.{u})
    (PA : StrictEtaleEvaluation T O ell)
    (PB : StrictEtaleEvaluation T O' mu) where
  ordinary : strictEtaleCoefficientSystem T O ell ⥤ strictEtaleCoefficientSystem T O' mu
  [additive : ordinary.Additive]
  evaluation : ∀ n, ordinary ⋙ coefficientEvaluation
    (J := T.smallEtaleTopology) (O := O') (ell := mu) n ≅
    coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) (index n) ⋙
      siteCoefficientTensor.{u + 1, u, u + 1} (J := T.smallEtaleTopology) (a.sheaf T n)
  unit : ∀ n, coefficientEvaluation (J := T.smallEtaleTopology)
    (O := O) (ell := ell) (index n) ⋙ SheafOfModules.toSheaf.{u + 1} _ ⟶
    ordinary ⋙ coefficientEvaluation (J := T.smallEtaleTopology)
      (O := O') (ell := mu) n ⋙ SheafOfModules.toSheaf.{u + 1} _
  derived : DerivedCategory (strictEtaleCoefficientSystem T O ell) ⥤
    DerivedCategory (strictEtaleCoefficientSystem T O' mu)
  factors : DerivedCategory.Q ⋙ derived ≅
    ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  level : ∀ n, StrictEtaleLevelScalar a T n
  derivedEvaluation : ∀ n, derived ⋙ PB.evaluation n ≅
    PA.evaluation (index n) ⋙ (level n).derived


attribute [instance] StrictEtaleCoefficientTransportData.additive

/-- The specified data and canonical coherence of `StrictEtaleCoefficientTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleCoefficientTransportCoherence
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) (T : Scheme.{u})
    (PA : StrictEtaleEvaluation T O ell)
    (PB : StrictEtaleEvaluation T O' mu)
    (record : StrictEtaleCoefficientTransportData a T PA PB) : Prop :=
    -- exact
    (PreservesFiniteLimits record.ordinary ∧ PreservesFiniteColimits record.ordinary) ∧
    -- unit_def
    (∀ n M, (record.unit n).app M =
      siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf T n) (M.level (index n)) ≫
        (SheafOfModules.toSheaf.{u + 1} _).map ((record.evaluation n).inv.app M)) ∧
    -- transition
    (∀ n (M : strictEtaleCoefficientSystem T O ell),
      (record.unit (n + 1)).app M ≫
        strictEtaleTransition (T := T) (O := O') (ell := mu) (record.ordinary.obj M) n =
      coefficientTransitionUnderlying.{u + 1, u, u + 1}
        (J := T.smallEtaleTopology) (O := O) (ell := ell) (index.monotone (Nat.le_succ n))
        (PA.strictTransition (index.monotone (Nat.le_succ n))) M ≫ (record.unit n).app M) ∧
    -- representative
    (∀ n K,
      (record.derivedEvaluation n).hom.app (DerivedCategory.Q.obj K) ≫
        (record.level n).derived.map ((PA.evaluationFactors (index n)).hom.app K) ≫
        (record.level n).counit.app
          (((coefficientEvaluation (J := T.smallEtaleTopology)
            (O := O) (ell := ell) (index n)).mapHomologicalComplex (.up ℤ)).obj K) =
      (PB.evaluation n).map (record.factors.hom.app K) ≫
        (PB.evaluationFactors n).hom.app ((record.ordinary.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (record.evaluation n) (.up ℤ)).hom.app K))

/-- The specified data and canonical coherence of `StrictEtaleCoefficientTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleCoefficientTransport
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) (T : Scheme.{u})
    (PA : StrictEtaleEvaluation T O ell)
    (PB : StrictEtaleEvaluation T O' mu) :=
  { record : StrictEtaleCoefficientTransportData a T PA PB //
    StrictEtaleCoefficientTransportCoherence a T PA PB record }

section
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) (T : Scheme.{u})
    (PA : StrictEtaleEvaluation T O ell)
    (PB : StrictEtaleEvaluation T O' mu)
variable {a T PA PB}

/-- The specified data and canonical coherence of `StrictEtaleCoefficientTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCoefficientTransport.ordinary
    (record : StrictEtaleCoefficientTransport a T PA PB) :=
  record.val.ordinary

/-- The specified data and canonical coherence of `StrictEtaleCoefficientTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCoefficientTransport.additive
    (record : StrictEtaleCoefficientTransport a T PA PB) :=
  record.val.additive


/-- The specified data and canonical coherence of `StrictEtaleCoefficientTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCoefficientTransport.unit (record : StrictEtaleCoefficientTransport a T PA PB) :=
  record.val.unit

/-- The specified data and canonical coherence of `StrictEtaleCoefficientTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCoefficientTransport.derived
    (record : StrictEtaleCoefficientTransport a T PA PB) :=
  record.val.derived

/-- The specified data and canonical coherence of `StrictEtaleCoefficientTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCoefficientTransport.factors
    (record : StrictEtaleCoefficientTransport a T PA PB) :=
  record.val.factors

/-- The specified data and canonical coherence of `StrictEtaleCoefficientTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCoefficientTransport.level (record : StrictEtaleCoefficientTransport a T PA PB) :=
  record.val.level

/-- The specified data and canonical coherence of `StrictEtaleCoefficientTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCoefficientTransport.derivedEvaluation
    (record : StrictEtaleCoefficientTransport a T PA PB) :=
  record.val.derivedEvaluation


end

attribute [instance] StrictEtaleCoefficientTransport.additive
/-- The canonical interchange of scalar extension and quotient tensor. The ordinary
square is fixed by tensor units; the derived square is fixed by the universal counits.
No flatness of a quotient map is imposed.
Source: Zheng, Proposition 2.29(2) and Construction 5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleTransportQuotientCoherence
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index} {T : Scheme.{u}}
    {PA : StrictEtaleEvaluation T O ell} {PB : StrictEtaleEvaluation T O' mu}
    (U : StrictEtaleCoefficientTransport a T PA PB)
    (ordinary : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientTensor (J := T.smallEtaleTopology) (O := O) (ell := ell) (index.monotone h) ⋙
      siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n) ≅
    siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T m) ⋙
      coefficientTensor (J := T.smallEtaleTopology) (O := O') (ell := mu) h)
    (derived : ∀ {m n : ℕ} (h : n ≤ m),
    (PA.scalar (index.monotone h)).derived ⋙ (U.level n).derived ≅
      (U.level m).derived ⋙ (PB.scalar h).derived) : Prop :=
    -- unit
    (∀ {m n : ℕ} (h : n ≤ m) M,
      siteTensorUnitUnderlying.{u + 1, u, u + 1}
          (coefficientQuotientMap (J := T.smallEtaleTopology) O ell (index.monotone h)) M ≫
        siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf T n) _ ≫
        (SheafOfModules.toSheaf.{u + 1} _).map ((ordinary h).hom.app M) =
      siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf T m) M ≫
        siteTensorUnitUnderlying.{u + 1, u, u + 1}
          (coefficientQuotientMap (J := T.smallEtaleTopology) O' mu h) _) ∧
    -- representative
    (∀ {m n : ℕ} (h : n ≤ m) K,
      (derived h).hom.app (DerivedCategory.Q.obj K) ≫
        (PB.scalar h).derived.map ((U.level m).counit.app K) ≫
        (PB.scalar h).counit.app
          ((siteCoefficientTensor.{u + 1, u, u + 1}
            (a.sheaf T m)).mapHomologicalComplex (.up ℤ) |>.obj K) =
      (U.level n).derived.map ((PA.scalar (index.monotone h)).counit.app K) ≫
        (U.level n).counit.app
          ((coefficientTensor (J := T.smallEtaleTopology) (O := O) (ell := ell)
            (index.monotone h)).mapHomologicalComplex (.up ℤ) |>.obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (ordinary h) (.up ℤ)).hom.app K))

/-- The coherence predicate for `StrictEtaleTransportQuotient`, separated from its data to share
its type during kernel checking. It is exactly the displayed canonical diagram equations.
Source: Zheng, Construction 4.1, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleTransportQuotient
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index} {T : Scheme.{u}}
    {PA : StrictEtaleEvaluation T O ell} {PB : StrictEtaleEvaluation T O' mu}
    (U : StrictEtaleCoefficientTransport a T PA PB) :=
  { record : (∀ {m n : ℕ} (h : n ≤ m),
  coefficientTensor (J := T.smallEtaleTopology) (O := O) (ell := ell) (index.monotone h) ⋙
    siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n) ≅
  siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T m) ⋙
    coefficientTensor (J := T.smallEtaleTopology) (O := O') (ell := mu) h) ×
      (∀ {m n : ℕ} (h : n ≤ m),
  (PA.scalar (index.monotone h)).derived ⋙ (U.level n).derived ≅
    (U.level m).derived ⋙ (PB.scalar h).derived) //
    StrictEtaleTransportQuotientCoherence U record.1 record.2 }

section
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index} {T : Scheme.{u}}
    {PA : StrictEtaleEvaluation T O ell} {PB : StrictEtaleEvaluation T O' mu}
    (U : StrictEtaleCoefficientTransport a T PA PB)
variable {U}


/-- The specified component of `StrictEtaleTransportQuotient`.
Source: Zheng, Construction 4.1, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleTransportQuotient.derived (record : StrictEtaleTransportQuotient U) :
    ∀ {m n : ℕ} (h : n ≤ m),
  (PA.scalar (index.monotone h)).derived ⋙ (U.level n).derived ≅
    (U.level m).derived ⋙ (PB.scalar h).derived :=
  record.val.2


end

/-- Forget the tensor-unit maps to the underlying set sheaves.
Source: Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleCoefficientTransport.setUnit
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index} {T : Scheme.{u}}
    {PA : StrictEtaleEvaluation T O ell}
    {PB : StrictEtaleEvaluation T O' mu}
    (U : StrictEtaleCoefficientTransport a T PA PB) (n : ℕ) :=
  whiskerRight (U.unit n)
    (sheafCompose T.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1}))
/-- The specified inverse-image comparison on underlying set sheaves.
Source: Zheng, Constructions 4.1 and 5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def strictEtaleInverseUnderlying {O : Type (u + 1)} [CommRing O] {ell : O}
    {T S : Scheme.{u}} {g : T ⟶ S} (A : StrictEtaleOrdinaryImage O ell g) (n : ℕ) :
    (A.inverse ⋙ coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) n) ⋙
        coefficientUnderlying (J := T.smallEtaleTopology) O ell n ≅
      coefficientEvaluation (J := S.smallEtaleTopology) (O := O) (ell := ell) n ⋙
        (coefficientUnderlying (J := S.smallEtaleTopology) O ell n ⋙
          Scheme.etaleSetPullback g) :=
  isoWhiskerRight (A.inverseEvaluation n) _ ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (A.lift n).moduleUnderlying
/-- Inverse-image transport, fixed by tensor units on the underlying set sheaves.
Its derived comparison is fixed on strict complexes. These equations determine
canonical geometric comparisons and exclude arbitrary natural automorphisms.
Source: Zheng, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleInverseTransportCoherence
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PTA : StrictEtaleEvaluation T O ell}
    {PSA : StrictEtaleEvaluation S O ell}
    {PTB : StrictEtaleEvaluation T O' mu}
    {PSB : StrictEtaleEvaluation S O' mu}
    (UT : StrictEtaleCoefficientTransport a T PTA PTB)
    (US : StrictEtaleCoefficientTransport a S PSA PSB)
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)
    (DA : CoefficientDerivedImage A.inverse A.rightSystem A.systemAdj)
    (DB : CoefficientDerivedImage B.inverse B.rightSystem B.systemAdj)
    (ordinary : US.ordinary ⋙ B.inverse ≅ A.inverse ⋙ UT.ordinary)
    (derived : US.derived ⋙ DB.inverse ≅ DA.inverse ⋙ UT.derived) : Prop :=
    -- normalized
    (∀ n M,
      (UT.setUnit n).app (A.inverse.obj M) ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map
          ((coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n).map
            (ordinary.inv.app M)) ≫
        (strictEtaleInverseUnderlying B n).hom.app (US.ordinary.obj M) =
      (strictEtaleInverseUnderlying A (index n)).hom.app M ≫
        (Scheme.etaleSetPullback g).map ((US.setUnit n).app M)) ∧
    -- representative
    (∀ K,
      derived.hom.app (DerivedCategory.Q.obj K) ≫
        UT.derived.map (DA.inverseFactors.hom.app K) ≫
        UT.factors.hom.app ((A.inverse.mapHomologicalComplex (.up ℤ)).obj K) =
      DB.inverse.map (US.factors.hom.app K) ≫
        DB.inverseFactors.hom.app ((US.ordinary.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app K))

/-- The coherence predicate for `StrictEtaleInverseTransport`, separated from its data to share
its type during kernel checking. It is exactly the displayed canonical diagram equations.
Source: Zheng, Construction 4.1, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleInverseTransport
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PTA : StrictEtaleEvaluation T O ell}
    {PSA : StrictEtaleEvaluation S O ell}
    {PTB : StrictEtaleEvaluation T O' mu}
    {PSB : StrictEtaleEvaluation S O' mu}
    (UT : StrictEtaleCoefficientTransport a T PTA PTB)
    (US : StrictEtaleCoefficientTransport a S PSA PSB)
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)
    (DA : CoefficientDerivedImage A.inverse A.rightSystem A.systemAdj)
    (DB : CoefficientDerivedImage B.inverse B.rightSystem B.systemAdj) :=
  { record : (US.ordinary ⋙ B.inverse ≅ A.inverse ⋙ UT.ordinary) ×
      (US.derived ⋙ DB.inverse ≅ DA.inverse ⋙ UT.derived) //
    StrictEtaleInverseTransportCoherence UT US A B DA DB record.1 record.2 }

section
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PTA : StrictEtaleEvaluation T O ell}
    {PSA : StrictEtaleEvaluation S O ell}
    {PTB : StrictEtaleEvaluation T O' mu}
    {PSB : StrictEtaleEvaluation S O' mu}
    (UT : StrictEtaleCoefficientTransport a T PTA PTB)
    (US : StrictEtaleCoefficientTransport a S PSA PSB)
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)
    (DA : CoefficientDerivedImage A.inverse A.rightSystem A.systemAdj)
    (DB : CoefficientDerivedImage B.inverse B.rightSystem B.systemAdj)
variable {UT US A B DA DB}


/-- The specified component of `StrictEtaleInverseTransport`.
Source: Zheng, Construction 4.1, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleInverseTransport.derived (record : StrictEtaleInverseTransport UT US A B DA DB) :
    US.derived ⋙ DB.inverse ≅ DA.inverse ⋙ UT.derived :=
  record.val.2


end

section FixedCoefficients
variable (O : Type (u + 1)) [CommRing O] (ell : O)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
/-- The termwise open extension and proper direct image, with universal derived images.
The open functor is fixed as the left adjoint of the canonical geometric inverse image.
The equations on ordinary evaluations and Hom transposes fix the system functor and all
its transition maps. The proper derived functor uses the universal K-injective interface.
Source: Zheng, Constructions 5.14--5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
structure StrictEtaleCompactSupportData where
  PX : StrictEtaleEvaluation X O ell
  PY : StrictEtaleEvaluation Y O ell
  PZ : StrictEtaleEvaluation c.Z O ell
  openImage : StrictEtaleOrdinaryImage O ell c.i
  properImage : StrictEtaleOrdinaryImage O ell c.g
  properDerived : CoefficientSystemDerivedImage (J := Y.smallEtaleTopology)
    (K := c.Z.smallEtaleTopology) O ell _ _ _ properImage PY PZ
  openExtension : strictEtaleCoefficientSystem X O ell ⥤
    strictEtaleCoefficientSystem c.Z O ell
  [openAdditive : openExtension.Additive]
  openAdjunction : openExtension ⊣ openImage.inverse
  levelOpen : ∀ n, strictEtaleLevel X O ell n ⥤ strictEtaleLevel c.Z O ell n
  [levelOpenAdditive : ∀ n, (levelOpen n).Additive]
  levelOpenAdjunction : ∀ n, levelOpen n ⊣ (openImage.lift n).modules
  openEvaluation : ∀ n, openExtension ⋙ coefficientEvaluation
    (J := c.Z.smallEtaleTopology) (O := O) (ell := ell) n ≅
    coefficientEvaluation (J := X.smallEtaleTopology) (O := O) (ell := ell) n ⋙ levelOpen n
  derivedOpen : DerivedCategory (strictEtaleCoefficientSystem X O ell) ⥤
    DerivedCategory (strictEtaleCoefficientSystem c.Z O ell)
  openDerived : CoefficientSystemDerivedImage (J := c.Z.smallEtaleTopology)
    (K := X.smallEtaleTopology) O ell _ _ _ openImage PZ PX
  derivedOpenAdjunction : derivedOpen ⊣ openDerived.system.inverse
  openFactors : DerivedCategory.Q ⋙ derivedOpen ≅
    openExtension.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  levelDerivedOpen : ∀ n, DerivedCategory (strictEtaleLevel X O ell n) ⥤
    DerivedCategory (strictEtaleLevel c.Z O ell n)
  levelDerivedOpenAdjunction : ∀ n, levelDerivedOpen n ⊣ (openDerived.level n).inverse
  levelOpenFactors : ∀ n, DerivedCategory.Q ⋙ levelDerivedOpen n ≅
    (levelOpen n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  openDerivedEvaluation : ∀ n, derivedOpen ⋙ PZ.evaluation n ≅
    PX.evaluation n ⋙ levelDerivedOpen n

attribute [instance] StrictEtaleCompactSupportData.openAdditive
  StrictEtaleCompactSupportData.levelOpenAdditive

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleCompactSupportCoherence
    (record : StrictEtaleCompactSupportData O ell c) : Prop :=
    -- openExact
    (PreservesFiniteLimits record.openExtension ∧ PreservesFiniteColimits record.openExtension) ∧
    -- openTranspose
    (∀ n, (record.openImage.inverseEvaluation n).hom =
      (mateEquiv record.openAdjunction (record.levelOpenAdjunction n)
        (.mk _ _ _ _ (record.openEvaluation n).inv)).natTrans) ∧
    -- derivedOpenTranspose
    (∀ P K
      (h : (record.openExtension.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      record.derivedOpenAdjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
        (record.openFactors.hom.app P ≫ DerivedCategory.Q.map h) =
      DerivedCategory.Q.map ((record.openAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P K h) ≫
        record.openDerived.system.inverseFactors.inv.app K) ∧
    -- levelDerivedOpenTranspose
    (∀ n P K
      (h : ((record.levelOpen n).mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      (record.levelDerivedOpenAdjunction n).homEquiv
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
        ((record.levelOpenFactors n).hom.app P ≫ DerivedCategory.Q.map h) =
      DerivedCategory.Q.map
        (((record.levelOpenAdjunction n).mapHomologicalComplex (.up ℤ)).homEquiv P K h) ≫
          (record.openDerived.level n).inverseFactors.inv.app K) ∧
    -- openDerivedEvaluation_rep
    (∀ n K,
      (record.openDerivedEvaluation n).hom.app (DerivedCategory.Q.obj K) ≫
        (record.levelDerivedOpen n).map ((record.PX.evaluationFactors n).hom.app K) ≫
        (record.levelOpenFactors n).hom.app
          (((coefficientEvaluation (J := X.smallEtaleTopology)
            (O := O) (ell := ell) n).mapHomologicalComplex (.up ℤ)).obj K) =
      (record.PZ.evaluation n).map (record.openFactors.hom.app K) ≫
        (record.PZ.evaluationFactors n).hom.app
          ((record.openExtension.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (record.openEvaluation n) (.up ℤ)).hom.app K))

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleCompactSupport :=
  { record : StrictEtaleCompactSupportData O ell c //
    StrictEtaleCompactSupportCoherence O ell c record }

section
variable {O ell c}

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.PX (record : StrictEtaleCompactSupport O ell c) :=
  record.val.PX

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.PY (record : StrictEtaleCompactSupport O ell c) :=
  record.val.PY

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.PZ (record : StrictEtaleCompactSupport O ell c) :=
  record.val.PZ

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.openImage (record : StrictEtaleCompactSupport O ell c) :=
  record.val.openImage

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.properImage (record : StrictEtaleCompactSupport O ell c) :=
  record.val.properImage

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.properDerived (record : StrictEtaleCompactSupport O ell c) :=
  record.val.properDerived








/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.derivedOpen (record : StrictEtaleCompactSupport O ell c) :=
  record.val.derivedOpen

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.openDerived (record : StrictEtaleCompactSupport O ell c) :=
  record.val.openDerived



/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.derivedOpenAdjunction
    (record : StrictEtaleCompactSupport O ell c) :=
  record.val.derivedOpenAdjunction


/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.levelDerivedOpen (record : StrictEtaleCompactSupport O ell c) :=
  record.val.levelDerivedOpen

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.levelDerivedOpenAdjunction
    (record : StrictEtaleCompactSupport O ell c) :=
  record.val.levelDerivedOpenAdjunction


/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.openDerivedEvaluation
    (record : StrictEtaleCompactSupport O ell c) :=
  record.val.openDerivedEvaluation



end


variable {O ell c}
/-- `Rp_* j_!`, as a composite of the specified actual derived functors.
Source: Zheng, Construction 5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleCompactSupport.functor (S : StrictEtaleCompactSupport O ell c) :=
  S.derivedOpen ⋙ S.properDerived.system.direct
/-- The ordinary finite-level compact-support functor in the constant-ring encoding.
Source: Zheng, Construction 5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleCompactSupport.levelFunctor (S : StrictEtaleCompactSupport O ell c) (n : ℕ) :=
  S.levelDerivedOpen n ⋙ (S.properDerived.level n).direct
/-- The canonical evaluated compact-support comparison, constructed from the open and
proper comparisons, rather than selected as an unspecified isomorphism.
Source: Zheng, Lemma 5.16
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleCompactSupport.evaluation (S : StrictEtaleCompactSupport O ell c) (n : ℕ) :
    S.functor ⋙ S.PY.evaluation n ≅ S.PX.evaluation n ⋙ S.levelFunctor n :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (S.properDerived.directEvaluation n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (S.openDerivedEvaluation n) _ ≪≫ Functor.associator _ _ _
variable (O ell c)
/-- The right adjoint with actual evaluated units, counits, and transition mates.
The isomorphisms are uniquely characterized by the two adjunction equations. Quotient
coefficient maps use the recorded universal derived tensor, including nonflat quotients.
Source: Zheng, Lemmas 5.16 and 5.22, Proposition 5.24, and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
structure StrictEtaleExceptionalAdjointData (S : StrictEtaleCompactSupport O ell c) where
  right : DerivedCategory (strictEtaleCoefficientSystem Y O ell) ⥤
    DerivedCategory (strictEtaleCoefficientSystem X O ell)
  [rightAdditive : right.Additive]
  [shift : right.CommShift ℤ]
  adjunction : S.functor ⊣ right
  scalarX : StrictEtaleScalarAction X O ell
  scalarY : StrictEtaleScalarAction Y O ell
  levelRight : ∀ n, DerivedCategory (strictEtaleLevel Y O ell n) ⥤
    DerivedCategory (strictEtaleLevel X O ell n)
  levelAdjunction : ∀ n, S.levelFunctor n ⊣ levelRight n
  evaluation : ∀ n, right ⋙ S.PX.evaluation n ≅ S.PY.evaluation n ⋙ levelRight n
  quotientOpen : ∀ {m n : ℕ} (h : n ≤ m),
    (S.PX.scalar h).derived ⋙ S.levelDerivedOpen n ≅
      S.levelDerivedOpen m ⋙ (S.PZ.scalar h).derived
  quotientProper : ∀ {m n : ℕ} (h : n ≤ m),
    (S.PZ.scalar h).derived ⋙ (S.properDerived.level n).direct ≅
      (S.properDerived.level m).direct ⋙ (S.PY.scalar h).derived
  quotientProjection : ∀ {m n : ℕ} (h : n ≤ m),
    (S.PX.scalar h).derived ⋙ S.levelFunctor n ≅
      S.levelFunctor m ⋙ (S.PY.scalar h).derived
  quotientComparison : ∀ {m n : ℕ} (h : n ≤ m),
    levelRight m ⋙ (S.PX.scalar h).derived ≅
      (S.PY.scalar h).derived ⋙ levelRight n


attribute [instance] StrictEtaleExceptionalAdjointData.rightAdditive
  StrictEtaleExceptionalAdjointData.shift

/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleExceptionalAdjointCoherence (S : StrictEtaleCompactSupport O ell c)
    (record : StrictEtaleExceptionalAdjointData O ell c S) : Prop :=
    -- exact
    (record.right.IsTriangulated) ∧
    -- linear
    (∀ r M, record.right.map ((record.scalarY.derived r).app M) =
      (record.scalarX.derived r).app (record.right.obj M)) ∧
    -- counit
    (∀ n, (record.evaluation n).hom =
      (mateEquiv record.adjunction (record.levelAdjunction n)
        (.mk _ _ _ _ (S.evaluation n).inv)).natTrans) ∧
    -- quotientOpenMate
    (∀ {m n : ℕ} (h : n ≤ m),
      (mateEquiv (S.levelDerivedOpenAdjunction m) (S.levelDerivedOpenAdjunction n)
        (.mk _ _ _ _ (record.quotientOpen h).hom)).natTrans =
      (S.openDerived.derivedTensor h).inv) ∧
    -- quotientProperMate
    (∀ {m n : ℕ} (h : n ≤ m),
      (record.quotientProper h).inv =
      (mateEquiv (S.properDerived.level m).adjunction (S.properDerived.level n).adjunction
        (.mk _ _ _ _ (S.properDerived.derivedTensor h).hom)).natTrans) ∧
    -- quotientProjection_def
    (∀ {m n : ℕ} (h : n ≤ m), record.quotientProjection h =
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (record.quotientOpen h) _ ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (record.quotientProper h) ≪≫
          (Functor.associator _ _ _).symm) ∧
    -- quotientMate
    (∀ {m n : ℕ} (h : n ≤ m),
      (record.quotientComparison h).hom =
      (mateEquiv (record.levelAdjunction m) (record.levelAdjunction n)
        (.mk _ _ _ _ (record.quotientProjection h).hom)).natTrans) ∧
    -- quotientIdentity
    (∀ n M,
      (record.quotientComparison (Nat.le_refl n)).hom.app M ≫
        (record.levelRight n).map ((S.PY.derivedUnit n).hom.app M) =
      (S.PX.derivedUnit n).hom.app ((record.levelRight n).obj M)) ∧
    -- quotientComposition
    (∀ {l m n : ℕ} (h₁ : m ≤ l) (h₂ : n ≤ m) M,
      (S.PX.derivedAssoc h₁ h₂).hom.app ((record.levelRight l).obj M) ≫
        (record.quotientComparison (h₂.trans h₁)).hom.app M =
      (S.PX.scalar h₂).derived.map ((record.quotientComparison h₁).hom.app M) ≫
        (record.quotientComparison h₂).hom.app ((S.PY.scalar h₁).derived.obj M) ≫
        (record.levelRight n).map ((S.PY.derivedAssoc h₁ h₂).hom.app M)) ∧
    -- transition
    (∀ {m n : ℕ} (h : n ≤ m) M,
      (S.PX.scalar h).derived.map ((record.evaluation m).hom.app M) ≫
        (record.quotientComparison h).hom.app ((S.PY.evaluation m).obj M) ≫
        (record.levelRight n).map
          (((S.PY.scalar h).derivedAdj.homEquiv _ _).symm ((S.PY.transition h).app M)) =
      ((S.PX.scalar h).derivedAdj.homEquiv _ _).symm
        ((S.PX.transition h).app (record.right.obj M)) ≫ (record.evaluation n).hom.app M) ∧
    -- bound
    (∃ c_f : ℕ, ∀ (a : ℤ) M, M.IsGE a → (record.right.obj M).IsGE (a - c_f)) ∧
    -- normalized
    (∀ M, (∃ a : ℤ, M.IsGE a) →
      IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
        (J := Y.smallEtaleTopology) O ell S.PY M →
        (∃ a : ℤ, (record.right.obj M).IsGE a) ∧
          IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
            (J := X.smallEtaleTopology) O ell S.PX (record.right.obj M))

/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleExceptionalAdjoint (S : StrictEtaleCompactSupport O ell c) :=
  { record : StrictEtaleExceptionalAdjointData O ell c S //
    StrictEtaleExceptionalAdjointCoherence O ell c S record }

section
variable (S : StrictEtaleCompactSupport O ell c)
variable {O ell c S}

/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalAdjoint.right (record : StrictEtaleExceptionalAdjoint O ell c S) :=
  record.val.right



/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalAdjoint.adjunction
    (record : StrictEtaleExceptionalAdjoint O ell c S) :=
  record.val.adjunction



/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalAdjoint.levelRight
    (record : StrictEtaleExceptionalAdjoint O ell c S) :=
  record.val.levelRight

/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalAdjoint.levelAdjunction
    (record : StrictEtaleExceptionalAdjoint O ell c S) :=
  record.val.levelAdjunction

/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalAdjoint.evaluation
    (record : StrictEtaleExceptionalAdjoint O ell c S) :=
  record.val.evaluation




/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalAdjoint.quotientComparison
    (record : StrictEtaleExceptionalAdjoint O ell c S) :=
  fun {m n : ℕ} (h : n ≤ m) ↦ record.val.quotientComparison h


end

end FixedCoefficients
section Transport
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
  {phi : O →+* O'} {index : ℕ →o ℕ}
  (a : StrictEtaleCoefficientChange O O' ell mu phi index)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
  (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
  (TY : StrictEtaleCoefficientTransport a Y SA.PY SB.PY)
  (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
/-- The canonical compact-support coefficient square, including the open and proper
mates that determine it. Inverse-image squares are normalized by tensor generators.
Source: Zheng, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
structure StrictEtaleCompactSupportTransportData where
  openSquare : StrictEtaleInverseTransport TX TZ SA.openImage SB.openImage
    SA.openDerived.system SB.openDerived.system
  properSquare : StrictEtaleInverseTransport TZ TY SA.properImage SB.properImage
    SA.properDerived.system SB.properDerived.system
  openComparison : TX.derived ⋙ SB.derivedOpen ≅ SA.derivedOpen ⋙ TZ.derived
  properComparison : SA.properDerived.system.direct ⋙ TY.derived ≅
    TZ.derived ⋙ SB.properDerived.system.direct


/-- The specified data and canonical coherence of `StrictEtaleCompactSupportTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleCompactSupportTransportCoherence
    (record : StrictEtaleCompactSupportTransportData a c SA SB TX TY TZ) : Prop :=
    -- openMate
    ((mateEquiv SA.derivedOpenAdjunction SB.derivedOpenAdjunction
      (.mk _ _ _ _ record.openComparison.hom)).natTrans = record.openSquare.derived.inv) ∧
    -- properMate
    (record.properComparison.hom =
      (mateEquiv SA.properDerived.system.adjunction SB.properDerived.system.adjunction
        (.mk _ _ _ _ record.properSquare.derived.hom)).natTrans)

/-- The specified data and canonical coherence of `StrictEtaleCompactSupportTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleCompactSupportTransport :=
  { record : StrictEtaleCompactSupportTransportData a c SA SB TX TY TZ //
    StrictEtaleCompactSupportTransportCoherence a c SA SB TX TY TZ record }

section
variable {a c SA SB TX TY TZ}



/-- The specified data and canonical coherence of `StrictEtaleCompactSupportTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupportTransport.openComparison
    (record : StrictEtaleCompactSupportTransport a c SA SB TX TY TZ) :=
  record.val.openComparison

/-- The specified data and canonical coherence of `StrictEtaleCompactSupportTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupportTransport.properComparison
    (record : StrictEtaleCompactSupportTransport a c SA SB TX TY TZ) :=
  record.val.properComparison


end

variable {a c SA SB TX TY TZ}
/-- Compose the open and proper canonical squares into the compact-support projection
square, retaining its actual map. Source: Zheng, Construction 5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleCompactSupportTransport.projection
    (P : StrictEtaleCompactSupportTransport a c SA SB TX TY TZ) :
    SA.functor ⋙ TY.derived ≅ TX.derived ⋙ SB.functor :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ P.properComparison ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight P.openComparison.symm _ ≪≫
      Functor.associator _ _ _
variable (a c SA SB TX TY TZ)
variable (GA : StrictEtaleExceptionalAdjoint O ell c SA)
  (GB : StrictEtaleExceptionalAdjoint O' mu c SB)
/-- The actual exceptional coefficient comparison. Its transpose is the inverse
compact-support projection followed by the extended counit. Evaluations identify it
with the identical finite-level transpose, including every quotient transition.
Source: Zheng, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
structure StrictEtaleExceptionalTransportData where
  compact : StrictEtaleCompactSupportTransport a c SA SB TX TY TZ
  right : GA.right ⋙ TX.derived ≅ TY.derived ⋙ GB.right
  levelProjection : ∀ n, SA.levelFunctor (index n) ⋙ (TY.level n).derived ≅
    (TX.level n).derived ⋙ SB.levelFunctor n
  levelRight : ∀ n, GA.levelRight (index n) ⋙ (TX.level n).derived ≅
    (TY.level n).derived ⋙ GB.levelRight n
  quotientX : StrictEtaleTransportQuotient TX
  quotientY : StrictEtaleTransportQuotient TY


/-- The specified data and canonical coherence of `StrictEtaleExceptionalTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleExceptionalTransportCoherence
    (record : StrictEtaleExceptionalTransportData a c SA SB TX TY TZ GA GB) : Prop :=
    -- mate
    (record.right.hom = (mateEquiv GA.adjunction GB.adjunction
      (.mk _ _ _ _ record.compact.projection.inv)).natTrans) ∧
    -- projectionEvaluation
    (∀ n K,
      (TY.derivedEvaluation n).hom.app (SA.functor.obj K) ≫
        (TY.level n).derived.map ((SA.evaluation (index n)).hom.app K) ≫
        (record.levelProjection n).hom.app ((SA.PX.evaluation (index n)).obj K) =
      (SB.PY.evaluation n).map (record.compact.projection.hom.app K) ≫
        (SB.evaluation n).hom.app (TX.derived.obj K) ≫
        (SB.levelFunctor n).map ((TX.derivedEvaluation n).hom.app K)) ∧
    -- levelMate
    (∀ n, (record.levelRight n).hom =
      (mateEquiv (GA.levelAdjunction (index n)) (GB.levelAdjunction n)
        (.mk _ _ _ _ (record.levelProjection n).inv)).natTrans) ∧
    -- quotient
    (∀ {m n : ℕ} (h : n ≤ m) M,
      (SB.PX.scalar h).derived.map ((record.levelRight m).hom.app M) ≫
        (GB.quotientComparison h).hom.app ((TY.level m).derived.obj M) ≫
        (GB.levelRight n).map ((record.quotientY.derived h).inv.app M) =
      (record.quotientX.derived h).inv.app ((GA.levelRight (index m)).obj M) ≫
        (TX.level n).derived.map ((GA.quotientComparison (index.monotone h)).hom.app M) ≫
        (record.levelRight n).hom.app ((SA.PY.scalar (index.monotone h)).derived.obj M)) ∧
    -- rightEvaluation
    (∀ n M,
      (TX.derivedEvaluation n).hom.app (GA.right.obj M) ≫
        (TX.level n).derived.map ((GA.evaluation (index n)).hom.app M) ≫
        (record.levelRight n).hom.app ((SA.PY.evaluation (index n)).obj M) =
      (SB.PX.evaluation n).map (record.right.hom.app M) ≫
        (GB.evaluation n).hom.app (TY.derived.obj M) ≫
        (GB.levelRight n).map ((TY.derivedEvaluation n).hom.app M))

/-- The specified data and canonical coherence of `StrictEtaleExceptionalTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleExceptionalTransport :=
  { record : StrictEtaleExceptionalTransportData a c SA SB TX TY TZ GA GB //
    StrictEtaleExceptionalTransportCoherence a c SA SB TX TY TZ GA GB record }

section
variable {a c SA SB TX TY TZ GA GB}


/-- The specified data and canonical coherence of `StrictEtaleExceptionalTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalTransport.right
    (record : StrictEtaleExceptionalTransport a c SA SB TX TY TZ GA GB) :=
  record.val.right






end

end Transport
/-- Ordinary etale exceptional adjoint on strict coefficient systems.
Source: Zheng, Constructions 5.14--5.15, Lemmas 5.16 and 5.22, Proposition 5.24
(blueprint: lem-pur-etale-coefficient-system-adjoint).
Proof plan (the node's nine steps):
1. The finite coefficient rings are finite ell-primary rings over the finite-field
base. Completeness of the integer ring and finite-type Noetherianity supply the
coefficient-system comparison. Extension by zero is exact, so Rp_* j_! is defined.
The system-level left-extension lemma supplies the Grothendieck system category.
2. For any finite coefficient map form derived tensor left adjoint to exact scalar
restriction. Derived direct-image composition and open extension identify the
restriction square. Its tensor mate is the proper projection formula and is an
isomorphism, including for nonflat coefficient quotients. On K-flat representatives,
units and the tensor associator show its identity and composition coherences.
3. These squares identify F LE_n with LE_n F_n. Proper direct image preserves
coproducts at every finite level; exact open extension does too. Evaluations detect
isomorphisms and compute coproducts. Grothendieck-derived Brown representability
therefore gives G. Transposition supplies its additive, O-linear, and shift
structures. The triangulated-right-adjoint lemma proves exactness.
4. Apply LE_n left adjoint to e_n, F left adjoint to G, and F_n left adjoint to G_n.
The resulting natural Hom bijections identify e_n G with G_n e_n. Transposition
identifies units, counits, and coefficient transitions, including composites.
5. Let N_f be the uniform finite-level upper cohomological amplitude of F. If M is
in degrees at least a and H in degrees at most a-N_f-1, then Hom(F H,M)=0.
Adjunction and standard truncation orthogonality give G M in degrees at least
 a-N_f. The same N_f works for every level.
6. The canonical tensor comparison for G is the transpose of the inverse projection
square followed by the scalar extension of the F/G counit. After restriction of
scalars it is the finite-level constant-tensor comparison, hence an isomorphism.
The evaluated adjoint transitions of G M are these comparisons followed by G_n of
the input adjoint transitions. They are invertible for normalized M. Step 5 gives
the asserted boundedness below. No quotient-flatness assumption is used.
7. Uniqueness of the extended absolute value embeds O in O'. DVR factorization
writes varpi=u*(varpi')^e, e positive. Completeness and the finite residue quotient
make O' finite over O; torsion-freeness and the DVR freeness theorem make it finite
free. Its reductions are finite free and its varpi powers are cofinal.
8. Apply the same counit-transpose construction to the exact scalar extension on
systems. Evaluations identify the comparison with the finite-level comparisons,
so it is invertible. For an identity its transpose is the counit. For composites,
naturality of the counit and the projection-square associativity identify the two
transposes. Injectivity of the Hom bijection proves coherence on system maps, also
for diagrams involving derived quotient tensors and their canonical associators.
9. Cofinal subsequence restriction U_r has the left extension L_r. Projection
squares identify F_full L_r with L_r F_r, including transitions. Apply L_r/U_r and
F/G adjunctions to obtain U_r G_full isomorphic to G_r U_r. The Hom bijection fixes
its counit and map action and gives composition coherence. For r(n)=e*n, the ideal
identity from step 7 identifies this with the varpi-power construction. All maps
are defined by actual derived operations and transposes, hence are independent of
resolutions. No inverse limit, integral output, or constructible restriction enters. -/
theorem etaleCoefficientSystemAdjoint
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    ∃ S : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionUniformizer l E) c,
      Nonempty (StrictEtaleExceptionalAdjoint _ _ c S) := by
  sorry
section IntegerMaps
variable (l : ℕ) [Fact l.Prime]
  {E F : Type (u + 1)} [Field E] [Field F]
  [Algebra (Padic l) E] [Algebra (Padic l) F]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
/-- A finite p-adic field embedding preserves the recorded integer rings.
Source: Zheng, coefficient change in Proposition 2.29(2); Serre, Local Fields II.2
(blueprint: lem-pur-etale-coefficient-system-adjoint).
Proof: uniqueness of the extending absolute value identifies the two absolute values
on E. The integer rings are their unit balls, so the embedding preserves membership. -/
theorem strictEtaleIntegerMap_mem (i : E →ₐ[Padic l] F)
    (x : Padic.coefficientExtensionIntegers l E) :
    i (x : E) ∈ Padic.coefficientExtensionIntegers l F := by
  have hE := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hF := (Padic.extension_integers_dvr l F
    (Padic.coefficientExtensionAbsoluteValue l F)
    (spectralNorm_extends (K := Padic l) (L := F))).choose_spec.choose_spec
  apply (hF.1 _).mpr
  change spectralNorm (Padic l) F (i (x : E)) ≤ 1
  have hmap : spectralNorm (Padic l) F (i (x : E)) =
      spectralNorm (Padic l) E (x : E) := by
    unfold spectralNorm
    rw [minpoly.algHom_eq i i.injective]
  rw [hmap]
  exact (hE.1 _).mp x.property
/-- Restrict the actual field embedding to the integer rings.
Source: Zheng, Proposition 2.29(2); Serre, Local Fields II.2
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def strictEtaleIntegerMap (i : E →ₐ[Padic l] F) :
    Padic.coefficientExtensionIntegers l E →+* Padic.coefficientExtensionIntegers l F :=
  (i.toRingHom.comp (Padic.coefficientExtensionIntegers l E).subtype).codRestrict
    (Padic.coefficientExtensionIntegers l F) (strictEtaleIntegerMap_mem l i)
end IntegerMaps
/-- Change coefficients at unchanged positive indices, with the actual quotient map.
Source: Zheng, Construction 4.1 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def strictEtaleSameIndexChange {O O' : Type (u + 1)} [CommRing O] [CommRing O']
    (ell : O) (phi : O →+* O') :
    StrictEtaleCoefficientChange O O' ell (phi ell) phi (OrderHom.id : ℕ →o ℕ) where
  ring := strictCoefficientRingMap ell phi
  generators := fun _n _x ↦ Ideal.Quotient.lift_mk _ _ _
/-- Positive-exponent indexing of the ramified subsequence: n means e*(n+1).
Source: Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def strictEtaleRamifiedIndex (e : ℕ) : ℕ →o ℕ where
  toFun n := e * (n + 1) - 1
  monotone' := fun _ _ h ↦
    Nat.sub_le_sub_right (Nat.mul_le_mul_left e (Nat.add_le_add_right h 1)) 1
/-- Reindex by the equal coefficient ideals, using the canonical quotient equivalences.
Source: Zheng, Construction 4.1; Serre, Local Fields II.2
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def strictEtaleRamifiedChange {O : Type (u + 1)} [CommRing O] (ell mu : O) (e : ℕ)
    (h : ∀ n, (Ideal.span ({ell} : Set O)) ^ (strictEtaleRamifiedIndex e n + 1) =
      (Ideal.span ({mu} : Set O)) ^ (n + 1)) :
    StrictEtaleCoefficientChange O O ell mu (RingHom.id O) (strictEtaleRamifiedIndex e) where
  ring n := (Ideal.quotEquivOfEq (h n)).toRingHom
  generators := fun n x ↦ Ideal.quotEquivOfEq_mk (h n) x
/-- The real quotient module induced by the coefficient-ring map.
Source: Zheng, Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def strictEtaleScalarLevelModule {O O' : Type (u + 1)} [CommRing O] [CommRing O']
    (ell : O) (phi : O →+* O') (n : ℕ) :=
  (ModuleCat.restrictScalars.{u + 1} (strictCoefficientRingMap ell phi n)).obj
    (ModuleCat.of (O' ⧸ (Ideal.span ({phi ell} : Set O')) ^ (n + 1))
      (O' ⧸ (Ideal.span ({phi ell} : Set O')) ^ (n + 1)))
/-- Each target quotient is finite free over the source quotient.
Source: Zheng, Proposition 2.29(2); Serre, Local Fields II.2
(blueprint: lem-pur-etale-coefficient-system-adjoint).
Proof: the integer-ring embedding is the restriction of the field embedding.
Completeness and the finite residue quotient make the target integer ring finite
over the source. It is torsion-free since it embeds in a field. A finite torsion-free
module over a DVR has a finite basis. Reducing that basis modulo the source
uniformizer power gives the displayed basis of the actual restricted quotient module. -/
theorem strictEtaleScalarLevelModule_finiteFree
    (l : ℕ) [Fact l.Prime] {E F : Type (u + 1)} [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] F) (n : ℕ) :
    ∃ r : ℕ, Nonempty (Module.Basis (Fin r)
      ((Padic.coefficientExtensionIntegers l E) ⧸
        (Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
          Set (Padic.coefficientExtensionIntegers l E))) ^ (n + 1))
      (strictEtaleScalarLevelModule (Padic.coefficientExtensionUniformizer l E)
        (strictEtaleIntegerMap l i) n)) := by
  classical
  let A := Padic.coefficientExtensionIntegers l E
  let B := Padic.coefficientExtensionIntegers l F
  let phi : A →+* B := strictEtaleIntegerMap l i
  let : Algebra E F := i.toRingHom.toAlgebra
  let : Algebra A F := (i.toRingHom.comp A.subtype).toAlgebra
  let : Algebra A B := phi.toAlgebra
  have : IsScalarTower A E F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A B F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (Padic l) E F :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (i.commutes x).symm
  have : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite (Padic l) E F
  have hA := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have : IsFractionRing A E := hA.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing A := hA.2.2.2.2.2.2.2.2.1
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap (Padic l) E).injective
  have : IsIntegralClosure B A F := by
    refine ⟨Subtype.val_injective, ?_⟩
    intro x
    change x ∈ integralClosure A F ↔ ∃ y : B, (y : F) = x
    rw [← Padic.padic_integers_integralClosure l E F i x]
    exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.property⟩
  have : Module.Finite A B := IsIntegralClosure.finite A E F B
  have : Module.Free A B := IsIntegralClosure.module_free A E F B
  let I : Ideal A := (Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set A)) ^
    (n + 1)
  let J : Ideal B := (Ideal.span ({phi (Padic.coefficientExtensionUniformizer l E)} : Set B)) ^
    (n + 1)
  have hJ : I.map (algebraMap A B) = J := by
    simp only [I, J, Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    rfl
  let Q := strictEtaleScalarLevelModule (Padic.coefficientExtensionUniformizer l E) phi n
  let : Module (A ⧸ I) (B ⧸ J) :=
    Module.compHom (B ⧸ J) (strictCoefficientRingMap
      (Padic.coefficientExtensionUniformizer l E) phi n)
  let e : (B ⧸ I.map (algebraMap A B)) ≃ₗ[A ⧸ I] Q :=
    (Ideal.quotEquivOfEq hJ).toAddEquiv.toLinearEquiv (by
      intro a x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl)
  exact ⟨Module.finrank A B,
    ⟨((Module.finBasis A B).baseChange (A ⧸ I)).map
      ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.toLinearEquiv.trans e)⟩⟩
/-- The canonical finite-extension comparison is invertible on actual derived systems.
The target uses the image of the original uniformizer, not the target uniformizer.
Source: Zheng, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint).
Proof: uniqueness of absolute values embeds integer rings. Completeness, finite
residue quotients and torsion-freeness make O' finite free over O. The induced
termwise tensor is exact. Construct the geometric inverse-image scalar squares on
tensor generators; their open/proper mates give the compact-support projection.
Transpose its inverse followed by the extended counit. Evaluation identifies this
map with the invertible finite-level constant-tensor comparison. Evaluation detects
isomorphisms, so this actual system map is invertible. All representative maps are
normalized by the universal derived counits and hence are independent of resolutions. -/
theorem etaleCoefficientSystemAdjoint_scalar
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (F : Type (u + 1)) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] (i : E →ₐ[Padic l] F)
    (SA : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionUniformizer l E) c)
    (GA : StrictEtaleExceptionalAdjoint _ _ c SA) :
    ∃ (SB : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l F)
        (strictEtaleIntegerMap l i (Padic.coefficientExtensionUniformizer l E)) c)
      (GB : StrictEtaleExceptionalAdjoint _ _ c SB)
      (TX : StrictEtaleCoefficientTransport
        (strictEtaleSameIndexChange (Padic.coefficientExtensionUniformizer l E)
          (strictEtaleIntegerMap l i)) X SA.PX SB.PX)
      (TY : StrictEtaleCoefficientTransport
        (strictEtaleSameIndexChange (Padic.coefficientExtensionUniformizer l E)
          (strictEtaleIntegerMap l i)) Y SA.PY SB.PY)
      (TZ : StrictEtaleCoefficientTransport
        (strictEtaleSameIndexChange (Padic.coefficientExtensionUniformizer l E)
          (strictEtaleIntegerMap l i)) c.Z SA.PZ SB.PZ),
      Nonempty (StrictEtaleExceptionalTransport _ c SA SB TX TY TZ GA GB) := by
  sorry
/-- Restriction to the ramified cofinal subsequence agrees with the construction
using powers of the original uniformizer, as functors and on all derived maps.
Source: Zheng, Construction 4.1 and the adjunction following Lemma 5.16
(blueprint: lem-pur-etale-coefficient-system-adjoint).
Proof: DVR factorization writes the original uniformizer as a unit times the e-th
power of the new uniformizer, with e positive. Thus the displayed quotient ideals
agree at every positive exponent. Their canonical quotient equivalences define the
coefficient transport. Cofinal restriction has the left extension L_r; projection
squares identify F_full L_r with L_r F_r including transitions. Apply both
adjunctions to obtain the displayed G comparison by the natural Hom bijection.
Its transpose is the inverse projection followed by the counit, which fixes the
map, its evaluations, and resolution independence. Positivity makes r(n)+1=e*(n+1),
so level zero retains the exponent e, and no positive level is silently discarded. -/
theorem etaleCoefficientSystemAdjoint_cofinal
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (F : Type (u + 1)) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] (i : E →ₐ[Padic l] F)
    (SF : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l F)
      (Padic.coefficientExtensionUniformizer l F) c)
    (GF : StrictEtaleExceptionalAdjoint _ _ c SF)
    (SB : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l F)
      (strictEtaleIntegerMap l i (Padic.coefficientExtensionUniformizer l E)) c)
    (GB : StrictEtaleExceptionalAdjoint _ _ c SB) :
    ∃ (e : ℕ) (_he : 0 < e)
      (h : ∀ n, (Ideal.span ({Padic.coefficientExtensionUniformizer l F} :
          Set (Padic.coefficientExtensionIntegers l F))) ^
          (strictEtaleRamifiedIndex e n + 1) =
        (Ideal.span ({strictEtaleIntegerMap l i (Padic.coefficientExtensionUniformizer l E)} :
          Set (Padic.coefficientExtensionIntegers l F))) ^ (n + 1))
      (RX : StrictEtaleCoefficientTransport
        (strictEtaleRamifiedChange (Padic.coefficientExtensionUniformizer l F)
          (strictEtaleIntegerMap l i (Padic.coefficientExtensionUniformizer l E)) e h)
        X SF.PX SB.PX)
      (RY : StrictEtaleCoefficientTransport
        (strictEtaleRamifiedChange (Padic.coefficientExtensionUniformizer l F)
          (strictEtaleIntegerMap l i (Padic.coefficientExtensionUniformizer l E)) e h)
        Y SF.PY SB.PY)
      (RZ : StrictEtaleCoefficientTransport
        (strictEtaleRamifiedChange (Padic.coefficientExtensionUniformizer l F)
          (strictEtaleIntegerMap l i (Padic.coefficientExtensionUniformizer l E)) e h)
        c.Z SF.PZ SB.PZ),
      Nonempty (StrictEtaleExceptionalTransport _ c SF SB RX RY RZ GF GB) := by
  sorry
/-- Compose the actual coefficient maps and index maps.
Source: Zheng, Construction 4.1 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleCoefficientChange.comp
    {O₁ O₂ O₃ : Type (u + 1)} [CommRing O₁] [CommRing O₂] [CommRing O₃]
    {ell₁ : O₁} {ell₂ : O₂} {ell₃ : O₃} {phi₁₂ : O₁ →+* O₂} {phi₂₃ : O₂ →+* O₃}
    {r₁₂ r₂₃ : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O₁ O₂ ell₁ ell₂ phi₁₂ r₁₂)
    (b : StrictEtaleCoefficientChange O₂ O₃ ell₂ ell₃ phi₂₃ r₂₃) :
    StrictEtaleCoefficientChange O₁ O₃ ell₁ ell₃ (phi₂₃.comp phi₁₂) (r₁₂.comp r₂₃) where
  ring n := (b.ring n).comp (a.ring (r₂₃ n))
  generators := fun n x ↦
    (congrArg (b.ring n) (a.generators (r₂₃ n) x)).trans (b.generators n (phi₁₂ x))
/-- The canonical tensor associator on strict systems, characterized on tensor units,
and its exact descent to complexes. This includes the identity coefficient-index cases.
Source: Zheng, Construction 4.1 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleTransportCompositionCoherence
    {O₁ O₂ O₃ : Type (u + 1)} [CommRing O₁] [CommRing O₂] [CommRing O₃]
    {ell₁ : O₁} {ell₂ : O₂} {ell₃ : O₃} {phi₁₂ : O₁ →+* O₂} {phi₂₃ : O₂ →+* O₃}
    {r₁₂ r₂₃ : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O₁ O₂ ell₁ ell₂ phi₁₂ r₁₂}
    {b : StrictEtaleCoefficientChange O₂ O₃ ell₂ ell₃ phi₂₃ r₂₃} {T : Scheme.{u}}
    {P₁ : StrictEtaleEvaluation T O₁ ell₁}
    {P₂ : StrictEtaleEvaluation T O₂ ell₂}
    {P₃ : StrictEtaleEvaluation T O₃ ell₃}
    (U₁₂ : StrictEtaleCoefficientTransport a T P₁ P₂)
    (U₂₃ : StrictEtaleCoefficientTransport b T P₂ P₃)
    (U₁₃ : StrictEtaleCoefficientTransport (a.comp b) T P₁ P₃)
    (ordinary : U₁₂.ordinary ⋙ U₂₃.ordinary ≅ U₁₃.ordinary)
    (derived : U₁₂.derived ⋙ U₂₃.derived ≅ U₁₃.derived) : Prop :=
    -- unit
    (∀ n M,
      (U₁₂.unit (r₂₃ n)).app M ≫ (U₂₃.unit n).app (U₁₂.ordinary.obj M) ≫
        (SheafOfModules.toSheaf.{u + 1} _).map
          ((coefficientEvaluation (J := T.smallEtaleTopology) (O := O₃) (ell := ell₃) n).map
            (ordinary.hom.app M)) = (U₁₃.unit n).app M) ∧
    -- representative
    (∀ K,
      U₂₃.derived.map (U₁₂.factors.hom.app K) ≫
        U₂₃.factors.hom.app ((U₁₂.ordinary.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app K) =
      derived.hom.app (DerivedCategory.Q.obj K) ≫ U₁₃.factors.hom.app K)

/-- The coherence predicate for `StrictEtaleTransportComposition`, separated from its data to share
its type during kernel checking. It is exactly the displayed canonical diagram equations.
Source: Zheng, Construction 4.1, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleTransportComposition
    {O₁ O₂ O₃ : Type (u + 1)} [CommRing O₁] [CommRing O₂] [CommRing O₃]
    {ell₁ : O₁} {ell₂ : O₂} {ell₃ : O₃} {phi₁₂ : O₁ →+* O₂} {phi₂₃ : O₂ →+* O₃}
    {r₁₂ r₂₃ : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O₁ O₂ ell₁ ell₂ phi₁₂ r₁₂}
    {b : StrictEtaleCoefficientChange O₂ O₃ ell₂ ell₃ phi₂₃ r₂₃} {T : Scheme.{u}}
    {P₁ : StrictEtaleEvaluation T O₁ ell₁}
    {P₂ : StrictEtaleEvaluation T O₂ ell₂}
    {P₃ : StrictEtaleEvaluation T O₃ ell₃}
    (U₁₂ : StrictEtaleCoefficientTransport a T P₁ P₂)
    (U₂₃ : StrictEtaleCoefficientTransport b T P₂ P₃)
    (U₁₃ : StrictEtaleCoefficientTransport (a.comp b) T P₁ P₃) :=
  { record : (U₁₂.ordinary ⋙ U₂₃.ordinary ≅ U₁₃.ordinary) ×
      (U₁₂.derived ⋙ U₂₃.derived ≅ U₁₃.derived) //
    StrictEtaleTransportCompositionCoherence U₁₂ U₂₃ U₁₃ record.1 record.2 }

section
variable {O₁ O₂ O₃ : Type (u + 1)} [CommRing O₁] [CommRing O₂] [CommRing O₃]
    {ell₁ : O₁} {ell₂ : O₂} {ell₃ : O₃} {phi₁₂ : O₁ →+* O₂} {phi₂₃ : O₂ →+* O₃}
    {r₁₂ r₂₃ : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O₁ O₂ ell₁ ell₂ phi₁₂ r₁₂}
    {b : StrictEtaleCoefficientChange O₂ O₃ ell₂ ell₃ phi₂₃ r₂₃} {T : Scheme.{u}}
    {P₁ : StrictEtaleEvaluation T O₁ ell₁}
    {P₂ : StrictEtaleEvaluation T O₂ ell₂}
    {P₃ : StrictEtaleEvaluation T O₃ ell₃}
    (U₁₂ : StrictEtaleCoefficientTransport a T P₁ P₂)
    (U₂₃ : StrictEtaleCoefficientTransport b T P₂ P₃)
    (U₁₃ : StrictEtaleCoefficientTransport (a.comp b) T P₁ P₃)
variable {U₁₂ U₂₃ U₁₃}


/-- The specified component of `StrictEtaleTransportComposition`.
Source: Zheng, Construction 4.1, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleTransportComposition.derived
    (record : StrictEtaleTransportComposition U₁₂ U₂₃ U₁₃) :
    U₁₂.derived ⋙ U₂₃.derived ≅ U₁₃.derived :=
  record.val.2


end

/-- The canonical tensor unit on strict systems and its exact descent.
Source: Zheng, Construction 4.1 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleTransportIdentityCoherence
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {T : Scheme.{u}}
    {P : StrictEtaleEvaluation T O ell}
    (U : StrictEtaleCoefficientTransport a T P P)
    (ordinary : U.ordinary ≅ 𝟭 _)
    (derived : U.derived ≅ 𝟭 _) : Prop :=
    -- unit
    (∀ n M, (U.unit n).app M ≫
      (SheafOfModules.toSheaf.{u + 1} _).map
        ((coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) n).map
          (ordinary.hom.app M)) = 𝟙 _) ∧
    -- representative
    (∀ K, derived.hom.app (DerivedCategory.Q.obj K) =
      U.factors.hom.app K ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app K))

/-- The coherence predicate for `StrictEtaleTransportIdentity`, separated from its data to share
its type during kernel checking. It is exactly the displayed canonical diagram equations.
Source: Zheng, Construction 4.1, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleTransportIdentity
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {T : Scheme.{u}}
    {P : StrictEtaleEvaluation T O ell}
    (U : StrictEtaleCoefficientTransport a T P P) :=
  { record : (U.ordinary ≅ 𝟭 _) ×
      (U.derived ≅ 𝟭 _) //
    StrictEtaleTransportIdentityCoherence U record.1 record.2 }

section
variable {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {T : Scheme.{u}}
    {P : StrictEtaleEvaluation T O ell}
    (U : StrictEtaleCoefficientTransport a T P P)
variable {U}


/-- The specified component of `StrictEtaleTransportIdentity`.
Source: Zheng, Construction 4.1, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleTransportIdentity.derived (record : StrictEtaleTransportIdentity U) :
    U.derived ≅ 𝟭 _ :=
  record.val.2


end

/-- Identity coefficient extension has the identity exceptional comparison, with the
canonical tensor units. Source: Zheng, Proposition 2.29(2) and Construction 5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint).
Proof: tensor unit maps determine the ordinary identity identifications. Localize
these maps on complexes. Under the displayed unit identifications, the transpose
of the exceptional comparison is the adjunction counit. The triangle identity and
injectivity of the adjunction Hom bijection therefore give the displayed equality. -/
theorem strictEtaleExceptionalTransport_identity
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {a : StrictEtaleCoefficientChange O O ell ell (RingHom.id O) (OrderHom.id : ℕ →o ℕ)}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {S : StrictEtaleCompactSupport O ell c}
    {G : StrictEtaleExceptionalAdjoint O ell c S}
    {TX : StrictEtaleCoefficientTransport a X S.PX S.PX}
    {TY : StrictEtaleCoefficientTransport a Y S.PY S.PY}
    {TZ : StrictEtaleCoefficientTransport a c.Z S.PZ S.PZ}
    (C : StrictEtaleExceptionalTransport a c S S TX TY TZ G G) :
    ∃ (IX : StrictEtaleTransportIdentity TX) (IY : StrictEtaleTransportIdentity TY)
      (_IZ : StrictEtaleTransportIdentity TZ),
      ∀ M, C.right.hom.app M ≫ G.right.map (IY.derived.hom.app M) =
        IX.derived.hom.app (G.right.obj M) := by
  sorry
/-- Composition of coefficient changes and reindexings respects the canonical tensor
associators as an equality of actual system maps. Source: Zheng, Construction 5.15
and Proposition 2.29(2) (blueprint: lem-pur-etale-coefficient-system-adjoint).
Proof: the ordinary tensor associator is fixed by sending the composite tensor unit
to the single tensor unit. Descent gives the representative-normalized derived
associators. Transpose the composite of the two exceptional comparisons. Substitute
the defining counit-mate equations twice and use counit naturality. The two inverse
projection squares compose to the single inverse projection square, since their
inverse-image normalizations agree on tensor units. Injectivity of the Hom bijection
identifies the transposes and proves the equality. This applies to composed cofinal
restrictions too; no faithfulness of evaluation on derived morphisms is used. -/
theorem strictEtaleExceptionalTransport_comp
    {O₁ O₂ O₃ : Type (u + 1)} [CommRing O₁] [CommRing O₂] [CommRing O₃]
    {ell₁ : O₁} {ell₂ : O₂} {ell₃ : O₃} {phi₁₂ : O₁ →+* O₂} {phi₂₃ : O₂ →+* O₃}
    {r₁₂ r₂₃ : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O₁ O₂ ell₁ ell₂ phi₁₂ r₁₂}
    {b : StrictEtaleCoefficientChange O₂ O₃ ell₂ ell₃ phi₂₃ r₂₃}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {S₁ : StrictEtaleCompactSupport O₁ ell₁ c}
    {S₂ : StrictEtaleCompactSupport O₂ ell₂ c}
    {S₃ : StrictEtaleCompactSupport O₃ ell₃ c}
    {G₁ : StrictEtaleExceptionalAdjoint O₁ ell₁ c S₁}
    {G₂ : StrictEtaleExceptionalAdjoint O₂ ell₂ c S₂}
    {G₃ : StrictEtaleExceptionalAdjoint O₃ ell₃ c S₃}
    {X₁₂ : StrictEtaleCoefficientTransport a X S₁.PX S₂.PX}
    {Y₁₂ : StrictEtaleCoefficientTransport a Y S₁.PY S₂.PY}
    {Z₁₂ : StrictEtaleCoefficientTransport a c.Z S₁.PZ S₂.PZ}
    {X₂₃ : StrictEtaleCoefficientTransport b X S₂.PX S₃.PX}
    {Y₂₃ : StrictEtaleCoefficientTransport b Y S₂.PY S₃.PY}
    {Z₂₃ : StrictEtaleCoefficientTransport b c.Z S₂.PZ S₃.PZ}
    {X₁₃ : StrictEtaleCoefficientTransport (a.comp b) X S₁.PX S₃.PX}
    {Y₁₃ : StrictEtaleCoefficientTransport (a.comp b) Y S₁.PY S₃.PY}
    {Z₁₃ : StrictEtaleCoefficientTransport (a.comp b) c.Z S₁.PZ S₃.PZ}
    (C₁₂ : StrictEtaleExceptionalTransport a c S₁ S₂ X₁₂ Y₁₂ Z₁₂ G₁ G₂)
    (C₂₃ : StrictEtaleExceptionalTransport b c S₂ S₃ X₂₃ Y₂₃ Z₂₃ G₂ G₃)
    (C₁₃ : StrictEtaleExceptionalTransport (a.comp b) c S₁ S₃ X₁₃ Y₁₃ Z₁₃ G₁ G₃) :
    ∃ (AX : StrictEtaleTransportComposition X₁₂ X₂₃ X₁₃)
      (AY : StrictEtaleTransportComposition Y₁₂ Y₂₃ Y₁₃)
      (_AZ : StrictEtaleTransportComposition Z₁₂ Z₂₃ Z₁₃),
      ∀ M, AX.derived.hom.app (G₁.right.obj M) ≫ C₁₃.right.hom.app M =
        X₂₃.derived.map (C₁₂.right.hom.app M) ≫
          C₂₃.right.hom.app (Y₁₂.derived.obj M) ≫ G₃.right.map (AY.derived.hom.app M) := by
  sorry
end AlgebraicGeometry
