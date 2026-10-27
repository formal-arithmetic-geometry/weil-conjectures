/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.FdCompletionInverseScalarCoherence
public import Sheaf.Paper.RationalRealizationScalarCoherence
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.CompletedCondensedCoefficients
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.Paper.ContinuousCoefficientModuleEncoding
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence

/-! # Coherent finite adic realizations

Source: Bhatt--Scholze, Proposition 6.6.11, Definition 6.8.8 and
Proposition 6.8.14(2); Hemo--Richarz--Scholbach, Theorem 7.7 and Lemma 7.9
(blueprint: def-sf-adic-finite-realization-data).

The integral comparison is the published identity on the completed ambient category.
Its scalar comparison retains the actual quotient-tower augmentation chi. Finite
realization is composed with that raw comparison, without an idempotent envelope.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [local irreducible] HasDerivedCategory.standard


universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped TensorProduct CategoryTheory.Obj

namespace WeilConjectures.AdicFiniteRealization

variable (l : ℕ) [Fact l.Prime] (T : Scheme.{u})

/-- The locally finite free description of the target, in ordinary module sheaves.
This predicate only spells out the target clause; it imposes no completeness condition.
Source: BS Definition 6.8.8 (blueprint: def-sf-adic-finite-realization-data). -/
def finiteFreeTarget (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    ObjectProperty (DerivedCategory (pbcModules T A)) := fun K ↦
  (∃ a b : ℤ, a ≤ b ∧ K.IsGE a ∧ K.IsLE b) ∧
    ∀ q : ℤ, ∃ S : FiniteLocallyClosedStratification T, ∀ i : Fin S.n,
      ((proEtaleModuleInverseImage (S.immersion i) A).obj
        ((DerivedCategory.homologyFunctor _ q).obj K)).IsFiniteLocallyFree

/-- The same finite-free condition in internal abelian sheaf modules, using the
existing stratification, module pullbacks and finite-free objects.
Source: BS Definition 6.8.8 (blueprint: def-sf-adic-finite-realization-data). -/
def internalFiniteFreeTarget (A : Sheaf (ProEt.topology T) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] :
    ObjectProperty (DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) A)) :=
  fun K ↦ (∃ a b : ℤ, a ≤ b ∧ K.IsGE a ∧ K.IsLE b) ∧
    ∀ q : ℤ, ∃ S : Scheme.Stratification T, ∀ i : Fin S.n,
      ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain i), ∀ j : C.I₀,
        Mod.IsFree
          ((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (C.f j)).obj
            ((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (S.immersion i)).obj A))
          (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (C.f j)).mapMod _).obj
            (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1}
              (S.immersion i)).mapMod A).obj
                ((DerivedCategory.homologyFunctor _ q).obj K)))

variable [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]

/-- The finite realizations and the inverse-completion comparison of raw systems.
`raw` includes the integral identity, all reductions, pure rational arrows and chi.
The realization's essential image is the stated full subcategory of ordinary D(E_T).
Source: BS 6.6.11, 6.8.8, 6.8.14(2)
(blueprint: def-sf-adic-finite-realization-data). -/
structure Core where
  stage : ∀ E : Padic.FiniteCoefficientFields l (PadicAlgCl l),
    FdRationalStageComparison l (PadicAlgCl l) T E
  raw : FdCompletionScalarComparison l (PadicAlgCl l) T stage
  realization : ∀ E : Padic.FiniteCoefficientFields l (PadicAlgCl l),
    RationalModuleRealization l (pbcFiniteField.{u} l (PadicAlgCl l) E) T
  fully_faithful : ∀ E K L, Function.Bijective
    ((realization E).J.map : (K ⟶ L) → (_ ⟶ _))
  image : ∀ E K,
    finiteFreeTarget T (rationalCoefficientSheaf l T
      (pbcFiniteField.{u} l (PadicAlgCl l) E)) K ↔
        ∃ M, Nonempty ((realization E).J.obj M ≅ K)

/-- The actual finite functor, composed from raw identity and continuous realization.
Source: BS 6.8.14(2) (blueprint: def-sf-adic-finite-realization-data). -/
def finiteFunctor (C : Core l T)
    (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) :=
  C.raw.family.Φ E ⋙ (C.realization E).J

/-- The integral commuting diagram, packaged to keep structure recursors small.
Source: BS 6.8.14(2) (blueprint: def-sf-adic-finite-realization-data). -/
@[irreducible] def integralNormalization (C : Core l T)
    (coefficient : ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F),
    RationalRealizationScalarComparison l
      (pbcFiniteField.{u} l (PadicAlgCl l) E)
      (pbcFiniteField.{u} l (PadicAlgCl l) F)
      (pbcFiniteFieldInclusion l (PadicAlgCl l) h) T
      (C.realization E) (C.realization F))
    (theta : ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F),
    (pbcScalarSystem l (PadicAlgCl l) T dT.out iT.out).T h ⋙ (C.realization F).J ≅
      (C.realization E).J ⋙ pbcDerivedExtend (coefficient h).coefficient)
    (completed_square : ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)}
      (h : E ≤ F),
    pbcCompletedScalarMap l (PadicAlgCl l) T h ≫
        rationalPullScalar l (pbcFiniteField.{u} l (PadicAlgCl l) F) (C.realization F) =
      rationalPullScalar l (pbcFiniteField.{u} l (PadicAlgCl l) E) (C.realization E) ≫
        (coefficient h).coefficient) : Prop :=
  ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F)
      (K : pbcIntegralStage l (PadicAlgCl l) T E),
    (theta h).hom.app ((pbcStageLocalization l (PadicAlgCl l) T E).obj K) ≫
      (pbcDerivedExtend (coefficient h).coefficient).map
        (eqToHom ((C.realization E).objects K)) ≫
      (pbcReductionNormalization
        (rationalPullScalar l (pbcFiniteField.{u} l (PadicAlgCl l) E) (C.realization E))
        (coefficient h).coefficient
        (rationalPullScalar l (pbcFiniteField.{u} l (PadicAlgCl l) E) (C.realization E) ≫
          (coefficient h).coefficient) rfl K.obj).hom =
    (C.realization F).J.map
      ((pbcScalarIntegralComparison l (PadicAlgCl l) T dT.out iT.out h).hom.app K) ≫
      eqToHom ((C.realization F).objects
        ((pbcIntegralScalarExtension l (PadicAlgCl l) T dT.out iT.out h).obj K)) ≫
      (pbcReductionNormalization (pbcCompletedScalarMap l (PadicAlgCl l) T h)
        (rationalPullScalar l (pbcFiniteField.{u} l (PadicAlgCl l) F) (C.realization F))
        (rationalPullScalar l (pbcFiniteField.{u} l (PadicAlgCl l) E) (C.realization E) ≫
          (coefficient h).coefficient) (completed_square h) K.obj).hom

/-- Continuous finite-field comparisons, including their integral normalization.
The comparison for completed S is subsequently composed with raw.beta inverse.
Source: BS 6.8.14(2); quotient comparison of the node
(blueprint: def-sf-adic-finite-realization-data). -/
structure ScalarData (C : Core l T) where
  coefficient : ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F),
    RationalRealizationScalarComparison l
      (pbcFiniteField.{u} l (PadicAlgCl l) E)
      (pbcFiniteField.{u} l (PadicAlgCl l) F)
      (pbcFiniteFieldInclusion l (PadicAlgCl l) h) T
      (C.realization E) (C.realization F)
  theta : ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F),
    (pbcScalarSystem l (PadicAlgCl l) T dT.out iT.out).T h ⋙ (C.realization F).J ≅
      (C.realization E).J ⋙ pbcDerivedExtend (coefficient h).coefficient
  completed_square : ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)}
      (h : E ≤ F),
    pbcCompletedScalarMap l (PadicAlgCl l) T h ≫
        rationalPullScalar l (pbcFiniteField.{u} l (PadicAlgCl l) F) (C.realization F) =
      rationalPullScalar l (pbcFiniteField.{u} l (PadicAlgCl l) E) (C.realization E) ≫
        (coefficient h).coefficient
  integral : integralNormalization l T C coefficient theta completed_square

/-- The specified comparison j: inverse quotient-completion comparison followed by
balanced continuous tensor multiplication. This is a composite of actual natural isos.
Source: BS 6.8.14(2), node scalar normalization
(blueprint: def-sf-adic-finite-realization-data). -/
@[irreducible] def scalarComparison (C : Core l T) (B : ScalarData l T C)
    {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F) :
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) T).T h ⋙
        finiteFunctor l T C F ≅
      finiteFunctor l T C E ⋙ pbcDerivedExtend (B.coefficient h).coefficient :=
  Functor.isoWhiskerRight (C.raw.family.β h).symm (C.realization F).J ≪≫
    Functor.isoWhiskerLeft (C.raw.family.Φ E) (B.theta h)

/-- The actual finite scalar associators and multiplication units are intertwined.
Source: BS 6.8.14(2); normalized balanced tower argument, node step 6
(blueprint: def-sf-adic-finite-realization-data). -/
structure Coherence (C : Core l T) (B : ScalarData l T C) where
  coefficient_comp : ∀ {E F G : Padic.FiniteCoefficientFields l (PadicAlgCl l)}
      (h : E ≤ F) (k : F ≤ G),
    (B.coefficient h).coefficient ≫ (B.coefficient k).coefficient =
      (B.coefficient (h.trans k)).coefficient
  tower : ∀ {E F G : Padic.FiniteCoefficientFields l (PadicAlgCl l)}
      (h : E ≤ F) (k : F ≤ G)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E),
    (finiteFunctor l T C G).map
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) T).assoc
          h k).hom.app K) ≫ (scalarComparison l T C B (h.trans k)).hom.app K =
      (scalarComparison l T C B k).hom.app
          (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) T).T h).obj
            K) ≫
        (pbcDerivedExtend (B.coefficient k).coefficient).map
          ((scalarComparison l T C B h).hom.app K) ≫
        (pbcReductionNormalization (B.coefficient h).coefficient (B.coefficient k).coefficient
          (B.coefficient (h.trans k)).coefficient (coefficient_comp h k)
          ((finiteFunctor l T C E).obj K)).hom
  unit : ∀ E : Padic.FiniteCoefficientFields l (PadicAlgCl l),
    pbcDerivedExtend (B.coefficient (le_refl E)).coefficient ≅ 𝟭 _
  unit_normalization : ∀ E,
    ∃ e : pbcExtend (B.coefficient (le_refl E)).coefficient ≅ 𝟭 _,
      (∀ (M : pbcModules T (rationalCoefficientSheaf l T
          (pbcFiniteField.{u} l (PadicAlgCl l) E))) (U : T.ProEtᵒᵖ)
          (a : (rationalCoefficientSheaf l T
            (pbcFiniteField.{u} l (PadicAlgCl l) E)).obj.obj U) (x : M.val.obj U),
        (e.hom.app M).val.app U
          (pbcTensorSection (B.coefficient (le_refl E)).coefficient M U a x) = a • x) ∧
      ∀ P : CochainComplex (pbcModules T (rationalCoefficientSheaf l T
          (pbcFiniteField.{u} l (PadicAlgCl l) E))) ℤ,
        (unit E).hom.app (DerivedCategory.Q.obj P) =
          pbcComplexCounit (B.coefficient (le_refl E)).coefficient P ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P)
  identity : ∀ (E : Padic.FiniteCoefficientFields l (PadicAlgCl l))
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E),
    HEq ((scalarComparison l T C B (le_refl E)).hom.app K ≫
        (unit E).hom.app ((finiteFunctor l T C E).obj K))
      ((finiteFunctor l T C E).map
        ((GeneralAlgebraicallyClosedCoefficients.unitor l (PadicAlgCl l) T E).hom.app K))

/-- The native coefficient ring is exactly the section presentation of the pullback
of finite-subextension-valued continuous functions.
Source: BS 6.8.1--6.8.2 (blueprint: def-sf-adic-finite-realization-data). -/
def closureRing := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
  (ProEt.topology T)
  (AlgebraicGeometry.ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) T)

/-- The section-module derived equivalence of the fixed internal coefficient.
Source: Stacks 00YV (blueprint: def-sf-adic-finite-realization-data). -/
@[irreducible] def sectionDerived (A : Sheaf (ProEt.topology T) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] :=
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology T) A
  letI := Functor.additive_of_preserves_binary_products e.functor
  letI := Functor.additive_of_preserves_binary_products e.inverse
  e.mapDerivedCategory.functor

/-- The common coefficient cocone, together with its actual finite-stage ring legs.
Only field inclusions and balanced tensor extension are allowed; the component
normalization tests every scalar function by the specified point adjunction.
Source: BS 6.8.2; node step 3 (blueprint: def-sf-adic-finite-realization-data). -/
structure ClosureData (C : Core l T) (B : ScalarData l T C) where
  leg : ∀ E : Padic.FiniteCoefficientFields l (PadicAlgCl l),
    rationalCoefficientSheaf l T (pbcFiniteField.{u} l (PadicAlgCl l) E) ⟶ closureRing l T
  finiteIso : ∀ E : Padic.FiniteCoefficientFields l (PadicAlgCl l),
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology T)
      (AlgebraicGeometry.ProEtale.padicSubfieldRingObj T l E) ≅
        rationalCoefficientSheaf l T (pbcFiniteField.{u} l (PadicAlgCl l) E)
  finite_normalization : ∀ (E : Padic.FiniteCoefficientFields l (PadicAlgCl l))
      (U : T.ProEtᵒᵖ)
      (s : (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (ProEt.topology T) (AlgebraicGeometry.ProEtale.padicSubfieldRingObj T l E)).obj.obj U)
      (x : U.unop.left),
    (Shrink.algEquiv (Padic l) E.val)
        (rationalCoefficientValue l (pbcFiniteField.{u} l (PadicAlgCl l) E) T U
          ((finiteIso E).hom.hom.app U s) x) =
      (((AlgebraicGeometry.ProEtale.chartComparison T E.val).hom.app U) s).down x
  leg_normalization : ∀ E,
    (finiteIso E).hom ≫ leg E =
      AlgebraicGeometry.ProEtale.CondensedRing.sectionRingMap T
        (AlgebraicGeometry.ProEtale.padicSubfieldRingObjToPadicAlgCl T l E)
  coefficient_normalization : ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)}
      (h : E ≤ F),
    (finiteIso E).hom ≫ (B.coefficient h).coefficient =
      AlgebraicGeometry.ProEtale.CondensedRing.sectionRingMap T
        (AlgebraicGeometry.ProEtale.padicSubfieldRingObjMap T l h) ≫ (finiteIso F).hom
  cocone : ∀ {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F),
    (B.coefficient h).coefficient ≫ leg F = leg E

/-- Balanced extension of j to the native coefficient ring. The flattening
comparison here is the universal K-flat scalar-composition comparison.
Source: node steps 5--6 (blueprint: def-sf-adic-finite-realization-data). -/
@[irreducible] def closureComparison (C : Core l T) (B : ScalarData l T C) (R : ClosureData l T C B)
    {E F : Padic.FiniteCoefficientFields l (PadicAlgCl l)} (h : E ≤ F) :
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) T).T h ⋙
        finiteFunctor l T C F ⋙ pbcDerivedExtend (R.leg F) ≅
      finiteFunctor l T C E ⋙ pbcDerivedExtend (R.leg E) :=
  Functor.isoWhiskerRight (scalarComparison l T C B h) (pbcDerivedExtend (R.leg F)) ≪≫
    Functor.isoWhiskerLeft (finiteFunctor l T C E)
      (Adjunction.leftAdjointCompIso
        (pbcDerivedScalarAdjunction (B.coefficient h).coefficient)
        (pbcDerivedScalarAdjunction (R.leg F)) (pbcDerivedScalarAdjunction (R.leg E))
        (pbcDerivedRestrictComp (B.coefficient h).coefficient (R.leg F)
          (R.leg E) (R.cocone h)))

/-- All clauses of the finite-realization cocone, including the constructibility
comparison in both module presentations and the native scalar tower equations.
Source: BS 6.6.11, 6.8.8, 6.8.14(2); HRS 7.7 and 7.9
(blueprint: def-sf-adic-finite-realization-data). -/
structure Data extends Core l T where
  scalar : ScalarData l T toCore
  coherence : Coherence l T toCore scalar
  closure : ClosureData l T toCore scalar
  finite_constructibility : ∀ (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) K,
    AlgebraicGeometry.ProEtale.boundedConstructible
        (AlgebraicGeometry.ProEtale.padicSubfieldRingObj T l E) K ↔
      internalFiniteFreeTarget T
        (AlgebraicGeometry.ProEtale.padicSubfieldRingObj T l E) K
  closure_constructibility : ∀ K,
    AlgebraicGeometry.ProEtale.boundedConstructible
        (AlgebraicGeometry.ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) T) K ↔
      internalFiniteFreeTarget T
        (AlgebraicGeometry.ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) T) K
  finite_sections : ∀ (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) K,
    AlgebraicGeometry.ProEtale.boundedConstructible
        (AlgebraicGeometry.ProEtale.padicSubfieldRingObj T l E) K ↔
      finiteFreeTarget T (rationalCoefficientSheaf l T
        (pbcFiniteField.{u} l (PadicAlgCl l) E))
        ((pbcDerivedExtend (closure.finiteIso E).hom).obj
          ((sectionDerived T (AlgebraicGeometry.ProEtale.padicSubfieldRingObj T l E)).obj K))
  closure_sections : ∀ K,
    AlgebraicGeometry.ProEtale.boundedConstructible
        (AlgebraicGeometry.ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) T) K ↔
      finiteFreeTarget T (closureRing l T)
        ((sectionDerived T
          (AlgebraicGeometry.ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) T)).obj K)
  closure_tower : ∀ {E F G : Padic.FiniteCoefficientFields l (PadicAlgCl l)}
      (h : E ≤ F) (k : F ≤ G)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E),
    (pbcDerivedExtend (closure.leg G)).map
        ((finiteFunctor l T toCore G).map
          (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) T).assoc
            h k).hom.app K)) ≫
        (closureComparison l T toCore scalar closure (h.trans k)).hom.app K =
      (closureComparison l T toCore scalar closure k).hom.app
          (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) T).T h).obj
            K) ≫ (closureComparison l T toCore scalar closure h).hom.app K
  closure_identity : ∀ (E : Padic.FiniteCoefficientFields l (PadicAlgCl l))
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) T E),
    HEq ((closureComparison l T toCore scalar closure (le_refl E)).hom.app K)
      ((pbcDerivedExtend (closure.leg E)).map
        ((finiteFunctor l T toCore E).map
          ((GeneralAlgebraicallyClosedCoefficients.unitor l (PadicAlgCl l) T E).hom.app K)))

end WeilConjectures.AdicFiniteRealization
