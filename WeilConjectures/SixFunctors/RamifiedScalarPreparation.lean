/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteScalarMateData
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections

/-! # Normalized data for ramified scalar realization

Source: the finite scalar-extension argument in the current blueprint
`sec-six-functors-basics/sk-prop-scalar-six/`, and steps 1--3 of
lem-coef-ramified-scalar-exceptional-limit. The preparation contains no exceptional
or compact-support limit isomorphisms and no comparison of the support maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RamifiedScalarPreparation
open FiniteScalarMate

attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)


variable {l E L i D hl f c}

/-- Simultaneous normalized reductions, scalar evaluations, cofinality and Tor bounds.
The five limit realizations are constructed from these data rather than assumed.
Source: steps 1--3 of the parent node
(blueprint: lem-coef-ramified-scalar-preparation). -/
structure Preparation (a : Context l E L i D hl f c) (e : ℕ)
    (he : PurCompactSupport.Ramification l E L i e) (hp : 1 ≤ e) where
  finiteX : ∀ (n : ℕ) (K : (FiniteExceptional.domain l E X n).FullSubcategory),
    FiniteExceptional.domain l L X (retainedIndex e n)
      ((finiteTensor l E L i e he hp X n).obj K.obj)
  finiteY : ∀ (n : ℕ) (K : (FiniteExceptional.domain l E Y n).FullSubcategory),
    FiniteExceptional.domain l L Y (retainedIndex e n)
      ((finiteTensor l E L i e he hp Y n).obj K.obj)
  scalarEvaluationX : ∀ n : ℕ,
    a.TX ⋙ FiniteAdjunctionDiagram.evaluation l L X (retainedIndex e n) ≅
      FiniteAdjunctionDiagram.evaluation l E X n ⋙
        finiteTensorRestricted l E L i e he hp X n (finiteX n)
  scalarEvaluationY : ∀ n : ℕ,
    a.TY ⋙ FiniteAdjunctionDiagram.evaluation l L Y (retainedIndex e n) ≅
      FiniteAdjunctionDiagram.evaluation l E Y n ⋙
        finiteTensorRestricted l E L i e he hp Y n (finiteY n)
  scalarTransitionX : ∀ (m n : ℕ) (hnm : n ≤ m)
      (N : (FiniteAdjunctionDiagram.domain l E X).FullSubcategory),
    (FiniteExceptional.reduction l L X (retainedIndex_mono e hnm)).map
        (((scalarEvaluationX m).hom.app N).hom) ≫
      (quotientTensorSquare l E L i e he hp X hnm).hom.app
        ((FiniteAdjunctionDiagram.evaluation l E X m).obj N).obj ≫
      (finiteTensor l E L i e he hp X n).map
        (FiniteAdjunctionDiagram.transition l E X a.r.quotientRestrictionX hnm N).hom =
    (FiniteAdjunctionDiagram.transition l L X a.s.quotientRestrictionX
      (retainedIndex_mono e hnm) (a.TX.obj N)).hom ≫ ((scalarEvaluationX n).hom.app N).hom
  scalarTransitionY : ∀ (m n : ℕ) (hnm : n ≤ m)
      (N : (FiniteAdjunctionDiagram.domain l E Y).FullSubcategory),
    (FiniteExceptional.reduction l L Y (retainedIndex_mono e hnm)).map
        (((scalarEvaluationY m).hom.app N).hom) ≫
      (quotientTensorSquare l E L i e he hp Y hnm).hom.app
        ((FiniteAdjunctionDiagram.evaluation l E Y m).obj N).obj ≫
      (finiteTensor l E L i e he hp Y n).map
        (FiniteAdjunctionDiagram.transition l E Y a.r.quotientRestrictionY hnm N).hom =
    (FiniteAdjunctionDiagram.transition l L Y a.s.quotientRestrictionY
      (retainedIndex_mono e hnm) (a.TY.obj N)).hom ≫ ((scalarEvaluationY n).hom.app N).hom
  adjunctionR : SemilinearSections.AdjunctionEvaluation a.RX a.RY a.adjR a.r.adjunction
  adjunctionS : SemilinearSections.AdjunctionEvaluation a.SXred a.SYred a.adjS a.s.adjunction
  completeRX : ∀ K : sfIntegralConstructibleCategory l E X,
    IsIso (a.SX.adjunction.unit.app K.obj)
  completeRY : ∀ K : sfIntegralConstructibleCategory l E Y,
    IsIso (a.SY.adjunction.unit.app K.obj)
  completeSX : ∀ K : sfIntegralConstructibleCategory l L X,
    IsIso (a.UX.adjunction.unit.app K.obj)
  completeSY : ∀ K : sfIntegralConstructibleCategory l L Y,
    IsIso (a.UY.adjunction.unit.app K.obj)
  scalarReductionX : a.TIX ⋙ a.SXred ≅ a.RX ⋙ a.TX
  scalarReductionY : a.TIY ⋙ a.SYred ≅ a.RY ⋙ a.TY
  scalarReductionX_normalization : ∀ K : sfIntegralConstructibleCategory l E X,
    (scalarReductionX.hom.app K).hom =
      (integralComparisonScalarCounit l E L i X a.SX a.UX
        ((FrobeniusExchange.models l L).roos X) a.scalarModelX).app K.obj
  scalarReductionY_normalization : ∀ K : sfIntegralConstructibleCategory l E Y,
    (scalarReductionY.hom.app K).hom =
      (integralComparisonScalarCounit l E L i Y a.SY a.UY
        ((FrobeniusExchange.models l L).roos Y) a.scalarModelY).app K.obj
  cofinalX : retainedLimit l L X e ≅ coefficientSequenceLimit l L X
  cofinalY : retainedLimit l L Y e ≅ coefficientSequenceLimit l L Y
  cofinalX_normalization : ∀ C : CochainComplex (coefficientSequenceModules l L X) ℤ,
    ∃ ρ : integralOperationsRoos
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj C).asFunctor ⟶
      integralOperationsRoos (PurCompactSupport.retainedTower e
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj C).asFunctor),
      PurCompactSupport.IsCofinalRoosMap e
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj C).asFunctor ρ ∧
      cofinalX.inv.app (DerivedCategory.Q.obj C) ≫ retainedRoosComparison l L X e C =
        fullRoosComparison l L X C ≫ DerivedCategory.Q.map ρ
  cofinalY_normalization : ∀ C : CochainComplex (coefficientSequenceModules l L Y) ℤ,
    ∃ ρ : integralOperationsRoos
        (((coefficientSequenceRestriction l L Y).mapHomologicalComplex (.up ℤ)).obj C).asFunctor ⟶
      integralOperationsRoos (PurCompactSupport.retainedTower e
        (((coefficientSequenceRestriction l L Y).mapHomologicalComplex (.up ℤ)).obj C).asFunctor),
      PurCompactSupport.IsCofinalRoosMap e
        (((coefficientSequenceRestriction l L Y).mapHomologicalComplex (.up ℤ)).obj C).asFunctor ρ ∧
      cofinalY.inv.app (DerivedCategory.Q.obj C) ≫ retainedRoosComparison l L Y e C =
        fullRoosComparison l L Y C ≫ DerivedCategory.Q.map ρ
  supportR_normalization : ∀ K : sfIntegralConstructibleCategory l E X,
    (coefficientSequenceLimit l E Y).map ((adjunctionR.left.hom.app K).hom) ≫
        a.supportR.iso.hom.app K =
      (@asIso _ _ _ _ (a.SY.adjunction.unit.app
        ((sfCompactSupportFiniteIntegralFunctor l D.k
          (finiteFieldDatumPrimeUnit D l hl) c E).obj K).obj) (completeRY _)).inv
  supportS_normalization : ∀ K : sfIntegralConstructibleCategory l L X,
    (coefficientSequenceLimit l L Y).map ((adjunctionS.left.hom.app K).hom) ≫
        a.supportS.iso.hom.app K =
      (@asIso _ _ _ _ (a.UY.adjunction.unit.app
        ((sfCompactSupportFiniteIntegralFunctor l D.k
          (finiteFieldDatumPrimeUnit D l hl) c L).obj K).obj) (completeSY _)).inv
  uniformReduction : ∀ M : sfIntegralConstructibleCategory l E Y,
    ∃ a₀ b₀ : ℤ, a₀ ≤ b₀ ∧ ∀ n : ℕ,
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (n + 1))
        ((coefficientSequenceDerivedEvaluation l E Y n).obj (a.RY.obj M).obj) a₀ b₀
  uniformExceptional : ∀ M : sfIntegralConstructibleCategory l E Y,
    ∃ a₀ b₀ : ℤ, a₀ ≤ b₀ ∧ ∀ n : ℕ,
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        ((coefficientSequenceDerivedEvaluation l E X n).obj (a.r.G.obj (a.RY.obj M)).obj) a₀ b₀

variable {e : ℕ} {he : PurCompactSupport.Ramification l E L i e} {hp : 1 ≤ e}
  {a : Context l E L i D hl f c}

namespace Preparation

attribute [local irreducible] integralComparisonDerivedSequenceScalar
  integralScalarExtensionOfUniverses

/-- Completeness gives the inverse-limit unit as a natural isomorphism on X.
Source: normalized effectivity, parent step 1
(blueprint: lem-coef-ramified-scalar-preparation). -/
def completionX (P : Preparation a e he hp) :
    (sfIntegralConstructible l L X).ι ≅
      a.SXred ⋙ (FiniteAdjunctionDiagram.domain l L X).ι ⋙ coefficientSequenceLimit l L X :=
  NatIso.ofComponents
    (fun K ↦ @asIso _ _ _ _ (a.UX.adjunction.unit.app K.obj) (P.completeSX K))
    (fun g ↦ a.UX.adjunction.unit.naturality g.hom)

/-- Exceptional source realization, composed from the actual inverse counit and scalar model.
Source: parent step 4 (blueprint: lem-coef-ramified-scalar-preparation). -/
def source (P : Preparation a e he hp) :
    a.RY ⋙ a.r.G ⋙ a.TX ⋙ (FiniteAdjunctionDiagram.domain l L X).ι ⋙
      retainedLimit l L X e ≅ a.GR ⋙ a.TIX ⋙ (sfIntegralConstructible l L X).ι :=
  Functor.isoWhiskerLeft
      (a.RY ⋙ a.r.G ⋙ a.TX ⋙ (FiniteAdjunctionDiagram.domain l L X).ι) P.cofinalX ≪≫
    Functor.isoWhiskerRight P.adjunctionR.right.symm
      (a.TX ⋙ (FiniteAdjunctionDiagram.domain l L X).ι ⋙ coefficientSequenceLimit l L X) ≪≫
    Functor.isoWhiskerLeft (a.GR ⋙ (sfIntegralConstructible l E X).ι)
      a.scalarModelX.realization.symm

/-- Exceptional target realization, using the same scalar-reduction counit and completion unit.
Source: parent step 4 (blueprint: lem-coef-ramified-scalar-preparation). -/
def target (P : Preparation a e he hp) :
    a.RY ⋙ a.TY ⋙ a.s.G ⋙ (FiniteAdjunctionDiagram.domain l L X).ι ⋙
      retainedLimit l L X e ≅ a.TIY ⋙ a.GS ⋙ (sfIntegralConstructible l L X).ι :=
  Functor.isoWhiskerLeft
      (a.RY ⋙ a.TY ⋙ a.s.G ⋙ (FiniteAdjunctionDiagram.domain l L X).ι) P.cofinalX ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight P.scalarReductionY.symm a.s.G)
      ((FiniteAdjunctionDiagram.domain l L X).ι ⋙ coefficientSequenceLimit l L X) ≪≫
    Functor.isoWhiskerLeft a.TIY
      (Functor.isoWhiskerRight P.adjunctionS.right.symm
        ((FiniteAdjunctionDiagram.domain l L X).ι ⋙ coefficientSequenceLimit l L X)) ≪≫
    Functor.isoWhiskerLeft (a.TIY ⋙ a.GS) P.completionX.symm

/-- Scalar realization on Y, using the specified scalar-model inverse.
Source: parent step 3 (blueprint: lem-coef-ramified-scalar-preparation). -/
def scalarY (P : Preparation a e he hp) :
    a.RY ⋙ a.TY ⋙ (FiniteAdjunctionDiagram.domain l L Y).ι ⋙
      retainedLimit l L Y e ≅ a.TIY ⋙ (sfIntegralConstructible l L Y).ι :=
  Functor.isoWhiskerLeft
      (a.RY ⋙ a.TY ⋙ (FiniteAdjunctionDiagram.domain l L Y).ι) P.cofinalY ≪≫
    Functor.isoWhiskerLeft (sfIntegralConstructible l E Y).ι a.scalarModelY.realization.symm

/-- Apply scalar extension to inverse exceptional reduction, then inverse scalar reduction.
Source: the system comparison in parent step 5
(blueprint: lem-coef-ramified-scalar-preparation). -/
def supportSystem (P : Preparation a e he hp) :
    a.RY ⋙ a.r.G ⋙ a.TX ≅ (a.GR ⋙ a.TIX) ⋙ a.SXred :=
  (Functor.associator a.RY a.r.G a.TX).symm ≪≫
    Functor.isoWhiskerRight P.adjunctionR.right.symm a.TX ≪≫
    Functor.associator a.GR a.RX a.TX ≪≫
    Functor.isoWhiskerLeft a.GR P.scalarReductionX.symm ≪≫
    (Functor.associator a.GR a.TIX a.SXred).symm

/-- Compose a cofinal comparison, a system comparison, and a support realization.
All intermediate functors have explicit parentheses.
Source: parent step 5 (blueprint: lem-coef-ramified-scalar-preparation). -/
def supportAssembly
    {A B C C' D E F H : Type*} [Category A] [Category B] [Category C] [Category C']
    [Category D] [Category E] [Category F] [Category H]
    (r : A ⥤ B) (g : B ⥤ C) (t : C ⥤ D) (s : D ⥤ E) (v : E ⥤ F)
    (L L' : F ⥤ H) (u : A ⥤ C') (w : C' ⥤ D) (h : C' ⥤ H)
    (b : r ⋙ g ⋙ t ≅ u ⋙ w) (z : w ⋙ s ⋙ v ⋙ L' ≅ h) (c : L ≅ L') :
    r ⋙ g ⋙ t ⋙ s ⋙ v ⋙ L ≅ u ⋙ h :=
  Functor.isoWhiskerLeft r (Functor.isoWhiskerLeft g
      (Functor.isoWhiskerLeft t (Functor.isoWhiskerLeft s (Functor.isoWhiskerLeft v c)))) ≪≫
    (Functor.associator r g (t ⋙ s ⋙ v ⋙ L')).symm ≪≫
    (Functor.associator (r ⋙ g) t (s ⋙ v ⋙ L')).symm ≪≫
    Functor.isoWhiskerRight b (s ⋙ v ⋙ L') ≪≫
    Functor.associator u w (s ⋙ v ⋙ L') ≪≫ Functor.isoWhiskerLeft u z

/-- The upper-support realization is obtained by applying support to the two counits.
Source: parent step 5 (blueprint: lem-coef-ramified-scalar-preparation). -/
def supportSource (P : Preparation a e he hp) :
    a.RY ⋙ a.r.G ⋙ a.TX ⋙ a.s.F ⋙
      (FiniteAdjunctionDiagram.domain l L Y).ι ⋙ retainedLimit l L Y e ≅
    a.GR ⋙ a.TIX ⋙
      sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) c L ⋙
        (sfIntegralConstructible l L Y).ι :=
  supportAssembly a.RY a.r.G a.TX a.s.F (FiniteAdjunctionDiagram.domain l L Y).ι
    (retainedLimit l L Y e) (coefficientSequenceLimit l L Y)
    (a.GR ⋙ a.TIX) a.SXred
    (sfCompactSupportFiniteIntegralFunctor l D.k
      (finiteFieldDatumPrimeUnit D l hl) c L ⋙ (sfIntegralConstructible l L Y).ι)
    P.supportSystem a.supportS.iso P.cofinalY ≪≫
    Functor.associator a.GR a.TIX _

/-- The lower-support realization uses the inverse left-adjoint evaluation and scalar model.
Source: parent step 5 (blueprint: lem-coef-ramified-scalar-preparation). -/
def supportTarget (P : Preparation a e he hp) :
    a.RY ⋙ a.r.G ⋙ a.r.F ⋙ a.TY ⋙
      (FiniteAdjunctionDiagram.domain l L Y).ι ⋙ retainedLimit l L Y e ≅
    a.GR ⋙ sfCompactSupportFiniteIntegralFunctor l D.k
      (finiteFieldDatumPrimeUnit D l hl) c E ⋙ a.TIY ⋙ (sfIntegralConstructible l L Y).ι := by
  let F := sfCompactSupportFiniteIntegralFunctor l D.k
    (finiteFieldDatumPrimeUnit D l hl) c E
  let b₁ : a.RY ⋙ a.r.G ⋙ a.r.F ≅ a.GR ⋙ a.RX ⋙ a.r.F :=
    Functor.isoWhiskerRight P.adjunctionR.right.symm a.r.F
  let b₂ : a.GR ⋙ a.RX ⋙ a.r.F ≅ a.GR ⋙ F ⋙ a.RY :=
    Functor.isoWhiskerLeft a.GR P.adjunctionR.left.symm
  let b := b₁ ≪≫ b₂
  let d := Functor.isoWhiskerRight b
    (a.TY ⋙ (FiniteAdjunctionDiagram.domain l L Y).ι ⋙ coefficientSequenceLimit l L Y)
  let t := Functor.isoWhiskerLeft (a.GR ⋙ F ⋙ (sfIntegralConstructible l E Y).ι)
    a.scalarModelY.realization.symm
  exact Functor.isoWhiskerLeft
    (a.RY ⋙ a.r.G ⋙ a.r.F ⋙ a.TY ⋙ (FiniteAdjunctionDiagram.domain l L Y).ι)
      P.cofinalY ≪≫ d ≪≫ t

end Preparation

variable (l E L i D hl f c)

/-- Construct normalized scalar and adjunction data, before realizing the five limits.
Source: parent node steps 1--3, and the current blueprint scalar-six compact-support
proof, isomorphism paragraph; exceptional proof, definition and formal properties
(blueprint: lem-coef-ramified-scalar-preparation).

Proof: choose the simultaneous finite adjunction realizations and the integral
constructible adjoints, using their ordinary units and counits to identify the
reduced adjunctions. Use one flat-term K-flat replacement and tensor reassociation
on each small site to construct the scalar evaluations and their quotient squares.
The strict proper coefficient projection and open balancing yield an invertible
system comparison: a reduced integral basis identifies its restriction with finite
sum distributivity. This proves invertibility before any finite evaluation.
Integral scalar preservation gives both constructible domains. Residue Tor applied
to a common interval of the first reduction of M, then integral exceptional
preservation, gives uniform intervals for its reduction and exceptional system.
Normalized effectivity makes the actual completion units and reduction counits
invertible; adjoint uniqueness gives adjunction evaluation with both triangle laws.
Reassociate the same K-flat complex over the retained quotients and use the
completed scalar comparison to identify its scalar counit. This proves the two
scalar-reduction normalizations as system maps. Arithmetic restriction of the full
strict tower gives cofinalX and cofinalY with the actual Roos-coordinate formulas.
Support realization and the completion-unit triangle prove both support
normalizations. Scalar Tor preservation applies at every upper level by choosing
a retained exponent above it, including levels not divisible by e. These
constructions precede the five limit isomorphisms and use dimension zero on an
empty scheme; no equality of system maps is inferred from finite evaluation. -/
theorem existsPreparation (e : ℕ)
    (he : PurCompactSupport.Ramification l E L i e) (hp : 1 ≤ e) :
    ∃ a : Context l E L i D hl f c,
      IsIso a.alpha ∧ Nonempty (Preparation a e he hp) := by sorry

end WeilConjectures.RamifiedScalarPreparation
