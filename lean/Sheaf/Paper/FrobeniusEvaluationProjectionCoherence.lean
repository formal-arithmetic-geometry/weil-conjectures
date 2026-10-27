/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.ConstructibleWeilModelSquares
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.DerivedAutomorphismHomEvaluation
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.Paper.SixFunctorOperationDatum
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
public import Sheaf.Paper.DerivedPullbackTensorIso
import Sheaf.Paper.NormalizedRationalEvaluationNaturality
import Sheaf.Paper.NormalizedCommonEvaluationNaturality
import Sheaf.Paper.CommonStageTensorBraidingNaturality
import all Sheaf.Paper.CompletedTensorHomTranspose
import Sheaf.SixFunctors.CanonicalPullTensor
import Sheaf.SixFunctors.ClopenCartesianTensorSquare
import all Sheaf.SixFunctors.ClopenComparisonTensorSquareDataExistence

/-! # Frobenius evaluation and projection coherence

Source: current blueprint, prop-weil-operations.proof.md, sentence 1, and
lem-fix-weil-operations.proof.md, paragraph beginning "For the ordinary adjunction"
(blueprint: lem-pod-frobenius-evaluation-projection-coherence).

Evaluation uses the actual partial closed structure, on its original permitted pairs.
Projection uses the recorded counit mate, rather than a projection isomorphism.
The open square is an identity on the ringed diagram site before realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v a b c d e f
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor Opposite
open CategoryTheory.SuppliedExchangeProjection AlgebraicGeometry
namespace WeilConjectures.PodEvaluationProjection
open WeilConjectures.PodConstructibleMate

private theorem argumentFirst_naturality
    {B : Type a} [Category.{b} B] [Preadditive B]
    {T : B × B ⥤ B} {J : ObjectProperty (Bᵒᵖ × B)} {H : J.FullSubcategory ⥤ B}
    (SC : PodPartialClosed T J H)
    (beta : ∀ M N, T.obj (M, N) ≅ T.obj (N, M))
    (hn : ∀ (Q R : J.FullSubcategory) (f : Q ⟶ R),
      T.map (Prod.mkHom (H.map f) (𝟙 _)) ≫ SC.evaluation R =
        T.map (Prod.mkHom (𝟙 _) f.hom.1.unop) ≫ SC.evaluation Q ≫ f.hom.2)
    (hb : ∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
      T.map (Prod.mkHom f g) ≫ (beta M' N').hom =
        (beta M N).hom ≫ T.map (Prod.mkHom g f))
    (Q R : J.FullSubcategory) (i : Q.obj.1.unop ≅ R.obj.1.unop)
    (f : Q.obj.2 ⟶ R.obj.2) :
    T.map (Prod.mkHom i.hom (H.map (ObjectProperty.homMk (X := Q) (Y := R)
        (Prod.mkHom i.inv.op f)))) ≫ podArgumentFirstEvaluation SC beta R =
      podArgumentFirstEvaluation SC beta Q ≫ f := by
  let g : Q ⟶ R := ObjectProperty.homMk (Prod.mkHom i.inv.op f)
  change T.map (Prod.mkHom i.hom (H.map g)) ≫
    ((beta _ _).hom ≫ SC.evaluation R) = ((beta _ _).hom ≫ SC.evaluation Q) ≫ f
  rw [← Category.assoc, hb, Category.assoc]
  have h := congrArg (fun z ↦ T.map (Prod.mkHom (𝟙 (H.obj Q)) i.hom) ≫ z)
    (hn Q R g)
  have h' : T.map (Prod.mkHom (H.map g) i.hom) ≫ SC.evaluation R =
      SC.evaluation Q ≫ f := by
    change T.map (Prod.mkHom (𝟙 (H.obj Q)) i.hom) ≫
        (T.map (Prod.mkHom (H.map g) (𝟙 _)) ≫ SC.evaluation R) =
      T.map (Prod.mkHom (𝟙 (H.obj Q)) i.hom) ≫
        (T.map (Prod.mkHom (𝟙 _) i.inv) ≫ SC.evaluation Q ≫ f) at h
    simpa only [← Category.assoc, ← T.map_comp, prod_comp, Category.id_comp,
      Category.comp_id, Iso.hom_inv_id, ← prod_id, T.map_id] using h
  rw [h', Category.assoc]

private theorem evaluation_equivariant
    {B : Type a} [Category.{b} B] [Preadditive B]
    (P : B ⥤ B) (T : B × B ⥤ B)
    (J : ObjectProperty (Bᵒᵖ × B)) (H : J.FullSubcategory ⥤ B)
    (SC : PodPartialClosed T J H)
    (beta : ∀ M N, T.obj (M, N) ≅ T.obj (N, M))
    (hJ : ∀ K : J.FullSubcategory, J ((P.op.prod P).obj K.obj))
    (kappa : H ⋙ P ≅ podPairPullback P J J hJ ⋙ H)
    (mu : T ⋙ P ≅ P.prod P ⋙ T)
    (hn : ∀ (Q R : J.FullSubcategory) (i : Q.obj.1.unop ≅ R.obj.1.unop)
      (f : Q.obj.2 ⟶ R.obj.2),
      T.map (Prod.mkHom i.hom (H.map (ObjectProperty.homMk (X := Q) (Y := R)
        (Prod.mkHom i.inv.op f)))) ≫ podArgumentFirstEvaluation SC beta R =
      podArgumentFirstEvaluation SC beta Q ≫ f)
    (he : ∀ Q : J.FullSubcategory,
      mu.hom.app (Q.obj.1.unop, H.obj Q) ≫
        T.map (Prod.mkHom (𝟙 _) (kappa.hom.app Q)) ≫
          podArgumentFirstEvaluation SC beta ((podPairPullback P J J hJ).obj Q) =
        P.map (podArgumentFirstEvaluation SC beta Q))
    (M N : IsoAlgebra P) (h : J (op M.carrier, N.carrier)) :
    mu.hom.app (M.carrier, H.obj ⟨(op M.carrier, N.carrier), h⟩) ≫
      T.map (Prod.mkHom M.str.hom
        (kappa.hom.app ⟨(op M.carrier, N.carrier), h⟩ ≫
          H.map (X := (podPairPullback P J J hJ).obj
            ⟨(op M.carrier, N.carrier), h⟩) (Y := ⟨(op M.carrier, N.carrier), h⟩)
            (ObjectProperty.homMk (Prod.mkHom M.str.inv.op N.str.hom)))) ≫
      podArgumentFirstEvaluation SC beta ⟨(op M.carrier, N.carrier), h⟩ =
    P.map (podArgumentFirstEvaluation SC beta ⟨(op M.carrier, N.carrier), h⟩) ≫
      N.str.hom := by
  let Q : J.FullSubcategory := ⟨(op M.carrier, N.carrier), h⟩
  let R := (podPairPullback P J J hJ).obj Q
  have hnat := hn R Q M.str N.str.hom
  change mu.hom.app (M.carrier, H.obj Q) ≫
    T.map (Prod.mkHom M.str.hom (kappa.hom.app Q ≫ H.map
      (ObjectProperty.homMk (X := R) (Y := Q) (Prod.mkHom M.str.inv.op N.str.hom)))) ≫
        podArgumentFirstEvaluation SC beta Q = _
  rw [show Prod.mkHom M.str.hom (kappa.hom.app Q ≫ H.map
      (ObjectProperty.homMk (X := R) (Y := Q) (Prod.mkHom M.str.inv.op N.str.hom))) =
      Prod.mkHom (𝟙 _) (kappa.hom.app Q) ≫
        Prod.mkHom M.str.hom (H.map
          (ObjectProperty.homMk (X := R) (Y := Q) (Prod.mkHom M.str.inv.op N.str.hom))) by
          simp,
    T.map_comp, Category.assoc, hnat]
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ N.str.hom) (he Q)


set_option linter.unusedVariables false in
/-- Evaluation at rational coefficients is a Weil arrow for precisely the recorded
Hom-constructible pairs. The first input of Hom uses the inverse Weil structure.
The auxiliary instance is the inherited prime inverse, not an extra hypothesis.
Source: lem-fix-weil-operations.proof.md, evaluation paragraph
(blueprint: lem-pod-frobenius-evaluation-projection-coherence).
Proof: the evaluation characterization of lem-pod-derived-automorphism-hom-evaluation
identifies evaluation after tensor and Hom transport with pullback of evaluation.
Naturality in the second argument moves theta_N to the target; extranaturality in
M cancels theta_M inverse against theta_M. Compose these two identities. The
argument-first evaluation is the published signed swap followed by evaluation.
All equations take place in the localized Hom groups, so no invariant lattice or
site-perfectness is used. -/
theorem rational_evaluation
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (X : Models D) (E : Type u) [Field E] [_root_.Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (P : sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left ⥤
      sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left)
    (hP : P = sfWeilFrobeniusPullback D C.l C.different X.obj E)
    (T : sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left ×
        sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left ⥤
      sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left)
    (hT : HEq T ((fun [hX : ∀ x : (D.geometricFiber X.obj).left,
        Invertible (C.l : (D.geometricFiber X.obj).left.residueField x)] ↦
      rationalDerivedTensor C.l E (D.geometricFiber X.obj).left)
        (hX := fun x ↦ sfWeilPrimeInvertible D C.l C.different X.obj x)))
    (H : (constructibleRationalHomPairs C.l E (D.geometricFiber X.obj).left).FullSubcategory ⥤
      sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left)
    (hH : H = rationalDerivedInternalHom C.l E (D.geometricFiber X.obj).left)
    (SC : PodPartialClosed T (constructibleRationalHomPairs C.l E
      (D.geometricFiber X.obj).left) H)
    (hSC : HEq SC ((fun [hX : ∀ x : (D.geometricFiber X.obj).left,
        Invertible (C.l : (D.geometricFiber X.obj).left.residueField x)] ↦
      podRationalClosed C.l E (D.geometricFiber X.obj).left)
        (hX := fun x ↦ sfWeilPrimeInvertible D C.l C.different X.obj x)))
    (hJ : ∀ K : ObjectProperty.FullSubcategory
      (constructibleRationalHomPairs C.l E (D.geometricFiber X.obj).left),
      constructibleRationalHomPairs C.l E (D.geometricFiber X.obj).left
        ((P.op.prod P).obj K.obj))
    (κ : H ⋙ P ≅ podPairPullback P _ _ hJ ⋙ H)
    (hκ : ∀ K : ObjectProperty.FullSubcategory
      (constructibleRationalHomPairs C.l E (D.geometricFiber X.obj).left), HEq (κ.hom.app K)
        ((fun [hX : ∀ x : (D.geometricFiber X.obj).left,
            Invertible (C.l : (D.geometricFiber X.obj).left.residueField x)] ↦
          podRationalHomComparison C.l E (D.geometricFrobenius X.obj).hom K)
            (hX := fun x ↦ sfWeilPrimeInvertible D C.l C.different X.obj x)))
    (μ : T ⋙ P ≅ P.prod P ⋙ T)
    (_hμ : ∀ K L, HEq (μ.app (K, L)) ((fun [hX : ∀ x : (D.geometricFiber X.obj).left,
          Invertible (C.l : (D.geometricFiber X.obj).left.residueField x)] ↦
        canonicalRationalPullbackTensor C.l E (D.geometricFrobenius X.obj).hom K L)
          (hX := fun x ↦ sfWeilPrimeInvertible D C.l C.different X.obj x)))
    (β : ∀ M N, T.obj (M, N) ≅ T.obj (N, M))
    (_hβ : ∀ M N, HEq (β M N)
      ((fun [hX : ∀ x : (D.geometricFiber X.obj).left,
          Invertible (C.l : (D.geometricFiber X.obj).left.residueField x)] ↦
        pullbackTensorRationalBraiding C.l E (D.geometricFiber X.obj).left M N)
          (hX := fun x ↦ sfWeilPrimeInvertible D C.l C.different X.obj x))) :
    ∀ (M N : IsoAlgebra P)
      (h : constructibleRationalHomPairs C.l E (D.geometricFiber X.obj).left
        (op M.carrier, N.carrier)),
      μ.hom.app (M.carrier, H.obj ⟨(op M.carrier, N.carrier), h⟩) ≫
        T.map (Prod.mkHom M.str.hom
          (κ.hom.app ⟨(op M.carrier, N.carrier), h⟩ ≫
            H.map (X := (podPairPullback P _ _ hJ).obj
                ⟨(op M.carrier, N.carrier), h⟩)
              (Y := ⟨(op M.carrier, N.carrier), h⟩)
              (ObjectProperty.homMk (Prod.mkHom M.str.inv.op N.str.hom)))) ≫
        podArgumentFirstEvaluation SC β ⟨(op M.carrier, N.carrier), h⟩ =
      P.map (podArgumentFirstEvaluation SC β ⟨(op M.carrier, N.carrier), h⟩) ≫
        N.str.hom := by
  let _ := fun x ↦ sfWeilPrimeInvertible D C.l C.different X.obj x
  subst P
  cases eq_of_heq hT
  subst H
  cases eq_of_heq hSC
  have hb : β = pullbackTensorRationalBraiding C.l E (D.geometricFiber X.obj).left := by
    funext M N
    exact eq_of_heq (_hβ M N)
  subst β
  apply evaluation_equivariant
  · intro Q R i f
    apply argumentFirst_naturality
    · exact normalizedRationalEvaluation_naturality C.l E (D.geometricFiber X.obj).left
    · intro M M' N N' f g
      exact localizedTensorBraiding_naturality C.l E (D.geometricFiber X.obj).left
        (integralBraiding_naturality C.l E (D.geometricFiber X.obj).left) M M' N N' f g
  · intro Q
    have h := (podArgumentFirst_integral_rational C.l E
      (D.geometricFrobenius X.obj).hom).2.1 Q
    have hk := eq_of_heq (hκ Q)
    have hm := congrArg Iso.hom (eq_of_heq (_hμ Q.obj.1.unop
      ((rationalDerivedInternalHom C.l E (D.geometricFiber X.obj).left).obj Q)))
    simp only [Iso.app_hom] at hm
    rw [hm, hk]
    exact h

set_option linter.unusedVariables false in
/-- Evaluation at algebraically closed coefficients, in the actual common-stage
category and for every allowed pair, including arrows represented only after a
field enlargement. Source: lem-fix-weil-operations.proof.md, evaluation paragraph
(blueprint: lem-pod-frobenius-evaluation-projection-coherence).
Proof: use the common-stage evaluation characterization from
lem-pod-derived-automorphism-hom-evaluation and the same two naturality identities
as for rational_evaluation. Equivalently represent the finite diagram, including
the two inverse Weil maps, over one finite coefficient field, apply the rational
identity, and take its morphism class. Scalar-extension identity and tower
compatibility identify all further representatives. No lattice is chosen. -/
theorem common_evaluation
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X : Models D) (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X.obj).left ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X.obj).left)
    (hP : P = sfCommonStageWeilFrobeniusPullback D l hl X.obj Ω)
    (T : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X.obj).left ×
        generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X.obj).left ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X.obj).left)
    (hT : HEq T ((fun [hX : ∀ x : (D.geometricFiber X.obj).left,
        Invertible (l : (D.geometricFiber X.obj).left.residueField x)] ↦
      commonStageDerivedTensor l Ω (D.geometricFiber X.obj).left)
        (hX := fun x ↦ sfWeilPrimeInvertible D l hl X.obj x)))
    (H : (commonStageHomPairs l Ω (D.geometricFiber X.obj).left).FullSubcategory ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X.obj).left)
    (hH : H = commonStageDerivedInternalHom l Ω (D.geometricFiber X.obj).left)
    (SC : PodPartialClosed T (commonStageHomPairs l Ω (D.geometricFiber X.obj).left) H)
    (hSC : HEq SC ((fun [hX : ∀ x : (D.geometricFiber X.obj).left,
        Invertible (l : (D.geometricFiber X.obj).left.residueField x)] ↦
      podCommonClosed l Ω (D.geometricFiber X.obj).left)
        (hX := fun x ↦ sfWeilPrimeInvertible D l hl X.obj x)))
    (hJ : ∀ K : (commonStageHomPairs l Ω (D.geometricFiber X.obj).left).FullSubcategory,
      commonStageHomPairs l Ω (D.geometricFiber X.obj).left ((P.op.prod P).obj K.obj))
    (κ : H ⋙ P ≅ podPairPullback P _ _ hJ ⋙ H)
    (hκ : ∀ K : (commonStageHomPairs l Ω (D.geometricFiber X.obj).left).FullSubcategory,
      HEq (κ.hom.app K) ((fun [hX : ∀ x : (D.geometricFiber X.obj).left,
          Invertible (l : (D.geometricFiber X.obj).left.residueField x)] ↦
        podCommonHomComparison l Ω (D.geometricFrobenius X.obj).hom K)
          (hX := fun x ↦ sfWeilPrimeInvertible D l hl X.obj x)))
    (μ : T ⋙ P ≅ P.prod P ⋙ T)
    (_hμ : ∀ K L, HEq (μ.app (K, L))
      ((fun [hX : ∀ x : (D.geometricFiber X.obj).left,
          Invertible (l : (D.geometricFiber X.obj).left.residueField x)] ↦
        canonicalCommonStagePullbackTensor l Ω (D.geometricFrobenius X.obj).hom K L)
          (hX := fun x ↦ sfWeilPrimeInvertible D l hl X.obj x)))
    (β : ∀ M N, T.obj (M, N) ≅ T.obj (N, M))
    (_hβ : ∀ M N, HEq (β M N)
      ((fun [hX : ∀ x : (D.geometricFiber X.obj).left,
          Invertible (l : (D.geometricFiber X.obj).left.residueField x)] ↦
        pullbackTensorCommonBraiding l Ω (D.geometricFiber X.obj).left M N)
          (hX := fun x ↦ sfWeilPrimeInvertible D l hl X.obj x))) :
    ∀ (M N : IsoAlgebra P)
      (h : commonStageHomPairs l Ω (D.geometricFiber X.obj).left (op M.carrier, N.carrier)),
      μ.hom.app (M.carrier, H.obj ⟨(op M.carrier, N.carrier), h⟩) ≫
        T.map (Prod.mkHom M.str.hom
          (κ.hom.app ⟨(op M.carrier, N.carrier), h⟩ ≫
            H.map (X := (podPairPullback P _ _ hJ).obj
                ⟨(op M.carrier, N.carrier), h⟩)
              (Y := ⟨(op M.carrier, N.carrier), h⟩)
              (ObjectProperty.homMk (Prod.mkHom M.str.inv.op N.str.hom)))) ≫
        podArgumentFirstEvaluation SC β ⟨(op M.carrier, N.carrier), h⟩ =
      P.map (podArgumentFirstEvaluation SC β ⟨(op M.carrier, N.carrier), h⟩) ≫
        N.str.hom := by
  let _ := fun x ↦ sfWeilPrimeInvertible D l hl X.obj x
  subst P
  cases eq_of_heq hT
  subst H
  cases eq_of_heq hSC
  have hb : β = pullbackTensorCommonBraiding l Ω (D.geometricFiber X.obj).left := by
    funext M N
    exact eq_of_heq (_hβ M N)
  subst β
  apply evaluation_equivariant
  · intro Q R i f
    apply argumentFirst_naturality
    · exact normalizedCommonEvaluation_naturality l Ω (D.geometricFiber X.obj).left
    · intro M M' N N' f g
      apply commonStageTensorBraiding_naturality
      intro E _ _ _ M M' N N' f g
      exact localizedTensorBraiding_naturality l E (D.geometricFiber X.obj).left
        (integralBraiding_naturality l E (D.geometricFiber X.obj).left) M M' N N' f g
  · intro Q
    have h := (podArgumentFirst_common l Ω (D.geometricFrobenius X.obj).hom).1 Q
    have hk := eq_of_heq (hκ Q)
    have hm := congrArg Iso.hom (eq_of_heq (_hμ Q.obj.1.unop
      ((commonStageDerivedInternalHom l Ω (D.geometricFiber X.obj).left).obj Q)))
    simp only [Iso.app_hom] at hm
    rw [hm, hk]
    exact h

private theorem tensorLift_map_first
    {C : Type a} {D : Type b} {E : Type e}
    [Category.{c} C] [Category.{d} D] [Category.{f} E]
    {F : C ⥤ C} {G : D ⥤ D} {H : E ⥤ E}
    (T : C ⥤ D ⥤ E)
    (mu : Functor.uncurry.obj T ⋙ H ≅ F.prod G ⋙ Functor.uncurry.obj T)
    {K L : IsoAlgebra F} (h : K ⟶ L) (N : IsoAlgebra G) :
    (((IsoAlgebra.mapOfNatIso₂ T mu).map h).app N).hom.f =
      (T.map h.hom.f).app N.carrier := by
  simp [IsoAlgebra.mapOfNatIso₂, IsoAlgebra.prod]

private theorem tensorLift_map_second
    {C : Type a} {D : Type b} {E : Type e}
    [Category.{c} C] [Category.{d} D] [Category.{f} E]
    {F : C ⥤ C} {G : D ⥤ D} {H : E ⥤ E}
    (T : C ⥤ D ⥤ E)
    (mu : Functor.uncurry.obj T ⋙ H ≅ F.prod G ⋙ Functor.uncurry.obj T)
    (K : IsoAlgebra F) {M N : IsoAlgebra G} (h : M ⟶ N) :
    (((IsoAlgebra.mapOfNatIso₂ T mu).obj K).map h).hom.f =
      (T.obj K.carrier).map h.hom.f := by
  simp [IsoAlgebra.mapOfNatIso₂, IsoAlgebra.prod]

section Projection
variable {X : Type a} {Y : Type b} [Category.{c} X] [Category.{d} Y]
  (PX : X ⥤ X) (PY : Y ⥤ Y)
  (L : Y ⥤ X) (R : X ⥤ Y) (adj : L ⊣ R)
  (TX : X ⥤ X ⥤ X) (TY : Y ⥤ Y ⥤ Y)
  (cL : L ⋙ PX ≅ PY ⋙ L) (cR : R ⋙ PY ≅ PX ⋙ R)
  (muX : Functor.uncurry.obj TX ⋙ PX ≅ PX.prod PX ⋙ Functor.uncurry.obj TX)
  (muY : Functor.uncurry.obj TY ⋙ PY ≅ PY.prod PY ⋙ Functor.uncurry.obj TY)

/-- The specified proper projection mate is a Weil arrow whenever the original
adjunction and tensor comparison have their stipulated Weil lifts. The equations
on A and muW retain the actual unit, counit and tensor/pullback comparison.
These supplied categories may be any of the node's full operation domains.
Source: def-exchange-projection, pi formula, and lem-fix-weil-operations.proof.md
(blueprint: lem-pod-frobenius-evaluation-projection-coherence).
Proof: expand rightAdjointProjectionMap as eta followed by R(mu; epsilon tensor 1).
The hypotheses say that eta, epsilon and this mu are Weil arrows. Tensoring Weil
arrows, applying the standard lift of R, and composing preserve their defining
commuting equation, by naturality of the Frobenius comparisons. Thus this very
counit projection mate satisfies that equation. No projection map is inverted. -/
theorem ordinary_projection
    (mu : (Functor.postcompose₂.obj L).obj TY ≅
      (((Functor.whiskeringLeft₂ X).obj L).obj L).obj TX)
    (A : IsoAlgebra.mapOfNatIso cL ⊣ IsoAlgebra.mapOfNatIso cR)
    (_unit : ∀ K, (A.unit.app K).hom.f = adj.unit.app K.carrier)
    (_counit : ∀ K, (A.counit.app K).hom.f = adj.counit.app K.carrier)
    (muW : (Functor.postcompose₂.obj (IsoAlgebra.mapOfNatIso cL)).obj
        (IsoAlgebra.mapOfNatIso₂ TY muY) ⟶
      (((Functor.whiskeringLeft₂ (IsoAlgebra PX)).obj (IsoAlgebra.mapOfNatIso cL)).obj
        (IsoAlgebra.mapOfNatIso cL)).obj (IsoAlgebra.mapOfNatIso₂ TX muX))
    (_mu : ∀ K N, ((muW.app K).app N).hom.f =
      (mu.hom.app K.carrier).app N.carrier) :
    ∀ (M : IsoAlgebra PX) (N : IsoAlgebra PY),
      ∃ w : ((IsoAlgebra.mapOfNatIso₂ TY muY).obj
          ((IsoAlgebra.mapOfNatIso cR).obj M)).obj N ⟶
        (IsoAlgebra.mapOfNatIso cR).obj
          (((IsoAlgebra.mapOfNatIso₂ TX muX).obj M).obj
            ((IsoAlgebra.mapOfNatIso cL).obj N)),
        w.hom.f = ((adj.rightAdjointProjectionMap mu.hom).app M.carrier).app N.carrier := by
  intro M N
  refine ⟨((A.rightAdjointProjectionMap muW).app M).app N, ?_⟩
  simp only [Adjunction.rightAdjointProjectionMap_app_app, Adjunction.homEquiv_unit,
    IsoAlgebra.comp_hom_f, IsoAlgebra.mapOfNatIso_map_hom_f,
    tensorLift_map_first, _unit, _counit, _mu,
    IsoAlgebra.mapOfNatIso₂_obj_obj_carrier, IsoAlgebra.mapOfNatIso_obj_carrier]

end Projection

namespace OpenSquare
open SheafOfModules.ClopenComparisonTensorSquare
open SheafOfModules.OpenTensorNormalization
open AlgebraicGeometry.Scheme.ProjectionRestriction

/-- A presentation of the canonical tensor comparison of a supplied derived
module pullback. Ordinary normalization is the adjunction insertion of one on
pure tensors; derived normalization is its signed total map on flat K-flat pairs.
This record only names the comparisons already supplied by 07A4, including on
the vertical site, with no assumption on coefficient transitions.
Source: lem-fix-weil-operations.proof.md, open projection calculation; Stacks 07A4
(blueprint: lem-pod-frobenius-evaluation-projection-coherence). -/
structure PullbackTensor {m : Mode} {V W : Scheme.{u}} (g : V ⟶ W)
    (R : Sheaf (topology m W) CommRingCat.{u + 1})
    (S : Sheaf (topology m V) CommRingCat.{u + 1})
    (c : R ⟶ ((baseChange m g).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology m W) (topology m V)).obj S)
    (p : Pullback R S (direct m g R S c)) (a : TensorModel R) (b : TensorModel S) where
  ordinary : ∀ M N : Mod R, p.ordinary.obj (((tensor R).obj M).obj N) ≅
    ((tensor S).obj (p.ordinary.obj M)).obj (p.ordinary.obj N)
  pure_unit : ∀ (M N : Mod R) (Z : (Site m W)ᵒᵖ)
      (x : M.val.obj Z) (y : N.val.obj Z),
    (((direct m g R S c).map (ordinary M N).hom).val.app Z)
      ((p.adjunction.unit.app (((tensor R).obj M).obj N)).val.app Z
        (pure R M N Z x y)) =
    pure S (p.ordinary.obj M) (p.ordinary.obj N) ((baseChange m g).op.obj Z)
      ((p.adjunction.unit.app M).val.app Z x) ((p.adjunction.unit.app N).val.app Z y)
  preserves : ∀ P, resolving R P →
    resolving S ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P)
  comm : ∀ (P Q : CochainComplex (Mod R) ℤ) (i j : ℤ),
    totalComponent a b p.ordinary ordinary P Q i ≫
        p.ordinary.map (((total R).obj (P, Q)).d i j) =
      ((total S).obj ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P,
        (p.ordinary.mapHomologicalComplex (.up ℤ)).obj Q)).d i j ≫
          totalComponent a b p.ordinary ordinary P Q j
  comparison : a.functor ⋙ p.derived ≅ p.derived.prod p.derived ⋙ b.functor
  representative : ∀ (P Q : CochainComplex (Mod R) ℤ)
      (hp : resolving R P) (hq : resolving R Q),
    p.derived.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      comparison.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      b.functor.map (Prod.mkHom
        (derivedPullbackComplexComparison p.ordinary p.derived p.epsilon P)
        (derivedPullbackComplexComparison p.ordinary p.derived p.epsilon Q)) ≫
      b.representative.inv.app
        (⟨(p.ordinary.mapHomologicalComplex (.up ℤ)).obj P, preserves P hp⟩,
          ⟨(p.ordinary.mapHomologicalComplex (.up ℤ)).obj Q, preserves Q hq⟩) ≫
      DerivedCategory.Q.map (totalMap a b p.ordinary ordinary comm P Q) =
    derivedPullbackComplexComparison p.ordinary p.derived p.epsilon
      ((total R).obj (P, Q))

/-- The canonical tensor transports at the two horizontal arrows and the normalized
open comparison at the primed corner. Its inverse is the specified open-adjunction
transpose, so gammaPrime is not a freely chosen isomorphism.
Source: lem-sf-open-tensor-normalization and the open square in the node
(blueprint: lem-pod-frobenius-evaluation-projection-coherence). -/
structure Transport {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) where
  ambient : PullbackTensor d.g d.R d.S d.coefficient o.gPull o.tensorX o.tensorX'
  openTransport : PullbackTensor d.gU (restrictRing m d.j d.R) (restrictRing m d.j' d.S)
    (cornerCoefficient t) o.gUPull o.tensorU o.tensorU'
  restriction : ∀ M N : Mod d.S,
    (restrict m d.j' d.S).obj (((tensor d.S).obj M).obj N) ≅
      ((tensor (restrictRing m d.j' d.S)).obj ((restrict m d.j' d.S).obj M)).obj
        ((restrict m d.j' d.S).obj N)
  restriction_sections : ∀ (M N : Mod d.S) (Z : (Site m d.U')ᵒᵖ)
      (x : M.val.obj ((openInclusion m d.j').op.obj Z))
      (y : N.val.obj ((openInclusion m d.j').op.obj Z)),
    (restriction M N).hom.val.app Z
      (pure d.S M N ((openInclusion m d.j').op.obj Z) x y) =
    pure (restrictRing m d.j' d.S) ((restrict m d.j' d.S).obj M)
      ((restrict m d.j' d.S).obj N) Z x y
  restrictionComparison : TensorComparison (restrict m d.j' d.S)
    (restrictionModel d.j' d.S) o.tensorX' o.tensorU' restriction
  gammaPrime : o.opens.jShriek'.prod (𝟭 _) ⋙ o.tensorX'.functor ≅
    (𝟭 _).prod o.opens.jStar' ⋙ o.tensorU'.functor ⋙ o.opens.jShriek'
  gammaPrime_inverse : ∀ M N,
    o.opens.adj'.homEquiv _ _ (gammaPrime.inv.app (M, N)) =
      o.tensorU'.functor.map (Prod.mkHom (o.opens.adj'.unit.app M) (𝟙 _)) ≫
        restrictionComparison.comparison.inv.app (o.opens.jShriek'.obj M, N)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def transportData {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) {A : Scheme.{u}} (s : A ⟶ d.U') [IsOpenImmersion s]
    (tp : PullTensor m d.g d.R d.S d.coefficient o.gPull o.tensorX o.tensorX')
    (tq : PullTensor m d.gU (restrictRing m d.j d.R) (restrictRing m d.j' d.S)
      (cornerCoefficient t) o.gUPull o.tensorU o.tensorU')
    (e : OpenExtension m s (restrictRing m d.j' d.S))
    (ar : restrict m s (restrictRing m d.j' d.S) ⊣ e.ordinary)
    (har : ∀ M, e.adjunction.unit.app M ≫ ar.counit.app M = 𝟙 M)
    (ta : TensorModel (restrictRing m s (restrictRing m d.j' d.S)))
    (tb : OpenTensor m d.j' d.S o.opens.extension' o.tensorX' o.tensorU')
    (ts : OpenTensor m s (restrictRing m d.j' d.S) e o.tensorU' ta) :
    Data o s := by
  let L := e.ordinary.mapDerivedCategory
  let S' := (restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory
  let B := o.opens.jShriek'
  let RB := o.opens.jStar'
  let aS := exactDerivedAdjunction e.adjunction
  let aB := o.opens.adj'
  let U := ta.functor
  let dk : (L ⋙ B).prod (𝟭 _) ⋙ o.tensorX'.functor ≅
      (𝟭 _).prod (RB ⋙ S') ⋙ U ⋙ (L ⋙ B) :=
    NatIso.ofComponents
      (fun Z ↦ tb.delta.app (L.obj Z.1, Z.2) ≪≫
        B.mapIso (ts.delta.app (Z.1, RB.obj Z.2))) (by
      intro X Y f
      have hb := tb.delta.hom.naturality (Prod.mkHom (L.map f.1) f.2)
      have hs := ts.delta.hom.naturality (Prod.mkHom f.1 (RB.map f.2))
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map,
        Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at hb hs ⊢
      simp only [Iso.trans_hom, Functor.mapIso_hom]
      erw [← Category.assoc, hb, Category.assoc, ← B.map_comp, hs, B.map_comp]
      exact (Category.assoc _ _ _).symm)
  refine {
    tensorP := tp
    tensorQ := tq
    tensorB := tb
    extensionS := e
    tensorA := ta
    tensorS := ts
    rightAdjunction := ar
    counit_normalization := har
    deltaK := dk
    inverse_transposeK := ?_ }
  intro M N
  change (aS.comp aB).homEquiv _ _
    (B.map (ts.delta.inv.app (M, RB.obj N)) ≫ tb.delta.inv.app (L.obj M, N)) = _
  rw [Adjunction.comp_homEquiv]
  change aS.homEquiv _ _ ((aB.homEquiv _ _)
    (B.map (ts.delta.inv.app (M, RB.obj N)) ≫ tb.delta.inv.app (L.obj M, N))) = _
  erw [aB.homEquiv_naturality_left, tb.inverse_transpose]
  erw [aS.homEquiv_naturality_right, ts.inverse_transpose]
  dsimp only [restrictionModel, Functor.comp_obj, Functor.prod_obj,
    Functor.id_obj] at *
  have hn := ts.tensorComparison.comparison.inv.naturality
    (Prod.mkHom (aB.unit.app (L.obj M)) (𝟙 (RB.obj N)))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj,
    restrictionModel, Functor.id_obj] at hn
  rw [Functor.map_comp]
  simp only [Category.assoc]
  slice_lhs 2 3 => erw [← hn]
  simp only [← Category.assoc]
  rw [← U.map_comp]
  have hp :
      Prod.mkHom (aS.unit.app M) (𝟙 (S'.obj (RB.obj N))) ≫
        Prod.mkHom (S'.map (aB.unit.app (L.obj M))) (S'.map (𝟙 (RB.obj N))) =
      Prod.mkHom ((aS.comp aB).unit.app M) (𝟙 _) := by
    ext
    · exact (Adjunction.comp_unit_app aS aB M).symm
    · simp
  rw [hp]


/-- Canonical transports exist, for ordinary ringed sites and for arbitrary strict
inverse coefficient systems. No functor out of a tower of derived categories is
used here. Source: Stacks 07A4, 0GL1 and the node's open projection calculation
(blueprint: lem-pod-frobenius-evaluation-projection-coherence).
Proof: construct module tensor transport by insertion of one; its inverse contracts
scalars. Descend the signed total comparison on flat K-flat pairs by the canonical
ringed tensor-pullback theorem. This gives ambient and open. Restriction is exact
and sends pure tensors to their restrictions, giving restrictionComparison. The
inverse of gammaPrime is the open-adjunction transpose of unit tensor identity
followed by inverse restriction tensor. The open tensor support theorem proves
it invertible. These constructions apply on the vertical site itself and therefore
respect every semilinear transition, with no flatness condition. -/
theorem transport_exists {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) : Nonempty (Transport o) := by
  obtain ⟨p⟩ := SheafOfModules.ClopenComparisonTensorSquare.canonical_pull_tensor
    m d.g d.R d.S d.coefficient o.gPull o.tensorX o.tensorX'
  obtain ⟨q⟩ := SheafOfModules.ClopenComparisonTensorSquare.canonical_pull_tensor
    m d.gU _ _ (cornerCoefficient t) o.gUPull o.tensorU o.tensorU'
  obtain ⟨b⟩ := SheafOfModules.ClopenComparisonTensorSquare.open_tensor_exists
    d.j' d.S o.opens.extension' o.tensorX' o.tensorU'
  exact ⟨{
    ambient := {
      ordinary := p.ordinary, pure_unit := p.pure_unit, preserves := p.preserves,
      comm := p.comm, comparison := p.comparison, representative := p.representative }
    openTransport := {
      ordinary := q.ordinary, pure_unit := q.pure_unit, preserves := q.preserves,
      comm := q.comm, comparison := q.comparison, representative := q.representative }
    restriction := b.ordinary
    restriction_sections := b.pure_sections
    restrictionComparison := b.tensorComparison
    gammaPrime := b.delta
    gammaPrime_inverse := b.inverse_transpose }⟩

/-- The displayed open projection square, with its pullback compositor explicit.
This holds for every normalized presentation of the canonical comparisons, and
already in the ordinary derived category of strict systems when m=systems.
Source: lem-fix-weil-operations.proof.md, open projection paragraph
(blueprint: lem-pod-frobenius-evaluation-projection-coherence).
Proof: call the two routes A and B. The second is an isomorphism into the image of
j'_!, so both source and target lie in that image up to isomorphism. The invertible
open unit and full faithfulness of j'_! make j'^* injective on these Hom sets.
The normalization of beta and both gammas removes them after restriction. The
remaining maps are mu_s followed by the pullback compositor. On flat K-flat
representatives, tensor transport and the compositor are the same signed total
pure-tensor map; their descent identifies the two restricted routes. Thus A=B.
The identical calculation on the vertical site proves equality before realization,
without an assertion that finite evaluations detect system morphisms. -/
theorem open_square {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) (a : Assertion o) (c : Transport o)
    (M : Der (restrictRing m d.j d.R)) (N : Der d.R) :
    o.gPull.derived.map (a.gamma.hom.app (M, N)) ≫
      a.beta.hom.app (o.tensorU.functor.obj (M, o.opens.jStar.obj N)) ≫
      o.opens.jShriek'.map
        (c.openTransport.comparison.hom.app (M, o.opens.jStar.obj N) ≫
          o.tensorU'.functor.map (Prod.mkHom (𝟙 _) (o.theta.inv.app N))) =
    c.ambient.comparison.hom.app (o.opens.jShriek.obj M, N) ≫
      o.tensorX'.functor.map (Prod.mkHom (a.beta.hom.app M) (𝟙 _)) ≫
      c.gammaPrime.hom.app (o.gUPull.derived.obj M, o.gPull.derived.obj N) := by
  let p : SheafOfModules.ClopenComparisonTensorSquare.PullTensor m d.g d.R d.S
      d.coefficient o.gPull o.tensorX o.tensorX' := {
    ordinary := c.ambient.ordinary, pure_unit := c.ambient.pure_unit,
    preserves := c.ambient.preserves, comparison := c.ambient.comparison,
    comm := c.ambient.comm, representative := c.ambient.representative }
  let q : SheafOfModules.ClopenComparisonTensorSquare.PullTensor m d.gU
      (restrictRing m d.j d.R) (restrictRing m d.j' d.S) (cornerCoefficient t)
      o.gUPull o.tensorU o.tensorU' := {
    ordinary := c.openTransport.ordinary, pure_unit := c.openTransport.pure_unit,
    preserves := c.openTransport.preserves, comparison := c.openTransport.comparison,
    comm := c.openTransport.comm, representative := c.openTransport.representative }
  let b : SheafOfModules.ClopenComparisonTensorSquare.OpenTensor m d.j' d.S
      o.opens.extension' o.tensorX' o.tensorU' := {
    ordinary := c.restriction, pure_sections := c.restriction_sections,
    tensorComparison := c.restrictionComparison, delta := c.gammaPrime,
    inverse_transpose := c.gammaPrime_inverse }
  obtain ⟨e, ar, har⟩ :=
    SheafOfModules.ClopenComparisonTensorSquare.clopen_reverse_module_adjunction
      m (𝟙 d.U') (restrictRing m d.j' d.S)
  obtain ⟨ta⟩ := SheafOfModules.OpenTensorNormalization.tensorModel_exists
    (restrictRing m (𝟙 d.U') (restrictRing m d.j' d.S))
  obtain ⟨ts⟩ := SheafOfModules.ClopenComparisonTensorSquare.open_tensor_exists
    (𝟙 d.U') (restrictRing m d.j' d.S) e o.tensorU' ta
  let v := transportData o (𝟙 d.U') p q e ar har ta b ts
  have hp : v.tensorP.comparison = c.ambient.comparison := by rfl
  have hq : v.tensorQ.comparison = c.openTransport.comparison := by rfl
  have hb : v.tensorB.delta = c.gammaPrime := by rfl
  have h := SheafOfModules.ClopenComparisonTensorSquare.cartesian_tensor a v M N
  rw [hp, hq, hb] at h
  simpa only [Functor.map_comp, Category.assoc] using h

/-- Realization, rationalization and common-stage passage carry the system identity
to the specified maps, with all supplied endpoint conjugations. The functor is
applied to an equality of system maps, never to separately equal evaluations.
Source: lem-fix-weil-operations.proof.md, projection paragraph and the supplied
realizations of lem-sf-integral-compactification-system-realization
(blueprint: lem-pod-frobenius-evaluation-projection-coherence).
Proof: apply the supplied realization functor to open_square and conjugate at its
endpoints. Its expression-wise comparison identifies the images with the specified
integral composites; adjacent inverse comparisons cancel. Rationalization applies
a functor to that equality. Common-stage passage takes the resulting finite-field
map as its morphism class using exchangeProjectionCoefficientRepresentative.
Identity and tower comparisons of def-exchange-projection identify all larger
representatives. The statement permits every supplied realization and hence also
its composite with localization or inclusion at any common field. -/
theorem realized_open_square {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) (a : Assertion o) (c : Transport o)
    (M : Der (restrictRing m d.j d.R)) (N : Der d.R)
    {B : Type e} [Category.{f} B] (F : Der d.S ⥤ B)
    (S T : B)
    (s : S ≅ F.obj (o.gPull.derived.obj
      (o.tensorX.functor.obj (o.opens.jShriek.obj M, N))))
    (z : F.obj (o.opens.jShriek'.obj (o.tensorU'.functor.obj
      (o.gUPull.derived.obj M, o.opens.jStar'.obj (o.gPull.derived.obj N)))) ≅ T) :
    exchangeProjectionCoefficientRepresentative F s z
      (o.gPull.derived.map (a.gamma.hom.app (M, N)) ≫
        a.beta.hom.app (o.tensorU.functor.obj (M, o.opens.jStar.obj N)) ≫
        o.opens.jShriek'.map
          (c.openTransport.comparison.hom.app (M, o.opens.jStar.obj N) ≫
            o.tensorU'.functor.map (Prod.mkHom (𝟙 _) (o.theta.inv.app N)))) =
    exchangeProjectionCoefficientRepresentative F s z
      (c.ambient.comparison.hom.app (o.opens.jShriek.obj M, N) ≫
        o.tensorX'.functor.map (Prod.mkHom (a.beta.hom.app M) (𝟙 _)) ≫
        c.gammaPrime.hom.app (o.gUPull.derived.obj M, o.gPull.derived.obj N)) := by
  exact congrArg (exchangeProjectionCoefficientRepresentative F s z)
    (open_square o a c M N)

end OpenSquare

section CompactProjection
variable {X : Type a} {B : Type b} {Y : Type e}
  [Category.{c} X] [Category.{d} B] [Category.{f} Y]
  (PX : X ⥤ X) (PB : B ⥤ B) (PY : Y ⥤ Y)
  (J : X ⥤ B) (jStar : B ⥤ X) (jAdj : J ⊣ jStar)
  (P : Y ⥤ B) (R : B ⥤ Y) (pAdj : P ⊣ R)
  (TX : X ⥤ X ⥤ X) (TB : B ⥤ B ⥤ B) (TY : Y ⥤ Y ⥤ Y)
  (cJ : J ⋙ PB ≅ PX ⋙ J) (cStar : jStar ⋙ PX ≅ PB ⋙ jStar)
  (cP : P ⋙ PB ≅ PY ⋙ P) (cR : R ⋙ PY ≅ PB ⋙ R)
  (muX : Functor.uncurry.obj TX ⋙ PX ≅ PX.prod PX ⋙ Functor.uncurry.obj TX)
  (muB : Functor.uncurry.obj TB ⋙ PB ≅ PB.prod PB ⋙ Functor.uncurry.obj TB)
  (muY : Functor.uncurry.obj TY ⋙ PY ≅ PY.prod PY ⋙ Functor.uncurry.obj TY)

/-- The open projection has exactly the prescribed inverse adjunction transpose.
The output w has gamma itself as carrier, so this is its Weil equation, without
replacing the specified map by another isomorphism.
Source: lem-sf-open-tensor-normalization, inverse gamma characterization
(blueprint: lem-pod-frobenius-evaluation-projection-coherence).
Proof: expand the inverse gamma as the open-unit projection map of
j_! left adjoint to j^*. Its three factors are tensoring the open unit, the inverse
tensor/restriction comparison, and the open counit. All are Weil arrows by the
stipulated ordinary-adjunction and tensor/pullback hypotheses. Their composite is
a Weil arrow with the actual inverse gamma as carrier. Since gamma is already an
isomorphism, cancellation of that inverse gives the Weil equation for gamma.
This is also obtained by specializing open_square to the Frobenius square and
postcomposing by j_! of the two input structures. -/
theorem open_projection
    (mu : (Functor.postcompose₂.obj jStar).obj TB ≅
      (((Functor.whiskeringLeft₂ X).obj jStar).obj jStar).obj TX)
    (A : IsoAlgebra.mapOfNatIso cJ ⊣ IsoAlgebra.mapOfNatIso cStar)
    (_unit : ∀ K, (A.unit.app K).hom.f = jAdj.unit.app K.carrier)
    (_counit : ∀ K, (A.counit.app K).hom.f = jAdj.counit.app K.carrier)
    (muW : (Functor.postcompose₂.obj (IsoAlgebra.mapOfNatIso cStar)).obj
        (IsoAlgebra.mapOfNatIso₂ TB muB) ≅
      (((Functor.whiskeringLeft₂ (IsoAlgebra PX)).obj
        (IsoAlgebra.mapOfNatIso cStar)).obj (IsoAlgebra.mapOfNatIso cStar)).obj
          (IsoAlgebra.mapOfNatIso₂ TX muX))
    (_mu : ∀ K N, ((muW.hom.app K).app N).hom.f =
      (mu.hom.app K.carrier).app N.carrier)
    (gamma : (((Functor.whiskeringLeft₂ B).obj J).obj (𝟭 B)).obj TB ≅
      (Functor.postcompose₂.obj J).obj
        ((((Functor.whiskeringLeft₂ X).obj (𝟭 X)).obj jStar).obj TX))
    (_normalization : gamma.inv = jAdj.projectionMap jStar TX TB mu.inv) :
    ∀ (M : IsoAlgebra PX) (N : IsoAlgebra PB),
      ∃ w : ((IsoAlgebra.mapOfNatIso₂ TB muB).obj
          ((IsoAlgebra.mapOfNatIso cJ).obj M)).obj N ⟶
        (IsoAlgebra.mapOfNatIso cJ).obj
          (((IsoAlgebra.mapOfNatIso₂ TX muX).obj M).obj
            ((IsoAlgebra.mapOfNatIso cStar).obj N)),
        w.hom.f = (gamma.hom.app M.carrier).app N.carrier := by
  intro M N
  let q := ((A.projectionMap (IsoAlgebra.mapOfNatIso cStar)
    (IsoAlgebra.mapOfNatIso₂ TX muX) (IsoAlgebra.mapOfNatIso₂ TB muB)
      muW.inv).app M).app N
  have hmu (K L : IsoAlgebra PB) : ((muW.inv.app K).app L).hom.f =
      (mu.inv.app K.carrier).app L.carrier := by
    apply (cancel_epi ((mu.hom.app K.carrier).app L.carrier)).1
    have h := congrArg (fun f ↦ (IsoAlgebra.forget PX).map f)
      (NatTrans.congr_app (NatTrans.congr_app muW.hom_inv_id K) L)
    change ((muW.hom.app K).app L).hom.f ≫ ((muW.inv.app K).app L).hom.f =
      𝟙 _ at h
    rw [_mu] at h
    exact h.trans (Iso.hom_inv_id_app_app mu K.carrier L.carrier).symm
  have hq : q.hom.f = (gamma.inv.app M.carrier).app N.carrier := by
    rw [_normalization]
    change J.map
        ((((IsoAlgebra.mapOfNatIso₂ TX muX).map (A.unit.app M)).app
            ((IsoAlgebra.mapOfNatIso cStar).obj N)).hom.f ≫
          ((muW.inv.app ((IsoAlgebra.mapOfNatIso cJ).obj M)).app N).hom.f) ≫
        (A.counit.app (((IsoAlgebra.mapOfNatIso₂ TB muB).obj
          ((IsoAlgebra.mapOfNatIso cJ).obj M)).obj N)).hom.f =
      J.map ((TX.map (jAdj.unit.app M.carrier)).app (jStar.obj N.carrier) ≫
        (mu.inv.app (J.obj M.carrier)).app N.carrier) ≫
          jAdj.counit.app ((TB.obj (J.obj M.carrier)).obj N.carrier)
    simp only [tensorLift_map_first, _unit, _counit, hmu,
      IsoAlgebra.mapOfNatIso₂_obj_obj_carrier, IsoAlgebra.mapOfNatIso_obj_carrier]
  have : IsIso ((IsoAlgebra.forget PB).map q) := by
    change IsIso q.hom.f
    rw [hq]
    infer_instance
  have : IsIso q := isIso_of_reflects_iso q (IsoAlgebra.forget PB)
  refine ⟨inv q, ?_⟩
  apply (cancel_epi ((gamma.inv.app M.carrier).app N.carrier)).1
  have h := congrArg (fun f ↦ (IsoAlgebra.forget PB).map f) (IsIso.hom_inv_id q)
  change q.hom.f ≫ (inv q).hom.f = 𝟙 _ at h
  rw [hq] at h
  exact h.trans (Iso.inv_hom_id_app_app gamma M.carrier N.carrier).symm

/-- The actual chosen-compactification projection Rp_*(gamma) pi_p is a Weil
arrow. All hypotheses are the assumed ordinary adjunction and tensor/pullback
Weil maps, together with the normalized open gamma. The supplied Weil pullback
compositor phi identifies j^*p^* with the actual pullback F=f^*.
The source and target retain their given full coefficient domains.
Source: def-exchange-projection, compactification projection formula, and
lem-fix-weil-operations.proof.md, projection paragraph
(blueprint: lem-pod-frobenius-evaluation-projection-coherence).
Proof: ordinary_projection applied to p gives a Weil lift of pi_p. Apply
open_projection to the normalized inverse-gamma transpose; its proof uses the
already stipulated open adjunction maps and tensor/restriction comparison.
Evaluate at (K,p^*L), apply the standard lift of R, and compose with pi_p.
The carrier is exactly compactificationProjectionFromData. For a compactification
not defined over k_0, use a k_0-compactification supplied by Nagata, base change it,
and conjugate by the canonical refinement comparison. The supplied refinement
comparisons are Weil arrows; the projection/refinement identity identifies the
result with this same chosen-compactification map. -/
theorem compact_projection
    (F : Y ⥤ X) (cF : F ⋙ PX ≅ PY ⋙ F)
    (phi : P ⋙ jStar ≅ F)
    (phiW : IsoAlgebra.mapOfNatIso cP ⋙ IsoAlgebra.mapOfNatIso cStar ≅
      IsoAlgebra.mapOfNatIso cF)
    (_phi : ∀ N, (phiW.hom.app N).hom.f = phi.hom.app N.carrier)
    (muP : (Functor.postcompose₂.obj P).obj TY ≅
      (((Functor.whiskeringLeft₂ B).obj P).obj P).obj TB)
    (muJ : (Functor.postcompose₂.obj jStar).obj TB ≅
      (((Functor.whiskeringLeft₂ X).obj jStar).obj jStar).obj TX)
    (AP : IsoAlgebra.mapOfNatIso cP ⊣ IsoAlgebra.mapOfNatIso cR)
    (_unitP : ∀ K, (AP.unit.app K).hom.f = pAdj.unit.app K.carrier)
    (_counitP : ∀ K, (AP.counit.app K).hom.f = pAdj.counit.app K.carrier)
    (AJ : IsoAlgebra.mapOfNatIso cJ ⊣ IsoAlgebra.mapOfNatIso cStar)
    (_unitJ : ∀ K, (AJ.unit.app K).hom.f = jAdj.unit.app K.carrier)
    (_counitJ : ∀ K, (AJ.counit.app K).hom.f = jAdj.counit.app K.carrier)
    (muPW : (Functor.postcompose₂.obj (IsoAlgebra.mapOfNatIso cP)).obj
        (IsoAlgebra.mapOfNatIso₂ TY muY) ⟶
      (((Functor.whiskeringLeft₂ (IsoAlgebra PB)).obj
        (IsoAlgebra.mapOfNatIso cP)).obj (IsoAlgebra.mapOfNatIso cP)).obj
          (IsoAlgebra.mapOfNatIso₂ TB muB))
    (_muP : ∀ K N, ((muPW.app K).app N).hom.f =
      (muP.hom.app K.carrier).app N.carrier)
    (muJW : (Functor.postcompose₂.obj (IsoAlgebra.mapOfNatIso cStar)).obj
        (IsoAlgebra.mapOfNatIso₂ TB muB) ≅
      (((Functor.whiskeringLeft₂ (IsoAlgebra PX)).obj
        (IsoAlgebra.mapOfNatIso cStar)).obj (IsoAlgebra.mapOfNatIso cStar)).obj
          (IsoAlgebra.mapOfNatIso₂ TX muX))
    (_muJ : ∀ K N, ((muJW.hom.app K).app N).hom.f =
      (muJ.hom.app K.carrier).app N.carrier)
    (gamma : (((Functor.whiskeringLeft₂ B).obj J).obj (𝟭 B)).obj TB ≅
      (Functor.postcompose₂.obj J).obj
        ((((Functor.whiskeringLeft₂ X).obj (𝟭 X)).obj jStar).obj TX))
    (_normalization : gamma.inv = jAdj.projectionMap jStar TX TB muJ.inv)
    (gammaP : (((Functor.whiskeringLeft₂ B).obj J).obj P).obj TB ≅
      (Functor.postcompose₂.obj J).obj
        ((((Functor.whiskeringLeft₂ X).obj (𝟭 X)).obj F).obj TX))
    (_gammaP : ∀ M N, (gammaP.hom.app M).app N =
      (gamma.hom.app M).app (P.obj N) ≫
        J.map ((TX.obj M).map (phi.hom.app N))) :
    ∀ (K : IsoAlgebra PX) (N : IsoAlgebra PY),
      ∃ w : ((IsoAlgebra.mapOfNatIso₂ TY muY).obj
          ((IsoAlgebra.mapOfNatIso cR).obj ((IsoAlgebra.mapOfNatIso cJ).obj K))).obj N ⟶
        (IsoAlgebra.mapOfNatIso cR).obj ((IsoAlgebra.mapOfNatIso cJ).obj
          (((IsoAlgebra.mapOfNatIso₂ TX muX).obj K).obj
            ((IsoAlgebra.mapOfNatIso cF).obj N))),
        w.hom.f = ((compactificationProjectionFromData J F P R pAdj
          TX TB TY muP gammaP).app K.carrier).app N.carrier := by
  intro K N
  obtain ⟨pi, hpi⟩ := ordinary_projection PB PY P R pAdj TB TY cP cR muB muY
    muP AP _unitP _counitP muPW _muP ((IsoAlgebra.mapOfNatIso cJ).obj K) N
  obtain ⟨ga, hga⟩ := open_projection PX PB J jStar jAdj TX TB cJ cStar muX muB
    muJ AJ _unitJ _counitJ muJW _muJ gamma _normalization K
      ((IsoAlgebra.mapOfNatIso cP).obj N)
  let w := pi ≫ (IsoAlgebra.mapOfNatIso cR).map
    (ga ≫ (IsoAlgebra.mapOfNatIso cJ).map
      (((IsoAlgebra.mapOfNatIso₂ TX muX).obj K).map (phiW.hom.app N)))
  refine ⟨w, ?_⟩
  change pi.hom.f ≫ R.map (ga.hom.f ≫ J.map
    ((((IsoAlgebra.mapOfNatIso₂ TX muX).obj K).map (phiW.hom.app N)).hom.f)) = _
  rw [hpi, hga, tensorLift_map_second, _phi]
  change ((pAdj.rightAdjointProjectionMap muP.hom).app (J.obj K.carrier)).app
      N.carrier ≫ R.map ((gamma.hom.app K.carrier).app (P.obj N.carrier) ≫
        J.map ((TX.obj K.carrier).map (phi.hom.app N.carrier))) =
    ((pAdj.rightAdjointProjectionMap muP.hom).app (J.obj K.carrier)).app N.carrier ≫
      R.map ((gammaP.hom.app K.carrier).app N.carrier)
  rw [_gammaP]

end CompactProjection

/-- Refinement compatibility is an equality of the actual Weil arrows, detected by
forgetting just the structure. The underlying equality is the supplied projection
refinement comparison, with all original finite-Tor and witnessed-origin domains.
Source: lem-fix-projection-compactification-comparison, displayed rho identity
(blueprint: lem-pod-frobenius-evaluation-projection-coherence).
Proof: expand the six carrier equalities and substitute the supplied underlying
refinement identity. Faithfulness of IsoAlgebra.forget proves equality of the two
composites. For an arbitrary compactification, conjugation by rho and its inverse
also transports the Weil equation from a model compactification. -/
theorem refinement_compatibility
    {B : Type a} [Category.{b} B] (P : B ⥤ B)
    {S₁ S₂ T₁ T₂ : IsoAlgebra P}
    (pf₁ : S₁ ⟶ T₁) (pf₂ : S₂ ⟶ T₂) (rhoS : S₁ ⟶ S₂) (rhoT : T₁ ⟶ T₂)
    (_underlying : pf₁.hom.f ≫ rhoT.hom.f = rhoS.hom.f ≫ pf₂.hom.f) :
    pf₁ ≫ rhoT = rhoS ≫ pf₂ := by
  apply (IsoAlgebra.forget P).map_injective
  exact _underlying

/-- Transport from a model compactification to an arbitrary representative uses
exactly the supplied refinement isomorphisms. The second projection is initially
only its specified underlying map; the conclusion supplies its Weil equation.
Source: lem-fix-weil-operations.proof.md, refinement paragraph
(blueprint: lem-pod-frobenius-evaluation-projection-coherence).
Proof: conjugate pf₁ by rhoS inverse and rhoT to obtain a Weil arrow. The assumed
underlying canonical projection/refinement identity, after cancellation of rhoS,
identifies its carrier with pf₂. Transport along that equality produces w. The
faithful forgetful functor then gives the claimed equality of Weil arrows. No
inverse to a projection map is used, only inverses to refinement comparisons. -/
theorem refinement_transport
    {B : Type a} [Category.{b} B] (P : B ⥤ B)
    {S₁ S₂ T₁ T₂ : IsoAlgebra P}
    (pf₁ : S₁ ⟶ T₁) (pf₂ : S₂.carrier ⟶ T₂.carrier)
    (rhoS : S₁ ≅ S₂) (rhoT : T₁ ≅ T₂)
    (_underlying : pf₁.hom.f ≫ rhoT.hom.hom.f = rhoS.hom.hom.f ≫ pf₂) :
    ∃ w : S₂ ⟶ T₂, w.hom.f = pf₂ ∧ pf₁ ≫ rhoT.hom = rhoS.hom ≫ w := by
  let w : S₂ ⟶ T₂ := rhoS.inv ≫ pf₁ ≫ rhoT.hom
  refine ⟨w, ?_, ?_⟩
  · change rhoS.inv.hom.f ≫ pf₁.hom.f ≫ rhoT.hom.hom.f = pf₂
    rw [_underlying, ← Category.assoc]
    have h := congrArg (fun f ↦ (IsoAlgebra.forget P).map f) rhoS.inv_hom_id
    change rhoS.inv.hom.f ≫ rhoS.hom.hom.f = 𝟙 S₂.carrier at h
    rw [h, Category.id_comp]
  · dsimp [w]
    simp only [Iso.hom_inv_id_assoc]

end WeilConjectures.PodEvaluationProjection
