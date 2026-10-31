/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses
public import WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionUniverses
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientHomChange
public import WeilConjectures.AlgebraicGeometry.IntegralHomReduction
public import WeilConjectures.SixFunctors.CoefIntegralFiniteExtension
public import WeilConjectures.AlgebraicGeometry.BasicOperationsCoefficientReduction
import WeilConjectures.AlgebraicGeometry.CoefficientTensorNormalization
import WeilConjectures.AlgebraicGeometry.IntegralHomPresentationEvaluation
import WeilConjectures.AlgebraicGeometry.ScalarHomPresentationEvaluation
import WeilConjectures.AlgebraicGeometry.IntegralHomComparisonIsIso
import WeilConjectures.AlgebraicGeometry.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
/-! # General internal-Hom coefficient comparison cocycles

Source: current blueprint, sec-six-functors/sk-thm-sf-compatibility,
fix-prop-coherence.proof.md, general Hom and coefficient-transport sentences
(blueprint: lem-sf-general-hom-comparison-cocycles).

All finite indices denote exponent n+1. The auxiliary declarations spell out
clauses of this one coherence statement using the published canonical maps.
The two tensor orders are identified by their evaluation normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
namespace GeneralHomComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The canonical identification of identity quotient extension, as the mate of
identity restriction. Source: blueprint identity coefficient change
(blueprint: lem-sf-general-hom-comparison-cocycles). -/
def finiteUnit (n : ℕ) :
    coefficientFiniteQuotientDerived l E X (Nat.le_refl n) ≅ 𝟭 _ :=
  Adjunction.leftAdjointIdIso
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction
      (Nat.le_refl n)) (normalizedDVRResUnit l E X n)

/-- Successive integral and finite reduction, as the mate of the actual restriction
composition identification. Source: blueprint integral-to-finite overlap
(blueprint: lem-sf-general-hom-comparison-cocycles). -/
def integralAssoc (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {n m : ℕ} (h : m ≤ n) :
    coefficientFiniteDerivedExtension l E X n ⋙ coefficientFiniteQuotientDerived l E X h ≅
      coefficientFiniteDerivedExtension l E X m :=
  Adjunction.leftAdjointCompIso (coefficientFiniteAdjunction l E X n)
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h)
    (coefficientFiniteAdjunction l E X m) (normalizedDVRResCompletedComp l E X D hl h)

/-- Reduced evaluation transposed in the published closed calculus. This names the
same c_n as the integral theorem, using Hom before its input in the tensor order.
Source: blueprint reduced-evaluation sentence
(blueprint: lem-sf-general-hom-comparison-cocycles). -/
def integralMap (n : ℕ) :=
  coefficientBaseChangeHom (scalarIntegralClosed l E X) (finiteIntrinsicClosed l E X n)
    (coefficientFiniteDerivedExtension l E X n)
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.finiteTensor n)

/-- The identity and successive-quotient equations for the specified finite v maps.
Only the finite-Tor constructible inputs in the node are used.
Source: blueprint identity coefficient change; thm-coef-finite-hom
(blueprint: lem-sf-general-hom-comparison-cocycles). -/
def finiteLaws : Prop :=
  (∀ (n : ℕ) (K M : normalizedDVRDerived l E X n),
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X K →
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X M →
    proEtaleFiniteHomCanonical l E X (Nat.le_refl n) K M ≫
        (coefficientFiniteInternalHom l E X n).map
          (Prod.mkHom ((finiteUnit l E X n).inv.app K).op
            ((finiteUnit l E X n).hom.app M)) =
      (finiteUnit l E X n).hom.app ((coefficientFiniteInternalHom l E X n).obj (op K, M))) ∧
  ∀ (n m : ℕ) (h : m ≤ n), FiniteHomIntrinsicCocycle l E X h

/-- The displayed integral-to-finite cocycle, with all three successive tensor
identifications explicit. There is no completeness or perfection assumption on
ambient K,M; the only domain condition is the stated finite-Tor condition at n.
Source: blueprint integral-to-finite overlap
(blueprint: lem-sf-general-hom-comparison-cocycles). -/
def integralLaws (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) : Prop :=
  ∀ (n m : ℕ) (h : m ≤ n)
    (K M : DerivedCategory (scalarReductionSource l E X)),
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X
      ((coefficientFiniteDerivedExtension l E X n).obj K) →
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X
      ((coefficientFiniteDerivedExtension l E X n).obj M) →
    (integralAssoc l E X D hl h).hom.app
        ((coefficientIntegralInternalHom l E X).obj (op K, M)) ≫ integralMap l E X m K M =
      (coefficientFiniteQuotientDerived l E X h).map (integralMap l E X n K M) ≫
        proEtaleFiniteHomCanonical l E X h
          ((coefficientFiniteDerivedExtension l E X n).obj K)
          ((coefficientFiniteDerivedExtension l E X n).obj M) ≫
        (coefficientFiniteInternalHom l E X m).map
          (Prod.mkHom ((integralAssoc l E X D hl h).inv.app K).op
            ((integralAssoc l E X D hl h).hom.app M))

/-- Agreement with the actual elementary finite arrow on its site-perfect overlap,
and with the arbitrary-variable integral reduction theorem for jointly chosen
source and reduction presentations. The equality fixes their comparisons on every
ambient input; K-flat normalization alone does not fix an arbitrary adjunction.
Source: blueprint agreement of general and elementary Hom comparisons
(blueprint: lem-sf-general-hom-comparison-cocycles). -/
def elementaryAgreement (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) : Prop :=
  (∀ (n m : ℕ) (h : m ≤ n) (K M : normalizedDVRDerived l E X n),
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X K →
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X M →
    IsProEtaleSitePerfect X (integralCoefficientCommRingSheaf l E X n) K →
    proEtaleFiniteHomCanonical l E X h K M = finiteIntrinsicReductionHom l E X h K M) ∧
  ∃ a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl),
    ∀ n : ℕ, ∃ m : IntegralHom.ReductionPresentation l E X D hl a n,
      ∀ K M : completedIntegralDerivedCategory l E X D hl,
        IsIso (IntegralHom.comparison l E X D hl m K M) ∧
        integralMap l E X n K M = IntegralHom.comparison l E X D hl m K M

/-- Equality of the completed scalar Hom comparison of the integral finite-extension
theorem and the elementary completed comparison, with the prescribed completion
units, on the integral bounded constructible domain. The source and target tensor
presentations are chosen jointly with this equality, as in the existential
finite-extension theorem, rather than quantified as arbitrary presentations.
Source: blueprint finite coefficient-field extension overlap
(blueprint: lem-sf-general-hom-comparison-cocycles). -/
def scalarAgreement : Prop :=
  ∀ (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L),
    ∃ (a : IntegralHom.TensorPresentation.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l E X))
      (b : IntegralHom.TensorPresentation.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l L X)),
      ∀ (K M : DerivedCategory (scalarReductionSource l E X))
        (hK : sfIntegralConstructible l E X K) (hM : sfIntegralConstructible l E X M),
        IsIso (IntegralFiniteExtension.v l E L ι X a b K M hK.1 hM.1) ∧
        IntegralFiniteExtension.v l E L ι X a b K M hK.1 hM.1 =
          (scalarHomCompleteInputs l E L ι X K M hK.1 hM.1).hom

/-- The reassociation square for a specified tensor comparison. This is the
three-factor equation, rather than an unnormalized choice of monoidal structure.
Source: blueprint tensor reassociation sentence
(blueprint: lem-sf-general-hom-comparison-cocycles). -/
def tensorReassociation
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) : Prop :=
  ∀ K M N : A,
    μ.hom.app (SA.tensor.obj (K, M), N) ≫
        SB.tensor.map (Prod.mkHom (μ.hom.app (K, M)) (𝟙 (F.obj N))) ≫
        (SB.monoidal.associator (F.obj K) (F.obj M) (F.obj N)).hom =
      F.map (SA.monoidal.associator K M N).hom ≫
        μ.hom.app (K, SA.tensor.obj (M, N)) ≫
        SB.tensor.map (Prod.mkHom (𝟙 (F.obj K)) (μ.hom.app (M, N)))

/-- Evaluation, arbitrary tensor-Hom transposes, internal composition, naturality
and reassociation for the actual finite, integral and ordinary scalar maps.
Completed scalar comparisons use scalarAgreement to transport these equations
through the canonical completeness units.
Source: blueprint evaluations, transposes and tensor reassociation sentence
(blueprint: lem-sf-general-hom-comparison-cocycles). -/
def evaluationCoherence : Prop :=
  (∀ (n m : ℕ) (h : m ≤ n),
    CoefficientEvaluationCompatible (finiteIntrinsicClosed l E X n)
      (finiteIntrinsicClosed l E X m) (coefficientFiniteQuotientDerived l E X h)
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h) ∧
    FiniteHomEvaluation (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
      (coefficientFiniteQuotientDerived l E X h)
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h) ∧
    tensorReassociation (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
      (coefficientFiniteQuotientDerived l E X h)
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h)) ∧
  (∀ n : ℕ,
    CoefficientEvaluationCompatible (scalarIntegralClosed l E X) (finiteIntrinsicClosed l E X n)
      (coefficientFiniteDerivedExtension l E X n)
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.finiteTensor n) ∧
    FiniteHomEvaluation (scalarIntegralClosed l E X) (finiteIntrinsicClosed l E X n)
      (coefficientFiniteDerivedExtension l E X n)
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.finiteTensor n) ∧
    tensorReassociation (scalarIntegralClosed l E X) (finiteIntrinsicClosed l E X n)
      (coefficientFiniteDerivedExtension l E X n)
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.finiteTensor n)) ∧
  ∀ (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L),
    CoefficientEvaluationCompatible (scalarIntegralClosed l E X) (scalarIntegralClosed l L X)
      (integralOrdinaryDerivedScalar l E L ι X) (scalarClosedTensor l E L ι X) ∧
    FiniteHomEvaluation (scalarIntegralClosed l E X) (scalarIntegralClosed l L X)
      (integralOrdinaryDerivedScalar l E L ι X) (scalarClosedTensor l E L ι X) ∧
    tensorReassociation (scalarIntegralClosed l E X) (scalarIntegralClosed l L X)
      (integralOrdinaryDerivedScalar l E L ι X) (scalarClosedTensor l E L ι X)

/-- The elementary rational comparison is the raw localization of the specified
integral comparison; common-stage Hom uses that comparison on every representative.
The equation clauses quantify all parallel arrows, so also every equation between
finite composites of the comparison, evaluation and associativity maps.
Source: blueprint raw localization and common finite-stage passage
(blueprint: lem-sf-general-hom-comparison-cocycles). -/
def fieldTransport (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] : Prop :=
  (∀ (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (P : (constructibleRationalHomPairs l E X).FullSubcategory),
    HEq (rationalHomScalarComparison l E L ι X P).hom
      ((sfRationalConstructibleLocalization l L X).map
        (integralHomScalarComparison l E L ι X (integralPairOfRationalHomPair l E X P)).hom)) ∧
  commonStageInternalHomRepresentativeLaws l Ω X ∧
  (∀ (K M : sfIntegralConstructibleCategory l E X) (f g : K ⟶ M), f = g →
    (sfRationalConstructibleLocalization l E X).map f =
      (sfRationalConstructibleLocalization l E X).map g) ∧
  (∀ (L F : Padic.FiniteCoefficientFields l Ω) (h : L ≤ F)
    (K M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L) (f g : K ⟶ M), f = g →
    (GeneralAlgebraicallyClosedCoefficients.transition l Ω X L F h).map f =
      (GeneralAlgebraicallyClosedCoefficients.transition l Ω X L F h).map g) ∧
  ∀ (L : Padic.FiniteCoefficientFields l Ω)
    (K M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L) (f g : K ⟶ M), f = g →
    (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) L).map f =
      (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) L).map g

private theorem scalarEvaluation_naturality
    {D : Type*} [Category.{c} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (P Q P' Q' : D)
    (f : P' ⟶ P) (g : Q ⟶ Q') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 P')) ≫
        S.evaluation P' Q' =
      S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q ≫ g := by
  let := S.monoidal
  have he : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P')) ≫
      S.evaluation P' Q = S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      S.evaluation_naturality P P' Q f
  have hg : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P')) ≫
      S.evaluation P' Q' = S.evaluation P' Q ≫ g := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      (S.adjunction P').counit.naturality g
  have hh : H.map (Prod.mkHom f.op g) =
      H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g) := by
    rw [← H.map_comp]
    congr 1
    ext <;> simp
  rw [hh]
  have ht : Prod.mkHom
      (H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') := by
    ext <;> simp
  rw [ht, S.tensor.map_comp, Category.assoc, hg, ← Category.assoc, he]
  exact Category.assoc _ _ _

private theorem scalarUncurry
    {D : Type*} [Category.{c} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (T P Q : D) (h : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm h =
      S.tensor.map (Prod.mkHom h (𝟙 P)) ≫ S.evaluation P Q := by
  let := S.monoidal
  simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    CoefficientClosedStructure.evaluation] using! (S.adjunction P).homEquiv_counit T Q h

private theorem scalarTensor_comp
    {D : Type*} [Category.{c} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {X Y Z U V W : D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : U ⟶ V) (k : V ⟶ W) :
    S.tensor.map (Prod.mkHom (f ≫ g) (h ≫ k)) =
      S.tensor.map (Prod.mkHom f h) ≫ S.tensor.map (Prod.mkHom g k) :=
  S.tensor.map_comp (Prod.mkHom f h) (Prod.mkHom g k)

private theorem scalarUncurry_pre
    {D : Type*} [Category.{c} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {T U P Q : D}
    (f : T ⟶ U) (h : U ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm (f ≫ h) =
      S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ (S.transpose U P Q).symm h := by
  rw [scalarUncurry, scalarUncurry]
  simpa only [Category.id_comp, Category.assoc] using
    congrArg (fun k => k ≫ S.evaluation P Q) (scalarTensor_comp S f h (𝟙 P) (𝟙 P))

private theorem scalarUncurry_post
    {D : Type*} [Category.{c} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {T P Q P' Q' : D}
    (h : T ⟶ H.obj (op P, Q)) (f : P' ⟶ P) (g : Q ⟶ Q') :
    (S.transpose T P' Q').symm (h ≫ H.map (Prod.mkHom f.op g)) =
      S.tensor.map (Prod.mkHom (𝟙 T) f) ≫ (S.transpose T P Q).symm h ≫ g := by
  rw [scalarUncurry_pre, scalarUncurry, scalarEvaluation_naturality]
  rw [scalarUncurry]
  simp only [← Category.assoc, ← S.tensor.map_comp]
  congr 2
  congr 1
  ext <;> simp

private theorem scalarBaseChangeHom_beta
    {A : Type*} {B : Type*} [Category.{c} A] [Category.{d} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (P Q : A) :
    (SB.transpose _ (F.obj P) (F.obj Q)).symm (coefficientBaseChangeHom SA SB F μ P Q) =
      μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q) :=
  Equiv.symm_apply_apply _ _

private theorem scalarBaseChangeHom_tower
    {A : Type*} {B : Type*} {D : Type b}
    [Category.{c} A] [Category.{d} B] [Category.{c} D]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B} {HD : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SD : CoefficientClosedStructure HD) (F : A ⥤ B) (G : B ⥤ D) (K : A ⥤ D)
    (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (ν : SB.tensor ⋙ G ≅ G.prod G ⋙ SD.tensor)
    (ξ : SA.tensor ⋙ K ≅ K.prod K ⋙ SD.tensor) (α : F ⋙ G ≅ K)
    (ht : ∀ X Y : A,
      G.map (μ.hom.app (X, Y)) ≫ ν.hom.app (F.obj X, F.obj Y) ≫
          SD.tensor.map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) =
        α.hom.app (SA.tensor.obj (X, Y)) ≫ ξ.hom.app (X, Y)) (P Q : A) :
    G.map (coefficientBaseChangeHom SA SB F μ P Q) ≫
        coefficientBaseChangeHom SB SD G ν (F.obj P) (F.obj Q) ≫
        HD.map (Prod.mkHom (α.inv.app P).op (α.hom.app Q)) =
      α.hom.app (HA.obj (op P, Q)) ≫ coefficientBaseChangeHom SA SD K ξ P Q := by
  have hi (X Y : A) :
      ν.inv.app (F.obj X, F.obj Y) ≫ G.map (μ.inv.app (X, Y)) ≫
          α.hom.app (SA.tensor.obj (X, Y)) =
        SD.tensor.map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) ≫ ξ.inv.app (X, Y) := by
    apply (cancel_mono (ξ.hom.app (X, Y))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← ht]
    simp [← G.map_comp, ← Category.assoc]
  have he : (SD.transpose _ (G.obj (F.obj P)) (G.obj (F.obj Q))).symm
      (G.map (coefficientBaseChangeHom SA SB F μ P Q) ≫
        coefficientBaseChangeHom SB SD G ν (F.obj P) (F.obj Q)) =
      ν.inv.app (F.obj (HA.obj (op P, Q)), F.obj P) ≫
        G.map (μ.inv.app (HA.obj (op P, Q), P)) ≫ G.map (F.map (SA.evaluation P Q)) := by
    rw [scalarUncurry_pre, scalarBaseChangeHom_beta]
    have hn := ν.inv.naturality
      (Prod.mkHom (coefficientBaseChangeHom SA SB F μ P Q) (𝟙 (F.obj P)))
    dsimp only [Functor.comp_map, Functor.prod_map] at hn
    erw [G.map_id] at hn
    rw [← Category.assoc, hn, Category.assoc, ← G.map_comp]
    rw [← scalarUncurry, scalarBaseChangeHom_beta, G.map_comp]
  apply (SD.transpose _ (K.obj P) (K.obj Q)).symm.injective
  rw [← Category.assoc, scalarUncurry_post, he, scalarUncurry_pre,
    scalarBaseChangeHom_beta]
  have hn := α.hom.naturality (SA.evaluation P Q)
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [hn, reassoc_of% hi (HA.obj (op P, Q)) P]
  rw [← Category.assoc, ← SD.tensor.map_comp]
  congr 2
  ext <;> simp

private theorem scalarBaseChangeHom_identity
    {A : Type*} [Category.{c} A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (F : A ⥤ A)
    (μ : S.tensor ⋙ F ≅ F.prod F ⋙ S.tensor) (u : F ≅ 𝟭 A)
    (hid : ∀ X Y : A,
      S.tensor.map (Prod.mkHom (u.inv.app X) (u.inv.app Y)) =
        u.inv.app (S.tensor.obj (X, Y)) ≫ μ.hom.app (X, Y)) (P Q : A) :
    coefficientBaseChangeHom S S F μ P Q ≫
        H.map (Prod.mkHom (u.inv.app P).op (u.hom.app Q)) =
      u.hom.app (H.obj (op P, Q)) := by
  have hi (X Y : A) : μ.inv.app (X, Y) ≫ u.hom.app (S.tensor.obj (X, Y)) =
      S.tensor.map (Prod.mkHom (u.hom.app X) (u.hom.app Y)) := by
    have : IsIso (S.tensor.map (Prod.mkHom (u.inv.app X) (u.inv.app Y))) := by
      change IsIso ((S.tensor.mapIso (Iso.prod (u.app X).symm (u.app Y).symm)).hom)
      infer_instance
    apply (cancel_epi (S.tensor.map (Prod.mkHom (u.inv.app X) (u.inv.app Y)))).1
    conv_lhs => rw [← Category.assoc, hid]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
    rw [← S.tensor.map_comp]
    simp
  apply (S.transpose _ P Q).symm.injective
  rw [scalarUncurry_post, scalarBaseChangeHom_beta, scalarUncurry]
  have hn := u.hom.naturality (S.evaluation P Q)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Category.assoc]
  rw [hn, reassoc_of% hi, ← Category.assoc, ← S.tensor.map_comp]
  congr 2
  ext <;> simp


/-- Evaluation and uniqueness follow directly from the closed adjunction. -/
private theorem finiteHomEvaluation_of_transpose
    {A B : Type a} [Category.{c} A] [Category.{c} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) :
    FiniteHomEvaluation SA SB F μ := by
  intro K M
  have hu (v : F.obj (HA.obj (op K, M)) ⟶ HB.obj (op (F.obj K), F.obj M)) :
      (SB.transpose _ (F.obj K) (F.obj M)).symm v =
        SB.tensor.map (Prod.mkHom v (𝟙 (F.obj K))) ≫
          SB.evaluation (F.obj K) (F.obj M) := by
    simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
      CoefficientClosedStructure.evaluation] using!
      (SB.adjunction (F.obj K)).homEquiv_counit _ (F.obj M) v
  constructor
  · rw [← hu, coefficientBaseChangeHom, Equiv.symm_apply_apply]
  · intro v hv
    apply (SB.transpose _ (F.obj K) (F.obj M)).symm.injective
    rw [hu, hv, coefficientBaseChangeHom, Equiv.symm_apply_apply]

end GeneralHomComparison

/-- The general internal-Hom comparisons have the identity, cocycle, elementary
agreement and evaluation/transpose coherence of the source, including transport
through raw rationalization and every common finite coefficient stage.
Source: current blueprint sec-six-functors/sk-thm-sf-compatibility,
fix-prop-coherence.proof.md, general Hom and field-transport sentences
(blueprint: lem-sf-general-hom-comparison-cocycles).

Proof:
1. Prove identity and composition of coefficientBaseChangeHom by uncurrying.
Evaluation naturality, functoriality and the tensorator equations suffice, without
any invertibility hypothesis on the Hom comparisons. Apply the tensor normalization
lemma to the prescribed identity and composite restriction-adjoint mates. The
remaining finite cocycle is finiteCoefficient_derivedHom_change.
2. The finite elementary overlap is definitional equality. Choose the integral
presentations from integralHom_presentation_evaluation. Its uncurried equation and
the closed bijection identify integralMap with comparison on every ambient input.
The existing comparison_isIso supplies invertibility.
3. Choose the scalar presentations and ordinary functor isomorphism e from
scalarHom_presentation_evaluation. Its completion equation identifies each
presentation completion with e followed by scalarCompletionIso. Expanding both
completed Hom maps factors their map on the two arguments; the ordinary Hom square
and cancellation of e inverse with e prove agreement. The canonical completed Hom
isomorphism supplies invertibility on the constructible domain.
4. Quotient evaluation laws come from finiteCoefficient_derivedHom_change; integral
compatibility is a field of the fixed evaluation calculus. The evaluation transpose
and its uniqueness follow directly from the closed adjunction. Ordinary scalar
evaluation laws come from basicOperationsCoefficientReduction. The tensor lemma
supplies each of the three associator squares.
5. Apply basicOperationsCoefficientReduction to the identity of X, using the
characteristic hypothesis to supply residue-field invertibility. Its raw rational
Hom and common-stage Hom clauses give fieldTransport's first two assertions. Each
remaining equation-transport clause is congruence under the stated functor map. -/
theorem generalHomComparisonCocycles
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))] :
    GeneralHomComparison.finiteLaws C.l E X ∧
    GeneralHomComparison.integralLaws C.l E X D C.different ∧
    GeneralHomComparison.elementaryAgreement C.l E X D C.different ∧
    GeneralHomComparison.scalarAgreement C.l E X ∧
    GeneralHomComparison.evaluationCoherence C.l E X ∧
    GeneralHomComparison.fieldTransport C.l E X C.Qbar := by
  classical
  let : ∀ x : X, Invertible (C.l : X.residueField x) := fun x ↦ (by
    simpa using (finiteFieldDatumPrimeUnit D C.l C.different).map
      ((X ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
        IsUnit (C.l : X.residueField x)).invertible
  have hb := basicOperationsCoefficientReduction.{u, u, u, u, u, u, u, u, u}
    C.l E C.Qbar X X (𝟙 X)
  have hs := hb.2.2.2.2.2.2.2.2.2.2.2.1
  have hr := hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc := hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hb
  obtain ⟨hi, ht, hfassoc, hrassoc, hsassoc⟩ :=
    coefficientTensor_normalization C.l E X D C.different
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro n K M _ _
      exact GeneralHomComparison.scalarBaseChangeHom_identity
        (finiteIntrinsicClosed C.l E X n) _ _ (GeneralHomComparison.finiteUnit C.l E X n)
        (hi n) K M
    · intro n m h
      exact (finiteCoefficient_derivedHom_change D C.l C.different E X n m h).2.2.2.2.2.2.2.1
  · intro n m h K M _ _
    exact (GeneralHomComparison.scalarBaseChangeHom_tower
      (scalarIntegralClosed C.l E X) (finiteIntrinsicClosed C.l E X n)
      (finiteIntrinsicClosed C.l E X m) _ _ _ _ _ _
      (GeneralHomComparison.integralAssoc C.l E X D C.different h) (ht n m h) K M).symm
  · refine ⟨?_, ?_⟩
    · intro n m h K M _ _ _
      rfl
    · obtain ⟨a, ha⟩ := integralHom_presentation_evaluation C.l E X D C.different
      refine ⟨a, ?_⟩
      intro n
      obtain ⟨m, hm⟩ := ha n
      refine ⟨m, ?_⟩
      intro K M
      refine ⟨IntegralHom.comparison_isIso C.l E X D C.different a n m K M, ?_⟩
      apply ((finiteIntrinsicClosed C.l E X n).transpose _
        ((coefficientFiniteDerivedExtension C.l E X n).obj K)
        ((coefficientFiniteDerivedExtension C.l E X n).obj M)).symm.injective
      exact (Equiv.symm_apply_apply _ _).trans (hm K M).symm
  · intro L _ _ _ ι
    obtain ⟨a, b, e, he, hc⟩ := scalarHom_presentation_evaluation C.l E X L ι
    have hv (K M : DerivedCategory (scalarReductionSource C.l E X))
        (hK : sfIntegralConstructible C.l E X K) (hM : sfIntegralConstructible C.l E X M) :
        IntegralFiniteExtension.v C.l E L ι X a b K M hK.1 hM.1 =
          (scalarHomCompleteInputs C.l E L ι X K M hK.1 hM.1).hom := by
      have ec (N : DerivedCategory (scalarReductionSource C.l E X))
          (hN : IsSfDerivedComplete C.l E X N) :
          IntegralFiniteExtension.completion C.l E L ι X N hN =
            e.app N ≪≫ scalarCompletionIso C.l E L ι X N hN := by
        apply Iso.ext
        exact hc N
      unfold IntegralFiniteExtension.v scalarHomCompleteInputs scalarHomCompleted
      rw [ec, ec, ec]
      simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        Iso.prod_hom, Iso.op_hom, Category.assoc]
      have hprod : Prod.mkHom
          (((scalarCompletionIso C.l E L ι X K hK.1).inv ≫ e.inv.app K).op)
          (e.hom.app M ≫ (scalarCompletionIso C.l E L ι X M hM.1).hom) =
          Prod.mkHom (e.inv.app K).op (e.hom.app M) ≫
            Prod.mkHom ((scalarCompletionIso C.l E L ι X K hK.1).inv.op)
              (scalarCompletionIso C.l E L ι X M hM.1).hom := by
        ext <;> simp
      erw [hprod, Functor.map_comp]
      erw [reassoc_of% he K M]
      simp only [Iso.app_inv, asIso_hom]
      erw [Iso.inv_hom_id_app_assoc]
      rfl
    refine ⟨a, b, ?_⟩
    intro K M hK hM
    refine ⟨?_, hv K M hK hM⟩
    rw [hv K M hK hM]
    infer_instance
  · refine ⟨?_, ?_, ?_⟩
    · intro n m h
      have hf := finiteCoefficient_derivedHom_change D C.l C.different E X n m h
      exact ⟨hf.2.2.2.1, hf.2.2.2.2.1, hfassoc n m h⟩
    · intro n
      exact ⟨(coefficientDerivedSystemEvaluationCalculus C.l E X).choose.finite_compatible n,
        GeneralHomComparison.finiteHomEvaluation_of_transpose _ _ _ _, hrassoc n⟩
    · intro L _ _ _ ι
      exact ⟨(hs L ι X).1, (hs L ι X).2, hsassoc L ι⟩
  · refine ⟨?_, hc X, ?_, ?_, ?_⟩
    · intro L _ _ _ ι P
      exact hr L ι X P
    · intro K M f g h
      exact congrArg (sfRationalConstructibleLocalization C.l E X).map h
    · intro L F h K M f g e
      exact congrArg (GeneralAlgebraicallyClosedCoefficients.transition C.l C.Qbar X L F h).map e
    · intro L K M f g e
      exact congrArg (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := X) L).map e

end WeilConjectures
