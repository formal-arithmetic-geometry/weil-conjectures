/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.ScalarCompletionAssociator
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.CompletedLineTensorCoherence
public import Sheaf.Paper.FdCoefficientComparison
import all Sheaf.Paper.PbcScalarExtension

/-! # Integral inverse scalar cocycle and normalized units

Source: trace-function coefficient-category comparison, extracted steps 4--6
(blueprint: lem-fd-integral-inverse-scalar-cocycle).

The fields are embedded in the fixed algebraic closure by the final embedding and
its composites with the two inclusions. All equations use the published completion
map and the specified normalized associator, in the common integral presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem inverseScalarNaturality {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (χ : F ⟶ G) {X Y : C} (f : X ⟶ Y)
    (b : F.obj X ≅ G.obj X) (hb : b.hom = χ.app X)
    (c : F.obj Y ≅ G.obj Y) (hc : c.hom = χ.app Y) :
    b.inv ≫ F.map f = G.map f ≫ c.inv := by
  apply b.inv_comp_eq.mpr
  rw [← Category.assoc]
  apply c.eq_comp_inv.mpr
  simpa only [Category.assoc, hb, hc] using χ.naturality f

private theorem inverseScalarSquare {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (χ : F ⟶ G) {X Y : C} (b : X ≅ Y)
    (c : F.obj Y ≅ G.obj Y) (hc : c.hom = χ.app Y)
    {Z W : D} (a : F.obj X ⟶ Z) (d : G.obj Y ⟶ W) (e : Z ≅ W)
    (h : χ.app X ≫ G.map b.hom ≫ d = a ≫ e.hom) :
    c.inv ≫ F.map b.inv ≫ a = d ≫ e.inv := by
  apply e.eq_comp_inv.mpr
  simp only [Category.assoc]
  rw [← h]
  rw [← Category.assoc (F.map b.inv), χ.naturality b.inv]
  simp only [Category.assoc, ← hc, c.inv_hom_id_assoc]
  rw [← G.map_comp_assoc, b.inv_hom_id, G.map_id, Category.id_comp]

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (ι : E →ₐ[ℚ_[l]] L) (κ : L →ₐ[ℚ_[l]] M) (T : Scheme.{u})

/-- Forward and inverse equations for the actual quotient-cocone completion maps.
The supplied associator package is the specified framework associator normalized by
ordinary balancing; its representative and uniqueness fields retain the actual cocones
and independence from K-flat and cofinal-exponent choices.
Source: trace-function final coefficient-category sentence, extracted steps 4--6
(blueprint: lem-fd-integral-inverse-scalar-cocycle).

Proof:
1. Integral stratified-perfect characterization identifies the integral full categories
through integralDetailedTransport. Their objects are derived complete. Apply the
normalization field of lem-fix-scalar-completion-associator to the actual chi maps.
Its ordinary_model and independent clauses fix balancing on representatives and remove
all representative and cofinal-exponent choices. This gives the forward equation.
2. Ordinary presentation transport fixes tensor generators and multiplication. Thus
ordinary balancing is the integral comparison underlying prop-weil-pbc-scalar-extension;
the companion transport statement below records this identification and rationalization.
3. Put D = chi_2 at C_1 K followed by U_2(chi_1). Naturality of chi_2 at chi_1 inverse
identifies D inverse with chi_2 inverse at U_1 K followed by C_2(chi_1 inverse).
Cancel D and chi_3 from the forward equation. The result is the inverse equation.
4. No inclusion was required to be strict, so this calculation includes every repeated
field case. The companion unit statement records the two resulting comparison squares.
-/
theorem fdIntegralInverseScalarCocycle
    (_D : FiniteFieldDatum.{d}) (_hl : l ≠ _D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_e : M →ₐ[ℚ_[l]] Ω) [IsNoetherian T]
    [_hdim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [_hinv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (A : ScalarCompletionAssociatorData.{u, u} l T)
    (K : sfIntegralConstructibleCategory l E T) :
    ((completedScalarComparison l L M κ T).app
        ((completedDerivedScalarExtension l E L ι T).obj K.obj) ≫
      (integralScalarExtensionOfUniverses l L M κ T).map
        ((completedScalarComparison l E L ι T).app K.obj) ≫
      (A.associator E L M ι κ).hom.app
        ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩ =
      (A.ordinary E L M ι κ).hom.app K.obj ≫
        (completedScalarComparison l E M (κ.comp ι) T).app K.obj) ∧
    ((CompletedLineTensor.chi l L T M κ _
        (A.preserves E L ι K.obj (CompletedLineTensor.intrinsic_complete l E T K))).inv ≫
      (completedDerivedScalarExtension l L M κ T).map
        (CompletedLineTensor.chi l E T L ι K.obj
          (CompletedLineTensor.intrinsic_complete l E T K)).inv ≫
      (A.ordinary E L M ι κ).hom.app K.obj =
      (A.associator E L M ι κ).hom.app
          ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩ ≫
        (CompletedLineTensor.chi l E T M (κ.comp ι) K.obj
          (CompletedLineTensor.intrinsic_complete l E T K)).inv) := by
  let hK := CompletedLineTensor.intrinsic_complete l E T K
  have h := A.normalization E L M ι κ ⟨K.obj, hK⟩
  refine ⟨h, ?_⟩
  exact inverseScalarSquare
    (completedDerivedScalarExtension l L M κ T)
    (integralScalarExtensionOfUniverses l L M κ T)
    (completedScalarComparison l L M κ T)
    (CompletedLineTensor.chi l E T L ι K.obj hK)
    (CompletedLineTensor.chi l L T M κ _ (A.preserves E L ι K.obj hK)) rfl
    ((A.ordinary E L M ι κ).hom.app K.obj)
    ((A.associator E L M ι κ).hom.app ⟨K.obj, hK⟩)
    (CompletedLineTensor.chi l E T M (κ.comp ι) K.obj hK) h

/-- The actual identity completion map, its normalized inverse, and both unit squares.
Here A.unit is eta inverse, and A.ordinaryUnit is tensor multiplication mu.
The last equation is the all-equal-fields square after these identifications.
Source: trace-function coefficient comparison, extracted steps 4--6
(blueprint: lem-fd-integral-inverse-scalar-cocycle).

Proof:
1. The identity-extension clause of lem-weil-finite-free-completed-scalar-comparison
identifies chi, on every K-flat representative, with multiplication followed by the
actual quotient completeness unit. Descent gives b = mu followed by eta. Invert this
equality to obtain b inverse followed by mu = eta inverse.
2. Substitute L = E in the inverse cocycle. The left ordinary associator is C(mu_E)
and the left completed associator is U(eta_E inverse). Replace b_EE inverse followed
by mu_E by eta_E inverse. Naturality of b inverse gives the first displayed square.
3. Substitute M = L. The right ordinary associator is mu_L and the right completed
associator is eta_L inverse. Naturality of mu_L at b inverse reduces the second
square to b inverse followed by eta_L inverse.
4. With all fields equal substitute the identity normalization. Both routes reduce
to eta inverse followed by itself. Conjugating by eta identifies every edge with
identity. Repetitions adjacent to a strict extension are included in steps 2 and 3.
-/
theorem fdIntegralInverseScalarUnits
    (_D : FiniteFieldDatum.{d}) (_hl : l ≠ _D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_e : L →ₐ[ℚ_[l]] Ω) [IsNoetherian T]
    [_hdim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [_hinv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (A : ScalarCompletionAssociatorData.{u, u} l T)
    (K : sfIntegralConstructibleCategory l E T) :
    ((completedScalarComparison l E E (AlgHom.id ℚ_[l] E) T).app K.obj =
      (A.ordinaryUnit E).hom.app K.obj ≫
        (A.unit E).inv.app ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩) ∧
    ((CompletedLineTensor.chi l E T E (AlgHom.id ℚ_[l] E) K.obj
        (CompletedLineTensor.intrinsic_complete l E T K)).inv ≫
      (A.ordinaryUnit E).hom.app K.obj =
      (A.unit E).hom.app ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩) ∧
    ((CompletedLineTensor.chi l E T L ι _
        (A.preserves E E (AlgHom.id ℚ_[l] E) K.obj
          (CompletedLineTensor.intrinsic_complete l E T K))).inv ≫
      (completedDerivedScalarExtension l E L ι T).map
        ((A.unit E).hom.app ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩) =
      (integralScalarExtensionOfUniverses l E L ι T).map
        ((A.unit E).hom.app ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩) ≫
        (CompletedLineTensor.chi l E T L ι K.obj
          (CompletedLineTensor.intrinsic_complete l E T K)).inv) ∧
    ((CompletedLineTensor.chi l L T L (AlgHom.id ℚ_[l] L) _
        (A.preserves E L ι K.obj (CompletedLineTensor.intrinsic_complete l E T K))).inv ≫
      (completedDerivedScalarExtension l L L (AlgHom.id ℚ_[l] L) T).map
        (CompletedLineTensor.chi l E T L ι K.obj
          (CompletedLineTensor.intrinsic_complete l E T K)).inv ≫
      (A.ordinaryUnit L).hom.app
        ((completedDerivedScalarExtension l E L ι T).obj K.obj) =
      (A.unit L).hom.app
          ⟨(integralScalarExtensionOfUniverses l E L ι T).obj K.obj,
            A.preserves E L ι K.obj (CompletedLineTensor.intrinsic_complete l E T K)⟩ ≫
        (CompletedLineTensor.chi l E T L ι K.obj
          (CompletedLineTensor.intrinsic_complete l E T K)).inv) ∧
    (HEq ((A.ordinary E E L (AlgHom.id ℚ_[l] E) ι).hom.app K.obj)
      ((completedDerivedScalarExtension l E L ι T).map
        ((A.ordinaryUnit E).hom.app K.obj))) ∧
    (HEq ((A.ordinary E L L ι (AlgHom.id ℚ_[l] L)).hom.app K.obj)
      ((A.ordinaryUnit L).hom.app ((completedDerivedScalarExtension l E L ι T).obj K.obj))) ∧
    ((A.associator E E L (AlgHom.id ℚ_[l] E) ι).hom.app
        ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩ =
      (integralScalarExtensionOfUniverses l E L ι T).map
        ((A.unit E).hom.app ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩)) ∧
    ((A.associator E L L ι (AlgHom.id ℚ_[l] L)).hom.app
        ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩ =
      (A.unit L).hom.app
        ⟨(integralScalarExtensionOfUniverses l E L ι T).obj K.obj,
          A.preserves E L ι K.obj (CompletedLineTensor.intrinsic_complete l E T K)⟩) ∧
    ((A.unit E).inv.app ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩ ≫
      (CompletedLineTensor.chi l E T E (AlgHom.id ℚ_[l] E) K.obj
        (CompletedLineTensor.intrinsic_complete l E T K)).inv ≫
      (A.ordinaryUnit E).hom.app K.obj = 𝟙 K.obj) := by
  let hK := CompletedLineTensor.intrinsic_complete l E T K
  let X : ObjectProperty.FullSubcategory (IsDerivedCompleteUnrestricted l E T) :=
    ⟨K.obj, hK⟩
  let b := CompletedLineTensor.chi l E T E (AlgHom.id ℚ_[l] E) K.obj hK
  have hu := A.unit_normalization E X
  have hi : b.inv ≫ (A.ordinaryUnit E).hom.app K.obj = (A.unit E).hom.app X :=
    b.inv_comp_eq.mpr hu.symm
  refine ⟨?_, hi, ?_, ?_, ?_, ?_, A.left_unit E L ι X, A.right_unit E L ι X, ?_⟩
  · exact ((A.unit E).app X).eq_comp_inv.mpr hu
  · exact inverseScalarNaturality
      (completedDerivedScalarExtension l E L ι T)
      (integralScalarExtensionOfUniverses l E L ι T)
      (completedScalarComparison l E L ι T) ((A.unit E).hom.app X)
      (CompletedLineTensor.chi l E T L ι _
        (A.preserves E E (AlgHom.id ℚ_[l] E) K.obj hK)) rfl
      (CompletedLineTensor.chi l E T L ι K.obj hK) rfl
  · let Y : ObjectProperty.FullSubcategory (IsDerivedCompleteUnrestricted l L T) :=
      ⟨_, A.preserves E L ι K.obj hK⟩
    let c := CompletedLineTensor.chi l L T L (AlgHom.id ℚ_[l] L) Y.obj Y.property
    have hc : c.inv ≫ (A.ordinaryUnit L).hom.app Y.obj = (A.unit L).hom.app Y :=
      c.inv_comp_eq.mpr (A.unit_normalization L Y).symm
    rw [(A.ordinaryUnit L).hom.naturality]
    simpa only [Category.assoc, Functor.id_map] using congrArg
      (fun f ↦ f ≫ (CompletedLineTensor.chi l E T L ι K.obj hK).inv) hc
  · have hn := A.normalization E E L (AlgHom.id ℚ_[l] E) ι X
    simp only [AlgHom.comp_id] at hn
    rw [A.left_unit] at hn
    change (completedScalarComparison l E L ι T).app _ ≫
      (integralScalarExtensionOfUniverses l E L ι T).map
        ((completedScalarComparison l E E (AlgHom.id ℚ_[l] E) T).app K.obj) ≫
      (integralScalarExtensionOfUniverses l E L ι T).map ((A.unit E).hom.app X) =
      (A.ordinary E E L (AlgHom.id ℚ_[l] E) ι).hom.app K.obj ≫
        (completedScalarComparison l E L ι T).app K.obj at hn
    rw [← Functor.map_comp, hu,
      ← (completedScalarComparison l E L ι T).naturality] at hn
    have he := (cancel_mono (CompletedLineTensor.chi l E T L ι K.obj hK).hom).mp hn
    exact heq_of_eq he.symm
  · have hn := A.normalization E L L ι (AlgHom.id ℚ_[l] L) X
    simp only [AlgHom.id_comp] at hn
    rw [A.right_unit] at hn
    rw [← (completedScalarComparison l L L (AlgHom.id ℚ_[l] L) T).naturality_assoc] at hn
    rw [A.unit_normalization L
      ⟨(integralScalarExtensionOfUniverses l E L ι T).obj X.obj,
        A.preserves E L ι X.obj X.property⟩] at hn
    rw [(A.ordinaryUnit L).hom.naturality] at hn
    simp only [Functor.id_map] at hn
    have he := (cancel_mono (CompletedLineTensor.chi l E T L ι K.obj hK).hom).mp hn
    exact heq_of_eq he.symm
  · rw [hi]
    exact (A.unit E).inv_hom_id_app X


section Presentation
variable (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {F G H : Padic.FiniteCoefficientFields l Ω}

/-- The finite-stage and ordinary coefficient maps are the same normalized map.
Source: trace-function coefficient comparison, ordinary presentation clause
(blueprint: lem-fd-integral-inverse-scalar-cocycle).

Proof: the finite-stage coefficient map is uniquely determined by its quotient
projections. The constant-presentation comparisons are their normalized sheafification
comparisons. On quotient representatives both maps are the same integer inclusion.
Thus their finite projections agree, and uniqueness of the completed limit map gives
the equality. This is an identification of existing maps, not a new construction.
-/
theorem fdIntegralCoefficientMap_eq (h : F ≤ G) :
    pbcCompletedScalarMap l Ω T h =
      pbcScalarCoefficientMap l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G)
        (pbcFiniteFieldInclusion l Ω h) T := by
  apply (pbcCompletedScalarMap_exists l Ω T h).unique
  · exact (pbcCompletedScalarMap_exists l Ω T h).exists.choose_spec
  · intro n
    have hc := (pbcScalarCoefficientMap_exists l (pbcFiniteField.{u} l Ω F)
      (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T).exists.choose_spec n
    change pbcScalarCoefficientMap l (pbcFiniteField.{u} l Ω F)
      (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T ≫ _ = _ at hc
    rw [hc]
    congr 1
    unfold pbcFiniteScalarMap
    rw [scalarLevelConstantComparison_naturality]
    change AdicCoefficients.coefficientMap T
      (pbcScalarQuotientMap l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G)
        (pbcFiniteFieldInclusion l Ω h) n) =
      (pbcLevelConstantComparison T (pbcStageDatum.{u} l Ω F) n).inv ≫
        (pbcLevelConstantComparison T (pbcStageDatum.{u} l Ω F) n).hom ≫
          AdicCoefficients.coefficientMap T (pbcQuotientInclusion l Ω h n)
    erw [Iso.inv_hom_id_assoc]
    rfl

/-- The derived ordinary presentation transport, uniquely fixed by its generator-normalized
cochain comparison and the two universal tensor counits. Only the proof is postponed.
Source: trace-function coefficient comparison, ordinary balancing clause, step 2
(blueprint: lem-fd-integral-inverse-scalar-cocycle).

Proof: apply the existing ordinary transport to every term of a flat-term K-flat complex.
The two derived tensor counits and coefficient-restriction localization isomorphisms
are invertible on these representatives. Conjugate the cochain comparison by them.
Naturality on chain maps descends through the good-complex localization. The same
counits show that every normalized candidate has these components; essential
surjectivity and fullness of localization give uniqueness. No new scalar functor is chosen.
-/
theorem fdIntegralOrdinaryPresentation_existsUnique (h : F ≤ G)
    (o : FdOrdinaryScalarTransport l Ω T h) :
    ∃! τ :
      completedDerivedScalarExtension l (pbcFiniteField.{u} l Ω F)
          (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T ⋙
        integralDetailedTransport T l (pbcFiniteField.{u} l Ω G) ≅
      integralDetailedTransport T l (pbcFiniteField.{u} l Ω F) ⋙
        pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω F)
          (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T,
      ∀ P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω F) T).FullSubcategory,
        (integralDetailedTransport T l (pbcFiniteField.{u} l Ω G)).map
            (completedScalarCounit l (pbcFiniteField.{u} l Ω F)
              (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T P.obj) ≫
          (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω G) T).hom.app
            ((completedOrdinaryScalarComplex l (pbcFiniteField.{u} l Ω F)
              (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T).obj P.obj) ≫
          DerivedCategory.Q.map ((o.complex l Ω).hom.app P.obj) ≫
          eqToHom (congrArg
            (fun φ : pbcAdicCompletion T (pbcIntegralDatum l (pbcFiniteField.{u} l Ω F)) ⟶
                pbcAdicCompletion T (pbcIntegralDatum l (pbcFiniteField.{u} l Ω G)) ↦
              DerivedCategory.Q.obj (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj
                (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω F) T).mapHomologicalComplex
                  (.up ℤ)).obj P.obj)))
            (fdIntegralCoefficientMap_eq l T Ω h)) =
        τ.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω F)
            (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T).map
              ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω F) T).hom.app P.obj) ≫
          pbcComplexCounit (pbcScalarCoefficientMap l (pbcFiniteField.{u} l Ω F)
            (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T)
              (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω F) T).mapHomologicalComplex
                (.up ℤ)).obj P.obj) := by
  sorry

/-- Ordinary presentation transport chosen from its unique generator/counit normalization.
Source: trace-function coefficient comparison, step 2
(blueprint: lem-fd-integral-inverse-scalar-cocycle). -/
def fdIntegralOrdinaryPresentation (h : F ≤ G)
    (o : FdOrdinaryScalarTransport l Ω T h) :=
  (fdIntegralOrdinaryPresentation_existsUnique l T Ω h o).exists.choose

set_option linter.unusedSectionVars false in
/-- The small finite-field models retain composition of their actual inclusions.
Source: trace-function coefficient comparison, ordinary presentation identification
(blueprint: lem-fd-integral-inverse-scalar-cocycle).

Proof: expand pbcFiniteFieldInclusion. The middle Shrink equivalence and its inverse
cancel. The two intermediate-field inclusions compose to the direct inclusion on
every element. Algebra-hom extensionality gives the equality. This is solely a
presentation equality, including identity inclusions.
-/
theorem fdIntegralCoefficientInclusion_comp (h : F ≤ G) (k : G ≤ H) :
    pbcFiniteFieldInclusion.{u} l Ω (h.trans k) =
      (pbcFiniteFieldInclusion.{u} l Ω k).comp (pbcFiniteFieldInclusion.{u} l Ω h) := by
  change (Shrink.algEquiv ℚ_[l] H.val).symm.toAlgHom.comp
      ((IntermediateField.inclusion (h.trans k)).comp
        (Shrink.algEquiv ℚ_[l] F.val).toAlgHom) =
    ((Shrink.algEquiv ℚ_[l] H.val).symm.toAlgHom.comp
      ((IntermediateField.inclusion k).comp (Shrink.algEquiv ℚ_[l] G.val).toAlgHom)).comp
        ((Shrink.algEquiv ℚ_[l] G.val).symm.toAlgHom.comp
          ((IntermediateField.inclusion h).comp (Shrink.algEquiv ℚ_[l] F.val).toAlgHom))
  ext x
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.apply_symm_apply]
  rfl

/-- Ordinary balancing expressed in the PBC presentation by the fixed tensor-generator
transport. The equality casts only identify composite and direct field inclusions.
Source: trace-function coefficient comparison, ordinary balancing clause
(blueprint: lem-fd-integral-inverse-scalar-cocycle). -/
def fdIntegralOrdinaryBalancingMap (A : ScalarCompletionAssociatorData.{u, u} l T)
    (h : F ≤ G) (k : G ≤ H)
    (o₁ : FdOrdinaryScalarTransport l Ω T h)
    (o₂ : FdOrdinaryScalarTransport l Ω T k)
    (o₃ : FdOrdinaryScalarTransport l Ω T (h.trans k))
    (K : DerivedCategory (integralTowerModules l (pbcFiniteField.{u} l Ω F) T)) :
    (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω G) (pbcFiniteField.{u} l Ω H)
      (pbcFiniteFieldInclusion l Ω k) T).obj ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω
      F) (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T).obj
      ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω F)).obj K)) ⟶
      (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω H)
        ((pbcFiniteFieldInclusion l Ω k).comp (pbcFiniteFieldInclusion l Ω h)) T).obj
        ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω F)).obj K) :=
  (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω G) (pbcFiniteField.{u} l Ω H)
    (pbcFiniteFieldInclusion l Ω k) T).map ((fdIntegralOrdinaryPresentation l T Ω h o₁).inv.app K) ≫
    (fdIntegralOrdinaryPresentation l T Ω k o₂).inv.app ((completedDerivedScalarExtension l
      (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T).obj
      K) ≫
    (integralDetailedTransport T l (pbcFiniteField.{u} l Ω H)).map ((A.ordinary
      (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G) (pbcFiniteField.{u} l Ω H)
      (pbcFiniteFieldInclusion l Ω h) (pbcFiniteFieldInclusion l Ω k)).hom.app K) ≫
    (integralDetailedTransport T l (pbcFiniteField.{u} l Ω H)).map (eqToHom (congrArg
    (fun a : (pbcFiniteField.{u} l Ω F) →ₐ[ℚ_[l]] (pbcFiniteField.{u} l Ω H) ↦
      (completedDerivedScalarExtension l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω H) a
      T).obj K)
    (fdIntegralCoefficientInclusion_comp l Ω h k)).symm) ≫
    (fdIntegralOrdinaryPresentation l T Ω (h.trans k) o₃).hom.app K ≫
    eqToHom (congrArg
    (fun a : (pbcFiniteField.{u} l Ω F) →ₐ[ℚ_[l]] (pbcFiniteField.{u} l Ω H) ↦
      (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω H) a T).obj
      ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω F)).obj K))
    (fdIntegralCoefficientInclusion_comp l Ω h k))

/-- The normalized integral balancing becomes precisely the PBC balancing and its
specified raw rational associator. J is the same integral object in the PBC presentation;
hJ identifies its underlying object with the canonical integral identity image.
Source: trace-function coefficient comparison, ordinary balancing clause, step 2
(blueprint: lem-fd-integral-inverse-scalar-cocycle).

Proof: both normalized ordinary presentation transports fix sheafified tensor generators.
On a flat-term K-flat representative both routes send (x tensor b) tensor c to x tensor bc,
with the same quotient coefficient projections. The cochain maps are therefore equal.
Conjugating by the universal tensor counits gives the first derived equation and removes
representative choices. IntegralStratifiedPerfectDetailed supplies precisely the common
integral full categories. Their full inclusions retain these same arrows. Apply raw
scalar localization to the equation. The target component is, by its construction,
pbcRationalScalarCompComponent, the specified rationalized PBC balancing. Direct versus
composite inclusion casts are the canonical coefficient presentation equality only.
-/
theorem fdIntegralOrdinaryBalancing
    (_D : FiniteFieldDatum.{d}) (_hl : l ≠ _D.p) [IsNoetherian T]
    [hdim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [hinv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (A : ScalarCompletionAssociatorData.{u, u} l T)
    (h : F ≤ G) (k : G ≤ H)
    (o₁ : FdOrdinaryScalarTransport l Ω T h)
    (o₂ : FdOrdinaryScalarTransport l Ω T k)
    (o₃ : FdOrdinaryScalarTransport l Ω T (h.trans k))
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω F) T) :
    (fdIntegralOrdinaryBalancingMap l T Ω A h k o₁ o₂ o₃ K.obj =
      (pbcAmbientScalarComp l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G)
        (pbcFiniteField.{u} l Ω H) (pbcFiniteFieldInclusion l Ω h) (pbcFiniteFieldInclusion l Ω k)
        T).hom.app
        ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω F)).obj K.obj)) ∧
    ∀ (J : PbcBoundedConstructibleComplete T (pbcIntegralDatum l (pbcFiniteField.{u} l Ω F)))
      (hJ : J.obj = (integralDetailedTransport T l (pbcFiniteField.{u} l Ω F)).obj K.obj),
      (pbcRationalization T (pbcIntegralDatum l (pbcFiniteField.{u} l Ω H)) (pbcUniformizer l
        (pbcFiniteField.{u} l Ω H))).map
        (ObjectProperty.homMk
          ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω G) (pbcFiniteField.{u} l Ω H)
            (pbcFiniteFieldInclusion l Ω k) T).map ((pbcEmbeddingAmbientTensor l
            (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h)
            T).map (eqToHom hJ)) ≫
            fdIntegralOrdinaryBalancingMap l T Ω A h k o₁ o₂ o₃ K.obj ≫
            (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω H)
              ((pbcFiniteFieldInclusion l Ω k).comp (pbcFiniteFieldInclusion l Ω h)) T).map
              (eqToHom hJ.symm)) :
          (pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω G) (pbcFiniteField.{u} l Ω H)
            (pbcFiniteFieldInclusion l Ω k) T hdim.out hinv.out).obj
              ((pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G)
                (pbcFiniteFieldInclusion l Ω h) T hdim.out hinv.out).obj J) ⟶
            (pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω H)
              ((pbcFiniteFieldInclusion l Ω k).comp (pbcFiniteFieldInclusion l Ω h)) T hdim.out
              hinv.out).obj J) =
      (pbcRationalScalarCompComponent l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G)
        (pbcFiniteField.{u} l Ω H) (pbcFiniteFieldInclusion l Ω h) (pbcFiniteFieldInclusion l Ω k)
        T hdim.out hinv.out ⟨J⟩).hom := by
  sorry

end Presentation
end WeilConjectures
