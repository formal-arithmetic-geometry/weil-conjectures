/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.Paper.FdRawLocalizationScalarData
import Sheaf.CategoryTheory.SemilinearScalarLocalization

/-! # Descent of the fixed integral scalar comparison

Source: trace-definition coefficient-category sentence, raw localization steps 1--3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FdRawLocalization

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)

/-- Localization of the fixed inverse integral comparison, before four-field contraction.
Source: trace-definition final coefficient-category sentence, raw localization argument,
steps 1--3 of lem-fd-raw-localization-scalar-coherence
(blueprint: lem-fd-raw-localization-scalar-descent).

Proof: Ordinary tensor extension and strict-tower extension are semilinear for the
coefficient inclusion. The source uniformizer is nonzero in the final field, hence
invertible there. Apply semilinear scalar localization to the hom and inverse of b.
The tensor formula and the supplied stage comparison identify the localized functors
with S followed by J, and J followed by P. On integral objects the component is
Q(b inverse) followed by the inverse of pbcScalarIntegralComparison, exactly as
stated. Integral naturality on pure tensors and additivity give naturality on every
rational arrow. The localized inverse equations give an isomorphism; the specified
shift squares and integral exactness give its shift compatibility and exactness.
Localize hcocycle over its final field. Preservation of composition and whiskering,
and the tensor-normalized integral-to-rational associator comparisons, give the
three-field equation. Localizing hunit gives the displayed identity value. Substitute
an identity extension in hcocycle in each position and use the two specified scalar
unit laws to obtain the two unit equations. Completeness is retained through its
actual unit, never replaced by an identity. All arguments allow repeated fields,
the zero object and the empty scheme; no strict inclusion or faithful localization
is required. This statement contains no four-field compatibility assertion. -/
theorem rawLocalizationScalarDescent
    (_D : FiniteFieldDatum.{d}) (_hl : l ≠ _D.p)
    (hI : ∀ E : Padic.FiniteCoefficientFields l Ω, (I l Ω T stage E).IsTriangulated)
    (ordinary : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      FdOrdinaryScalarTransport l Ω T h)
    (b : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L)
    (hshift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      NatTrans.CommShift (b h).hom ℤ ∧ NatTrans.CommShift (b h).inv ℤ)
    (hexact : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      (I l Ω T stage E ⋙ C l Ω T h).IsTriangulated ∧
        (U l Ω T h ⋙ I l Ω T stage L).IsTriangulated)
    (hlift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
      (V : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
      (hV : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T
        (DerivedCategory.Q.obj V.obj)),
      HEq (((b h).hom.app ⟨DerivedCategory.Q.obj V.obj, hV⟩).hom ≫
        eqToHom (congrArg (fun F ↦ F.obj
          ((U l Ω T h).obj ⟨DerivedCategory.Q.obj V.obj, hV⟩))
          (stage L).integral_identity) ≫
        (integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).map
          ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).hom.app V) ≫
        (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω L) T).hom.app
          ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).obj V.obj))
        ((pbcAmbientScalarExtension l Ω T h).map
          ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T).hom.app V.obj) ≫
        pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
          (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex
            (.up ℤ)).obj V.obj) ≫
        DerivedCategory.Q.map ((ordinary h).completion l Ω V.obj)))
    (hcocycle : ∀ {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      (b k).inv.app ((U l Ω T h).obj K) ≫
        (C l Ω T k).map ((b h).inv.app K) ≫
        (pbcIntegralScalarAssociator l Ω T dT.out iT.out h k).hom.app
          ((I l Ω T stage E).obj K) =
      (I l Ω T stage M).map ((integralAssoc l Ω T h k).hom.app K) ≫
        (b (h.trans k)).inv.app K)
    (hunit : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      (b (le_refl E)).inv.app K ≫
        (pbcIntegralScalarUnit l Ω T dT.out iT.out E).hom.app ((I l Ω T stage E).obj K) =
      (I l Ω T stage E).map ((integralUnit l Ω T E).hom.app K)) :
    ∃ family : RationalFamily l Ω T stage,
    ∃ j : RawComparison l Ω T stage family,
      (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
        NatTrans.CommShift (j h).hom ℤ ∧ NatTrans.CommShift (j h).inv ℤ ∧
        (scalar l Ω T h ⋙ J l Ω T stage family L).IsTriangulated ∧
        (J l Ω T stage family E ⋙ (P l Ω T).T h).IsTriangulated) ∧
      (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
        (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
        (K' : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        HEq K' ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K) →
        HEq ((j h).hom.app K')
          ((pbcStageLocalization l Ω T L).map ((b h).inv.app K) ≫
            (pbcScalarIntegralComparison l Ω T dT.out iT.out h).inv.app
              ((I l Ω T stage E).obj K))) ∧
      (∀ (E : Padic.FiniteCoefficientFields l Ω)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        HEq ((j (le_refl E)).hom.app K)
          ((J l Ω T stage family E).map
            ((unit l Ω T E).hom.app K))) ∧
      (∀ {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        (j k).hom.app ((scalar l Ω T h).obj K) ≫
          ((P l Ω T).T k).map ((j h).hom.app K) ≫
          ((P l Ω T).assoc h k).hom.app ((J l Ω T stage family E).obj K) =
        (J l Ω T stage family M).map ((assoc l Ω T h k).hom.app K) ≫
          (j (h.trans k)).hom.app K) ∧
      (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        (j h).hom.app ((scalar l Ω T (le_refl E)).obj K) ≫
          ((P l Ω T).T h).map ((j (le_refl E)).hom.app K) ≫
          ((P l Ω T).assoc (le_refl E) h).hom.app ((J l Ω T stage family E).obj K) =
        (J l Ω T stage family L).map ((scalar l Ω T h).map
          ((unit l Ω T E).hom.app K)) ≫
          (j h).hom.app K) ∧
      (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        (j (le_refl L)).hom.app ((scalar l Ω T h).obj K) ≫
          ((P l Ω T).T (le_refl L)).map ((j h).hom.app K) ≫
          ((P l Ω T).assoc h (le_refl L)).hom.app ((J l Ω T stage family E).obj K) =
        (J l Ω T stage family L).map
          ((unit l Ω T L).hom.app
            ((scalar l Ω T h).obj K)) ≫ (j h).hom.app K) := by
  sorry

end WeilConjectures.FdRawLocalization
