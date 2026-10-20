/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.SixFunctors.IntegralVerdier
public import Sheaf.SixFunctors.IntegralDualizing
public import Sheaf.SixFunctors.CoefIntegralFiniteExtension
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.SixFunctors.ConstructibleTensorCompletion
public import Sheaf.Paper.DirectImagesConstructible
import Sheaf.Paper.IntegralResidueTor
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.FiniteTorAmplitude
import Sheaf.CategoryTheory.ScalarLocalization
import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.IntegralOperationsPreserveConstructible

/-! # Rational Verdier duality and coherent coefficient extension

Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-tower,
`thm-coef-rational-verdier.md` and its proof (blueprint: thm-coef-rational-verdier).

All categories are the recorded raw scalar localizations. The presentation records
below retain the actual integral RHom, normalized completion map, evaluation,
and double-dual arrow. No dualizing object is chosen from a mere existence proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]

/-- The residue-field inverses are transported from the base, with no extra hypothesis.
Source: blueprint global coefficient convention (blueprint: thm-coef-rational-verdier). -/
@[instance_reducible] def units : ∀ x : X, Invertible (l : X.residueField x) :=
  fun x ↦ (by
    simpa using (finiteFieldDatumPrimeUnit D l hl).map
      ((X ↘ Spec (.of D.k)).residueFieldAlgebraMap x) : IsUnit (l : X.residueField x)).invertible

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The recorded completed integral tensor, with its derived residue-field inverses.
Source: blueprint tensor convention (blueprint: thm-coef-rational-verdier). -/
abbrev integralTensor :=
  @constructibleIntegralTensor l _ E _ _ _ X (units D l hl X)

/-- The recorded rational tensor, using the identical coefficient-passage operation.
Source: blueprint tensor convention (blueprint: thm-coef-rational-verdier). -/
abbrev tensor := @rationalDerivedTensor l _ E _ _ _ X (units D l hl X)

variable [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The actual chain completion map from the recorded comparison theorem. Its quotient
coordinates on every homogeneous local tensor generator and its zero shifted coordinate
uniquely determine this chain map: the two mapping-fiber coordinates are jointly monic,
and the total tensor is generated locally by these tensors. The theorem therefore
specifies the data up to equality, rather than merely asserting an unspecified lift.
Source: blueprint proof step 5 (blueprint: thm-coef-rational-verdier). -/
def completionChain :
    constructibleTensorTotal l E X ⟶ integralOperationsTensorComplexFunctor l E X :=
  (@constructibleTensorCompletion l _ E _ _ _ X
    (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)))
    (quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of D.k)))
    (units D l hl X)).choose_spec.choose_spec.choose

/-- Ordinary-to-completed tensor comparison with the recorded quotient-map normalization.
The fixed chain map retains both mapping-fiber coordinates; its representative descent
fixes the derived natural transformation in the ordinary tensor presentation of duality.
Source: blueprint proof step 5 (blueprint: thm-coef-rational-verdier). -/
structure Completion
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X)) where
  map : a.tensor ⟶ integralCompletedTensor l E X
  invertible : ∀ K M : sfIntegralConstructibleCategory l E X, IsIso (map.app (K.obj, M.obj))
  representative : ∀ P Q : (integralOperationsGoodComplex l E X).FullSubcategory,
    HEq (a.representative.hom.app (⟨P.obj, P.property.1⟩, ⟨Q.obj, Q.property.1⟩) ≫
      map.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (integralCompletedTensorComparison l E X).hom.app (P, Q))
      (DerivedCategory.Q.map ((completionChain D l hl X E).app (P.obj, Q.obj)))


/-- A presentation of rationalized integral duality. The object and pure-tensor formulas
fix the functor, and evaluation and biduality are the specified localized integral maps.
E-linearity uses the canonical field coordinates sfRationalCoefficientEquiv.
Source: blueprint first three assertions (blueprint: thm-coef-rational-verdier). -/
structure Datum (w : IntegralFiniteExtension.DualizingDatum l X D hl E) where
  ordinary : IntegralHom.TensorPresentation.{u, u} X
    (completedIntegralCommRingSheafUnrestricted l E X)
  symmetry : IntegralVerdier.SignedSymmetry X _ ordinary
  completion : Completion D l hl X E ordinary
  preserves : ∀ K : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l E X ((IntegralVerdier.dual l E X w.omega.obj).obj (op K.obj))
  dual : (sfRationalConstructibleCategory l E X)ᵒᵖ ⥤ sfRationalConstructibleCategory l E X
  objects : ∀ K : sfRationalConstructibleCategory l E X,
    dual.obj (op K) = (sfRationalConstructibleLocalization l E X).obj
      ((IntegralVerdier.restrictedDual l E X w.omega.obj preserves).obj (op K.obj))
  additive : dual.Additive
  linear : ∀ (K M : sfRationalConstructibleCategory l E X)
    (f : K ⟶ M) (c : E),
    dual.map (Quiver.Hom.op ((sfRationalCoefficientEquiv l E).symm c • f)) =
      (sfRationalCoefficientEquiv l E).symm c • dual.map f.op
  pure : ∀ (K M : sfIntegralConstructibleCategory l E X) (f : K ⟶ M)
    (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
    HEq (dual.map (Quiver.Hom.op (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
      (sfRationalConstructibleLocalization l E X).obj K ⟶
        (sfRationalConstructibleLocalization l E X).obj M)))
      (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
        (IntegralVerdier.restrictedDual l E X w.omega.obj preserves).map f.op)
  equivalence : dual.IsEquivalence
  exact : ∃ s : dual.CommShift ℤ, ∀ T : Triangle (sfRationalConstructibleCategory l E X)ᵒᵖ,
    T ∈ distTriang (sfRationalConstructibleCategory l E X)ᵒᵖ →
    Triangle.mk (dual.map T.mor₁) (dual.map T.mor₂)
      (dual.map T.mor₃ ≫ (s.commShiftIso (1 : ℤ)).hom.app T.obj₁) ∈
        distTriang (sfRationalConstructibleCategory l E X)
  bidual : 𝟭 (sfRationalConstructibleCategory l E X) ≅ dual.rightOp ⋙ dual
  bidual_integral : ∀ K : sfIntegralConstructibleCategory l E X,
    HEq (bidual.hom.app ((sfRationalConstructibleLocalization l E X).obj K))
      ((sfRationalConstructibleLocalization l E X).map
        (ObjectProperty.homMk (X := K)
          (Y := (IntegralVerdier.restrictedDual l E X w.omega.obj preserves).obj
            (op ((IntegralVerdier.restrictedDual l E X w.omega.obj preserves).obj (op K))))
          (IntegralVerdier.delta X ordinary symmetry w.omega.obj K.obj)))
  evaluation : ∀ K : sfRationalConstructibleCategory l E X,
    (tensor D l hl X E).obj (K, dual.obj (op K)) ⟶
      (sfRationalConstructibleLocalization l E X).obj w.omega
  evaluation_integral : ∀ K : sfIntegralConstructibleCategory l E X,
    HEq (evaluation ((sfRationalConstructibleLocalization l E X).obj K))
      ((sfRationalConstructibleLocalization l E X).map
        (ObjectProperty.homMk
          (X := (integralTensor D l hl X E).obj
            (K, (IntegralVerdier.restrictedDual l E X w.omega.obj preserves).obj (op K)))
          (Y := w.omega)
          ((@asIso _ _ _ _ (completion.map.app
            (K.obj, (IntegralVerdier.dual l E X w.omega.obj).obj (op K.obj)))
              (completion.invertible K
                ((IntegralVerdier.restrictedDual l E X w.omega.obj preserves).obj (op K)))).inv ≫
            (ordinary.adjunction K.obj).counit.app w.omega.obj)))
  evaluation_natural : ∀ (K M : sfRationalConstructibleCategory l E X) (f : K ⟶ M),
    (tensor D l hl X E).map (Prod.mkHom f (𝟙 (dual.obj (op M)))) ≫ evaluation M =
      (tensor D l hl X E).map (Prod.mkHom (𝟙 K) (dual.map f.op)) ≫ evaluation K


end WeilConjectures.RationalVerdier

namespace WeilConjectures.RationalVerdier

/-- Scalar extension on the recorded raw rational category; the auxiliary characteristic
parameter is unused in the object and arrow formulas. Choosing zero here agrees exactly
with the coefficient-passage tensor comparison's convention.
Source: blueprint coefficient-extension clause (blueprint: thm-coef-rational-verdier). -/
abbrev scalar (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) :=
  sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι

/-- Integral representatives of the same completed scalar extension.
Source: blueprint coefficient-extension clause (blueprint: thm-coef-rational-verdier). -/
abbrev integralScalar (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) :=
  sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)
  (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
  (wL : IntegralFiniteExtension.DualizingDatum l X D hl L)

/-- The rational dualizing and natural duality comparison maps. Their canonical integral
normalizations and the evaluation and double-dual squares are ExtensionProperties.
Source: blueprint finite-extension paragraph (blueprint: thm-coef-rational-verdier). -/
structure Extension (A : Datum D l hl X E wE) (B : Datum D l hl X L wL) where
  omega : (scalar l X E L ι).obj ((sfRationalConstructibleLocalization l E X).obj wE.omega) ≅
    (sfRationalConstructibleLocalization l L X).obj wL.omega
  comparison : A.dual ⋙ scalar l X E L ι ≅ (scalar l X E L ι).op ⋙ B.dual

/-- Equations fixing both scalar comparisons to their integral origins, and their
compatibility with completed evaluation and the actual double-dual map.
Source: blueprint finite-extension paragraph (blueprint: thm-coef-rational-verdier). -/
def ExtensionProperties (A : Datum D l hl X E wE) (B : Datum D l hl X L wL)
    (e : Extension D l hl X E L ι wE wL A B) : Prop :=
  (HEq e.omega.hom ((sfRationalConstructibleLocalization l L X).map
    (ObjectProperty.homMk (X := (integralScalar l X E L ι).obj wE.omega) (Y := wL.omega)
      (IntegralFiniteExtension.u l E L ι X D hl wE wL)))) ∧
  (∀ K : sfIntegralConstructibleCategory l E X,
    HEq (e.comparison.hom.app (op ((sfRationalConstructibleLocalization l E X).obj K)))
      ((sfRationalConstructibleLocalization l L X).map
        (ObjectProperty.homMk
          (X := (integralScalar l X E L ι).obj
            ((IntegralVerdier.restrictedDual l E X wE.omega.obj A.preserves).obj (op K)))
          (Y := (IntegralVerdier.restrictedDual l L X wL.omega.obj B.preserves).obj
            (op ((integralScalar l X E L ι).obj K)))
          (IntegralFiniteExtension.beta l E L ι X D hl wE wL A.ordinary B.ordinary
            K.obj K.property.1)))) ∧
  (∀ K : sfRationalConstructibleCategory l E X,
    (tensor D l hl X L).map
        (Prod.mkHom (𝟙 ((scalar l X E L ι).obj K)) (e.comparison.hom.app (op K))) ≫
      B.evaluation ((scalar l X E L ι).obj K) =
    (@rationalTensorScalarComparison l _ E _ _ _ L _ _ _ ι X (units D l hl X)).inv.app
        (K, A.dual.obj (op K)) ≫
      (scalar l X E L ι).map (A.evaluation K) ≫ e.omega.hom) ∧
  (∀ K : sfRationalConstructibleCategory l E X,
    (scalar l X E L ι).map (A.bidual.hom.app K) ≫
      e.comparison.hom.app (op (A.dual.obj (op K))) =
    B.bidual.hom.app ((scalar l X E L ι).obj K) ≫ B.dual.map (e.comparison.hom.app (op K)).op)


/-- Simultaneous duality and scalar comparisons for every finite coefficient field and
coherent dualizing presentation. Unit and associator maps are the rationalizations of
integral multiplication and tensor associativity, and the equations concern the specified
comparison itself. The quantified presentations introduce no extra existence assumption:
IntegralFiniteExtension.dualizingDatum_nonempty supplies them from integral dualizing.
Source: blueprint all clauses (blueprint: thm-coef-rational-verdier). -/
def Conclusion : Prop :=
  ∃ (duality : ∀ (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (wF : IntegralFiniteExtension.DualizingDatum l X D hl F), Datum D l hl X F wF),
  ∃ (extension : ∀ (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
    (i : F →ₐ[Padic l] G)
    (wF : IntegralFiniteExtension.DualizingDatum l X D hl F)
    (wG : IntegralFiniteExtension.DualizingDatum l X D hl G),
    Extension D l hl X F G i wF wG (duality F wF) (duality G wG)),
  (∀ (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
    (i : F →ₐ[Padic l] G)
    (wF : IntegralFiniteExtension.DualizingDatum l X D hl F)
    (wG : IntegralFiniteExtension.DualizingDatum l X D hl G),
    ExtensionProperties D l hl X F G i wF wG (duality F wF) (duality G wG)
      (extension F G i wF wG)) ∧
  (∀ (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (wF : IntegralFiniteExtension.DualizingDatum l X D hl F),
    ∃ j : scalar l X F F (AlgHom.id (Padic l) F) ≅ 𝟭 (sfRationalConstructibleCategory l F X),
      (∀ K : sfIntegralConstructibleCategory l F X,
        HEq (j.hom.app ((sfRationalConstructibleLocalization l F X).obj K))
          ((sfRationalConstructibleLocalization l F X).map
            (ObjectProperty.homMk
              (X := (integralScalar l X F F (AlgHom.id (Padic l) F)).obj K) (Y := K)
              (IntegralFiniteExtension.unit l F X K.obj K.property.1).hom))) ∧
      ∀ K : sfRationalConstructibleCategory l F X,
        (extension F F (AlgHom.id (Padic l) F) wF wF).comparison.hom.app (op K) =
          j.hom.app ((duality F wF).dual.obj (op K)) ≫
            (duality F wF).dual.map (j.hom.app K).op) ∧
  ∀ (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
    (H : Type u) [Field H] [Algebra (Padic l) H] [FiniteDimensional (Padic l) H]
    (i : F →ₐ[Padic l] G) (j : G →ₐ[Padic l] H)
    (wF : IntegralFiniteExtension.DualizingDatum l X D hl F)
    (wG : IntegralFiniteExtension.DualizingDatum l X D hl G)
    (wH : IntegralFiniteExtension.DualizingDatum l X D hl H),
    ∃ a : scalar l X F G i ⋙ scalar l X G H j ≅ scalar l X F H (j.comp i),
      (∀ K : sfIntegralConstructibleCategory l F X,
        HEq (a.hom.app ((sfRationalConstructibleLocalization l F X).obj K))
          ((sfRationalConstructibleLocalization l H X).map
            (ObjectProperty.homMk
              (X := (integralScalar l X G H j).obj ((integralScalar l X F G i).obj K))
              (Y := (integralScalar l X F H (j.comp i)).obj K)
              (IntegralFiniteExtension.comp l F G i X H j K.obj K.property.1).hom))) ∧
      ∀ K : sfRationalConstructibleCategory l F X,
        (scalar l X G H j).map ((extension F G i wF wG).comparison.hom.app (op K)) ≫
          (extension G H j wG wH).comparison.hom.app (op ((scalar l X F G i).obj K)) =
        a.hom.app ((duality F wF).dual.obj (op K)) ≫
          (extension F H (j.comp i) wF wH).comparison.hom.app (op K) ≫
            (duality H wH).dual.map (a.hom.app K).op


end WeilConjectures.RationalVerdier

namespace WeilConjectures

/-- Integral duality induces rational Verdier duality, with canonical evaluation,
biduality, dualizing object and coherent finite coefficient-field comparisons.
Source: Weil blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
thm-coef-rational-verdier, proof paragraphs 1--3
(blueprint: thm-coef-rational-verdier).

Proof (the seven DAG steps):
1. lem-coef-integral-residue-tor identifies the whole integral constructible category
with its finite-Tor subcategory. thm-coef-integral-verdier gives exact duality and the
actual invertible delta. prop-coef-integral-dualizing supplies omega. Internal Hom
precomposition is O_E-linear, so duality does not apply a scalar involution.
2. On unchanged objects put D_E K = D_R K and on pure tensors put
D_E(c tensor f) = c tensor D_R(f). Integral linearity preserves balancing;
contravariant composition and identities extend to sums. This also identifies the
localization of the opposite category with the opposite raw localization.
3. Every rational distinguished triangle is isomorphic to a localized integral one.
Apply integral exact duality and localize its shift comparison and inverse. This
proves exactness for the specified triangulation, without adjoining idempotents.
4. Integral full faithfulness gives inverse linear Hom maps, whose tensor extensions
remain inverse. Localized integral delta gives essential surjectivity. Its naturality
on pure tensors is integral naturality multiplied by the scalar, then extended to sums
(as in prop-weil-pbc-rational-transport for the covariant double-dual functors).
5. lem-pur-integral-operations-preserve-constructible keeps completed tensor in the
integral category. lem-fix-constructible-tensor-completion gives the normalized map chi
and its inverse. Integral evaluation on ordinary tensor, composed with chi inverse,
is completed evaluation. Localize this and the actual integral delta; naturality of
chi preserves evaluation and its transpose, with omega_E = Q omega_R.
6. lem-coef-integral-finite-extension supplies the canonical u and beta with their
inverses, evaluation and delta squares. Rationalize beta. Naturality on pure tensors
is integral naturality multiplied by the coefficient. Conjugating the ordinary tensor
comparison by chi identifies the completed comparison of the recorded tensor operation.
Localizing the two integral squares gives the evaluation and biduality clauses
of ExtensionProperties.
7. Localize the integral tensor unit and associator. Every factor in their equations
is integral, so functoriality of Q gives the displayed unit and associator equations
for these same specified canonical comparisons. Identity extensions are included. -/
theorem coef_rational_verdier
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] :
    RationalVerdier.Conclusion D l hl X := by
  sorry

end WeilConjectures
