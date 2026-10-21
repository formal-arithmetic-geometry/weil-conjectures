/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.Paper.ContinuousConstructibleModule
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
import Sheaf.CategoryTheory.ScalarLocalizationSheafExact
import Sheaf.CategoryTheory.ExtOneExtensionClassification
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# Integral models of extensions from an Ext denominator criterion

Source: Bhatt--Scholze, Lemma 6.8.13, final paragraph; Stacks Project, Tag 06XV.
(blueprint: lem-weil-pbc-integral-models-extension-closed)

The surjectivity hypothesis is written using short exact representatives of numerators:
for every rational Ext class xi there is an integral short exact sequence whose actual
scalar extension has class varpi^m xi. Ext-one classification and exactness of scalar
extension identify this with surjectivity of Ext^1(P,Q)[1/varpi] -> Ext^1(SP,SQ).
The integral numerator's middle object is not assumed constructible.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Scalar extension along the actual inclusion of continuous integral coefficients.
Source: Bhatt--Scholze, Definition 6.8.1 and Lemma 6.8.13
(blueprint: lem-weil-pbc-integral-models-extension-closed). -/
abbrev integralModelScalarExtension (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (M : SheafOfModules.{u + 1} (latticeModuleRing X (latticeCoefficientIntegers l E))) :
    SheafOfModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))) :=
  SheafOfModules.changeOfRings.{u, u + 1, u + 1} (integralLatticeCoefficientMap X l E) M

/-- Scalar extension of an arrow, with the prescribed map on pure tensors.
Source: Bhatt--Scholze, Lemma 6.8.13; Stacks Project, Tag 03EK
(blueprint: lem-weil-pbc-integral-models-extension-closed). -/
abbrev integralModelScalarExtensionMap (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {M N : SheafOfModules.{u + 1} (latticeModuleRing X (latticeCoefficientIntegers l E))}
    (f : M ⟶ N) :
    integralModelScalarExtension X l E M ⟶ integralModelScalarExtension X l E N :=
  SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} (integralLatticeCoefficientMap X l E) M f

/-- A coefficient acts on a continuous-coefficient module by its constant section.
Source: Bhatt--Scholze, Definition 6.8.1 and Lemma 6.8.13
(blueprint: lem-weil-pbc-integral-models-extension-closed). -/
def integralModelConstantScalar (X : Scheme.{u}) (K : Type u) [CommRing K]
    [TopologicalSpace K] [IsTopologicalRing K]
    (M : SheafOfModules.{u + 1} (latticeModuleRing X K)) (a : K) : M ⟶ M where
  val :=
    { app := fun V ↦ ModuleCat.ofHom
        (LinearMap.lsmul ((latticeCoefficientSheaf X K).obj.obj V) (M.val.obj V)
          (ULift.up (ContinuousMap.const V.unop.left a)))
      naturality := fun {V W} f ↦ by
        ext x
        exact (M.val.map_smul f (ULift.up (ContinuousMap.const V.unop.left a)) x).symm }

/-- An extension of two rationalized constructible integral modules admits an integral model.
Source: Bhatt--Scholze, Lemma 6.8.13, final paragraph; Stacks Project, Tag 06XV
(blueprint: lem-weil-pbc-integral-models-extension-closed).

The denominator hypothesis is precisely the fraction-surjectivity condition, expressed
without choosing a model of the localized Ext map. An integral short exact representative
has class alpha; its scalar extension has class S(alpha) by exact-functor compatibility.
The equation below is S(alpha) = varpi^m xi. Since the constant varpi is a unit over E,
this is equivalent to xi = varpi^(-m) S(alpha). Every localized class has a numerator
and a power denominator (LocalizedModule.Away), and every numerator has a short exact
representative (ext_one_extension_classification). Thus no integral constructibility
condition is included in the hypothesis on numerator representatives.

Proof:
1. The continuous-coefficient immersion-restriction theorem identifies A_X with its
completed finite coefficient tower and identifies A_X -> E_X with localization at varpi.
The scalar-localization sheaf exactness theorem makes the specified scalar extension exact.
2. Take the Ext class xi of the given short exact sequence and apply the denominator
hypothesis to obtain an integral short exact sequence Q -> B -> P, with scalar-extended
class varpi^m xi. This is choosing alpha/varpi^m above xi.
3. Its middle sheaf B is constructible: put this integral short exact sequence in degree
zero. The complex-SES triangle gives Q[0] -> B[0] -> P[0]. In the integral stratified
perfect characterization, Q[0] and P[0] satisfy condition (iii); the continuous coefficient
restriction comparison identifies the coefficients on every stratum. Closure under shifts
and cones puts B[0] in that subcategory; condition (iii) back gives continuous
constructibility of B with ordinary finitely presented A-module local models.
4. Change the given rational inclusion by precomposition with varpi^(-m) on S(Q).
Naturality of the SES connecting class shows that the modified sequence has class
varpi^m xi. Its middle object is still F. Equality of classes with the scalar-extended
integral sequence gives an isomorphism S(B) = F by Ext-one classification. Its compatibility
is with the modified inclusion only; the conclusion imposes none with the original one.
The finite-extension, noetherian, finite-dimensional and invertibility hypotheses used
by the characterization are exactly those below. No torsion-freeness is needed. -/
theorem integralModels_extension_closed
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X]
    (_hdim : ∃ n : ℕ, topologicalKrullDim X ≤ n) (_hl : IsUnit (l : Γ(X, ⊤)))
    [HasExt.{w} (SheafOfModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))]
    (P Q : SheafOfModules.{u + 1} (latticeModuleRing X (latticeCoefficientIntegers l E)))
    (_hP : IsContinuousConstructible X (latticeCoefficientIntegers l E) P)
    (_hQ : IsContinuousConstructible X (latticeCoefficientIntegers l E) Q)
    (_hsurj : ∀ ξ : Abelian.Ext (integralModelScalarExtension X l E P)
        (integralModelScalarExtension X l E Q) 1,
      ∃ (m : ℕ)
        (B : SheafOfModules.{u + 1} (latticeModuleRing X (latticeCoefficientIntegers l E)))
        (i : Q ⟶ B) (p : B ⟶ P) (z : i ≫ p = 0),
        (ShortComplex.mk i p z).ShortExact ∧
        ∃ (zE : integralModelScalarExtensionMap X l E i ≫
            integralModelScalarExtensionMap X l E p = 0)
          (hE : (ShortComplex.mk (integralModelScalarExtensionMap X l E i)
            (integralModelScalarExtensionMap X l E p) zE).ShortExact),
          hE.extClass = ξ.comp (Abelian.Ext.mk₀
            (integralModelConstantScalar X
              (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))
              (integralModelScalarExtension X l E Q)
              (((WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E)).symm
                (Padic.coefficientExtensionUniformizer l E : E)) ^ m))) (add_zero 1))
    (F : SheafOfModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
    (i : integralModelScalarExtension X l E Q ⟶ F)
    (p : F ⟶ integralModelScalarExtension X l E P) (z : i ≫ p = 0)
    (_h : (ShortComplex.mk i p z).ShortExact) :
    ∃ N : SheafOfModules.{u + 1} (latticeModuleRing X (latticeCoefficientIntegers l E)),
      IsContinuousConstructible X (latticeCoefficientIntegers l E) N ∧
        Nonempty (integralModelScalarExtension X l E N ≅ F) := by
  sorry

end AlgebraicGeometry.ProEtale
