/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.SfBidualityClass
public import WeilConjectures.AlgebraicGeometry.CompletedCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.CompactSupportRealizationCoordinates
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.CondensedVerdierBiduality
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.FiniteConstructibleHom

/-! # The coefficient-class theorem on ordinary condensed categories

Source: latest blueprint thm-sf-biduality-class, entire statement
(blueprint: thm-sf-biduality-class).

The dual is formed from the supplied constructible exceptional adjunction; its
normalization is determined up to the unique adjunction-compatible isomorphism.
The evaluation map is the existing Koszul-symmetric internal-Hom transpose.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry Scheme Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor MonoidalCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Actual ordinary derived reduction modulo the (n+1)-st uniformizer power.
The point map is postcomposition of continuous functions with the quotient map.
No completion of the derived category or of this scalar functor is performed.
Source: latest blueprint thm-sf-biduality-class, uniform finite reductions
(blueprint: thm-sf-biduality-class). -/
def condensedSfReduction (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E)
    (n : ℕ) (X : Scheme.{u}) :
    moduleDerived (Profinite.padicIntegersRingObj ell E) X ⥤
      moduleDerived (Profinite.continuousMapRingObj (completedResidue ell E π n)) X :=
  (Mod.extendScalars ((upperStarFromPoint X).map
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (completedReduction ell E π n)))).leftDerivedFunctor

/-- General biduality and the signed dimension bounds at all four ordinary coefficients.
The finite and integral bounds allow any nonnegative dimension upper bound, including
zero for the empty scheme. The integral interval is uniform over all positive reductions.
Source: latest blueprint thm-sf-biduality-class, all paragraphs
(blueprint: thm-sf-biduality-class).

Proof: use the ordinary coefficient comparison to transport finite geometric biduality,
including evaluation and signed Tor bounds. For integral coefficients, scalar-six
comparison identifies every reduction with finite duality. Integral models give derived
uniformizer completeness; Nakayama makes the evaluation map invertible. The residue Tor
criterion gives a uniform interval, and the finite bounds give the displayed common output
interval. Apply this to the coefficient unit to obtain omega's interval. Integral models
and exact localization give field duality, and finite coefficient-field descent gives
algebraically closed coefficient duality. The contravariant tensor-Hom adjunction makes
the evaluation biduality into the unit and counit of the self-duality, proving the exact
anti-equivalence. Uniqueness of constructible right adjoints transfers these statements
to every supplied operation datum. No ambient exceptional adjoint is used. -/
theorem condensedSfBidualityClass (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] [Fact (ell ≠ D.p)] :
    (∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj Λ] [IsCommMonObj Λ]
      (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E)
      (_hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E))
      (n : ℕ+),
      (Nonempty (Mon.mk Λ ≅ Mon.mk (IntegralModelsEmbedded.discreteObj
        (PadicAlgCl.integers ell E ⧸ (Ideal.span {π}) ^ (n : ℕ)))) ∨
       Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
       Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1)) ∨
       Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) →
      ∀ (T : Over (Spec (.of D.k))) [LocallyOfFiniteType T.hom]
        [QuasiCompact T.hom] [IsSeparated T.hom] (c : Compactification T.hom)
        (S : CondensedSixFunctorOperationDatum Λ c)
        (N : ConstantModelBoundedConstructible Λ (Spec (.of D.k))),
        N.obj = 𝟙_ (moduleDerived Λ (Spec (.of D.k))) →
        Nonempty (WeilConjectures.SfClassAmbientDuality (moduleDerived Λ T.left)
          (dctfPred Λ T.left) (S.verdier N)
          ((condensedVerdierBiduality Λ T.left (S.dualizing N)).app)) ∧
        (Nonempty (Mon.mk Λ ≅ Mon.mk (IntegralModelsEmbedded.discreteObj
          (PadicAlgCl.integers ell E ⧸ (Ideal.span {π}) ^ (n : ℕ)))) →
          ∀ d : ℕ, topologicalKrullDim T.left ≤ (d : WithBot ℕ∞) →
            (∀ (K : ConstantModelConstructibleFiniteTor Λ T.left) (a b : ℤ),
              a ≤ b → _root_.DerivedCategory.torAmplitudeIn _ a b K.obj →
              _root_.DerivedCategory.torAmplitudeIn _ (-b - 2 * (d : ℤ)) (-a)
                ((S.verdier N).obj (op K.obj))) ∧
            _root_.DerivedCategory.torAmplitudeIn _ (-(2 * (d : ℤ))) 0 (S.dualizing N)) ∧
        ((Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1)) ∨
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) →
          dctfPred Λ T.left = constantModelBoundedConstructible Λ T.left)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E),
      Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E) →
      ∀ (T : Over (Spec (.of D.k))) [LocallyOfFiniteType T.hom]
        [QuasiCompact T.hom] [IsSeparated T.hom] (c : Compactification T.hom)
        (S : CondensedSixFunctorOperationDatum (Profinite.padicIntegersRingObj ell E) c)
        (N : ConstantModelBoundedConstructible
          (Profinite.padicIntegersRingObj ell E) (Spec (.of D.k))),
        N.obj = 𝟙_ (moduleDerived (Profinite.padicIntegersRingObj ell E) (Spec (.of D.k))) →
        ∀ d : ℕ, topologicalKrullDim T.left ≤ (d : WithBot ℕ∞) →
          (∀ (K : ConstantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E)
              T.left) (a b : ℤ), a ≤ b →
            (∀ n : ℕ, _root_.DerivedCategory.torAmplitudeIn _ a b
              ((condensedSfReduction ell E π n T.left).obj K.obj)) →
            ∀ n : ℕ, _root_.DerivedCategory.torAmplitudeIn _ (-b - 2 * (d : ℤ)) (-a)
              ((condensedSfReduction ell E π n T.left).obj
                ((S.verdier N).obj (op K.obj)))) ∧
          ∀ n : ℕ, _root_.DerivedCategory.torAmplitudeIn _ (-(2 * (d : ℤ))) 0
            ((condensedSfReduction ell E π n T.left).obj (S.dualizing N))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
