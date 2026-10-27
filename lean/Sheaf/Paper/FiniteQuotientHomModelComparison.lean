/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z9
-/
module

public import Sheaf.Paper.FiniteRationalDerivedOperations
public import Sheaf.Algebra.Homology.SitePerfectScalarHomComparison

/-! # Comparison of normalized finite quotient Hom models -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
/-- Compare the evaluation-defined maps of any normalized scalar Hom model with
those of the published finite quotient calculus, on every ambient pair. There is no
perfectness hypothesis or invertibility assertion here.
Source: current blueprint lem-fix-operation-reduction.proof.md, first paragraph;
Stacks Tags 08JJ and 08J9; the normalized K-flat models of
lem-fix-site-perfect-scalar-hom and lem-coef-derived-system-evaluation-calculus.
(blueprint: lem-sf-finite-quotient-hom-model-comparison).

Proof: the model's ordinary scalar functor and the quotient calculus are the same
sheafified balanced tensor functor. Their universal derived counits give the unique
isomorphism e respecting those counits. Compare the closed tensor products through
the unique isomorphism of left adjoints of their common internal Hom. On K-flat
representatives these tensor identifications send each total pure tensor to itself:
this follows from the representative tensor-model squares and their evaluation
normalizations. The two scalar tensor comparisons then agree on every pure tensor,
and hence on sheafified tensor products; localization and simultaneous K-flat
resolutions descend this equality to all derived pairs. Their Koszul symmetries agree
on each signed summand, so the symmetric version used by siteScalarHomComparison is
the same map as the Hom-tensor-P version used by finiteIntrinsicReductionHom.
Uncurry the displayed square with the target closed adjunction. Naturality of e,
the tensor comparison square and the evaluation normalization identify both sides
with the same scalar-extended source evaluation. Injectivity of transposition proves
the equality. This argument uses arbitrary P and Q, without perfectness, and includes
identity quotients, the zero object and the empty scheme. -/
theorem finiteQuotient_homModel_comparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (m n : ℕ) (h : m ≤ n) :
    letI : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
    letI := integralCoefficientAbSheafify.{u, u} W
    letI := integralCoefficientAbLocallyBijective.{u, u} W
    letI := HasDerivedCategory.standard (RingedTensorModules.{u + 1, u, u}
      (ProEt.topology W) (integralCoefficientCommRingSheaf l E W n))
    letI := HasDerivedCategory.standard (RingedTensorModules.{u + 1, u, u}
      (ProEt.topology W) (integralCoefficientCommRingSheaf l E W m))
    ∀ A : SitePerfectScalarHomData.{u + 1, u, u, u + 2} (ProEt.topology W)
      (coefficientFiniteQuotient l E W h),
    ∃ e : SheafOfModules.DerivedChangeOfRingsCochainModel.T.{u + 1, u, u + 1, u + 2, u + 2}
        (SitePerfectScalarHomData.scalar.{u + 1, u, u, u + 2} A) ≅
          coefficientFiniteQuotientDerived l E W h,
      ∀ P Q : normalizedDVRDerived l E W n,
        siteScalarHomComparison.{u + 1, u, u, u + 2} _ (coefficientFiniteQuotient l E W h) A P Q ≫
            (coefficientFiniteInternalHom l E W m).map
              (Prod.mkHom (e.inv.app P).op (e.hom.app Q)) =
          e.hom.app ((coefficientFiniteInternalHom l E W n).obj (op P, Q)) ≫
            finiteIntrinsicReductionHom l E W h P Q := by sorry

end WeilConjectures
