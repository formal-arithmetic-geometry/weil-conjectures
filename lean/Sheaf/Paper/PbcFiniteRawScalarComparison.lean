/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.Paper.FiniteStagePairCategory
public import Sheaf.Paper.PbcScalarExtension

/-! # Normalized finite-stage and embedding scalar extension

Source: BS Proposition 6.8.14(2), Remark 6.8.15; Stacks 03EK and 0D6D
(blueprint: def-zl-pbc-finite-raw-scalar-comparison).

## Main definitions

- `pbcFiniteRawScalarComparison`: the integral-normalized comparison between the
  StageSystem transition and raw scalar tensor on the same small coefficient fields.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)

/-- The two finite-field scalar constructions have a unique integral-normalized
comparison. HEq retains the canonical equality of the quotient-normalized
coefficient maps and hence of their actual derived tensor objects.
Source: BS 6.8.14(2), 6.8.15; Stacks 03EK and 0D6D
(blueprint: def-zl-pbc-finite-raw-scalar-comparison).
Proof: on every finite quotient the transported field inclusion defining
pbcCompletedScalarMap is the same coefficient map as pbcScalarCoefficientMap for
the canonical small fields. The inverse-limit universal property makes the two
completed maps equal. Ordinary derived extension along equal maps is the same
functor. Their full integral restrictions therefore agree by proof irrelevance.
For distinct fields the unique raw localization factorization is the embedding
scalar functor, since both maps send a localized integral arrow to its scalar
extension with the coefficient scalar transported by the inclusion. At equal
fields use the canonical tensor-multiplication unit, exactly as in
pbcScalarIntegralComparison. This gives a natural isomorphism whose integral
components are the displayed ones. Every object of raw localization is Q(K),
and every arrow is a sum of localized integral arrows, so these components and
naturality determine the isomorphism uniquely, including the reflexive case. -/
theorem pbcFiniteRawScalarComparison_existsUnique :
    ∃! c : (pbcScalarSystem l Ω T dT.out iT.out).T h ≅
        pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h)
          T dT.out iT.out,
      ∀ K : pbcIntegralStage l Ω T E,
        HEq (c.hom.app ((pbcStageLocalization l Ω T E).obj K))
          ((pbcScalarIntegralComparison l Ω T dT.out iT.out h).hom.app K) := by
  sorry

/-- The unique comparison fixed on every integral representative; its identity-field
case is the recorded tensor-multiplication unit, rather than an arbitrary automorphism.
Source: BS 6.8.14(2), 6.8.15; Stacks 03EK and 0D6D
(blueprint: def-zl-pbc-finite-raw-scalar-comparison). -/
def pbcFiniteRawScalarComparison :=
  (pbcFiniteRawScalarComparison_existsUnique l Ω T h).exists.choose

end AlgebraicGeometry.Scheme
