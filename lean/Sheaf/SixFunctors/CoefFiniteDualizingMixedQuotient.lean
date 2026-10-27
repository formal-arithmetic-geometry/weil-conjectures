/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.CoefScalarReductionExchange
public import Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels

/-! # The finite dualizing mixed quotient square

Source: current blueprint lem-coef-integral-finite-extension, paragraphs 3--4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

variable [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Cross-field finite dualizing counit maps commute with the actual exceptional
quotient transitions, through the mixed scalar/quotient map. No integral
presentation of a dualizing object occurs in this statement.
Source: lem-coef-integral-finite-extension, paragraphs 2--3, and
lem-coef-finite-dualizing, quotient cocycle and finite realization.
(blueprint: lem-sf-finite-dualizing-mixed-quotient)

Proof: Work first on the ordinary etale site. The coefficient square sends a
representative x to the class of its image in L along either path. Paste the
proper coefficient counit mates and the open balancing comparisons for these
two paths. Proper functoriality and tensor associativity identify their outer
compact-support comparisons. At the regular coefficient object their scalar
unit maps agree, since both send 1 to 1. Transpose the resulting compact-support
square under the exceptional adjunction and the two scalar adjunctions. The
triangle identities and counit naturality identify its horizontal maps with
finiteEtaleU and its vertical maps with finiteDualizingEtaleTransition. Equivalently
one may first work at a larger ramification-multiple exponent, use the finite-free
coefficient comparison there, and compose with the finite dualizing quotient
comparison; its cocycle identifies the two factorizations at every exponent.
The comparison-site realization restriction square is normalized by identity
on scalar sections, so its two pasted versions agree before localization and
continue to agree after exact localization. Transport the etale square through
finiteDualizingOrigin and finiteRealizationRestriction. Their inverse pairs
cancel, giving finiteU and integralDualizingExceptionalTransition. The mixed
map is precisely the mate defining scalarReductionExchange, so the resulting
square is the displayed one. This uses no integral lift, no finite-evaluation
faithfulness, and no invertibility of scalarReductionExchange. Identity
extensions, m=n, level zero, and empty X satisfy the same unit formulas. -/
/- Mate form of the finite quotient transition square.

The equality is obtained by transposing the displayed square under the scalar
adjunction at level `m`; the exceptional and realization mates reduce it to the
coefficient counit square. This is the central mate calculation in the proof.
Source: lem-coef-integral-finite-extension, paragraphs 2--3.
(blueprint: lem-sf-finite-dualizing-mixed-quotient-mate) -/
theorem finiteU_quotient_transition_mate {m n : ℕ} (h : n ≤ m) :
    (pbcDerivedScalarAdjunction
      (integralScalarQuotientSheafMap l E L ι X m)).homEquiv _ _
      ((pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X m)).map
          (integralDualizingExceptionalTransition l E D X hl h) ≫
        (scalarReductionExchange l E L ι X h).app
          (integralDualizingFiniteTerm l E D X n) ≫
        (normalizedDVRRes l L X h).map
          (finiteU l E L ι X D n)) =
    (pbcDerivedScalarAdjunction
      (integralScalarQuotientSheafMap l E L ι X m)).homEquiv _ _
      (finiteU l E L ι X D m ≫
        integralDualizingExceptionalTransition l L D X hl h) := by
  sorry

theorem finiteU_quotient_transition {m n : ℕ} (h : n ≤ m) :
    (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X m)).map
        (integralDualizingExceptionalTransition l E D X hl h) ≫
      (scalarReductionExchange l E L ι X h).app (integralDualizingFiniteTerm l E D X n) ≫
      (normalizedDVRRes l L X h).map (finiteU l E L ι X D n) =
    finiteU l E L ι X D m ≫ integralDualizingExceptionalTransition l L D X hl h := by
  apply Equiv.injective ((pbcDerivedScalarAdjunction
    (integralScalarQuotientSheafMap l E L ι X m)).homEquiv _ _)
  exact finiteU_quotient_transition_mate l E L ι X D hl h

end WeilConjectures.IntegralFiniteExtension
