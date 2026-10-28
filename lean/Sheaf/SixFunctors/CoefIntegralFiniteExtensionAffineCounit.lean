module

public import Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels
public import Sheaf.SixFunctors.DualizingOpenMate

/-! # The cross-field dualizing counit on an affine scheme

Source: current blueprint lem-coef-integral-finite-extension.proof.md, paragraph 2,
and lem-coef-finite-dualizing.proof.md, affine closed-chart argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

/-- On an affine finite-type scheme, the coefficient-extension mate of the dualizing
counit is invertible, including the native (possibly nonflat) quotient levels.

Source: current blueprint lem-coef-integral-finite-extension.proof.md, paragraph 2,
and lem-coef-finite-dualizing.proof.md, paragraphs 2--3.
(blueprint: lem-sf-integral-finite-extension-affine-counit)

Proof: write R = O_E and S = O_L, and let e be the ramification index.
The quotient S/(pi_E^(n+1)) is finite free over R/(pi_E^(n+1)).
Apply the finite-free exceptional counit comparison at this cofinal level.
Identify its upper coefficient ring with S/(pi_L^(e*(n+1))) using the
unit-times-uniformizer relation. The finite dualizing quotient theorem over L
then reduces from exponent e*(n+1) to exponent n+1. The counit composition
identity identifies the composite of these two invertible comparisons with the
native quotient comparison induced by ι. Scalar extension preserves the first
isomorphism, so the composite is invertible. This also explains why no flatness
of the native quotient map R/(pi_E^(n+1)) -> S/(pi_L^(n+1)) is asserted.
Transfer from the canonical exceptional adjoints to GA and GB using uniqueness
of right adjoints. Their counit equations identify the transported comparison
with exactly globalMate for c. The affine quotient calculation can equivalently
be computed in a closed affine-space chart by the finite-dualizing proof;
no open-cover descent or intrinsic site normalization is part of this lemma.
For Y empty the categories are zero. For an identity embedding the same
composition and adjunction identities give the identity comparison.
-/
theorem affineCounit_isIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (n : ℕ)
    (Y : Scheme.{u}) [IsAffine Y] (aY : Y ⟶ Spec (.of D.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (c : Compactification aY)
    (GA : Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) (Spec (.of D.k)) ⥤
      Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) Y)
    (GB : Etale.DerivedCategoryModule (finiteDualizingCoeff l L n) (Spec (.of D.k)) ⥤
      Etale.DerivedCategoryModule (finiteDualizingCoeff l L n) Y)
    (aA : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c ⊣ GA)
    (aB : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (finiteDualizingCoeff l L n)) c ⊣ GB) :
    IsIso (Etale.DualizingOpenMate.globalMate
      (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n))
      c GA GB aA aB) := by sorry

end WeilConjectures.IntegralFiniteExtension
