/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

/-! # Signed exactness of the native derived internal Hom

Source: Stacks Project, Tags 08J9 and 08JC.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.ProEtale


section Shift
variable {D : Type d} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [MonoidalCategory D] [MonoidalClosed D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]

/-- The existing tensor shift in its parameter, assembled as a natural isomorphism.
Source: Stacks 08JC, total-tensor signs
(blueprint: lem-sf-site-hom-comparison-thick). -/
@[irreducible] def siteHomTensorParameterShift (K : D) (n : ℤ) :
    tensorLeft (K⟦n⟧) ≅ tensorLeft K ⋙ shiftFunctor D n :=
  NatIso.ofComponents (fun M ↦ (((curriedTensor D).flip.obj M).commShiftIso n).app K)
    (fun f ↦ (NatTrans.shift_app_comm ((curriedTensor D).flip.map f) n K).symm)

/-- The canonical source-Hom shift, as the right-adjoint mate of total-tensor shift.
This is the fixed-coefficient counterpart of the recorded ringed source shift, with
orientation H(K[n],-) → H(K,-)[-n]. Its opposite exact structure includes the correction
(-1)^(n(n+1)/2), prescribed below, rather than treating the raw shifts as coherent.
Source: Stacks 0A8X, 08JC (blueprint: lem-sf-site-hom-comparison-thick). -/
@[irreducible] def siteHomSourceShift (K : D) (n : ℤ) :
    ihom (K⟦n⟧) ≅ ihom K ⋙ shiftFunctor D (-n) :=
  (ihom.adjunction (K⟦n⟧)).rightAdjointUniq
    (((shiftEquiv D n).toAdjunction.comp (ihom.adjunction K)).ofNatIsoLeft
      ((tensorLeft K).commShiftIso n ≪≫ (siteHomTensorParameterShift K n).symm))
/-- The same canonical source shift with the opposite-category integer parameter.
The equality transport records -(-n)=n explicitly. Source: Stacks 08JC
(blueprint: lem-sf-site-hom-comparison-thick). -/
@[irreducible] def siteHomOppositeSourceShift (K : D) (n : ℤ) :
    ihom (K⟦-n⟧) ≅ ihom K ⋙ shiftFunctor D n :=
  siteHomSourceShift K (-n) ≪≫
    Functor.isoWhiskerLeft (ihom K) (eqToIso (congrArg (shiftFunctor D) (neg_neg n)))

end Shift

/-- Native derived internal Hom has the signed exact contravariant structure.
Source: Stacks Project, Tag 08JC, and the signed cone calculation of
lem-coef-signed-derived-internal-hom-exact
(blueprint: lem-sf-native-derived-hom-signed-exact).

Proof: represent M by a K-injective complex I. The ordinary internal Hom complex
Hom(E,I) computes the native closed derived Hom by qhInternalHomToIhom. Source
shift by m is signed reindexing, multiplying degree k by (-1)^(m*k); its transpose
under total-tensor evaluation is the adjoint mate siteHomSourceShift. Correct the
opposite shift n by (-1)^(n*(n+1)/2). The cocycle identity for this quadratic
exponent cancels the interchange sign of the two tensor shifts, giving coherent
integer shifts. Ordinary Hom sends a cone to the mapping cocone, via the identity
on Hom(G,I) and the factor (-1)^(k+1) on Hom(E,I)[-1] in degree k. This identifies
the reversed third arrow with the corrected boundary. Localize these equations;
Hom into I inverts quasi-isomorphisms, and every distinguished derived triangle is
isomorphic to a localized cone triangle. The representative comparison is
characterized by evaluation, so its transported shifts are exactly the displayed
mates in every degree, including n=0, n=1 and n=-1. -/
theorem nativeDerivedHom_signed_exact
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (M : DerivedCategory C) :
    let H := MonoidalClosed.internalHom.flip.obj M
    ∃ s : H.CommShift ℤ,
      (fun [_s : H.CommShift ℤ] ↦ H.IsTriangulated ∧
        ∀ (K : DerivedCategory C) (n : ℤ),
          (H.commShiftIso n).hom.app (op K) =
            (n * (n + 1) / 2).negOnePow •
              (siteHomOppositeSourceShift K n).hom.app M) (_s := s) := by sorry

end AlgebraicGeometry.ProEtale
