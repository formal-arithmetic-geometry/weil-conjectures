/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q1, C3
-/
module

public import Mathlib.CategoryTheory.Shift.CommShiftTwo
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Coherence laws for the signed source-Hom mates

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

section SignedShift
variable {D : Type d} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [MonoidalCategory D] [MonoidalClosed D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]

/-- The prescribed signed source-Hom map for the triangulated opposite shift.
Source: Stacks Project, Tag 08JC
(blueprint: lem-sf-native-hom-signed-shift-laws). -/
def siteHomSignedSourceComponent (M : D) (n : ℤ) (X : Dᵒᵖ) :
    (MonoidalClosed.internalHom.flip.obj M).obj (X⟦n⟧) ⟶
      ((MonoidalClosed.internalHom.flip.obj M).obj X)⟦n⟧ :=
  (n * (n + 1) / 2).negOnePow • (siteHomOppositeSourceShift X.unop n).hom.app M

/-- The signed mates have the correct zero component and satisfy addition
coherence, stated before assembling a `CommShift` structure.
Source: Stacks Project, Tags 08J9 and 08JC, signed total-tensor evaluation
(blueprint: lem-sf-native-hom-signed-shift-laws).

Proof: write T_K for tensorLeft K, c_K^r for its argument-shift
comparison, and t_K^r for the parameter-shift comparison. The raw source
shift is the right-adjoint mate of c_K^r followed by (t_K^r) inverse.
At zero the two CommShift zero laws cancel the middle zero unitor and its
inverse. The composite on L becomes K tensor the zero-unitor map on L,
followed by the inverse zero-unitor map on K tensor L. Taking mates gives
precomposition by the inverse zero unitor on K followed by the inverse
zero unitor on ihom K. The opposite zero-unitor formula is precisely the
zero equation below, and q(0)=0 contributes no scalar.

For addition expand the successive mates using conjugateEquiv_comp and the
units and counits of the two shift adjunctions. Move the parameter shift
past the argument shift once. The CommShift₂Int.comm identity changes
c_(K[m])^n followed by the n-shift of t_K^m into t_K^m at L[n], followed
by the m-shift of c_K^n, shiftComm inverse, and (-1)^(m*n). Combine the
remaining argument shifts by their addition law and likewise the parameter
shifts. The shift adjunction triangles cancel adjacent units and counits;
the remaining shiftComm reverses the opposite-shift order. Applying this
with -m,-n gives the raw version of the displayed addition equation with
one extra factor (-1)^(m*n). Tensor and ihom are additive, so that scalar
passes through the transposition. Finally q(t)=t*(t+1)/2 satisfies
q(m+n)=q(m)+q(n)+m*n: expand the numerators and divide the exact equality
by 2, using that t*(t+1) is even for every integer. Thus multiplication by
the prescribed quadratic signs cancels the extra factor, including for
negative m and n. This gives exactly the second displayed equation. -/
theorem siteHom_signed_source_shift_laws [MonoidalPreadditive D] (M : D) :
    let H := MonoidalClosed.internalHom.flip.obj M
    (∀ X : Dᵒᵖ, siteHomSignedSourceComponent M 0 X =
      (Functor.CommShift.isoZero H ℤ).hom.app X) ∧
    (∀ (m n : ℤ) (X : Dᵒᵖ), siteHomSignedSourceComponent M (m + n) X =
      H.map ((shiftFunctorAdd Dᵒᵖ m n).hom.app X) ≫
        siteHomSignedSourceComponent M n (X⟦m⟧) ≫
        (siteHomSignedSourceComponent M m X)⟦n⟧' ≫
        (shiftFunctorAdd D m n).inv.app (H.obj X)) := by sorry

end SignedShift

end AlgebraicGeometry.ProEtale
