/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.TwistedPullbackScalars.TwistedPullbackScalarFamilies
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Normalized shifts of the completed tensor Tate twist

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, purity transport,
canonical cochain shifts and the degree-zero Tate line
(blueprint: def-pur-twisted-pullback-shift-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.TwistedPullbackScalars
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)
variable {X X' Y Y' : Scheme.{u}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ x : X', Invertible (l : X'.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ y : Y', Invertible (l : Y'.residueField y)]
section ShiftNormalization
variable (W : Scheme.{u}) [∀ x : W, Invertible (l : W.residueField x)] (d : ℕ)

end ShiftNormalization

section FamilyShifts
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Component form of w_(K[n])=w_K[n] under the specified canonical shifts.
Source: purity transport, shift clause
(blueprint: def-pur-twisted-pullback-shift-normalization). -/
def ShiftCompatible {A B : Scheme.{u}} (F : Family l Ω A B)
    (s : ∀ R : Fields l Ω, (F.F R).CommShift ℤ) : Prop :=
  ∀ (R S : Fields l Ω) (h : R ≤ S) (n : ℤ)
    (K : sfRationalConstructibleCategory l R.val A),
    (F.w R S h (K⟦n⟧)).hom ≫
      (F.F S).map ((Functor.commShiftIso
        (T l R.val S.val (IntermediateField.inclusion h) A)
        (self := RationalSmoothPurityCanonical.scalarShift l R.val S.val
          (IntermediateField.inclusion h) A) n).hom.app K) ≫
      (Functor.commShiftIso (F.F S) (self := s S) n).hom.app
        ((T l R.val S.val (IntermediateField.inclusion h) A).obj K) =
    (T l R.val S.val (IntermediateField.inclusion h) B).map
        ((Functor.commShiftIso (F.F R) (self := s R) n).hom.app K) ≫
      (Functor.commShiftIso (T l R.val S.val (IntermediateField.inclusion h) B)
        (self := RationalSmoothPurityCanonical.scalarShift l R.val S.val
          (IntermediateField.inclusion h) B) n).hom.app ((F.F R).obj K) ≫
      (F.w R S h K).hom⟦n⟧'

end FamilyShifts
end WeilConjectures.TwistedPullbackScalars
