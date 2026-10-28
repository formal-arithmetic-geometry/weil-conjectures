/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module
public import Sheaf.Paper.IntegralHomReductionModels
/-! Finite-coordinate existence and uniqueness for the two-term Hom--tensor map.
Source: Stacks Tags 0A8X and 08J7; blueprint lem-sf-two-term-free-hom-tensor-components.
(blueprint: lem-sf-two-term-free-hom-tensor-components-coordinate-existence).
-/
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom
variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
/-- The actual signed evaluation formula for tensoring an internal Hom complex.
The degree transport only reassociates integer addition.
Source: Stacks Tags 0A8X and 08J7, homogeneous tensor--Hom evaluation.
(blueprint: lem-sf-two-term-free-hom-tensor-components-coordinate-existence). -/
def IsSignedHomTensor
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (f : ((totalTensor Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q ⟶
      homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
        (((totalTensor Y R).obj I).obj Q)) : Prop :=
  ∀ (a b p : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (v : (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I).X a
      |>.val.obj U)
    (z : (Q.X b).val.obj U) (x : (P.X p).val.obj U),
    evaluate Y R P (((totalTensor Y R).obj I).obj Q) (a + b) p U
        ((f.f (a + b)).val.app U
          (totalPair Y R
            (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)
            Q a b U v z)) x =
      (b * p).negOnePow •
        (eqToHom (congrArg
          (fun k : ℤ ↦ (((totalTensor Y R).obj I).obj Q).X k)
          (add_assoc p a b))).val.app U
            (totalPair Y R I Q (p + a) b U (evaluate Y R P I a p U v x) z)

/-- The finite-free coordinate construction produces an isomorphism in each total degree.
The construction uses the two surviving coefficient summands, unit tensorors, and the
product universal property of the internal Hom. Its proof is the finite-free calculation
of Stacks Tags 0A8X and 08J7, with no boundedness assumption on P or I. -/
theorem twoTermFreeHomTensor_coordinate_exists
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (eZero : Q.X 0 ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (j : ℤ) : ∃ g : ((totalTensor Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q ⟶
      homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
        (((totalTensor Y R).obj I).obj Q), IsIso (g.f j) ∧
      ∀ (a b p : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
        (v : (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I).X a
          |>.val.obj U) (z : (Q.X b).val.obj U) (x : (P.X p).val.obj U),
        evaluate Y R P (((totalTensor Y R).obj I).obj Q) (a + b) p U
          ((g.f (a + b)).val.app U
            (totalPair Y R (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
              (R := R) P I) Q a b U v z)) x =
          (b * p).negOnePow •
            (eqToHom (congrArg (fun k : ℤ ↦ (((totalTensor Y R).obj I).obj Q).X k)
              (add_assoc p a b))).val.app U
              (totalPair Y R I Q (p + a) b U (evaluate Y R P I a p U v x) z) := by sorry
/-- The product projections make the signed coordinate construction unique. Testing on
local pure tensors and then using the Hom product projections proves equality with any
chain map satisfying `IsSignedHomTensor`; this is the uniqueness half of Tags 0A8X/08J7.
(blueprint: lem-sf-two-term-free-hom-tensor-coordinate-uniqueness). -/
theorem twoTermFreeHomTensor_coordinate_unique
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (eZero : Q.X 0 ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (f g : ((totalTensor Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q ⟶
      homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
        (((totalTensor Y R).obj I).obj Q))
    (hf : IsSignedHomTensor Y R P I Q f) (j : ℤ)
    (hg : ∀ (a b p : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
        (v : (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I).X a
          |>.val.obj U) (z : (Q.X b).val.obj U) (x : (P.X p).val.obj U),
        evaluate Y R P (((totalTensor Y R).obj I).obj Q) (a + b) p U
          ((g.f (a + b)).val.app U
            (totalPair Y R (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
              (R := R) P I) Q a b U v z)) x =
          (b * p).negOnePow •
            (eqToHom (congrArg (fun k : ℤ ↦ (((totalTensor Y R).obj I).obj Q).X k)
              (add_assoc p a b))).val.app U
              (totalPair Y R I Q (p + a) b U (evaluate Y R P I a p U v x) z)) :
    f.f j = g.f j := by sorry
end WeilConjectures.IntegralHom
