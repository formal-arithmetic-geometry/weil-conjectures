/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module
public import Sheaf.Paper.IntegralHomReductionModels
import WeilConjectures.Algebra.Homology.HomComplexComponents
import Sheaf.Algebra.Homology.TensorHomEvaluationExt

/-! Finite-coordinate existence and uniqueness for the two-term Hom--tensor map.
Source: Stacks Tags 0A8X and 08J7; blueprint lem-sf-two-term-free-hom-tensor-components.
(blueprint: lem-sf-two-term-free-hom-tensor-coordinate-existence).
-/
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
namespace WeilConjectures.IntegralHom
attribute [local instance 2000] abSheafify abLocallyBijective
attribute [local irreducible] homComplexFunctor SheafOfModules.monoidalCategory

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

/-- The actual signed evaluation formula for tensoring an internal Hom complex.
The degree transport only reassociates integer addition.
Source: Stacks Tags 0A8X and 08J7, homogeneous tensor--Hom evaluation.
(blueprint: lem-sf-two-term-free-hom-tensor-coordinate-existence). -/
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
Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraph 1;
Stacks Tags 0A8X and 08J7
(blueprint: lem-sf-two-term-free-hom-tensor-coordinate-existence).

Proof: in degree j, the support hypothesis leaves the two source summands
Hom(P,I)^(j+1) tensor Q^(-1) and Hom(P,I)^j tensor Q^0. Use eNeg and eZero and the
unit tensorors to identify these with the two Hom degrees. For each p, apply the
same decomposition to (I tensor Q)^(p+j). Internal Hom out of P^p preserves this
binary product; its product over all p commutes with the binary product. Multiply
the coefficient-degree -1 coordinate at index p by (-1)^p. The resulting map is
invertible, since that sign squares to one, and has the displayed formula.
The differential of Hom is d_I v - (-1)^a v d_P, and the tensor differential on
v tensor z is d(v) tensor z + (-1)^a v tensor d(z). Substituting the signed formula
into these two differentials gives the same expression: the coefficient-differential
term has sign (-1)^(a+(b+1)*p), and the two d_P signs agree because 2*b is even.
Thus the degree maps assemble into a chain map. The product and tensor universal
properties justify testing these identities on every local pure tensor and every
section of P^p. No bound on P or I, and no special form of d_Q, is required. -/
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
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The product projections make the signed coordinate construction unique.
Source: Stacks Tags 0A8X/08J7, uniqueness of the homogeneous tensor--Hom formula
(blueprint: lem-sf-two-term-free-hom-tensor-coordinate-uniqueness).

Proof: the total tensor coproduct inclusions and Hom product projections reduce
maps to their internal Hom components on individual tensor summands. Precompose
with the inverse tensor comparison and apply the sheafification adjunction.
Naturality recovers every slice component from evaluation at identity slices.
Induction on presheaf tensors then reduces equality to the two identical signed
formulas. The support and unit-identification hypotheses are unnecessary for
uniqueness, but are retained in the statement. -/
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
    f.f j = g.f j := by
  let := countableColimits.{t, u} Y R
  let := ordinaryTensorZero.{t, u} Y R
  let : ∀ M : Modules.{t, u} Y R,
      ((ordinaryTensor.{t, u} Y R).obj M).PreservesZeroMorphisms :=
    fun M ↦ ordinaryTensorObjZero.{t, u} Y R M
  have _ := hzero
  have _ := eNeg
  have _ := eZero
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  change a + b = j at hab
  subst j
  apply homComplex_hom_ext
  intro p q hpq
  subst q
  apply tensorHomEvaluation_ext.{t + 1, t, u} R
  intro U v z x
  exact (hf a b p U v z x).trans (hg a b p U v z x).symm
end WeilConjectures.IntegralHom
