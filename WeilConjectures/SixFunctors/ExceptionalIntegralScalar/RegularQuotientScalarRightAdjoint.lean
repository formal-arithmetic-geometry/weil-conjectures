/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.SixFunctors.Regular.RegularQuotientTraceIsIso
import WeilConjectures.SixFunctors.Regular.RegularQuotientRestrictionBounds
import WeilConjectures.SixFunctors.Regular.RegularQuotientRestrictionComplete

/-! # Regular quotient extension is a right adjoint on finite-Tor categories

Regular quotient extension, restricted to the prescribed finite-Tor categories, has a left
adjoint, namely restriction followed by `[-1]`.

## Implementation details

The quotient `B = A/π^(n+1)` of the completed coefficient sheaf `A` has a locally free
resolution of length one, whose algebra-valued dual is `B[-1]`; hence derived coinduction is
derived extension followed by `[-1]`. Restriction of a bounded finite-Tor constructible
`B`-complex is derived complete, and its reductions stay constructible with Tor interval enlarged
by at most one, so the adjunction restricts to the finite-Tor categories. The realization of the
ring-level duality formula on the specified sheaf categories is part of this argument.

## References

* [Zheng, Lemma 5.22 and Proposition 5.26]
* [Stacks, Tag 0A70], [Stacks, Tag 0A71] (perfect coefficient duality and coinduction)
* [Stacks, Tag 06YY], [Stacks, Tag 07A6] (derived change of coefficients)
* [Stacks, Tag 0BZH], [Stacks, Tag 0BZE] (regular-quotient duality, perfect-algebra evaluation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

attribute [-instance] PrincipalKoszulStrictReplacement.siteSmall
  PrincipalKoszulStrictReplacement.abSheafify PrincipalKoszulStrictReplacement.abLocallyBijective
  integralCoefficientAbSheafify integralCoefficientAbLocallyBijective
  scalarReductionSourceDerived scalarReductionTargetDerived
  GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] HasDerivedCategory.standard

private local instance (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
private local instance (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} T
private local instance (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} T
attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits

private noncomputable def reverseShiftAdjunction
    {A B : Type*} [Category* A] [Category* B] [HasShift A ℤ]
    {U : B ⥤ A} {G F : A ⥤ B} (a : U ⊣ G)
    (e : G ≅ shiftFunctor A (-1 : ℤ) ⋙ F) :
    U ⋙ shiftFunctor A (-1 : ℤ) ⊣ F := by
  let s : shiftFunctor A (-1 : ℤ) ⊣ shiftFunctor A (1 : ℤ) :=
    (shiftEquiv' A (-1 : ℤ) 1 (by omega)).toAdjunction
  let aa : U ⋙ shiftFunctor A (-1 : ℤ) ⊣ shiftFunctor A (1 : ℤ) ⋙ G := a.comp s
  let ee : shiftFunctor A (1 : ℤ) ⋙ G ≅ F :=
    Functor.isoWhiskerLeft (shiftFunctor A (1 : ℤ)) e ≪≫
      (Functor.associator _ _ F).symm ≪≫
      Functor.isoWhiskerRight (shiftFunctorCompIsoId A 1 (-1 : ℤ) (by omega)) F ≪≫
      F.leftUnitor
  exact aa.ofNatIsoRight ee

private theorem restrictReverseAdjunction
    (l : ℕ) [Fact l.Prime]
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : FieldStage.{u} l) (n : ℕ) (T : Scheme.{u})
    (S : Scalar.{u, u} l Ω (s := .integral E)
      (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n)) T)
    (U : DerivedCategory (pbcModules.{u} T
        (((RingStage.finite.{u} E ⟨n + 1, Nat.succ_pos n⟩).coefficients l).ring T)) ⥤
      DerivedCategory (pbcModules.{u} T (((RingStage.integral.{u} E).coefficients l).ring T)))
    (a : U ⊣ pbcDerivedExtend.{u}
      ((PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n)).map T))
    (hU : ∀ K : C.{u, u} l Ω T (.finite E ⟨n + 1, Nat.succ_pos n⟩),
      finiteTorConstructibleIntegral l E.carrier T (U.obj K.obj)) :
    S.functor.IsRightAdjoint := by
  let L := (finiteTorConstructibleIntegral l E.carrier T).lift
    (RingStage.inclusion.{u, u} l Ω T (.finite E ⟨n + 1, Nat.succ_pos n⟩) ⋙ U) hU
  exact (a.restrictFullyFaithful
    (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) T).fullyFaithfulι
    (finiteTorConstructibleIntegral l E.carrier T).fullyFaithfulι
    (L := L) (R := S.functor) (Iso.refl _) S.realization.symm).isRightAdjoint

private theorem regularQuotientScalarRightAdjoint_of_trace
    (l : ℕ) [Fact l.Prime]
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : FieldStage.{u} l) (n : ℕ) (T : Scheme.{u})
    (S : Scalar.{u, u} l Ω (s := .integral E)
      (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n)) T)
    (ht : IsIso (reductionCoinductionTrace.{u} l E.carrier T n))
    (hb : ∀ (K : DerivedCategory (scalarReductionTarget.{u, u} l E.carrier T n)),
      finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) T K →
      ∃ a b : ℤ, a ≤ b ∧ ∀ m : ℕ,
        intrinsicFiniteTorsionConstructible l E.carrier (m + 1) (Nat.succ_pos m) T
            ((scalarReductionDerivedExtension.{u, u} l E.carrier T m).obj
              ((scalarReductionDerivedRestriction.{u, u} l E.carrier T n).obj K)) ∧
          proEtaleCohomologicalSupport
            ((scalarReductionDerivedExtension.{u, u} l E.carrier T m).obj
              ((scalarReductionDerivedRestriction.{u, u} l E.carrier T n).obj K)) ⊆ Set.Icc a b ∧
          HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E.carrier (m + 1))
            ((scalarReductionDerivedExtension.{u, u} l E.carrier T m).obj
              ((scalarReductionDerivedRestriction.{u, u} l E.carrier T n).obj K)) a b) :
    S.functor.IsRightAdjoint := by
  let := ht
  let U := scalarReductionDerivedRestriction.{u, u} l E.carrier T n
  let V := U ⋙ shiftFunctor _ (-1 : ℤ)
  let a := (reverseShiftAdjunction
    (scalarReductionDerivedCoinductionAdjunction l E.carrier T n)
    (asIso (reductionCoinductionTrace l E.carrier T n)).symm).ofNatIsoRight
      (reductionCochainModelIso l E.carrier T n ≪≫
        (PurCompactSupport.finiteReductionIso l E.carrier T n).symm)
  have hU (K : C.{u, u} l Ω T (.finite E ⟨n + 1, Nat.succ_pos n⟩)) :
      finiteTorConstructibleIntegral l E.carrier T (U.obj K.obj) := by
    obtain ⟨c, d, hcd, h⟩ := hb K.obj K.property
    exact ⟨⟨scalarReductionDerivedRestriction_complete l E.carrier T n K.obj,
      c, d, hcd, fun m ↦ ⟨(h m).1, (h m).2.1⟩⟩,
      c, d, hcd, fun m ↦ (h m).2.2⟩
  have : (finiteTorConstructibleIntegral l E.carrier T).IsTriangulated :=
    integralTriangulated l E T
  exact restrictReverseAdjunction l Ω E n T S V a (fun K ↦
    (finiteTorConstructibleIntegral l E.carrier T).le_shift (-1 : ℤ) _ (hU K))

/-- Regular quotient extension, restricted to the prescribed finite-Tor categories,
has a left adjoint. This assertion contains no geometric operation or compactification. -/
theorem regularQuotientScalarRightAdjoint
    (l : ℕ) [Fact l.Prime]
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : FieldStage.{u} l) (n : ℕ) (T : Scheme.{u})
    (S : Scalar.{u} l Ω (s := .integral E)
      (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n)) T) :
    S.functor.IsRightAdjoint := by
  exact regularQuotientScalarRightAdjoint_of_trace l Ω E n T S
    (reductionCoinductionTrace_isIso l E.carrier T n)
    (scalarReductionDerivedRestriction_bounds l E.carrier T n)

end WeilConjectures.ExceptionalIntegralScalar
