/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleLevelData
public import Submission.WeilConjectures.AlgebraicGeometry.Etale.EtaleUniversalNormalization
import Submission.WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The constant half of the finite perfect normalization diagram

Source: Stacks Project, Tags 09C6, 06YY and 093J.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Coefficient transport along the lifted ring equivalence is an equivalence.
Source: Stacks Tag 05RU.
(blueprint: def-weil-pbc-finite-perfect-adic-constant-normalization). -/
instance finitePerfectAdicLiftRestrictEquivalence (B : Type t) [CommRing B] :
    (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).IsEquivalence :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{t + 1}
    (ULift.ringEquiv : ULift.{t + 1} B ≃+* B)).isEquivalence_functor

/-- Coefficient transport along the lifted ring equivalence preserves limits.
Source: Stacks Tag 05RU.
(blueprint: def-weil-pbc-finite-perfect-adic-constant-normalization). -/
instance finitePerfectAdicLiftRestrictLimits (B : Type t) [CommRing B] :
    PreservesLimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom) :=
  Adjunction.isEquivalencePreservesLimits _

/-- Coefficient transport along the lifted ring equivalence preserves colimits.
Source: Stacks Tag 05RU.
(blueprint: def-weil-pbc-finite-perfect-adic-constant-normalization). -/
instance finitePerfectAdicLiftRestrictColimits (B : Type t) [CommRing B] :
    PreservesColimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom) :=
  Adjunction.isEquivalence_preservesColimits _

/-- The coefficient-universe lift commutes with restriction of scalars.
Source: Stacks Tag 05RU; both termwise functors have the identical lifted action.
(blueprint: def-weil-pbc-finite-perfect-adic-constant-normalization). -/
def finitePerfectAdicAlgebraLiftRestrict {B D : Type t} [CommRing B] [CommRing D]
    (q : B →+* D) :
    finitePerfectAdicAlgebraLift D ⋙ normalizationModuleRestrict (RingHom.ulift q) ≅
      (ModuleCat.restrictScalars.{t} q).mapDerivedCategory ⋙
        finitePerfectAdicAlgebraLift B := by
  let L (R : Type t) [CommRing R] := ModuleCat.uliftFunctor.{t + 1, t} R ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} R ≃+* R).toRingHom
  let e : ModuleCat.restrictScalars.{t} q ⋙ L B ≅
      L D ⋙ ModuleCat.restrictScalars.{t + 1} (RingHom.ulift q) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  exact (Functor.mapDerivedCategorySquareIso e).symm

/-- Lift the specified algebraic transition, using the coefficient interchange.
Source: Stacks Tag 09C6, the arrows of the normalized algebraic diagram.
(blueprint: def-weil-pbc-finite-perfect-adic-constant-normalization). -/
def finitePerfectAdicLiftedTransition {A : Type t} [CommRing A]
    {d : AdicCoefficientDatum A} (T : FinitePerfectAdicAlgebraTower d) (n : ℕ) :
    (finitePerfectAdicAlgebraLift _).obj (T.level (n + 1)) ⟶
      (normalizationModuleRestrict
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).obj
          ((finitePerfectAdicAlgebraLift _).obj (T.level n)) :=
  (finitePerfectAdicAlgebraLift _).map (T.transition n) ≫
    (finitePerfectAdicAlgebraLiftRestrict
      (Ideal.Quotient.factorPowSucc d.ideal (n + 1))).inv.app (T.level n)

/-- The actual constant etale model of an algebraic level.
Source: Stacks Tags 09C6 and 093J.
(blueprint: def-weil-pbc-finite-perfect-adic-constant-normalization). -/
def finitePerfectAdicEtaleConstant (Y : Scheme.{t}) {A : Type t} [CommRing A]
    {d : AdicCoefficientDatum A} (T : FinitePerfectAdicAlgebraTower d) (n : ℕ) :=
  (normalizationConstant Y.smallEtaleTopology).obj
    ((finitePerfectAdicAlgebraLift _).obj (T.level n))

/-- The specified normalization arrow between the constant etale models.
Source: Stacks Tags 09C6 and 06YY.
(blueprint: def-weil-pbc-finite-perfect-adic-constant-normalization). -/
def finitePerfectAdicEtaleConstantTransition (Y : Scheme.{t})
    {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    (T : FinitePerfectAdicAlgebraTower d) (n : ℕ) :=
  normalizationConstantArrow Y.smallEtaleTopology _ (finitePerfectAdicLiftedTransition T n)

end AlgebraicGeometry.Scheme
