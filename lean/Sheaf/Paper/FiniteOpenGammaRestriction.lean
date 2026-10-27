/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteOpenProductSwap

/-! # Restriction of the published finite open projection formula

Source: Stacks 0GL1 and 0E8I, lemma-j-shriek-and-tensor
(blueprint: lem-pur-finite-open-gamma-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicGeometry
open SheafOfModules.OpenTensorNormalization
namespace WeilConjectures.FiniteOpenProduct

/-- The canonical open derived adjunction has invertible unit.
Source: Stacks 03DI, exact localization of the open adjunction
(blueprint: lem-pur-finite-open-gamma-restriction). -/
instance finiteOpenUnit_isIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : IsIso (adj A j).unit := by
  exact Adjunction.isIso_mapDerivedCategoryAdjunction_unit
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)

/-- The extension-first projection map has the prescribed open-unit transpose.
Source: Stacks 0GL1 and 0E8I, lemma-j-shriek-and-tensor; Step 1 of
lem-pur-two-open-tensor-chain-normalization
(blueprint: lem-pur-finite-open-gamma-restriction).

Proof: the published projection map p is the adjoint transpose of the tensor
of the open unit with the identity, followed by the inverse mixed tensor
comparison t. Hence eta followed by pull(p) equals tensor(eta,1) followed by t.
Cancel pull(p), using the actual projection isomorphism and the invertible
open unit, to obtain pull(p inverse) = t inverse followed by tensor(eta inverse,1)
and eta. The definition of gamma then postcomposes p inverse by extension of
the comparison from left-derived to exact pullback in its second tensor input.
Naturality of eta moves this factor before the final eta. Expand t and the
published tensorPullIso; they have the same pullback identification and derived
tensor comparison. Naturality of the tensor bifunctor moves the second-input
comparison past tensor(eta inverse,1), giving exactly the displayed formula. -/
theorem finiteOpenGammaRestriction (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : FiniteD A U) (N : FiniteD A X) :
    (pull A j).map (gamma A j M N) =
      (tensorPullIso A j ((finiteShriek A j).obj M) N).hom ≫
        tensorMap A U (inv ((adj A j).unit.app M)) (𝟙 ((pull A j).obj N)) ≫
        (adj A j).unit.app (tensor A U M ((pull A j).obj N)) := by sorry

end WeilConjectures.FiniteOpenProduct
