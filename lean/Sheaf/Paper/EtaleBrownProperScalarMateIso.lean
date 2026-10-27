/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.EtaleBrownProjectionRealization

/-! # Invertibility of the proper Brown scalar mate

Source: Zheng, Constructions 4.1 and 5.14--5.15 and Lemma 5.16;
Stacks 0F0G, 06YY and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

/-- The proper geometric mate used by the Brown projection is invertible.
Source: Zheng, Lemma 5.16; Stacks 0F0G and 07A4.
(blueprint: lem-pur-etale-brown-proper-scalar-mate-is-iso).

The proof is the finite-coefficient proper projection argument after restriction to
ordinary scalars. The normalized direct-image comparison and scalar pullback mate
are isomorphisms; the finite proper projection formula makes the remaining scalar
mate invertible, and exact restriction of scalars reflects isomorphisms. -/
theorem etaleBrownProperScalarMate_isIso
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) [IsProper g]
    (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (rg : ∀ n, StrictEtaleBrownImageRealization O t g n A (B.level n) RV RW)
    {m n : ℕ} (h : m ≤ n) [Finite (strictEtaleBrownRing O t n)] :
    IsIso ((mateEquiv (B.level n).adjunction (B.level m).adjunction
      (.mk _ _ _ _ (B.derivedTensor h).hom)).natTrans) := by
  sorry

end AlgebraicGeometry
