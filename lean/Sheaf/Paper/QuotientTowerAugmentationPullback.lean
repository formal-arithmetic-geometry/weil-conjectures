/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.Paper.CompletionMateComparison

/-! # Pullback and the canonical augmentation of the strict quotient tower -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion

namespace CategoryTheory.AdicSites

variable {Y X : Site.{u}} {A : Type u} [CommRing A] {I : Ideal A}

/-- The actual quotient augmentation, transposed from the prescribed completion unit.
This construction uses the fixed constant-tower/derived-limit adjunction.
Source: Stacks 0941 and 099M
(blueprint: lem-pur-quotient-tower-augmentation-pullback). -/
def Site.quotientAugmentation (T : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A) :
    T.delta A ⟶ T.reduction A I where
  app M := ((T.deltaAdjunction A).homEquiv M ((T.reduction A I).obj M)).symm
    ((T.unit A I).app M)
  naturality M N q := by
    apply ((T.deltaAdjunction A).homEquiv _ _).injective
    rw [(T.deltaAdjunction A).homEquiv_naturality_left,
      (T.deltaAdjunction A).homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact (T.unit A I).naturality q

/-- Pullback carries the actual quotient augmentation to the quotient augmentation.
No perfectness, flatness of the quotient map, or completeness of the input is needed.

Source: Stacks, Cohomology on Sites, Tags 07A4 and 0941; More on Algebra,
Tag 099M; completed projection coherence, proof Steps 3, 4 and 10
(blueprint: lem-pur-quotient-tower-augmentation-pullback).

Proof: Choose one flat-term K-flat representative P of M. Its diagonal is K-flat
because tensoring an acyclic tower is acyclic at every index. The ordinary quotient
augmentation in every degree sends m to 1 tensor m. The defining insertion equation
for moduleReductionPullIso says precisely that applying pullback to this map and
then its quotient comparison equals the quotient augmentation after pullback.
It holds simultaneously at every index and respects all transition maps.
Apply this equation termwise to P and localize. The normalized reductionPullIso
comparison identifies the two reduced complexes. The prescribed completion-unit
formula and the normalized constant-tower/derived-limit adjunction identify the
adjunct of that localized augmentation with Site.unit, so the augmentation is
exactly quotientAugmentation. Transport through the resolution isomorphism and
use naturality. This proves the equality on every ambient derived object. -/
theorem quotientAugmentation_pullback (f : Morphism Y X) (M : Y.derived A) :
    (f.towerPull A).map ((Y.quotientAugmentation A I).app M) ≫
        (f.reductionPullIso A I).hom.app M =
      (f.constantPullIso A).hom.app M ≫
        (X.quotientAugmentation A I).app ((f.pull A).obj M) := by
  sorry

end CategoryTheory.AdicSites
