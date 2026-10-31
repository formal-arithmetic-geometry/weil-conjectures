/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenProperClopenWitness

import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenInjectiveProperAcyclicOpenRestriction
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenInjectiveProperAcyclicBoundaryRestriction
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedDetection

/-!
# Acyclicity from a clopen geometric witness

This is the sheaf-theoretic part of the proper/open acyclicity argument.  Its
geometric input is isolated in `OpenProperClopenWitness`.
(blueprint: lem-sp-proetale-open-injective-proper-acyclic-from-witness)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The pro-etale acyclicity conclusion from the clopen geometric factorisation.

Source: Weil blueprint, `sec-smooth-purity/sk-prop-sf-existence`, clause (b),
with the geometric factorisation supplied by
`OpenProperClopenWitness`.  The proof uses the open--closed sequence, derived
open restriction, and the proper-boundary cohomology argument.
(blueprint: lem-sp-proetale-open-injective-proper-acyclic-from-witness)
-/
theorem isZero_higherDirectImage_open_injective_of_proper_of_witness
    (A : Type u) [CommRing A] [Finite A]
    {B D C E : Scheme.{u}} (p : B ⟶ D) (r : C ⟶ E)
    (k : C ⟶ B) (i : E ⟶ D)
    [IsProper p] [IsProper r]
    [IsOpenImmersion k] [QuasiCompact k]
    [IsOpenImmersion i] [QuasiCompact i]
    (hcomm : k ≫ p = r ≫ i)
    (J : proEtaleRingModules C (proEtaleConstantRing C A)) [Injective J]
    (w : OpenProperClopenWitness p r k i) :
    ∀ q : ℕ, 0 < q →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules D (proEtaleConstantRing D A)) (q : ℤ)).obj
        ((proEtaleConstantDerivedDirectImage p A).obj
          ((DerivedCategory.singleFunctor
            (proEtaleRingModules B (proEtaleConstantRing B A)) 0).obj
            ((sfIntrinsicExtensionByZero k A).obj J)))) := by
  intro q hq
  apply proEtaleRingModule_isZero_of_open_closed i.closedComplement i
    (by rw [i.range_closedComplement, compl_compl])
    (proEtaleConstantRing D A) (proEtaleConstantRing _ A) (proEtaleConstantRing E A)
    (proEtaleConstantRingComparison i.closedComplement A)
    (proEtaleConstantRingComparison i A)
  · exact isZero_openRestriction_higherDirectImage_open_injective_of_proper
      A p r k i hcomm J q hq
  · exact isZero_boundaryRestriction_higherDirectImage_open_injective_of_proper
      A p r k i hcomm J w q hq

end AlgebraicGeometry.Scheme
