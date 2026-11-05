/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.ConePseudoCoherent
import WeilConjectures.RingTheory.FiniteHomologyOfMPseudoCoherent
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.RingTheory.FiniteScalarSurjections
import WeilConjectures.RingTheory.FiniteConeCycleAttachmentFunctors

/-! # One descending step in a simultaneous finite free approximation

Source: Stacks Project, Tag 08EE, proof of lemma-lift-pseudo-coherent.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace DerivedCategory

end DerivedCategory
