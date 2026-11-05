/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.MPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Free
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle

/-!
# Local pseudo-coherence of a localization cone

Source: Stacks Project, More on Algebra, Tag 066D, local cone step,
and Tag 064R, first distinguished-triangle assertion.
(blueprint: lem-pc-m-pseudo-coherent-localization-cone-local).
-/

@[expose] public section

universe w₁ w₂ v₁ u₁

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

-- The unused hypotheses belong to the unchanged interface of the cone construction.

end DerivedCategory
