/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck

/-!
# Composable pairs and acyclicity

Source: blueprint, node def-sp-composite-acyclicity; Stacks Project, Derived Categories,
Section 13.22, Lemma 13.22.1 (Tag 015M) (blueprint: def-sp-composite-acyclicity).

## Main definitions

- `CategoryTheory.GrothendieckComposablePair`: a pair of left exact additive functors.
- `CategoryTheory.GrothendieckComposablePair.SendsInjectivesToAcyclics`: its acyclicity
  condition.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

end CategoryTheory
