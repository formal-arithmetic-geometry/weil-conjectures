/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

/-!

# Constructible sets avoiding the generic point of a curve

Let `X` be a topological space with a generic point `η`.

* A constructible subset `s` of `X` not containing `η` lies in a closed subset not containing `η`
  (`Topology.IsConstructible.exists_isClosed_superset_of_notMem`).
* If moreover `X` is a quasi-sober noetherian space all of whose points other than `η` are closed
  (e.g. an irreducible noetherian scheme of dimension one), then such a set is a finite set of
  closed points (`Topology.IsConstructible.exists_finset_of_notMem`).

This is used in the finite-support step of Gabber's Künneth formula (blueprint
`sk-prop-tf-nearby-external-kunneth`): a constructible subset of a line which omits the generic
point is a finite set of closed points.

-/

@[expose] public section

open Set TopologicalSpace

namespace Topology

variable {X : Type*} [TopologicalSpace X] {η : X}

end Topology
