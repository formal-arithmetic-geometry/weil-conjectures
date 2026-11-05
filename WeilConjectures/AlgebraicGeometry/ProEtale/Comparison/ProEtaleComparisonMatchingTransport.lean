/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport

/-! # Transport of matching families to fpqc descent data

Source: Stacks Project, Tag 0GLZ, first paragraph; Tag 09XN.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

-- The base change of an identity is terminal, with its explicit inverse pullback lift.

-- Inverse-image restriction evaluated on terminal sections.

-- Terminal transport after cancelling the second-projection isomorphism.

end AlgebraicGeometry
